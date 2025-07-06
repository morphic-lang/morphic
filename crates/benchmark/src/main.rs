#![allow(dead_code)]

use morphic_common::config::{
    self as cfg, ArrayKind, ArtifactDir, GcKind, ProfileMode, RcStrategy,
};
use morphic_common::file_cache::FileCache;
use morphic_common::progress_ui::ProgressMode;
use morphic_compiler::build;

use rand::{Rng, SeedableRng};
use rand_pcg::Pcg64;
use serde::Deserialize;
use serde::Serialize;
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
use std::path::PathBuf;
use std::process;
use std::time::Duration;

fn drive_subprocess(
    mut child: process::Child,
    iters: u64,
    extra_stdin: &str,
    expected_stdout: &str,
) {
    write!(child.stdin.as_mut().unwrap(), "{}\n{}", iters, extra_stdin)
        .expect("Could not write iteration to child stdin");

    child
        .stdin
        .as_mut()
        .unwrap()
        .flush()
        .expect("Could not flush child stdin");

    let output = child.wait_with_output().expect("Waiting on child failed");

    assert!(
        output.status.success() && &output.stdout as &[u8] == expected_stdout.as_bytes(),
        "Child process failed:\n\
         Exit status: {:?}\n\
         Stderr:\n{}\n\
         Expected stdout: {:?}\n\
         Actual stdout: {:?}",
        output.status.code(),
        String::from_utf8(output.stderr).unwrap(),
        expected_stdout,
        String::from_utf8_lossy(&output.stdout),
    );
}

fn run_exe<Report: for<'a> Deserialize<'a>>(
    exe_path: impl AsRef<Path>,
    iters: u64,
    extra_stdin: &str,
    expected_stdout: &str,
) -> Report {
    let report_path = tempfile::Builder::new()
        .prefix(".tmp-report-")
        .suffix(".json")
        .tempfile_in("")
        .expect("Could not create temp file")
        .into_temp_path();

    // let child = process::Command::new("valgrind")
    //     .args(["--leak-check=full", "--error-exitcode=1"])
    //     .arg(exe_path.as_ref().canonicalize().unwrap())
    //     .env("MORPHIC_PROFILE_PATH", &report_path)
    //     .stdin(process::Stdio::piped())
    //     .stdout(process::Stdio::piped())
    //     .stderr(process::Stdio::piped())
    //     .spawn()
    //     .expect("Could not spawn child process");

    if !exe_path.as_ref().exists() {
        panic!("Executable does not exist: {}", exe_path.as_ref().display());
    }

    let child = process::Command::new(exe_path.as_ref().canonicalize().unwrap())
        .env("MORPHIC_PROFILE_PATH", &report_path)
        .stdin(process::Stdio::piped())
        .stdout(process::Stdio::piped())
        .stderr(process::Stdio::piped())
        .spawn()
        .expect("Could not spawn child process");

    drive_subprocess(child, iters, extra_stdin, expected_stdout);

    let report: Report = serde_json::from_reader(BufReader::new(
        File::open(&report_path).expect("Failed to open child performance report file"),
    ))
    .expect("Failed to read child performance report file");

    report
}

const BINARY_SIZES_DIR: &str = "target/binary_sizes";

fn write_binary_size(benchmark_name: &str, exe_path: impl AsRef<Path>) {
    let disp = exe_path.as_ref().display();
    let size = exe_path
        .as_ref()
        .metadata()
        .expect(&format!("Could not get metadata for binary {}", disp))
        .len();

    std::fs::create_dir_all(BINARY_SIZES_DIR).expect("Could not create binary sizes directory");

    let mut file = File::create(format!("{}/{}.txt", BINARY_SIZES_DIR, benchmark_name))
        .expect("Could not create binary size file");

    writeln!(file, "{}", size).expect("Could not write binary size to file");
}

const RUN_TIME_DIR: &str = "target/run_time";

fn write_run_time(benchmark_name: &str, data: Vec<Duration>) {
    std::fs::create_dir_all(RUN_TIME_DIR).expect("Could not create run_time directory");

    let mut file = File::create(format!("{}/{}.txt", RUN_TIME_DIR, benchmark_name))
        .expect("Could not create run time file");

    let nanoseconds: Vec<u128> = data.iter().map(|d| d.as_nanos()).collect();

    writeln!(file, "{}", serde_json::to_string(&nanoseconds).unwrap())
        .expect("Could not write run time to file");
}

#[derive(Clone, Copy, Serialize)]
struct RcCounts {
    total_retain_count: u64,
    total_release_count: u64,
    total_rc1_count: u64,
}

const RC_COUNT_DIR: &str = "target/rc_count";

fn write_rc_counts(benchmark_name: &str, data: Vec<RcCounts>) {
    std::fs::create_dir_all(RC_COUNT_DIR).expect("Could not create rc_count directory");

    let mut file = File::create(format!("{}/{}.txt", RC_COUNT_DIR, benchmark_name))
        .expect("Could not create rc counts file");

    writeln!(file, "{}", serde_json::to_string(&data).unwrap())
        .expect("Could not write rc counts to file");
}

#[derive(Clone, Debug, Deserialize)]
#[serde(transparent)]
struct MlProfReport {
    entries: Vec<MlProfReportEntry>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct MlProfReportEntry {
    func_id: u64,
    total_calls: u64,
    total_clock_nanos: u64,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProfReport {
    clock_res_nanos: u64,
    timings: Vec<ProfTiming>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProfTiming {
    module: Vec<String>,
    function: String,
    specializations: Vec<ProfSpecialization>,
    skipped_tail_rec_specializations: Vec<ProfSkippedTail>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProfSpecialization {
    low_func_id: u64,
    total_calls: u64,
    total_clock_nanos: u64,
    total_retain_count: Option<u64>,
    total_release_count: Option<u64>,
    total_rc1_count: Option<u64>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProfSkippedTail {
    low_func_id: u64,
    tail_func_id: u64,
}

const OUT_DIR: &str = "out2";

fn build_exe(
    bench_name: &str,
    tag: &str,
    src_path: impl AsRef<Path> + Clone,
    profile_mod: &[&str],
    profile_func: &str,
    variant: &Variant,
) -> (PathBuf, ArtifactDir) {
    let variant_name = format!("{bench_name}-{tag}");

    if !std::env::current_dir().unwrap().join(OUT_DIR).exists() {
        std::fs::create_dir(std::env::current_dir().unwrap().join(OUT_DIR)).unwrap();
    }

    let exe_path = std::env::current_dir()
        .unwrap()
        .join(OUT_DIR)
        .join(variant_name.clone());

    let artifact_path = std::env::current_dir()
        .unwrap()
        .join(OUT_DIR)
        .join(format!("{bench_name}-{tag}-artifacts"));

    let artifact_dir = ArtifactDir {
        dir_path: artifact_path.clone(),
        filename_prefix: exe_path.file_name().unwrap().into(),
    };

    if !artifact_dir.dir_path.exists() {
        std::fs::create_dir(artifact_dir.dir_path.clone()).unwrap();
    }

    let mut files = FileCache::new();

    build(
        variant.build_config(
            src_path.as_ref().to_path_buf(),
            profile_mod,
            profile_func,
            exe_path.clone(),
            Some(artifact_dir.clone()),
        ),
        &mut files,
    )
    .expect("Compilation failed");

    (exe_path, artifact_dir)
}

#[derive(Clone, Debug)]
struct LlvmVariant {
    rc_strat: RcStrategy,
    profile_mode: ProfileMode,
    gc_kind: GcKind,
    array_kind: ArrayKind,
}

#[derive(Clone, Debug)]
struct MlVariant {
    variant: cfg::MlVariant,
    stage: cfg::CompilationStage,
}

#[derive(Clone, Debug)]
enum Variant {
    Llvm(LlvmVariant),
    Ml(MlVariant),
}

impl Variant {
    fn tag(&self) -> String {
        match self {
            Variant::Llvm(llvm_variant) => {
                let profile_mode_str = match llvm_variant.profile_mode {
                    ProfileMode::RecordRc => "record_counts",
                    ProfileMode::NoRecordRc => "record_time",
                };
                format!(
                    "{}-{}-{}-{}",
                    llvm_variant.rc_strat.to_str(),
                    profile_mode_str,
                    llvm_variant.gc_kind.to_str(),
                    llvm_variant.array_kind.to_str(),
                )
            }
            Variant::Ml(ml_variant) => {
                let ml_variant_str = match ml_variant.variant {
                    cfg::MlVariant::Sml => "sml",
                    cfg::MlVariant::OCaml => "ocaml",
                };
                format!("{}-{}", ml_variant_str, ml_variant.stage.to_str())
            }
        }
    }

    fn record_rc(&self) -> bool {
        match self {
            Variant::Llvm(llvm_variant) => llvm_variant.profile_mode == ProfileMode::RecordRc,
            Variant::Ml(_) => false,
        }
    }

    fn build_config(
        &self,
        src_path: PathBuf,
        profile_mod: &[&str],
        profile_func: &str,
        output_path: PathBuf,
        artifact_dir: Option<ArtifactDir>,
    ) -> cfg::BuildConfig {
        let profile_syms = vec![cfg::SymbolName(format!(
            "{mod_}{func}",
            mod_ = profile_mod
                .iter()
                .map(|component| format!("{}.", component))
                .collect::<Vec<_>>()
                .concat(),
            func = profile_func,
        ))];
        match self {
            Variant::Llvm(llvm_variant) => {
                let llvm_config = cfg::LlvmConfig {
                    rc_strat: llvm_variant.rc_strat,
                    gc_kind: llvm_variant.gc_kind,
                    array_kind: llvm_variant.array_kind,
                    opt_level: cfg::default_llvm_opt_level(),
                    target: cfg::TargetConfig::Native,
                };
                cfg::BuildConfig {
                    src_path,
                    progress: ProgressMode::Visible,
                    purity_mode: cfg::PurityMode::Checked,
                    defunc_mode: cfg::DefuncMode::Specialize,
                    backend_opts: cfg::BackendOptions::Llvm(llvm_config),
                    profile_syms,
                    profile_mode: llvm_variant.profile_mode,
                    output_path,
                    artifact_dir,
                }
            }
            Variant::Ml(ml_variant) => {
                let ml_config = cfg::MlConfig {
                    variant: ml_variant.variant,
                    stage: ml_variant.stage,
                };
                cfg::BuildConfig {
                    src_path,
                    progress: ProgressMode::Visible,
                    purity_mode: cfg::PurityMode::Checked,
                    defunc_mode: cfg::DefuncMode::Specialize,
                    backend_opts: cfg::BackendOptions::Ml(ml_config),
                    profile_syms,
                    profile_mode: ProfileMode::NoRecordRc,
                    output_path,
                    artifact_dir,
                }
            }
        }
    }
}

fn variants() -> Vec<Variant> {
    let mut variants = Vec::new();

    // Run time and retain count comparison with Perceus.
    for rc_strat in [RcStrategy::Default, RcStrategy::Perceus] {
        for profile_mode in [ProfileMode::RecordRc, ProfileMode::NoRecordRc] {
            variants.push(Variant::Llvm(LlvmVariant {
                rc_strat,
                profile_mode,
                gc_kind: GcKind::Rc,
                array_kind: ArrayKind::Cow,
            }));
        }
    }

    // Run time comparison with BDWGC.
    for gc_kind in [GcKind::Rc, GcKind::Bdw] {
        variants.push(Variant::Llvm(LlvmVariant {
            rc_strat: RcStrategy::Default,
            profile_mode: ProfileMode::NoRecordRc,
            gc_kind,
            array_kind: ArrayKind::Persistent,
        }));
    }

    // Run time for SML and OCaml.
    for ml_variant in [cfg::MlVariant::Sml, cfg::MlVariant::OCaml] {
        for stage in [
            cfg::CompilationStage::Typed,
            cfg::CompilationStage::FirstOrder,
        ] {
            variants.push(Variant::Ml(MlVariant {
                variant: ml_variant,
                stage,
            }));
        }
    }

    variants
}

fn compile_sample(
    bench_name: &str,
    src_path: impl AsRef<Path> + Clone,
    profile_mod: &[&str],
    profile_func: &str,
) {
    for variant in variants() {
        let tag = variant.tag();
        println!("compiling {bench_name}-{tag}");
        let (exe_path, _artifact_dir) = build_exe(
            bench_name,
            &tag,
            src_path.clone(),
            profile_mod,
            profile_func,
            &variant,
        );

        write_binary_size(&format!("{bench_name}-{tag}"), &exe_path);
    }
}

fn bench_sample(
    iters: (u64, u64),
    bench_name: &str,
    profile_mod: &[&str],
    profile_func: &str,
    extra_stdin: &str,
    expected_stdout: &str,
) {
    for variant in variants() {
        let variant_name = format!("{bench_name}-{tag}", tag = variant.tag());
        println!("benchmarking {}", variant_name);

        let exe_path = std::env::current_dir()
            .unwrap()
            .join(OUT_DIR)
            .join(variant_name.clone());

        let needed_iters_0 = if variant.record_rc() { 1 } else { 1 };
        let needed_iters_1 = if variant.record_rc() { 1 } else { 1 };

        let mut results = Vec::new();
        let mut counts: Option<Vec<RcCounts>> = None;

        for _ in 0..needed_iters_0 {
            match variant {
                Variant::Llvm(_) => {
                    let report: ProfReport =
                        run_exe(&exe_path, needed_iters_1, extra_stdin, expected_stdout);

                    let timing = &report.timings[0];
                    assert_eq!(&timing.module, profile_mod);
                    assert_eq!(&timing.function, profile_func);
                    assert_eq!(timing.specializations.len(), 1);
                    assert_eq!(timing.skipped_tail_rec_specializations.len(), 0);

                    let specialization = &timing.specializations[0];
                    assert_eq!(specialization.total_calls, needed_iters_1);

                    let total_nanos = specialization.total_clock_nanos;
                    results.push(Duration::from_nanos(total_nanos));

                    match (
                        specialization.total_retain_count,
                        specialization.total_release_count,
                        specialization.total_rc1_count,
                    ) {
                        (
                            Some(total_retain_count),
                            Some(total_release_count),
                            Some(total_rc1_count),
                        ) => {
                            let counts = counts.get_or_insert_with(|| Vec::new());
                            counts.push(RcCounts {
                                total_retain_count: total_retain_count * iters.1,
                                total_release_count: total_release_count * iters.1,
                                total_rc1_count: total_rc1_count * iters.1,
                            });
                        }
                        (None, None, None) => {}
                        _ => {
                            panic!("Expected all counts to be present or none");
                        }
                    }
                }
                Variant::Ml(_) => {
                    let report: MlProfReport =
                        run_exe(&exe_path, iters.1, extra_stdin, expected_stdout);

                    assert_eq!(report.entries.len(), 1);
                    assert_eq!(report.entries[0].total_calls, iters.1);

                    let total_nanos = report.entries[0].total_clock_nanos;
                    results.push(Duration::from_nanos(total_nanos));
                }
            }
        }

        write_run_time(&variant_name, results);

        if let Some(counts) = counts {
            write_rc_counts(&variant_name, counts);
        }
    }
}

fn sample_primes() {
    // let iters = (10, 100);
    let iters = (10, 10);

    let stdin = "100000\n";
    let stdout = "There are 9592 primes <= 100000\n";

    compile_sample(
        "bench_primes_iter.mor",
        "samples/bench_primes_iter.mor",
        &[],
        "count_primes",
    );

    bench_sample(
        iters,
        "bench_primes_iter.mor",
        &[],
        "count_primes",
        stdin,
        stdout,
    );
}

fn sample_quicksort() {
    // let iters = (10, 1000);
    let iters = (10, 100);

    let length = 10000;

    let mut input_ints: Vec<i64> = Vec::new();
    let mut rng = Pcg64::seed_from_u64(7251862977019338101); // seed is arbitrary
    while input_ints.len() < length {
        let next = rng.random();
        if next >= 0 {
            input_ints.push(next);
        }
    }

    let mut output_ints = input_ints.clone();
    output_ints.sort();

    let mut stdin = format!("{}\n", input_ints.len());
    for int in input_ints.iter() {
        let line = format!("{}\n", int);
        stdin.push_str(&line);
    }
    let stdout = format!(
        "The sorted version of\n  {:?}\nis\n  {:?}\n",
        input_ints, output_ints
    );

    compile_sample(
        "bench_quicksort.mor",
        "samples/bench_quicksort.mor",
        &[],
        "quicksort",
    );

    bench_sample(
        iters,
        "bench_quicksort.mor",
        &[],
        "quicksort",
        &stdin,
        &stdout,
    );
}

fn sample_primes_sieve() {
    // let iters = (10, 1000);
    let iters = (10, 100);

    let stdin = "10000\n";
    let stdout = include_str!("../../../samples/expected-output/primes_10000.txt");

    compile_sample(
        "bench_primes_sieve.mor",
        "samples/bench_primes_sieve.mor",
        &[],
        "sieve",
    );

    bench_sample(iters, "bench_primes_sieve.mor", &[], "sieve", stdin, stdout);
}

fn sample_parse_json() {
    // let iters = (10, 100);
    let iters = (10, 10);

    let stdin = concat!(
        include_str!("../../../samples/sample-input/citm_catalog.json"),
        "\n"
    );
    let stdout = "-7199371743916571250\n";

    compile_sample(
        "bench_parse_json.mor",
        "samples/bench_parse_json.mor",
        &[],
        "parse_json",
    );

    bench_sample(
        iters,
        "bench_parse_json.mor",
        &[],
        "parse_json",
        stdin,
        &stdout,
    );
}

fn sample_calc() {
    // let iters = (10, 2000);
    let iters = (10, 200);

    let stdin = concat!(
        include_str!("../../../samples/sample-input/calc_exprs.txt"),
        "\n"
    );
    let stdout = concat!(
        include_str!("../../../samples/expected-output/calc_values.txt"),
        "\n"
    );

    compile_sample(
        "bench_calc.mor",
        "samples/bench_calc.mor",
        &[],
        "eval_exprs",
    );

    bench_sample(iters, "bench_calc.mor", &[], "eval_exprs", stdin, stdout);
}

fn sample_unify() {
    let iters = (10, 1);

    let stdin = concat!(
        include_str!("../../../samples/sample-input/unify_problems.txt"),
        "\n"
    );
    let stdout = include_str!("../../../samples/expected-output/unify_solutions.txt");

    compile_sample(
        "bench_unify.mor",
        "samples/bench_unify.mor",
        &[],
        "solve_problems",
    );

    bench_sample(
        iters,
        "bench_unify.mor",
        &[],
        "solve_problems",
        stdin,
        stdout,
    );
}

fn sample_words_trie() {
    let iters = (10, 10);

    let stdin = concat!(
        include_str!("../../../samples/sample-input/udhr.txt"),
        "\n",
        include_str!("../../../samples/sample-input/udhr_queries.txt"),
        "\n",
    );

    let stdout = include_str!("../../../samples/expected-output/udhr_query_counts.txt");

    compile_sample(
        "bench_words_trie.mor",
        "samples/bench_words_trie.mor",
        &[],
        "count_words",
    );

    bench_sample(
        iters,
        "bench_words_trie.mor",
        &[],
        "count_words",
        stdin,
        stdout,
    );
}

fn sample_text_stats() {
    let iters = (10, 30);

    let stdin = include_str!("../../../samples/sample-input/shakespeare.txt");

    let stdout = "317\n";

    compile_sample(
        "bench_text_stats.mor",
        "samples/bench_text_stats.mor",
        &[],
        "compute_stats",
    );

    bench_sample(
        iters,
        "bench_text_stats.mor",
        &[],
        "compute_stats",
        stdin,
        stdout,
    );
}

fn sample_lisp() {
    let iters = (10, 30);

    let stdin = include_str!("../../../samples/sample-input/lisp-interpreter.lisp");

    let stdout = "((O . ()) . ((O . (O . ())) . ((O . (O . (O . ()))) . ((O . (O . (O . (O . ())))) . ((O . (O . (O . (O . (O . ()))))) . ())))))\n";

    compile_sample(
        "bench_lisp.mor",
        "samples/bench_lisp.mor",
        &[],
        "run_program",
    );

    bench_sample(iters, "bench_lisp.mor", &[], "run_program", stdin, stdout);
}

fn sample_cfold() {
    let iters = (10, 10);

    let stdin = "16\n";
    let stdout = "192457\n";

    compile_sample(
        "bench_cfold.mor",
        "samples/bench_cfold.mor",
        &[],
        "test_cfold",
    );

    bench_sample(iters, "bench_cfold.mor", &[], "test_cfold", stdin, stdout);
}

fn sample_deriv() {
    let iters = (10, 10);

    let stdin = "8\n";
    let stdout = "598592\n";

    compile_sample(
        "bench_deriv.mor",
        "samples/bench_deriv.mor",
        &[],
        "run_deriv",
    );

    bench_sample(iters, "bench_deriv.mor", &[], "run_deriv", stdin, stdout);
}

fn sample_nqueens_functional() {
    let iters = (10, 5);

    let stdin = "nqueens-functional\n13\n";
    let stdout = "73712\n";

    compile_sample(
        "bench_nqueens_functional.mor",
        "samples/bench_nqueens.mor",
        &[],
        "nqueens",
    );

    bench_sample(
        iters,
        "bench_nqueens_functional.mor",
        &[],
        "nqueens",
        stdin,
        stdout,
    );
}

fn sample_nqueens_iterative() {
    let iters = (10, 5);

    let stdin = "nqueens-iterative\n13\n";
    let stdout = "73712\n";

    compile_sample(
        "bench_nqueens_iterative.mor",
        "samples/bench_nqueens.mor",
        &[],
        "nqueens2",
    );

    bench_sample(
        iters,
        "bench_nqueens_iterative.mor",
        &[],
        "nqueens2",
        stdin,
        stdout,
    );
}

fn sample_rbtree() {
    let iters = (10, 10);

    let stdin = "rbtree\n420000";
    let stdout = "42000\n";

    compile_sample(
        "bench_rbtree.mor",
        "samples/bench_rbtree.mor",
        &[],
        "test_rbtree",
    );

    bench_sample(iters, "bench_rbtree.mor", &[], "test_rbtree", stdin, stdout);
}

fn sample_rbtreeck() {
    let iters = (10, 10);

    let stdin = "rbtree-ck\n420000";
    let stdout = "42000\n";

    compile_sample(
        "bench_rbtree_ck.mor",
        "samples/bench_rbtree.mor",
        &[],
        "test_rbtreeck",
    );

    bench_sample(
        iters,
        "bench_rbtree_ck.mor",
        &[],
        "test_rbtreeck",
        stdin,
        stdout,
    );
}

fn main() {
    if !Path::new("samples").exists() {
        eprintln!();
        eprintln!("Please run the benchmark executable from the project root directory.");
        eprintln!();
        eprintln!("You can invoke the executable from the project root using the command");
        eprintln!();
        eprintln!("    cargo run -p benchmark");
        eprintln!();
        std::process::exit(1);
    }

    // these have 0 retains omitted (there are 0 retains to begin with), so we don't run them
    // sample_quicksort();
    // sample_primes();

    sample_calc();
    sample_cfold();
    sample_deriv();
    sample_lisp();
    sample_nqueens_functional();
    sample_nqueens_iterative();
    sample_parse_json();
    sample_primes_sieve();
    sample_rbtree();
    sample_rbtreeck();
    sample_text_stats();
    sample_unify();
    sample_words_trie();
}
