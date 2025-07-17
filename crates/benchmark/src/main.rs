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

fn out_dir() -> PathBuf {
    let mut path = std::env::current_dir().unwrap();
    path.push("out2");
    path
}

fn rc_count_file() -> PathBuf {
    let mut path = std::env::current_dir().unwrap();
    path.push("target");
    path.push("rc_counts.csv");
    path
}

fn run_time_file() -> PathBuf {
    let mut path = std::env::current_dir().unwrap();
    path.push("target");
    path.push("run_times.csv");
    path
}

fn binary_sizes_file() -> PathBuf {
    let mut path = std::env::current_dir().unwrap();
    path.push("target");
    path.push("binary_sizes.csv");
    path
}

// Output we get from benchmark executables:

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct MlProfReportEntry {
    func_id: u64,
    total_calls: u64,
    total_clock_nanos: u64,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(transparent)]
struct MlProfReport {
    entries: Vec<MlProfReportEntry>,
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
struct ProfReport {
    clock_res_nanos: u64,
    timings: Vec<ProfTiming>,
}

// The summary data we output:

type Dataframe<T> = Vec<(String, Vec<(Experiment, T)>)>;

#[derive(Clone, Copy, Serialize)]
struct RcCounts {
    total_retain_count: u64,
    total_release_count: u64,
    total_rc1_count: u64,
}

struct Output {
    binary_sizes: Dataframe<u64>,
    run_times: Dataframe<Vec<Duration>>,
    rc_counts: Dataframe<RcCounts>,
}

fn get_binary_size(exe_path: impl AsRef<Path>) -> u64 {
    let disp = exe_path.as_ref().display();
    exe_path
        .as_ref()
        .metadata()
        .expect(&format!("Could not get metadata for binary {}", disp))
        .len()
}

fn write_binary_size(dataframe: &Dataframe<u64>) {
    let mut file = File::create(binary_sizes_file()).expect("Could not open binary sizes file");
    assert!(file.metadata().unwrap().len() == 0, "File is not empty");

    // Suitable for consumption by pandas.
    let header = ",benchmark,config,size (bytes)";
    writeln!(file, "{}", header).expect("Could not write header to file");

    let mut i = 0;
    for (benchmark, configs) in dataframe {
        for (config, size) in configs {
            writeln!(file, "{},{},{},{}", i, benchmark, config.tag(), size)
                .expect("Could not write binary size to file");
            i += 1;
        }
    }
}

fn write_run_time(dataframe: &Dataframe<Vec<Duration>>) {
    let mut file = File::create(run_time_file()).expect("Could not open run time file");
    assert!(file.metadata().unwrap().len() == 0, "File is not empty");

    // Suitable for consumption by pandas.
    let header = ",benchmark,config,time (ns)";
    writeln!(file, "{}", header).expect("Could not write header to file");

    let mut i = 0;
    for (benchmark, configs) in dataframe {
        for (config, times) in configs {
            for time in times {
                assert!(!config.record_rc());
                writeln!(
                    file,
                    "{},{},{},{}",
                    i,
                    benchmark,
                    config.tag(),
                    time.as_nanos(),
                )
                .expect("Could not write run time to file");
                i += 1;
            }
        }
    }
}

fn write_rc_counts(dataframe: &Dataframe<RcCounts>) {
    let mut file = File::create(rc_count_file()).expect("Could not open rc count file");
    assert!(file.metadata().unwrap().len() == 0, "File is not empty");

    // Suitable for consumption by pandas.
    let header = ",benchmark,config,retain count,release count,rc1 count";
    writeln!(file, "{}", header).expect("Could not write header to file");

    let mut i = 0;
    for (benchmark, configs) in dataframe {
        for (config, rc_counts) in configs {
            assert!(config.record_rc());
            writeln!(
                file,
                "{},{},{},{},{},{}",
                i,
                benchmark,
                config.tag(),
                rc_counts.total_retain_count,
                rc_counts.total_release_count,
                rc_counts.total_rc1_count
            )
            .expect("Could not write rc counts to file");
            i += 1;
        }
    }
}

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

fn build_exe(
    bench_name: &str,
    tag: &str,
    src_path: impl AsRef<Path> + Clone,
    profile_mod: &[&str],
    profile_func: &str,
    experiment: &Experiment,
) -> (PathBuf, ArtifactDir) {
    let out_dir = out_dir();
    let exe_path = out_dir.join(format!("{bench_name}-{tag}"));
    let artifact_path = out_dir.join(format!("{bench_name}-{tag}-artifacts"));

    let artifact_dir = ArtifactDir {
        dir_path: artifact_path,
        filename_prefix: exe_path.file_name().unwrap().into(),
    };

    if !artifact_dir.dir_path.exists() {
        std::fs::create_dir(&artifact_dir.dir_path).unwrap();
    }

    let mut files = FileCache::new();
    let build_config = experiment.build_config(
        src_path.as_ref().to_path_buf(),
        profile_mod,
        profile_func,
        exe_path.clone(),
        Some(artifact_dir.clone()),
    );

    build(build_config, &mut files).expect("Compilation failed");
    (exe_path, artifact_dir)
}

#[derive(Clone, Debug)]
struct LlvmExperiment {
    rc_strat: RcStrategy,
    profile_mode: ProfileMode,
    gc_kind: GcKind,
    array_kind: ArrayKind,
}

#[derive(Clone, Debug)]
struct MlExperiment {
    variant: cfg::MlVariant,
    stage: cfg::CompilationStage,
}

#[derive(Clone, Debug)]
enum Experiment {
    Llvm(LlvmExperiment),
    Ml(MlExperiment),
}

impl Experiment {
    fn tag(&self) -> String {
        match self {
            &Experiment::Llvm(LlvmExperiment {
                profile_mode,
                rc_strat,
                gc_kind,
                array_kind,
            }) => {
                let profile_mode_str = match profile_mode {
                    ProfileMode::RecordRc => "record_rc",
                    ProfileMode::NoRecordRc => "record_time",
                };
                format!(
                    "llvm-{}-{}-{}-{}",
                    profile_mode_str,
                    rc_strat.to_str(),
                    gc_kind.to_str(),
                    array_kind.to_str(),
                )
            }
            &Experiment::Ml(MlExperiment { variant, stage }) => {
                format!("{}-{}", variant.to_str(), stage.to_str())
            }
        }
    }

    fn record_rc(&self) -> bool {
        match self {
            Experiment::Llvm(experiment) => experiment.profile_mode == ProfileMode::RecordRc,
            Experiment::Ml(_) => false,
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
            &Experiment::Llvm(LlvmExperiment {
                rc_strat,
                profile_mode,
                gc_kind,
                array_kind,
            }) => {
                let llvm_config = cfg::LlvmConfig {
                    rc_strat,
                    gc_kind,
                    array_kind,
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
                    profile_mode,
                    output_path,
                    artifact_dir,
                }
            }
            &Experiment::Ml(MlExperiment { variant, stage }) => {
                let ml_config = cfg::MlConfig { variant, stage };
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

fn experiments() -> Vec<Experiment> {
    let mut experiments = Vec::new();

    // Run time and retain count comparison with Perceus.
    for rc_strat in [RcStrategy::Default, RcStrategy::Perceus] {
        for array_kind in [ArrayKind::Cow, ArrayKind::Persistent] {
            for profile_mode in [ProfileMode::RecordRc, ProfileMode::NoRecordRc] {
                experiments.push(Experiment::Llvm(LlvmExperiment {
                    rc_strat,
                    profile_mode,
                    gc_kind: GcKind::Rc,
                    array_kind,
                }));
            }
        }
    }

    // Run time comparison with BDWGC.
    for rc_strat in [RcStrategy::Default, RcStrategy::Perceus] {
        experiments.push(Experiment::Llvm(LlvmExperiment {
            rc_strat,
            profile_mode: ProfileMode::NoRecordRc,
            gc_kind: GcKind::Bdw,
            array_kind: ArrayKind::Persistent,
        }));
    }

    // Run time for SML and OCaml.
    for variant in [cfg::MlVariant::Sml, cfg::MlVariant::OCaml] {
        for stage in [
            cfg::CompilationStage::Typed,
            cfg::CompilationStage::FirstOrder,
        ] {
            experiments.push(Experiment::Ml(MlExperiment { variant, stage }));
        }
    }

    experiments
}

fn compile_sample(
    output: &mut Output,
    bench_name: &str,
    src_path: impl AsRef<Path> + Clone,
    profile_mod: &[&str],
    profile_func: &str,
) {
    for experiment in experiments() {
        let tag = experiment.tag();
        println!("compiling {bench_name}-{tag}");

        let (exe_path, _artifact_dir) = build_exe(
            bench_name,
            &tag,
            src_path.clone(),
            profile_mod,
            profile_func,
            &experiment,
        );

        let size = get_binary_size(&exe_path);
        let entry = (bench_name.to_string(), vec![(experiment, size)]);
        output.binary_sizes.push(entry);
    }
}

fn bench_sample(
    output: &mut Output,
    iters: (u64, u64),
    bench_name: &str,
    profile_mod: &[&str],
    profile_func: &str,
    extra_stdin: &str,
    expected_stdout: &str,
) {
    for experiment in experiments() {
        let name = format!("{bench_name}-{tag}", tag = experiment.tag());
        println!("benchmarking {}", name);
        let exe_path = out_dir().join(name);

        fn check_prof_report<'a>(
            report: &'a ProfReport,
            profile_mod: &[&str],
            profile_func: &str,
            needed_iters_1: u64,
        ) -> &'a ProfSpecialization {
            let timing = &report.timings[0];
            assert_eq!(&timing.module, profile_mod);
            assert_eq!(&timing.function, profile_func);
            assert_eq!(timing.specializations.len(), 1);
            assert_eq!(timing.skipped_tail_rec_specializations.len(), 0);

            let specialization = &timing.specializations[0];
            assert_eq!(specialization.total_calls, needed_iters_1);

            specialization
        }

        match experiment {
            Experiment::Llvm(LlvmExperiment {
                profile_mode: ProfileMode::NoRecordRc,
                ..
            }) => {
                let mut results = Vec::new();

                for _ in 0..iters.0 {
                    let report: ProfReport =
                        run_exe(&exe_path, iters.1, extra_stdin, expected_stdout);

                    let specialization =
                        check_prof_report(&report, profile_mod, profile_func, iters.1);

                    let total_nanos = specialization.total_clock_nanos;
                    results.push(Duration::from_nanos(total_nanos));
                }

                let entry = (bench_name.to_string(), vec![(experiment, results)]);
                output.run_times.push(entry);
            }
            Experiment::Llvm(LlvmExperiment {
                profile_mode: ProfileMode::RecordRc,
                ..
            }) => {
                let actual_iters_1 = 1;

                let report: ProfReport =
                    run_exe(&exe_path, actual_iters_1, extra_stdin, expected_stdout);

                let specialization =
                    check_prof_report(&report, profile_mod, profile_func, actual_iters_1);

                let total_retain_count = specialization.total_retain_count.unwrap();
                let total_release_count = specialization.total_release_count.unwrap();
                let total_rc1_count = specialization.total_rc1_count.unwrap();

                let counts = RcCounts {
                    total_retain_count: total_retain_count * iters.1,
                    total_release_count: total_release_count * iters.1,
                    total_rc1_count: total_rc1_count * iters.1,
                };
                let entry = (bench_name.to_string(), vec![(experiment, counts)]);
                output.rc_counts.push(entry);
            }
            Experiment::Ml(_) => {
                let mut results = Vec::new();

                for _ in 0..iters.0 {
                    let report: MlProfReport =
                        run_exe(&exe_path, iters.1, extra_stdin, expected_stdout);

                    assert_eq!(report.entries.len(), 1);
                    assert_eq!(report.entries[0].total_calls, iters.1);

                    let total_nanos = report.entries[0].total_clock_nanos;
                    results.push(Duration::from_nanos(total_nanos));
                }

                let entry = (bench_name.to_string(), vec![(experiment, results)]);
                output.run_times.push(entry);
            }
        }
    }
}

fn sample_primes(output: &mut Output) {
    // let iters = (10, 100);
    let iters = (10, 10);

    let stdin = "100000\n";
    let stdout = "There are 9592 primes <= 100000\n";

    compile_sample(
        output,
        "bench_primes_iter.mor",
        "samples/bench_primes_iter.mor",
        &[],
        "count_primes",
    );

    bench_sample(
        output,
        iters,
        "bench_primes_iter.mor",
        &[],
        "count_primes",
        stdin,
        stdout,
    );
}

fn sample_quicksort(output: &mut Output) {
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
        output,
        "bench_quicksort.mor",
        "samples/bench_quicksort.mor",
        &[],
        "quicksort",
    );

    bench_sample(
        output,
        iters,
        "bench_quicksort.mor",
        &[],
        "quicksort",
        &stdin,
        &stdout,
    );
}

fn sample_primes_sieve(output: &mut Output) {
    // let iters = (10, 1000);
    let iters = (10, 100);

    let stdin = "10000\n";
    let stdout = include_str!("../../../samples/expected-output/primes_10000.txt");

    compile_sample(
        output,
        "bench_primes_sieve.mor",
        "samples/bench_primes_sieve.mor",
        &[],
        "sieve",
    );

    bench_sample(
        output,
        iters,
        "bench_primes_sieve.mor",
        &[],
        "sieve",
        stdin,
        stdout,
    );
}

fn sample_parse_json(output: &mut Output) {
    // let iters = (10, 100);
    let iters = (10, 10);

    let stdin = concat!(
        include_str!("../../../samples/sample-input/citm_catalog.json"),
        "\n"
    );
    let stdout = "-7199371743916571250\n";

    compile_sample(
        output,
        "bench_parse_json.mor",
        "samples/bench_parse_json.mor",
        &[],
        "parse_json",
    );

    bench_sample(
        output,
        iters,
        "bench_parse_json.mor",
        &[],
        "parse_json",
        stdin,
        &stdout,
    );
}

fn sample_calc(output: &mut Output) {
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
        output,
        "bench_calc.mor",
        "samples/bench_calc.mor",
        &[],
        "eval_exprs",
    );

    bench_sample(
        output,
        iters,
        "bench_calc.mor",
        &[],
        "eval_exprs",
        stdin,
        stdout,
    );
}

fn sample_unify(output: &mut Output) {
    let iters = (10, 1);

    let stdin = concat!(
        include_str!("../../../samples/sample-input/unify_problems.txt"),
        "\n"
    );
    let stdout = include_str!("../../../samples/expected-output/unify_solutions.txt");

    compile_sample(
        output,
        "bench_unify.mor",
        "samples/bench_unify.mor",
        &[],
        "solve_problems",
    );

    bench_sample(
        output,
        iters,
        "bench_unify.mor",
        &[],
        "solve_problems",
        stdin,
        stdout,
    );
}

fn sample_words_trie(output: &mut Output) {
    let iters = (10, 10);

    let stdin = concat!(
        include_str!("../../../samples/sample-input/udhr.txt"),
        "\n",
        include_str!("../../../samples/sample-input/udhr_queries.txt"),
        "\n",
    );

    let stdout = include_str!("../../../samples/expected-output/udhr_query_counts.txt");

    compile_sample(
        output,
        "bench_words_trie.mor",
        "samples/bench_words_trie.mor",
        &[],
        "count_words",
    );

    bench_sample(
        output,
        iters,
        "bench_words_trie.mor",
        &[],
        "count_words",
        stdin,
        stdout,
    );
}

fn sample_text_stats(output: &mut Output) {
    let iters = (10, 30);

    let stdin = include_str!("../../../samples/sample-input/shakespeare.txt");

    let stdout = "317\n";

    compile_sample(
        output,
        "bench_text_stats.mor",
        "samples/bench_text_stats.mor",
        &[],
        "compute_stats",
    );

    bench_sample(
        output,
        iters,
        "bench_text_stats.mor",
        &[],
        "compute_stats",
        stdin,
        stdout,
    );
}

fn sample_lisp(output: &mut Output) {
    let iters = (10, 30);

    let stdin = include_str!("../../../samples/sample-input/lisp-interpreter.lisp");

    let stdout = "((O . ()) . ((O . (O . ())) . ((O . (O . (O . ()))) . ((O . (O . (O . (O . ())))) . ((O . (O . (O . (O . (O . ()))))) . ())))))\n";

    compile_sample(
        output,
        "bench_lisp.mor",
        "samples/bench_lisp.mor",
        &[],
        "run_program",
    );

    bench_sample(
        output,
        iters,
        "bench_lisp.mor",
        &[],
        "run_program",
        stdin,
        stdout,
    );
}
fn sample_cfold(output: &mut Output) {
    let iters = (10, 10);

    let stdin = "16\n";
    let stdout = "192457\n";

    compile_sample(
        output,
        "bench_cfold.mor",
        "samples/bench_cfold.mor",
        &[],
        "test_cfold",
    );

    bench_sample(
        output,
        iters,
        "bench_cfold.mor",
        &[],
        "test_cfold",
        stdin,
        stdout,
    );
}
fn sample_deriv(output: &mut Output) {
    let iters = (10, 10);

    let stdin = "8\n";
    let stdout = "598592\n";

    compile_sample(
        output,
        "bench_deriv.mor",
        "samples/bench_deriv.mor",
        &[],
        "run_deriv",
    );

    bench_sample(
        output,
        iters,
        "bench_deriv.mor",
        &[],
        "run_deriv",
        stdin,
        stdout,
    );
}
fn sample_nqueens_functional(output: &mut Output) {
    let iters = (10, 5);

    let stdin = "nqueens-functional\n13\n";
    let stdout = "73712\n";

    compile_sample(
        output,
        "bench_nqueens_functional.mor",
        "samples/bench_nqueens.mor",
        &[],
        "nqueens",
    );

    bench_sample(
        output,
        iters,
        "bench_nqueens_functional.mor",
        &[],
        "nqueens",
        stdin,
        stdout,
    );
}

fn sample_nqueens_iterative(output: &mut Output) {
    let iters = (10, 5);

    let stdin = "nqueens-iterative\n13\n";
    let stdout = "73712\n";

    compile_sample(
        output,
        "bench_nqueens_iterative.mor",
        "samples/bench_nqueens.mor",
        &[],
        "nqueens2",
    );

    bench_sample(
        output,
        iters,
        "bench_nqueens_iterative.mor",
        &[],
        "nqueens2",
        stdin,
        stdout,
    );
}

fn sample_rbtree(output: &mut Output) {
    let iters = (10, 10);

    let stdin = "rbtree\n420000";
    let stdout = "42000\n";

    compile_sample(
        output,
        "bench_rbtree.mor",
        "samples/bench_rbtree.mor",
        &[],
        "test_rbtree",
    );

    bench_sample(
        output,
        iters,
        "bench_rbtree.mor",
        &[],
        "test_rbtree",
        stdin,
        stdout,
    );
}

fn sample_rbtreeck(output: &mut Output) {
    let iters = (10, 10);

    let stdin = "rbtree-ck\n420000";
    let stdout = "42000\n";

    compile_sample(
        output,
        "bench_rbtree_ck.mor",
        "samples/bench_rbtree.mor",
        &[],
        "test_rbtreeck",
    );

    bench_sample(
        output,
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

    std::fs::create_dir_all(out_dir()).expect("Could not create out directory");

    let mut existing = Vec::new();
    if binary_sizes_file().exists() {
        existing.push(binary_sizes_file());
    }
    if run_time_file().exists() {
        existing.push(run_time_file());
    }
    if rc_count_file().exists() {
        existing.push(rc_count_file());
    }

    if !existing.is_empty() {
        eprintln!("Files already exist:");
        for path in existing {
            eprintln!("    {}", path.display());
        }
        eprintln!("Please delete or rename the files and try again.");
        std::process::exit(1);
    }

    let mut output = Output {
        binary_sizes: Vec::new(),
        run_times: Vec::new(),
        rc_counts: Vec::new(),
    };

    let start_time = std::time::Instant::now();
    let print_time = |n: usize| {
        let elapsed = start_time.elapsed();
        let minutes = elapsed.as_secs() / 60;
        let seconds = elapsed.as_secs() % 60;
        println!("Finished benchmark {n:02}/13; total time elapsed: {minutes}m {seconds}s");
    };

    // these have 0 retains omitted (there are 0 retains to begin with), so we don't run them
    // sample_quicksort();
    // sample_primes();

    sample_calc(&mut output);
    print_time(1);
    sample_cfold(&mut output);
    print_time(2);
    sample_deriv(&mut output);
    print_time(3);
    sample_lisp(&mut output);
    print_time(4);
    sample_nqueens_functional(&mut output);
    print_time(5);
    sample_nqueens_iterative(&mut output);
    print_time(6);
    sample_parse_json(&mut output);
    print_time(7);
    sample_primes_sieve(&mut output);
    print_time(8);
    sample_rbtree(&mut output);
    print_time(9);
    sample_rbtreeck(&mut output);
    print_time(10);
    sample_text_stats(&mut output);
    print_time(11);
    sample_unify(&mut output);
    print_time(12);
    sample_words_trie(&mut output);
    print_time(13);

    write_binary_size(&output.binary_sizes);
    write_run_time(&output.run_times);
    write_rc_counts(&output.rc_counts);
}
