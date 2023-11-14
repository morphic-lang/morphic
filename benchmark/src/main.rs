#![allow(dead_code)]

use morphic::build;
use morphic::cli;
use morphic::cli::ArtifactDir;
use morphic::cli::LlvmConfig;
use morphic::cli::MlConfig;
use morphic::cli::MutationMode;
use morphic::cli::PassOptions;
use morphic::cli::RcMode;
use morphic::cli::SpecializationMode;
use morphic::file_cache::FileCache;
use morphic::progress_ui::ProgressMode;

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
        output.status.success(),
        "Child process did not exit successfully: exit status {:?}, stderr:\n{}",
        output.status.code(),
        String::from_utf8(output.stderr).unwrap(),
    );
    assert!(
        &output.stdout as &[u8] == expected_stdout.as_bytes(),
        "Sample stdout did not match expected stdout.\
                 \n  Expected: {:?}\
                 \n    Actual: {:?}\
                 \n",
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
    let size = exe_path
        .as_ref()
        .metadata()
        .expect("Could not get metadata for binary")
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

const RC_COUNT_DIR: &str = "target/rc_count";

fn write_rc_counts(benchmark_name: &str, data: Vec<RcCounts>) {
    std::fs::create_dir_all(RC_COUNT_DIR).expect("Could not create rc_count directory");

    let mut file = File::create(format!("{}/{}.txt", RC_COUNT_DIR, benchmark_name))
        .expect("Could not create rc counts file");

    writeln!(file, "{}", serde_json::to_string(&data).unwrap())
        .expect("Could not write rc counts to file");
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct MlProfReport {
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
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProfSkippedTail {
    low_func_id: u64,
    tail_func_id: u64,
}

#[derive(Copy, Clone, Debug)]
struct SampleOptions {
    is_native: bool,
    rc_mode: RcMode,
    mutation_mode: MutationMode,
    profile_record_rc: bool,
}

const OUT_DIR: &str = "out2";

fn build_exe(
    bench_name: &str,
    tag: &str,
    src_path: impl AsRef<Path> + Clone,
    profile_mod: &[&str],
    profile_func: &str,
    defunc_mode: SpecializationMode,
    options: SampleOptions,
) -> (PathBuf, ArtifactDir) {
    let variant_name = format!("{bench_name}_{tag}");

    if !std::env::current_dir().unwrap().join("out2").exists() {
        std::fs::create_dir(std::env::current_dir().unwrap().join("out2")).unwrap();
    }

    let binary_path = std::env::current_dir()
        .unwrap()
        .join("out2")
        .join(variant_name.clone());

    let artifact_path = std::env::current_dir()
        .unwrap()
        .join("out2")
        .join(format!("{bench_name}-{tag}-artifacts"));

    let artifact_dir = ArtifactDir {
        dir_path: artifact_path.clone(),
        filename_prefix: binary_path.file_name().unwrap().into(),
    };

    if options.is_native {
        if binary_path.exists() {
            return (binary_path, artifact_dir);
        }
    } else {
        if artifact_dir.dir_path.exists() {
            return (binary_path, artifact_dir);
        } else {
            std::fs::create_dir(artifact_dir.dir_path.clone()).unwrap();
        }
    }

    let mut files = FileCache::new();

    build(
        cli::BuildConfig {
            src_path: src_path.as_ref().to_path_buf(),
            profile_syms: vec![cli::SymbolName(format!(
                "{mod_}{func}",
                mod_ = profile_mod
                    .iter()
                    .map(|component| format!("{}.", component))
                    .collect::<Vec<_>>()
                    .concat(),
                func = profile_func,
            ))],
            profile_record_rc: false,
            target: {
                if options.is_native {
                    cli::TargetConfig::Llvm(LlvmConfig::Native)
                } else {
                    cli::TargetConfig::Ml(MlConfig::Ocaml) // both do the same thing
                }
            },
            llvm_opt_level: cli::default_llvm_opt_level(),
            output_path: binary_path.to_owned(),
            artifact_dir: if options.is_native {
                None
            } else {
                Some(artifact_dir.clone())
            },
            progress: ProgressMode::Hidden,
            pass_options: PassOptions {
                defunc_mode,
                rc_mode: options.rc_mode,
                mutation_mode: options.mutation_mode,
                ..Default::default()
            },
        },
        &mut files,
    )
    .expect("Compilation failed");

    (binary_path, artifact_dir)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Variant {
    rc_mode: RcMode,
    record_rc: bool,
}

impl Variant {
    fn tag(&self) -> String {
        let rc_mode_str = match self.rc_mode {
            RcMode::Elide => "elide",
            RcMode::Trivial => "trivial",
        };
        let record_rc_str = if self.record_rc { "rc" } else { "time" };
        format!("{}_{}", rc_mode_str, record_rc_str)
    }
}

fn variants() -> Vec<Variant> {
    let mut variants = Vec::new();
    for rc_mode in [RcMode::Elide, RcMode::Trivial] {
        for record_rc in [false, true] {
            variants.push(Variant { rc_mode, record_rc });
        }
    }
    variants
}

#[derive(Clone, Copy, Serialize)]
struct RcCounts {
    total_retain_count: u64,
    total_release_count: u64,
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
        let variant_name = format!("{bench_name}_{tag}", tag = variant.tag());

        let exe_path = std::env::current_dir()
            .unwrap()
            .join("out2")
            .join(variant_name.clone());

        let mut results = Vec::new();
        let mut counts: Option<Vec<RcCounts>> = None;
        for _ in 0..iters.0 {
            let report: ProfReport = run_exe(&exe_path, iters.1, extra_stdin, expected_stdout);

            let timing = &report.timings[0];

            assert_eq!(&timing.module as &[String], profile_mod as &[&str]);
            assert_eq!(&timing.function, profile_func);
            assert_eq!(timing.specializations.len(), 1);
            assert_eq!(timing.skipped_tail_rec_specializations.len(), 0);

            let specialization = &timing.specializations[0];

            assert_eq!(specialization.total_calls, iters.1);

            let total_nanos = specialization.total_clock_nanos;

            results.push(Duration::from_nanos(total_nanos));

            match (
                specialization.total_retain_count,
                specialization.total_release_count,
            ) {
                (Some(total_retain_count), Some(total_release_count)) => {
                    let counts = counts.get_or_insert_with(|| Vec::new());
                    counts.push(RcCounts {
                        total_retain_count,
                        total_release_count,
                    });
                }
                (None, None) => {}
                _ => {
                    panic!("Expected both retain and release counts to be present, or neither");
                }
            }
        }

        write_run_time(&variant_name, results);

        if let Some(counts) = counts {
            write_rc_counts(&variant_name, counts);
        }
    }
}

fn compile_sample(
    bench_name: &str,
    src_path: impl AsRef<Path> + Clone,
    profile_mod: &[&str],
    profile_func: &str,
    mutation_mode: MutationMode,
) {
    for variant in variants() {
        let tag = variant.tag();
        println!("compiling {bench_name}_{tag}");
        let (exe_path, _artifact_dir) = build_exe(
            bench_name,
            &tag,
            src_path.clone(),
            profile_mod,
            profile_func,
            SpecializationMode::Specialize,
            SampleOptions {
                is_native: true,
                rc_mode: variant.rc_mode,
                mutation_mode,
                profile_record_rc: variant.record_rc,
            },
        );

        write_binary_size(&format!("{bench_name}_{tag}"), &exe_path);
    }
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct BasicProfReport {
    total_calls: u64,
    total_clock_nanos: u64,
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
        MutationMode::Optimize,
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
        let next = rng.gen();
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
        MutationMode::Optimize,
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
    let stdout = include_str!("../../samples/expected-output/primes_10000.txt");

    compile_sample(
        "bench_primes_sieve.mor",
        "samples/bench_primes_sieve.mor",
        &[],
        "sieve",
        MutationMode::Optimize,
    );

    bench_sample(iters, "bench_primes_sieve.mor", &[], "sieve", stdin, stdout);
}

fn sample_parse_json() {
    // let iters = (10, 100);
    let iters = (10, 10);

    let stdin = concat!(
        include_str!("../../samples/sample-input/citm_catalog.json"),
        "\n"
    );
    let stdout = "-7199371743916571250\n";

    compile_sample(
        "bench_parse_json.mor",
        "samples/bench_parse_json.mor",
        &[],
        "parse_json",
        MutationMode::AlwaysImmut,
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
        include_str!("../../samples/sample-input/calc_exprs.txt"),
        "\n"
    );
    let stdout = concat!(
        include_str!("../../samples/expected-output/calc_values.txt"),
        "\n"
    );

    compile_sample(
        "bench_calc.mor",
        "samples/bench_calc.mor",
        &[],
        "eval_exprs",
        MutationMode::Optimize,
    );

    bench_sample(iters, "bench_calc.mor", &[], "eval_exprs", stdin, stdout);
}

fn sample_unify() {
    let iters = (10, 1);

    let stdin = concat!(
        include_str!("../../samples/sample-input/unify_problems.txt"),
        "\n"
    );
    let stdout = include_str!("../../samples/expected-output/unify_solutions.txt");

    compile_sample(
        "bench_unify.mor",
        "samples/bench_unify.mor",
        &[],
        "solve_problems",
        MutationMode::AlwaysImmut,
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
        include_str!("../../samples/sample-input/udhr.txt"),
        "\n",
        include_str!("../../samples/sample-input/udhr_queries.txt"),
        "\n",
    );

    let stdout = include_str!("../../samples/expected-output/udhr_query_counts.txt");

    compile_sample(
        "bench_words_trie.mor",
        "samples/bench_words_trie.mor",
        &[],
        "count_words",
        MutationMode::AlwaysImmut,
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

    sample_quicksort();

    sample_primes();

    sample_primes_sieve();

    sample_parse_json();

    sample_calc();

    sample_unify();

    sample_words_trie()
}
