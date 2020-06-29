use find_clang::find_clang;
use morphic::build;
use morphic::cli;
use morphic::file_cache::FileCache;

use criterion::measurement::WallTime;
use criterion::{BenchmarkGroup, Criterion};
use serde::Deserialize;
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
use std::process;
use std::time::Duration;

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

    let mut child = process::Command::new(exe_path.as_ref().canonicalize().unwrap())
        .env("MORPHIC_PROFILE_PATH", &report_path)
        .stdin(process::Stdio::piped())
        .stdout(process::Stdio::piped())
        .stderr(process::Stdio::null())
        .spawn()
        .expect("Could not spawn child process");

    write!(child.stdin.as_mut().unwrap(), "{}\n{}", iters, extra_stdin)
        .expect("Could not write iteration to child stdin");

    child
        .stdin
        .as_mut()
        .unwrap()
        .flush()
        .expect("Could not flush child stdin");

    let output = child.wait_with_output().expect("Waiting on child failed");

    assert!(output.status.success(), output.status);
    assert!(
        &output.stdout as &[u8] == expected_stdout.as_bytes(),
        "Sample stdout did not match expected stdout.\
                 \n  Expected: {:?}\
                 \n    Actual: {:?}\
                 \n",
        expected_stdout,
        String::from_utf8_lossy(&output.stdout),
    );

    let report: Report = serde_json::from_reader(BufReader::new(
        File::open(&report_path).expect("Failed to open child performance report file"),
    ))
    .expect("Failed to read child performance report file");

    report
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
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProfSkippedTail {
    low_func_id: u64,
    tail_func_id: u64,
}

fn bench_sample(
    g: &mut BenchmarkGroup<WallTime>,
    bench_name: &str,
    src_path: impl AsRef<Path>,
    profile_mod: &[&str],
    profile_func: &str,
    extra_stdin: &str,
    expected_stdout: &str,
) {
    let exe_path = tempfile::Builder::new()
        .prefix(".tmp-exe-")
        .tempfile_in("")
        .expect("Could not create temp file")
        .into_temp_path();

    let mut files = FileCache::new();

    build(
        cli::BuildConfig {
            src_path: src_path.as_ref().into(),
            profile_syms: vec![cli::SymbolName(format!(
                "{mod_}{func}",
                mod_ = profile_mod
                    .iter()
                    .map(|component| format!("{}.", component))
                    .collect::<Vec<_>>()
                    .concat(),
                func = profile_func,
            ))],
            target: cli::TargetConfig::Native,
            llvm_opt_level: cli::default_llvm_opt_level(),
            output_path: exe_path.to_owned(),
            artifact_dir: None,
        },
        &mut files,
    )
    .expect("Compilation failed");

    g.bench_function(bench_name, |b| {
        b.iter_custom(|iters| {
            let report: ProfReport = run_exe(&exe_path, iters, extra_stdin, expected_stdout);

            let timing = &report.timings[0];

            assert_eq!(&timing.module as &[String], profile_mod as &[&str]);
            assert_eq!(&timing.function, profile_func);
            assert_eq!(timing.specializations.len(), 1);
            assert_eq!(timing.skipped_tail_rec_specializations.len(), 0);

            let specialization = &timing.specializations[0];

            assert_eq!(specialization.total_calls, iters);

            let total_nanos = specialization.total_clock_nanos;

            Duration::from_nanos(total_nanos)
        })
    });
}

const CLANG_VERSION: u32 = 10;

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CProfReport {
    total_calls: u64,
    total_clock_nanos: u64,
}

fn bench_c_sample(
    g: &mut BenchmarkGroup<WallTime>,
    bench_name: &str,
    src_path: impl AsRef<Path>,
    extra_stdin: &str,
    expected_stdout: &str,
) {
    let exe_path = tempfile::Builder::new()
        .prefix(".tmp-exe-")
        .tempfile_in("")
        .expect("Could not create temp file")
        .into_temp_path();

    let clang = find_clang(CLANG_VERSION)
        .unwrap_or_else(|err| panic!("Could not find clang {}: {:?}", CLANG_VERSION, err));

    let clang_output = process::Command::new(&clang.path)
        .arg(src_path.as_ref())
        .arg(format!("-o{}", exe_path.to_str().unwrap()))
        .arg("-O3")
        .arg("-march=native")
        .arg("-Wall")
        .arg("-Werror")
        .output()
        .expect("Compilation failed");

    assert!(
        clang_output.status.success(),
        "Compilation failed:\n{}",
        String::from_utf8_lossy(&clang_output.stderr)
    );

    g.bench_function(bench_name, |b| {
        b.iter_custom(|iters| {
            let report: CProfReport = run_exe(&exe_path, iters, extra_stdin, expected_stdout);

            assert_eq!(report.total_calls, iters);

            Duration::from_nanos(report.total_clock_nanos)
        })
    });
}

fn sample_primes(c: &mut Criterion) {
    let mut g = c.benchmark_group("primes");
    g.sample_size(20);

    let stdin = "100000\n";
    let stdout = "There are 9592 primes <= 100000\n";

    bench_sample(
        &mut g,
        "primes",
        "samples/bench_primes.mor",
        &[],
        "count_primes",
        stdin,
        stdout,
    );

    bench_c_sample(
        &mut g,
        "primes C",
        "samples/c_samples/bench_primes.c",
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

    let mut c = Criterion::default()
        .default_mode_bench()
        .configure_from_args();

    sample_primes(&mut c);
}
