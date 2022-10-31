use find_clang::find_default_clang;
use morphic::build;
use morphic::cli;
use morphic::file_cache::FileCache;
use morphic::progress_ui::ProgressMode;

use criterion::measurement::WallTime;
use criterion::{BenchmarkGroup, Criterion};
use rand::{Rng, SeedableRng};
use rand_pcg::Pcg64;
use serde::Deserialize;
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
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
        "Child process did not exit successfully: exit status {:?}",
        output.status
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
        .stderr(process::Stdio::null())
        .spawn()
        .expect("Could not spawn child process");

    drive_subprocess(child, iters, extra_stdin, expected_stdout);

    let report: Report = serde_json::from_reader(BufReader::new(
        File::open(&report_path).expect("Failed to open child performance report file"),
    ))
    .expect("Failed to read child performance report file");

    report
}

fn run_ghc_exe(
    exe_path: impl AsRef<Path>,
    iters: u64,
    extra_stdin: &str,
    expected_stdout: &str,
) -> GhcProfReport {
    let report_path = tempfile::Builder::new()
        .prefix(".tmp-report-")
        .suffix(".prof")
        .tempfile_in("")
        .expect("Could not create temp file")
        .into_temp_path();

    let child = process::Command::new(exe_path.as_ref().canonicalize().unwrap())
        .arg("+RTS")
        .arg("-pj")
        .arg(format!(
            "-po{}",
            report_path.file_stem().unwrap().to_str().unwrap()
        ))
        .stdin(process::Stdio::piped())
        .stdout(process::Stdio::piped())
        .stderr(process::Stdio::null())
        .spawn()
        .expect("Could not spawn child process");

    drive_subprocess(child, iters, extra_stdin, expected_stdout);

    serde_json::from_reader(BufReader::new(
        File::open(&report_path).expect("Failed to open child performance report file"),
    ))
    .expect("Failed to read child performance report file")
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
    let mut exe_path_cache = None;

    g.bench_function(bench_name, |b| {
        b.iter_custom(|iters| {
            let exe_path = exe_path_cache.get_or_insert_with(|| {
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
                        defunc_mode: cli::SpecializationMode::Specialize,
                        progress: ProgressMode::Hidden,
                    },
                    &mut files,
                )
                .expect("Compilation failed");

                exe_path
            });

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

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct BasicProfReport {
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
    let mut exe_path_cache = None;

    g.bench_function(bench_name, |b| {
        b.iter_custom(|iters| {
            let exe_path = exe_path_cache.get_or_insert_with(|| {
                let exe_path = tempfile::Builder::new()
                    .prefix(".tmp-exe-")
                    .tempfile_in("")
                    .expect("Could not create temp file")
                    .into_temp_path();

                let clang = find_default_clang().expect("clang must be present to run benchmarks");

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

                exe_path
            });

            let report: BasicProfReport = run_exe(&exe_path, iters, extra_stdin, expected_stdout);

            assert_eq!(report.total_calls, iters);

            Duration::from_nanos(report.total_clock_nanos)
        })
    });
}

fn bench_rust_sample(
    g: &mut BenchmarkGroup<WallTime>,
    bench_name: &str,
    src_path: impl AsRef<Path>,
    extra_stdin: &str,
    expected_stdout: &str,
) {
    let mut exe_path_cache = None;

    g.bench_function(bench_name, |b| {
        b.iter_custom(|iters| {
            let exe_path = exe_path_cache.get_or_insert_with(|| {
                let exe_path = tempfile::Builder::new()
                    .prefix(".tmp-exe-")
                    .tempfile_in("")
                    .expect("Could not create temp file")
                    .into_temp_path();

                let rustc_output = process::Command::new("rustc")
                    .arg(format!("-o{}", exe_path.to_str().unwrap()))
                    .arg("-Ctarget-cpu=native")
                    .arg("-Copt-level=3")
                    .arg("--edition=2018")
                    .arg("--deny=warnings")
                    .arg("--")
                    .arg(src_path.as_ref())
                    .output()
                    .expect("Compilation failed");

                assert!(
                    rustc_output.status.success(),
                    "Compilation failed:\n{}",
                    String::from_utf8_lossy(&rustc_output.stderr)
                );

                exe_path
            });

            let report: BasicProfReport = run_exe(&exe_path, iters, extra_stdin, expected_stdout);

            assert_eq!(report.total_calls, iters);

            Duration::from_nanos(report.total_clock_nanos)
        })
    });
}

// N.B. GHC uses the British English spelling 'centre'

#[derive(Clone, Debug, Deserialize)]
struct GhcProfReport {
    total_time: f64,
    total_ticks: u64,
    tick_interval: f64,
    cost_centres: Vec<GhcCostCentre>,
    profile: GhcProfileTree,
}

#[derive(Clone, Debug, Deserialize)]
struct GhcCostCentre {
    id: u32,
    label: String,
}

#[derive(Clone, Debug, Deserialize)]
struct GhcProfileTree {
    id: u32,
    entries: u64,
    ticks: u64,
    children: Vec<GhcProfileTree>,
}

fn find_ghc_cost_centre_in_tree(tree: &GhcProfileTree, id: u32) -> Option<&GhcProfileTree> {
    if tree.id == id {
        return Some(tree);
    }

    for child in &tree.children {
        if let Some(found) = find_ghc_cost_centre_in_tree(child, id) {
            return Some(found);
        }
    }

    None
}

fn find_labeled_ghc_cost_centre<'a>(report: &'a GhcProfReport, label: &str) -> &'a GhcProfileTree {
    let id = report
        .cost_centres
        .iter()
        .find(|cost_centre| &cost_centre.label == label)
        .unwrap_or_else(|| panic!("Could not find cost centre with label {}", label))
        .id;

    find_ghc_cost_centre_in_tree(&report.profile, id)
        .unwrap_or_else(|| panic!("Cost centre with id {} not found", id))
}

fn bench_haskell_sample(
    g: &mut BenchmarkGroup<WallTime>,
    bench_name: &str,
    src_path: impl AsRef<Path>,
    cost_centre: &str,
    extra_stdin: &str,
    expected_stdout: &str,
) {
    let mut exe_path_cache = None;

    g.bench_function(bench_name, |b| {
        b.iter_custom(|iters| {
            let exe_path = exe_path_cache.get_or_insert_with(|| {
                let exe_path = tempfile::Builder::new()
                    .prefix(".tmp-exe-")
                    .tempfile_in("")
                    .expect("Could not create temp file")
                    .into_temp_path();

                let out_dir = tempfile::Builder::new()
                    .prefix(".tmp-ghc-out-")
                    .tempdir_in("")
                    .expect("Could not create temp directory");

                let ghc_output = process::Command::new("ghc")
                    .arg("-o")
                    .arg(&exe_path)
                    .arg("-odir")
                    .arg(out_dir.as_ref())
                    .arg("-hidir")
                    .arg(out_dir.as_ref())
                    .arg("-O2")
                    .arg("-prof")
                    .arg("-rtsopts")
                    .arg("-Wall")
                    .arg("-Werror")
                    .arg("samples/haskell_samples/BenchCommon.hs")
                    .arg(src_path.as_ref())
                    .arg("-main-is")
                    .arg(
                        src_path
                            .as_ref()
                            .file_stem()
                            .expect("Source path should have stem"),
                    )
                    .output()
                    .expect("Compilation failed");

                assert!(
                    ghc_output.status.success(),
                    "Compilation failed:\n{}",
                    String::from_utf8_lossy(&ghc_output.stderr)
                );

                exe_path
            });

            let report: GhcProfReport = run_ghc_exe(&exe_path, iters, extra_stdin, expected_stdout);

            let prof_tree = find_labeled_ghc_cost_centre(&report, cost_centre);

            // 'tick_interval' appears to be measured in microseconds, although I can't find this
            // documented anywhere.
            assert!(
                report.tick_interval * 1e-6 * (report.total_ticks as f64) - report.total_time
                    <= 0.01
            );

            assert!(prof_tree.children.is_empty());
            assert_eq!(prof_tree.entries, iters);

            // TODO: Should we have a check here to ensure the time resolution is sufficiently
            // precise to obtain a meaningful estimate?
            let tick_nanos = report.tick_interval * 1e3 * (prof_tree.ticks as f64);

            assert!(tick_nanos.is_finite());

            Duration::from_nanos(tick_nanos as u64)
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
        "bench_primes.mor",
        "samples/bench_primes.mor",
        &[],
        "count_primes",
        stdin,
        stdout,
    );

    bench_sample(
        &mut g,
        "bench_primes_iter.mor",
        "samples/bench_primes_iter.mor",
        &[],
        "count_primes",
        stdin,
        stdout,
    );

    bench_c_sample(
        &mut g,
        "bench_primes.c",
        "samples/c_samples/bench_primes.c",
        stdin,
        stdout,
    );

    bench_rust_sample(
        &mut g,
        "bench_primes.rs",
        "samples/rust_samples/bench_primes.rs",
        stdin,
        stdout,
    );

    bench_rust_sample(
        &mut g,
        "bench_primes_iter.rs",
        "samples/rust_samples/bench_primes_iter.rs",
        stdin,
        stdout,
    );
}

fn sample_quicksort(c: &mut Criterion) {
    let mut g = c.benchmark_group("quicksort");
    g.sample_size(10);

    let length = 1000;

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

    bench_sample(
        &mut g,
        "bench_quicksort.mor",
        "samples/bench_quicksort.mor",
        &[],
        "quicksort",
        &stdin,
        &stdout,
    );

    bench_rust_sample(
        &mut g,
        "bench_quicksort.rs",
        "samples/rust_samples/bench_quicksort.rs",
        &stdin,
        &stdout,
    );
}

fn sample_primes_sieve(c: &mut Criterion) {
    let mut g = c.benchmark_group("primes_sieve");
    g.sample_size(20);

    let stdin = "10000\n";
    let stdout = include_str!("../../samples/expected-output/primes_10000.txt");

    bench_sample(
        &mut g,
        "bench_primes_sieve.mor",
        "samples/bench_primes_sieve.mor",
        &[],
        "sieve",
        stdin,
        stdout,
    );

    bench_c_sample(
        &mut g,
        "bench_primes_sieve.c",
        "samples/c_samples/bench_primes_sieve.c",
        stdin,
        stdout,
    );

    bench_c_sample(
        &mut g,
        "bench_primes_sieve_boxed.c",
        "samples/c_samples/bench_primes_sieve_boxed.c",
        stdin,
        stdout,
    );

    bench_rust_sample(
        &mut g,
        "bench_primes_sieve.rs",
        "samples/rust_samples/bench_primes_sieve.rs",
        stdin,
        stdout,
    );

    bench_rust_sample(
        &mut g,
        "bench_primes_sieve_boxed.rs",
        "samples/rust_samples/bench_primes_sieve_boxed.rs",
        stdin,
        stdout,
    );

    g.measurement_time(Duration::from_secs(10));

    bench_haskell_sample(
        &mut g,
        "BenchPrimesSieve.hs",
        "samples/haskell_samples/BenchPrimesSieve.hs",
        "BenchPrimesSieve.sieve",
        stdin,
        stdout,
    );

    bench_haskell_sample(
        &mut g,
        "BenchPrimesSieveSeq.hs",
        "samples/haskell_samples/BenchPrimesSieveSeq.hs",
        "BenchPrimesSieveSeq.sieve",
        stdin,
        stdout,
    );

    bench_haskell_sample(
        &mut g,
        "BenchPrimesSieveArray.hs",
        "samples/haskell_samples/BenchPrimesSieveArray.hs",
        "BenchPrimesSieveArray.sieve",
        stdin,
        stdout,
    );
}

fn sample_words_trie(c: &mut Criterion) {
    let mut g = c.benchmark_group("words_trie");
    g.sample_size(20);
    g.measurement_time(Duration::from_secs(75));

    let stdin = concat!(
        include_str!("../../samples/sample-input/udhr.txt"),
        "\n",
        include_str!("../../samples/sample-input/udhr_queries.txt"),
        "\n",
    );

    let stdout = include_str!("../../samples/expected-output/udhr_query_counts.txt");

    bench_sample(
        &mut g,
        "bench_words_trie.mor",
        "samples/bench_words_trie.mor",
        &[],
        "count_words",
        stdin,
        stdout,
    );

    bench_rust_sample(
        &mut g,
        "bench_words_trie.rs",
        "samples/rust_samples/bench_words_trie.rs",
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

    sample_quicksort(&mut c);

    sample_primes(&mut c);

    sample_primes_sieve(&mut c);

    sample_words_trie(&mut c);
}
