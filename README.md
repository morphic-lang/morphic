# Borrow Inference: Experimental Evaluation

## Changes for Major Revision

We plan to add some additional benchmarks in our major revision, but the benchmarking harness and the plotting code will not change significantly (at least in-so-far as the steps required to run them).

## Introduction

This artifact consists of the Morphic compiler and its benchmarking harness. It supports the empirical claims made in our paper, namely:

- Our novel "borrow inference" technique is able to eliminate reference count increments relative to a Perceus baseline (a state-of-the-art technique for static reference count elision).
- This improves overall program performance.

In particular, this artifact reproduces Figure 10 from our paper.

## Getting Started Guide

To run the benchmark suite, run the following command in the root of the `morphic/` project directory:

```bash
$ cargo run --release -p benchmark
```

After running the benchmarks, you can view a summary of the run time results by running the script `summarize_results.py`:

```bash
$ python3 summarize_results.py
```

This will produce Figure 10 from our paper in directory `figure_out`.

## Step by Step Instructions

### How do I run the benchmarks from the paper?

The file `crates/benchmark/src/main.rs` contains the implementation of the evaluation harness which we use for all experiments. Running this harness via `cargo run --release -p benchmark` will automatically:

1. Compile each benchmark under the Morphic compiler and produce:
   - Pretty-printed program intermediate representations in
     - `out2/<benchmark>.mor_default_rc-artifacts`
     - `out2/<benchmark>.mor_default_time-artifacts`
     - `out2/<benchmark>.mor_perceus_rc-artifacts`
     - `out2/<benchmark>.mor_perceus_time-artifacts`
   - Binaries
     - `out2/<benchmark>.mor_default_rc`
     - `out2/<benchmark>.mor_default_time`
     - `out2/<benchmark>.mor_perceus_rc`
     - `out2/<benchmark>.mor_perceus_time`
2. Run each benchmark for a set number of iterations, check its output for correctness, and produce:
   - The runtime under borrow inference in `target/run_time/<benchmark>.mor_default_time.txt`.
   - The number of RC increments ("dups") under borrow inference in `target/run_time/<benchmark>.mor_default_rc.txt`.
   - The runtime under our implementation of Perceus in `target/run_time/<benchmark>.mor_perceus_time.txt`.
   - The number of RC increments ("dups") under our implementation of Perceus in `target/run_time/<benchmark>.mor_perceus_rc.txt`.

Step 1 will be skipped for benchmarks whose binaries are already present in `out2`, so `out2` must be deleted to regenerate the binaries. In general, if you get into a weird state, deleting `out2` and `target` will probably fix it.

After populating `target/run_time` with measurements, you can view a summary of the results by running the following script

```bash
$ python3 summarize_results.py
```

For each benchmark, this will calculate the mean run time of one iteration of the benchmark's inner loop under borrow inference and under Perceus, and plot the ratio of the latter to the former. It will also calculate and plot the percentage decrease in RC increments under borrow inference as compared to Perceus. This is intended to support the run time speedup and RC increment reduction claims in the evaluation section of our paper (Figure 10).

### Where can I find the Morphic source for the benchmarks?

The Morphic source code for all benchmarks can be found in the `samples/` directory, alongside a number of other sample Morphic programs used in the compiler's internal test suite for correctness testing. All Morphic programs participating in benchmarking have filenames beginning with the "`bench_`" prefix. Some of the code for these benchmarks is factored out into common libraries, which can be found in the `samples/lib` directory.

## Reusability Guide

The Morphic compiler as a whole should be evaluated for reusability. This project was built on top of an existing version of the Morphic compiler and it is suitable for further extension. Each compiler pass is written as a transformation between two ASTs expressing the pass invariants. These ASTs can be found in `morphic/crates/morphic_common/src/data`. The passes particular to borrow inference are invoked from `compile_to_low_ast` in `morphic/crates/morphic_backend/src/lib.rs` beginning with `guard_types` and ending with `rc_specialize`.
