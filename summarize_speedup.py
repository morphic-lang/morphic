import matplotlib.pyplot as plt
import os
import re
import json
from collections import defaultdict
import numpy as np

def parse_times(results_dir):
    all_times = defaultdict(dict)
    for fname in os.listdir(results_dir):
        # parse a filename of the form "bench_{name}.mor_native_{tag}_time.txt" into a tuple
        # (name, tag) using regular expressions
        match = re.match(r"^bench_(?P<name>[^\.]+)\.mor_(?P<tag>[a-zA-Z0-9_]+)_time\.txt$", fname)
        if not match:
            continue
        # the file contains a comma-separated list of integers, which we can parse as a JSON array
        with open(os.path.join(results_dir, fname), "r") as f:
            times = json.load(f)
        all_times[match.group("name")][match.group("tag")] = np.mean(times)
    return all_times

def parse_rcs(results_dir):
    retain_counts = defaultdict(dict)
    release_counts = defaultdict(dict)
    for fname in os.listdir(results_dir):
        # parse a filename of the form "bench_{name}.mor_native_{tag}_time.txt" into a tuple
        # (name, tag) using regular expressions
        match = re.match(r"^bench_(?P<name>[^\.]+)\.mor_(?P<tag>[a-zA-Z0-9_]+)_rc\.txt$", fname)
        if not match:
            continue
        # the file contains a comma-separated list of integers, which we can parse as a JSON array
        with open(os.path.join(results_dir, fname), "r") as f:
            rcs = json.load(f)
        retain_counts[match.group("name")][match.group("tag")] = rcs[0]["total_retain_count"]
        release_counts[match.group("name")][match.group("tag")] = rcs[0]["total_release_count"]
    return (retain_counts, release_counts)

def get_speedups(bench_name, all_times):
    speedups = dict()
    for name, times in all_times.items():
        baseline = times[bench_name]
        elide = times["default"]
        speedup = baseline / elide
        print(f"{name}: {speedup:.2f}x")
        speedups[name] = speedup
    return speedups

def plot_speedups(name, speedups):
    names = sorted(speedups.keys())
    values = [speedups[name] for name in names]
    plt.figure(figsize=(8, 4))
    plt.bar(names, values)
    plt.ylabel("Speedup")
    plt.xticks(rotation=45, ha="right")
    # add a label over each bar
    for i, v in enumerate(values):
        plt.text(i, v + 0.05, f"{v:.2f}", ha="center", va="bottom")
    plt.ylim(0, 8.5)
    # add a horizontal line at y=1
    plt.axhline(1, color="black", linewidth=1, linestyle="--")
    plt.title(f"Speedup due to full borrow inference vs {name}")
    plt.tight_layout()
    os.makedirs("figure_out", exist_ok=True)
    plt.savefig(f"figure_out/speedups_{name}.png")
    plt.show()

def plot_rcs(rcs):
    retain_counts, release_counts = rcs
    names = sorted(retain_counts.keys())
    
    # Create a figure with a subplot for each benchmark
    num_benchmarks = len(names)
    fig, axes = plt.subplots(num_benchmarks, 1, figsize=(10, 4*num_benchmarks))
    
    configs = ["default", "perceus", "immutable_beans"]
    x = np.arange(len(configs))
    width = 0.35
    
    # Create a subplot for each benchmark
    for idx, name in enumerate(names):
        ax = axes[idx]
        
        # Get retain and release counts for this benchmark
        retains = [retain_counts[name][config] for config in configs]
        releases = [release_counts[name][config] for config in configs]
        
        # Plot bars for retain and release counts
        ax.bar(x - width/2, retains, width, label='Retain')
        ax.bar(x + width/2, releases, width, label='Release')
        ax.set_ylabel("Count")
        ax.set_title(f"RC Operations for {name}")
        ax.set_xticks(x)
        ax.set_xticklabels(configs, rotation=45, ha="right")
        ax.legend()
    
        # Add value labels on top of bars
        for i, v in enumerate(retains):
            ax.text(i - width/2, v, f'{v:,}', ha='center', va='bottom')
        for i, v in enumerate(releases):
            ax.text(i + width/2, v, f'{v:,}', ha='center', va='bottom')
    
    plt.tight_layout()
    os.makedirs("figure_out", exist_ok=True)
    plt.savefig(f"figure_out/rcs.png")
    plt.show()

def main():
    all_times = parse_times("target/run_time/")
    rcs = parse_rcs("target/rc_count/")
    plot_speedups("perceus", get_speedups("perceus", all_times))
    plot_speedups("immutable_beans", get_speedups("immutable_beans", all_times))
    plot_rcs(rcs)

if __name__ == "__main__":
    main()
