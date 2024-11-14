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
        # Calculate quartiles (25%, 50% (median), 75%)
        quartiles = np.percentile(times, [25, 50, 75])
        all_times[match.group("name")][match.group("tag")] = quartiles
    return all_times

def parse_rcs(results_dir):
    retain_counts = defaultdict(dict)
    release_counts = defaultdict(dict)
    rc1_counts = defaultdict(dict)
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
        rc1_counts[match.group("name")][match.group("tag")] = rcs[0]["total_rc1_count"]
    return (retain_counts, release_counts)

def get_speedups(bench_name, all_times):
    speedups = dict()
    for name, times in all_times.items():
        baseline = times[bench_name]  # [Q1, median, Q3]
        elide = times["default"]      # [Q1, median, Q3]
        # Calculate speedup for each quartile
        q1_speedup = baseline[0] / elide[0]      # Q1 speedup
        median_speedup = baseline[1] / elide[1]   # median speedup
        q3_speedup = baseline[2] / elide[2]      # Q3 speedup
        speedups[name] = [q1_speedup, median_speedup, q3_speedup]
        print(f"{name}: Q1={q1_speedup:.2f}x, median={median_speedup:.2f}x, Q3={q3_speedup:.2f}x")
    return speedups

def plot_speedups(name, speedups):
    names = sorted(speedups.keys())
    plt.figure(figsize=(8, 4))
    
    x = np.arange(len(names))
    width = 0.6
    
    # Create bars for median speedup (using index 1 for median from speedups)
    medians = [speedups[benchmark][1] for benchmark in names]
    bars = plt.bar(x, medians, width, color='blue')
    
    # Add error bars for Q1 and Q3
    q1s = [speedups[benchmark][0] for benchmark in names]
    q3s = [speedups[benchmark][2] for benchmark in names]
    yerr = np.array([(m-q1, q3-m) for m, q1, q3 in zip(medians, q1s, q3s)]).T
    # Ensure yerr values are non-negative
    yerr_low = np.maximum(0, np.array(medians) - np.array(q1s))
    yerr_high = np.maximum(0, np.array(q3s) - np.array(medians))
    yerr = np.array([yerr_low, yerr_high])
    plt.errorbar(x, medians, yerr=yerr, fmt='none', color='black', capsize=5, capthick=1, elinewidth=2)
    plt.ylabel("Speedup")
    plt.xticks(x, names, rotation=45, ha="right")
    
    # Add labels for median values
    for i, v in enumerate(medians):
        plt.text(i, v + 0.05, f"{v:.2f}", ha="center", va="bottom")
    
    plt.ylim(0, 8.5)
    # Add a horizontal line at y=1
    plt.axhline(1, color="black", linewidth=1, linestyle="--")
    plt.title(f"Speedup due to full borrow inference vs {name}")
    
    plt.tight_layout()
    os.makedirs("figure_out", exist_ok=True)
    plt.savefig(f"figure_out/speedups_{name}.png")
    plt.show()

def plot_rcs(rcs):
    retain_counts, release_counts = rcs
    names = sorted(retain_counts.keys())
    
    # Create a single figure
    plt.figure(figsize=(10, 6))
    
    configs = ["default", "perceus"]
    
    # Calculate percentage of retains omitted for each benchmark
    percentages = []
    for name in names:
        baseline_retains = retain_counts[name]["perceus"]  # perceus is the baseline
        optimized_retains = retain_counts[name]["default"]  # default is the optimized version
        if baseline_retains == 0:
            percent_omitted = 0  # If there are no retains in baseline, we consider 0% omitted
        else:
            percent_omitted = ((baseline_retains - optimized_retains) / baseline_retains) * 100
        percentages.append(percent_omitted)
        
    # Create bars
    x = np.arange(len(names))
    width = 0.6
    bars = plt.bar(x, percentages, width, color='blue')
    
    # Customize the plot
    plt.ylabel("Percent of Retains Omitted")
    plt.title("RC Retains Eliminated by Benchmark")
    plt.xticks(x, names, rotation=45, ha="right")
    
    # Set y-axis to go from 0 to 100%
    plt.ylim(0, 100)
    
    # Add value labels on top of bars
    for i, bar in enumerate(bars):
        height = bar.get_height()
        plt.text(bar.get_x() + bar.get_width()/2., height,
                f'{percentages[i]:.1f}%',
                ha='center', va='bottom')
    
    # Add horizontal line at 0%
    plt.axhline(y=0, color='black', linestyle='-', linewidth=0.5)
    
    plt.tight_layout()
    os.makedirs("figure_out", exist_ok=True)
    plt.savefig(f"figure_out/rcs.png")
    plt.show()

def main():
    all_times = parse_times("target/run_time/")
    rcs = parse_rcs("target/rc_count/")
    plot_speedups("perceus", get_speedups("perceus", all_times))
    # plot_speedups("immutable_beans", get_speedups("immutable_beans", all_times))
    plot_rcs(rcs)

if __name__ == "__main__":
    main()
