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

def plot_speedups_and_rcs(name, speedups, rcs):
    plt.style.use('seaborn-v0_8-whitegrid')
    
    # Create a figure with two subplots side by side
    # Letter size in inches is 8.5 x 11
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.5, 4.25))
    
    # First subplot: Speedups
    names = sorted(speedups.keys())
    x = np.arange(len(names))
    width = 0.5
    
    medians = [speedups[benchmark][1] for benchmark in names]
    bars1 = ax1.bar(x, medians, width, color='#1a85ff', alpha=0.8)
    
    q1s = [speedups[benchmark][0] for benchmark in names]
    q3s = [speedups[benchmark][2] for benchmark in names]
    yerr_low = np.maximum(0, np.array(medians) - np.array(q1s))
    yerr_high = np.maximum(0, np.array(q3s) - np.array(medians))
    yerr = np.array([yerr_low, yerr_high])
    ax1.errorbar(x, medians, yerr=yerr, fmt='none', color='#404040',
                capsize=4, capthick=1.5, elinewidth=1.5)

    ax1.set_ylabel("Speedup", fontsize=10, fontweight='bold')
    ax1.set_xticks(x)
    ax1.set_xticklabels(names, rotation=45, ha="right", fontsize=8)
    ax1.tick_params(axis='y', labelsize=8)
    
    for i, v in enumerate(medians):
        ax1.text(i, v + 0.05, f"{v:.2f}x", ha="center", va="bottom",
                fontsize=8, color='#404040')
    
    ax1.set_ylim(0, 4)
    ax1.axhline(1, color="#404040", linewidth=1, linestyle="--", alpha=0.5)
    ax1.set_title("Speedup vs Perceus", fontsize=10, fontweight='bold', pad=10)
    
    # Second subplot: RC counts
    retain_counts, release_counts = rcs
    names = sorted(retain_counts.keys())
    
    percentages = []
    for name in names:
        baseline_retains = retain_counts[name]["perceus"]
        optimized_retains = retain_counts[name]["default"]
        percent_omitted = ((baseline_retains - optimized_retains) / baseline_retains) * 100 if baseline_retains != 0 else 0
        percentages.append(percent_omitted)
        
    x = np.arange(len(names))
    bars2 = ax2.bar(x, percentages, width, color='#1a85ff', alpha=0.8)
    
    ax2.set_ylabel("Percent of Retains Omitted", fontsize=10, fontweight='bold')
    ax2.set_title("RC Retains Eliminated", fontsize=10, fontweight='bold', pad=10)
    ax2.set_xticks(x)
    ax2.set_xticklabels(names, rotation=45, ha="right", fontsize=8)
    ax2.tick_params(axis='y', labelsize=8)
    
    ax2.set_ylim(0, 100)
    
    for i, bar in enumerate(bars2):
        height = bar.get_height()
        ax2.text(bar.get_x() + bar.get_width()/2., height,
                f'{percentages[i]:.1f}%',
                ha='center', va='bottom',
                fontsize=8, color='#404040')
    
    ax2.axhline(y=0, color='#404040', linestyle='-', linewidth=0.5, alpha=0.5)
    
    # Adjust layout and save
    plt.tight_layout()
    os.makedirs("figure_out", exist_ok=True)
    plt.savefig(f"figure_out/combined_{name}.png", dpi=300, bbox_inches='tight')
    plt.show()

def plot_time_per_rc(name, all_times, rcs):
    plt.style.use('seaborn-v0_8-whitegrid')
    fig, ax = plt.subplots(figsize=(8.5, 4.25))
    
    retain_counts, release_counts = rcs
    names = sorted(retain_counts.keys())
    
    time_per_rc = []
    for benchmark in names:
        if not (all_times[benchmark]):
            continue
        baseline_time = all_times[benchmark]["perceus"][1]  # median time
        optimized_time = all_times[benchmark]["default"][1]  # median time
        baseline_retains = retain_counts[benchmark]["perceus"]
        optimized_retains = retain_counts[benchmark]["default"]
        rc_eliminated = baseline_retains - optimized_retains
        print(f"Benchmark: {name}")
        print(baseline_time)
        print(optimized_time)
        print(baseline_retains)
        print(optimized_retains)
        print(rc_eliminated)
        if rc_eliminated > 0:
            time_diff = baseline_time - optimized_time
            time_per_rc.append((time_diff / rc_eliminated))  # convert to ns
        else:
            time_per_rc.append(0)
    
    x = np.arange(len(names))
    width = 0.5
    bars = ax.bar(x, time_per_rc, width, color='#1a85ff', alpha=0.8)
    
    ax.set_ylabel("Time per RC Operation (ns)", fontsize=10, fontweight='bold')
    ax.set_title("Time Saved per Reference Count Operation", fontsize=10, fontweight='bold', pad=10)
    ax.set_xticks(x)
    ax.set_xticklabels(names, rotation=45, ha="right", fontsize=8)
    ax.tick_params(axis='y', labelsize=8)
    
    for i, v in enumerate(time_per_rc):
        ax.text(i, v, f"{v:.1f}ns", ha="center", va="bottom", fontsize=8, color='#404040')
    
    plt.tight_layout()
    os.makedirs("figure_out", exist_ok=True)
    plt.savefig(f"figure_out/time_per_rc_{name}.png", dpi=300, bbox_inches='tight')
    plt.show()


def plot_speedups(name, speedups):
    # Call the combined plotting function
    all_times = parse_times("target/run_time/")
    rcs = parse_rcs("target/rc_count/")
    plot_speedups_and_rcs(name, speedups, rcs)

def main():
    all_times = parse_times("target/run_time/")
    rcs = parse_rcs("target/rc_count/")
    plot_speedups("perceus", get_speedups("perceus", all_times))
    plot_time_per_rc("perceus", all_times, rcs)

if __name__ == "__main__":
    main()
