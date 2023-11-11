import matplotlib.pyplot as plt
import os
import re
import json
from collections import defaultdict
import numpy as np

def parse_times(results_dir):
    all_times = defaultdict(dict)
    for fname in os.listdir(results_dir):
        # parse a filename of the form "bench_{name}.mor_native_{tag}.txt" into a tuple
        # (name, tag) using regular expressions
        match = re.match(r"^bench_(?P<name>[^\.]+)\.mor_native_(?P<tag>[a-zA-Z0-9_]+)\.txt$", fname)
        if not match:
            continue
        # the file contains a comma-separated list of integers, which we can parse as a JSON array
        with open(os.path.join(results_dir, fname), "r") as f:
            times = json.load(f)
        all_times[match.group("name")][match.group("tag")] = np.mean(times)
    return all_times

def get_speedups(all_times):
    speedups = dict()
    for name, times in all_times.items():
        baseline = times["trivial"]
        elide = times["elide"]
        speedup = baseline / elide
        print(f"{name}: {speedup:.2f}x")
        speedups[name] = speedup
    return speedups

def plot_speedups(speedups):
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
    plt.title("Speedup due to full borrow inference vs perceus")
    plt.tight_layout()
    os.makedirs("figure_out", exist_ok=True)
    plt.savefig("figure_out/speedups.png")
    plt.show()

def main():
    all_times = parse_times("target/run_time/")
    speedups = get_speedups(all_times)
    plot_speedups(speedups)

if __name__ == "__main__":
    main()
