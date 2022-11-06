from typing import List
import matplotlib.pyplot as plt
import os.path
import re
import json
import numpy as np
from dataclasses import dataclass


@dataclass
class Interval:
    estimate: float
    lo: float
    hi: float


@dataclass
class Experiment:
    name: str
    baseline_nanos: Interval
    defunc_nanos: Interval


@dataclass
class Results:
    experiments: List[Experiment]


def parse_mean_interval(path: str) -> Interval:
    with open(path, "r") as f:
        content = json.load(f)
    return Interval(
        content["mean"]["point_estimate"],
        content["mean"]["confidence_interval"]["lower_bound"],
        content["mean"]["confidence_interval"]["upper_bound"],
    )


def parse_benchmarks(tag: str, criterion_path: str) -> Results:
    results = []
    for group in os.listdir(criterion_path):
        benchmarks = set(os.listdir(os.path.join(criterion_path, group)))
        for baseline_dir in benchmarks:
            if tag == "sml" or tag == "ocaml":
                baseline_tag = f"{tag}_typed"
                defunc_tag = f"{tag}_first_order"
            elif tag == "native":
                baseline_tag = "native_single"
                defunc_tag = "native_specialize"
            else:
                raise ValueError(f"Unknown tag {tag}")
            regex = r"^(?P<name>[^\.]+)\.mor_(?P<baseline_tag>[a-zA-Z0-9_]+)$"
            match = re.match(regex, baseline_dir)
            if not match or match.group("baseline_tag") != baseline_tag:
                continue
            name = match.group("name")
            defunc_dir = f"{name}.mor_{defunc_tag}"
            if defunc_dir not in benchmarks:
                continue
            baseline_nanos = parse_mean_interval(
                os.path.join(
                    criterion_path, group, baseline_dir, "new", "estimates.json"
                )
            )
            defunc_nanos = parse_mean_interval(
                os.path.join(
                    criterion_path, group, defunc_dir, "new", "estimates.json"
                )
            )
            results.append(Experiment(name, baseline_nanos, defunc_nanos))
    return Results(results)


def plot_results(title: str, results: Results, out_path: str) -> None:
    # Plot a bar chart of the relative increase in speed of the defunctionalized version
    # of each benchmark.
    fig, ax = plt.subplots()
    ax.set_title(title)
    ax.set_xlabel("Relative speedup from Morphic defunctionalization")
    ax.set_ylabel("Benchmark")
    names = [e.name for e in results.experiments]
    names = [re.sub(r"^bench_", "", name) for name in names]
    baseline_nanos = [e.baseline_nanos.estimate for e in results.experiments]
    defunc_nanos = [e.defunc_nanos.estimate for e in results.experiments]
    speedups = [b / d - 1.0 for b, d in zip(baseline_nanos, defunc_nanos)]
    x_range = int(np.ceil(max(speedups) * 1.1))
    # Sort by speedup.
    names, speedups = zip(*sorted(zip(names, speedups), key=lambda x: x[1]))
    # label the x axis with ticks of the form "+percent%", computed programmatically
    base = 5
    nearest_power = base ** int(np.ceil(np.log(x_range) / np.log(base)))
    x_ticks = np.linspace(0, nearest_power, 6)
    x_tick_labels = [f"+{int(100 * x)}%" for x in x_ticks]
    ax.set_xlim(0.0, x_range)
    ax.set_xticks(x_ticks)
    ax.set_xticklabels(x_tick_labels)
    ax.barh(names, speedups)
    # label each bar with its speedup
    for i, speedup in enumerate(speedups):
        ax.text(speedup, i, f"{int(100 * speedup)}%", va="center", ha="left")
    # ensure labels are not cut off
    fig.tight_layout()
    fig.savefig(out_path)


def main():
    script_dir = os.path.dirname(os.path.realpath(__file__))
    for tag in ["sml", "ocaml", "native"]:
        results = parse_benchmarks(tag, os.path.join(script_dir, "..", "target", "criterion"))
        if not results.experiments:
            continue
        out_dir = os.path.join(script_dir, "out")
        os.makedirs(out_dir, exist_ok=True)
        if tag == "sml":
            title = "MLton"
        elif tag == "ocaml":
            title = "OCaml"
        elif tag == "native":
            title = "Native"
        plot_results(
            f"{title} Benchmarks",
            results,
            os.path.join(out_dir, f"{tag}_benchmarks.png"),
        )


if __name__ == "__main__":
    main()
