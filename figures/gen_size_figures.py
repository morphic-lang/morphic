from typing import List
import matplotlib.pyplot as plt
import os.path
import re
import json
import numpy as np
from dataclasses import dataclass


@dataclass
class Experiment:
    name: str
    baseline_bytes: int
    defunc_bytes: int


@dataclass
class Results:
    experiments: List[Experiment]


def parse_sizes(tag: str, sizes_dir: str) -> Results:
    if tag == "sml" or tag == "ocaml":
        baseline_tag = f"{tag}_typed"
        defunc_tag = f"{tag}_first_order"
    elif tag == "native":
        baseline_tag = "native_single"
        defunc_tag = "native_specialize"
    else:
        raise ValueError(f"Unknown tag {tag}")

    baseline_regex = r"^(?P<name>[^\.]+)\.mor_(?P<baseline_tag>[a-zA-Z0-9_]+)\.txt$"

    results = []

    fnames = set(os.listdir(sizes_dir))
    for fname in fnames:
        match = re.match(baseline_regex, fname)
        if not match or match.group("baseline_tag") != baseline_tag:
            continue
        name = match.group("name")
        defunc_fname = f"{name}.mor_{defunc_tag}.txt"
        if defunc_fname not in fnames:
            continue
        with open(os.path.join(sizes_dir, fname), "r") as f:
            baseline_bytes = int(f.read())
        with open(os.path.join(sizes_dir, defunc_fname), "r") as f:
            defunc_bytes = int(f.read())
        results.append(Experiment(name, baseline_bytes, defunc_bytes))

    return Results(results)


def plot_sizes(title: str, results: Results, out_path: str) -> None:
    # Sort by baseline size
    experiments = sorted(results.experiments, key=lambda e: e.baseline_bytes)
    # Plot a horizontal bar chart consisting of two bars per benchmark, one for the baseline and one
    # for the defunctionalized version.
    fig, ax = plt.subplots()
    ax.set_title(title)
    ax.set_xlabel("Size (bytes)")
    ax.set_ylabel("Benchmark")
    names = [e.name for e in experiments]
    baseline_sizes = [e.baseline_bytes for e in experiments]
    defunc_sizes = [e.defunc_bytes for e in experiments]
    # display bars in groups of 2
    width = 0.35
    x = np.arange(len(names))
    ax.barh(x - width / 2, baseline_sizes, width, label="Baseline")
    ax.barh(x + width / 2, defunc_sizes, width, label="Defunctionalized")
    ax.set_yticks(x)
    ax.set_yticklabels(names)
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_path)


def main() -> None:
    script_dir = os.path.dirname(os.path.realpath(__file__))
    sizes_dir = os.path.join(script_dir, "..", "target", "binary_sizes")
    out_dir = os.path.join(script_dir, "..", "figures", "out", "binary_sizes")
    os.makedirs(out_dir, exist_ok=True)

    results = parse_sizes("sml", sizes_dir)
    plot_sizes("SML", results, os.path.join(out_dir, "sml_sizes.png"))

    results = parse_sizes("ocaml", sizes_dir)
    plot_sizes("OCaml", results, os.path.join(out_dir, "ocaml_sizes.png"))

    results = parse_sizes("native", sizes_dir)
    plot_sizes("Native", results, os.path.join(out_dir, "native_sizes.png"))


if __name__ == "__main__":
    main()
