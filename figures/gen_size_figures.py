from typing import List, Optional, Dict
from collections import defaultdict
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
    mono_bytes: Optional[int]
    defunc_bytes: int


@dataclass
class Results:
    experiments: List[Experiment]


deny_list = ["words_trie", "primes"]


def parse_sizes(tag: str, sizes_dir: str) -> Results:
    if tag == "sml" or tag == "ocaml":
        baseline_tag = f"{tag}_typed"
        mono_tag = f"{tag}_mono"
        defunc_tag = f"{tag}_first_order"
    elif tag == "native":
        baseline_tag = "native_single"
        mono_tag = None
        defunc_tag = "native_specialize"
    else:
        raise ValueError(f"Unknown tag {tag}")

    baseline_regex = (
        r"^bench_(?P<name>[^\.]+)\.mor_(?P<baseline_tag>[a-zA-Z0-9_]+)\.txt$"
    )

    results = []

    fnames = set(os.listdir(sizes_dir))
    for fname in fnames:
        match = re.match(baseline_regex, fname)
        if not match or match.group("baseline_tag") != baseline_tag:
            continue
        name = match.group("name")
        if name in deny_list:
            continue
        defunc_fname = f"bench_{name}.mor_{defunc_tag}.txt"
        if defunc_fname not in fnames:
            continue
        with open(os.path.join(sizes_dir, fname), "r") as f:
            baseline_bytes = int(f.read())
        with open(os.path.join(sizes_dir, defunc_fname), "r") as f:
            defunc_bytes = int(f.read())
        if mono_tag is not None:
            mono_fname = f"bench_{name}.mor_{mono_tag}.txt"
            if mono_fname not in fnames:
                continue
            with open(os.path.join(sizes_dir, mono_fname), "r") as f:
                mono_bytes = int(f.read())
        else:
            mono_bytes = None
        results.append(Experiment(name, baseline_bytes, mono_bytes, defunc_bytes))

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
    mono_sizes = [e.mono_bytes for e in experiments]
    defunc_sizes = [e.defunc_bytes for e in experiments]
    # display bars in groups of 2
    x = np.arange(len(names))
    if all(m is not None for m in mono_sizes):
        width = 0.2
        ax.barh(x + width, baseline_sizes, width, label="Baseline")
        ax.barh(x, mono_sizes, width, label="Monomorphized")
        ax.barh(x - width, defunc_sizes, width, label="Defunctionalized")
    else:
        width = 0.35
        ax.barh(x + width / 2, baseline_sizes, width, label="Baseline")
        ax.barh(x - width / 2, defunc_sizes, width, label="Defunctionalized")
    ax.set_yticks(x)
    ax.set_yticklabels(names)
    # shrink the plot to make room for the legend in the y direction
    box = ax.get_position()
    ax.set_position([box.x0, box.y0 - box.height * 0.1, box.width, box.height * 1.1])
    # display the legend below the chart, and make space so it doesn't overlap with the x axis title
    fig.legend(loc="lower center", bbox_to_anchor=(0.5, 0.01), ncol=3, fontsize="small")
    fig.tight_layout()
    fig.savefig(out_path)

colors = {
    "OCaml": "#ee6a1a",
    # "MLton": "#ff1e5c",
    "MLton": "#dc566d",
    "Morphic": "#1a85ff",
}

# def plot_all_sizes(title: str, results: Dict[str, Results], out_path: str) -> None:
#     lang_names = list(results.keys())
#     bench_names = set()
#     for lang_results in results.values():
#         for experiment in lang_results.experiments:
#             bench_names.add(experiment.name)
#     bench_names = sorted(bench_names)
#     bench_indices = {name: i for i, name in enumerate(bench_names)}

#     x = np.arange(len(bench_names))
#     width = 0.8 / len(lang_names)

#     plt.style.use("ggplot")
#     fig, ax = plt.subplots()
#     ax.set_title(title)
#     ax.set_xlabel("Benchmark")
#     ax.set_ylabel("Size Ratio")
#     ax.set_xticks(x)
#     ax.set_xticklabels(bench_names)
#     ax.set_ylim(0, 1.5)

#     for i, lang_name in enumerate(lang_names):
#         lang_results = results[lang_name]
#         baseline_sizes = [e.baseline_bytes for e in lang_results.experiments]
#         defunc_sizes = [e.defunc_bytes for e in lang_results.experiments]
#         ratios = [d / b for b, d in zip(baseline_sizes, defunc_sizes)]
#         offset = i * width - width * (len(lang_names) - 1) / 2
#         lang_x = [bench_indices[e.name] + offset for e in lang_results.experiments]
#         ax.bar(lang_x, ratios, width * 0.9, label=lang_name, color=colors[lang_name])
#         # add text labels for each bar
#         # for x, ratio in zip(lang_x, ratios):
#         #     ax.text(x, ratio + 0.05, f"{ratio:.2f}×", ha="center", va="bottom", fontsize=5)

#     plt.axhline(y=1, color="black", linestyle="--")

#     # shrink the plot to make room for the legend in the y direction
#     box = ax.get_position()
#     ax.set_position([box.x0, box.y0 - box.height * 0.08, box.width, box.height * 1.08])
#     # display the legend below the chart, and make space so it doesn't overlap with the x axis title
#     fig.legend(loc="lower center", bbox_to_anchor=(0.5, 0.01), ncol=3, fontsize="small")
#     fig.tight_layout()
#     fig.savefig(f"{out_path}.png")
#     fig.savefig(f"{out_path}.pdf")

def plot_all_sizes(title: str, results: Dict[str, Results], out_path: str) -> None:
    lang_names = list(results.keys())
    bench_names = set()
    for lang_results in results.values():
        for experiment in lang_results.experiments:
            bench_names.add(experiment.name)
    bench_names = list(reversed(sorted(bench_names)))
    bench_indices = {name: i for i, name in enumerate(bench_names)}

    x = np.arange(len(bench_names))
    width = 0.8 / len(lang_names)

    plt.style.use("bmh")
    fig, ax = plt.subplots()
    ax.set_title(title)
    # ax.set_ylabel("Benchmark")
    ax.set_xlabel("Size Ratio (Lower is Better)")
    ax.set_yticks(x)
    ax.set_yticklabels(bench_names)
    ax.set_xlim(0, 1.6)

    for i, lang_name in enumerate(lang_names):
        lang_results = results[lang_name]
        baseline_sizes = [e.baseline_bytes for e in lang_results.experiments]
        defunc_sizes = [e.defunc_bytes for e in lang_results.experiments]
        ratios = [d / b for b, d in zip(baseline_sizes, defunc_sizes)]
        offset = -(i * width - width * (len(lang_names) - 1) / 2)
        lang_x = [bench_indices[e.name] + offset for e in lang_results.experiments]
        ax.barh(lang_x, ratios, width * 0.9, label=lang_name, color=colors[lang_name])
        # add text labels for each bar
        for x, ratio in zip(lang_x, ratios):
            if 0.9 < ratio < 1.0:
                text_pos = 1.1
            else:
                text_pos = ratio + 0.08
            # text_offset = 0.1 if 0.9 < ratio
            ax.text(text_pos, x - width / 2, f"{ratio:.2f}×", ha="center", va="bottom", fontsize=10)

    plt.axvline(x=1, color="black", linestyle="--")

    # shrink the plot to make room for the legend in the y direction
    box = ax.get_position()
    ax.set_position([box.x0, box.y0 - box.height * 0.08, box.width, box.height * 1.08])
    # display the legend below the chart, and make space so it doesn't overlap with the x axis title
    fig.legend(loc="lower center", bbox_to_anchor=(0.5, 0.01), ncol=3, fontsize="small")
    fig.tight_layout()
    fig.savefig(f"{out_path}.png")
    fig.savefig(f"{out_path}.pdf")

    # bars = defaultdict(defaultdict)
    # for lang, r in results.items():
    #     for e in r.experiments:
    #         bars[e.name][lang] = e.defunc_bytes / e.baseline_bytes
    # bench_names = sorted(bars.keys())

    # width = 0.7 / len(results)
    # offsets = {
    #     t: offset
    #     for t, offset in zip(
    #         results.keys(),
    #         np.linspace(
    #             -width * len(results) / 2, width * len(results) / 2, len(results)
    #         ),
    #     )
    # }
    # fig, ax = plt.subplots()
    # ax.set_title(title)
    # ax.set_xlabel("Benchmark")
    # ax.set_ylabel("Defunctionalized size / baseline size")
    # for i, bench_name in enumerate(bench_names):
    #     for lang, ratio in bars[bench_name].items():
    #         ax.bar(i + offsets[lang], ratio, width, label=lang)
    # ax.set_xticks(range(len(bench_names)))
    # ax.set_xticklabels(bench_names)
    # # shrink the plot to make room for the legend in the y direction
    # box = ax.get_position()
    # ax.set_position([box.x0, box.y0 - box.height * 0.1, box.width, box.height * 1.1])
    # # display the legend below the chart, and make space so it doesn't overlap with the x axis title
    # fig.legend(loc="lower center", bbox_to_anchor=(0.5, 0.01), ncol=3, fontsize="small")
    # fig.tight_layout()
    # fig.savefig(out_path)


def main() -> None:
    script_dir = os.path.dirname(os.path.realpath(__file__))
    sizes_dir = os.path.join(script_dir, "..", "target", "binary_sizes")
    out_dir = os.path.join(script_dir, "..", "figures", "out", "binary_sizes")
    os.makedirs(out_dir, exist_ok=True)

    results_sml = parse_sizes("sml", sizes_dir)
    plot_sizes("SML", results_sml, os.path.join(out_dir, "sml_sizes.png"))

    results_ocaml = parse_sizes("ocaml", sizes_dir)
    plot_sizes("OCaml", results_ocaml, os.path.join(out_dir, "ocaml_sizes.png"))

    results_native = parse_sizes("native", sizes_dir)
    plot_sizes("Native", results_native, os.path.join(out_dir, "native_sizes.png"))

    results_all = {
        "MLton": results_sml,
        "OCaml": results_ocaml,
        "Morphic": results_native,
    }
    plot_all_sizes(
        "Binary Sizes: Effect of Specializing Defunc.",
        results_all,
        os.path.join(out_dir, "all_sizes"),
    )


if __name__ == "__main__":
    main()
