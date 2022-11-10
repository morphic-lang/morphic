from typing import List, Dict
import matplotlib.pyplot as plt
import os.path
import re
import json
import numpy as np
from dataclasses import dataclass
from collections import defaultdict


@dataclass
class Experiment:
    name: str

    baseline_nanos: float
    min_baseline_nanos: float
    max_baseline_nanos: float
    std_baseline_nanos: float

    defunc_nanos: float
    min_defunc_nanos: float
    max_defunc_nanos: float
    std_defunc_nanos: float


@dataclass
class Results:
    experiments: List[Experiment]


deny_list = ["words_trie", "primes"]


def parse_benchmarks(
    baseline_suffix: str, defunc_suffix: str, criterion_path: str
) -> Results:
    results = []
    regex = r"^bench_(?P<name>[^\.]+)\.mor_(?P<suffix>[a-zA-Z0-9_]+)$"
    for group in os.listdir(criterion_path):
        benchmarks = set(os.listdir(os.path.join(criterion_path, group)))
        for dir_name in benchmarks:
            match = re.match(regex, dir_name)
            if not match:
                continue
            name = match.group("name")
            if name in deny_list:
                continue
            suffix = match.group("suffix")
            if suffix != baseline_suffix:
                continue
            defunc_dir = f"bench_{name}.mor_{defunc_suffix}"
            if defunc_dir not in benchmarks:
                continue
            with open(
                os.path.join(criterion_path, group, dir_name, "new", "estimates.json"),
                "r",
            ) as f:
                baseline_nanos = json.load(f)["mean"]["point_estimate"]
            with open(
                os.path.join(
                    criterion_path, group, defunc_dir, "new", "estimates.json"
                ),
                "r",
            ) as f:
                defunc_nanos = json.load(f)["mean"]["point_estimate"]
            results.append(Experiment(name, baseline_nanos, defunc_nanos))
    return Results(results)


def parse_new_benchmarks(
    baseline_suffix: str, defunc_suffix: str, run_time_path: str
) -> Results:
    regex = r"^bench_(?P<name>[^\.]+)\.mor_(?P<suffix>[a-zA-Z0-9_]+)\.txt$"
    results = []
    fnames = set(os.listdir(run_time_path))
    for fname in sorted(fnames):
        match = re.match(regex, fname)
        if not match:
            continue
        name = match.group("name")
        if name in deny_list:
            continue
        suffix = match.group("suffix")
        if suffix != baseline_suffix:
            continue
        defunc_fname = f"bench_{name}.mor_{defunc_suffix}.txt"
        if defunc_fname not in fnames:
            continue
        with open(os.path.join(run_time_path, fname), "r") as f:
            data = json.load(f)
            print(fname, np.std(data) / np.mean(data))
            baseline_nanos = np.mean(data)
            min_baseline_nanos = np.min(data)
            max_baseline_nanos = np.max(data)
            std_baseline_nanos = np.std(data)
        with open(os.path.join(run_time_path, defunc_fname), "r") as f:
            data = json.load(f)
            print(defunc_fname, np.std(data) / np.mean(data))
            defunc_nanos = np.mean(data)
            min_defunc_nanos = np.min(data)
            max_defunc_nanos = np.max(data)
            std_defunc_nanos = np.std(data)
        results.append(
            Experiment(
                name,
                baseline_nanos,
                min_baseline_nanos,
                max_baseline_nanos,
                std_baseline_nanos,
                defunc_nanos,
                min_defunc_nanos,
                max_defunc_nanos,
                std_defunc_nanos,
            )
        )
    return Results(results)


colors = {
    "OCaml": "#ee6a1a",
    # "MLton": "#ff1e5c",
    "MLton": "#dc566d",
    "Morphic": "#1a85ff",
}


# def plot(title: str, results: Dict[str, Results], out_path: str) -> None:
#     lang_names = list(results.keys())
#     bench_names = set()
#     for lang_results in results.values():
#         for experiment in lang_results.experiments:
#             bench_names.add(experiment.name)
#     bench_names = sorted(bench_names)
#     bench_indices = {name: i for i, name in enumerate(bench_names)}

#     fig, ax = plt.subplots()
#     ax.set_title(title)
#     ax.set_ylabel("Speedup")
#     ax.set_xticks(np.arange(len(bench_names)))
#     ax.set_xticklabels(bench_names)

#     for i, lang_name in enumerate(lang_names):
#         offset = i * width - width * (len(lang_names) - 1) / 2
#         lang_results = results[lang_name]
#         xs = []
#         ys = []
#         for experiment in lang_results.experiments:
#             xs.append(bench_indices[experiment.name] + offset)
#             ys.append(experiment.baseline_nanos / experiment.defunc_nanos)
#         ax.bar(xs, ys, width * 0.9, label=lang_name, color=colors[lang_name])
#         # put a text label on top of each bar displaying its height
#         for x, y in zip(xs, ys):
#             ax.text(
#                 x,
#                 y + 0.05,
#                 f"{y:.2f}×",
#                 ha="center",
#                 va="bottom",
#                 fontsize=8 if len(lang_names) > 1 else 10,
#             )

#     plt.axhline(y=1, color="black", linestyle="--")

#     # shrink the plot to make room for the legend in the y direction
#     box = ax.get_position()
#     ax.set_position([box.x0, box.y0 - box.height * 0.08, box.width, box.height * 1.08])
#     # display the legend below the chart, and make space so it doesn't overlap with the x axis title
#     fig.legend(loc="lower center", bbox_to_anchor=(0.5, 0.01), ncol=3, fontsize="small")
#     fig.tight_layout()
#     fig.savefig(f"{out_path}.png")
#     fig.savefig(f"{out_path}.pdf")


def plot(title: str, results: Dict[str, Results], out_path: str) -> None:
    width = 0.8 / 2

    lang_names = list(results.keys())
    bench_names = set()
    for lang_results in results.values():
        for experiment in lang_results.experiments:
            bench_names.add(experiment.name)
    bench_names = list(reversed(sorted(bench_names)))
    bench_indices = {name: i for i, name in enumerate(bench_names)}

    fig, ax = plt.subplots()
    ax.set_title(title)
    ax.set_xlabel("Speedup Factor")
    ax.set_yticks(np.arange(len(bench_names)))
    ax.set_yticklabels(bench_names)

    max_ratio = max(
        experiment.baseline_nanos / experiment.defunc_nanos
        for lang_results in results.values()
        for experiment in lang_results.experiments
    )

    if max_ratio > 10:
        ax.set_xlim(0.0, max_ratio * 1.15)
    else:
        ax.set_xlim(0.0, max_ratio * 1.1)

    for i, lang_name in enumerate(lang_names):
        offset = -(i * width - width * (len(lang_names) - 1) / 2)
        lang_results = results[lang_name]
        xs = []
        ys = []
        err_min = []
        err_max = []
        for experiment in lang_results.experiments:
            xs.append(bench_indices[experiment.name] + offset)
            y = experiment.baseline_nanos / experiment.defunc_nanos
            ys.append(y)
            err_min.append(
                -(experiment.min_baseline_nanos / experiment.max_defunc_nanos - y)
            )
            err_max.append(
                experiment.max_baseline_nanos / experiment.min_defunc_nanos - y
            )
        ax.barh(
            xs,
            ys,
            width * 0.9,
            xerr=[err_min, err_max],
            label=lang_name,
            color=colors[lang_name],
        )
        # put a text label on top of each bar displaying its height
        for x, y, e in zip(xs, ys, err_max):
            ax.text(
                y + e + max_ratio * 0.01,
                x,
                f"{y:.2f}×",
                ha="left",
                va="center",
                # fontsize=10,
            )

    plt.axvline(x=1, color="black", linestyle="--")

    # shrink the plot to make room for the legend in the y direction
    box = ax.get_position()
    ax.set_position([box.x0, box.y0 - box.height * 0.08, box.width, box.height * 1.08])
    # display the legend below the chart, and make space so it doesn't overlap with the x axis title
    fig.legend(loc="lower center", bbox_to_anchor=(0.5, 0.01), ncol=3, fontsize="small")
    fig.tight_layout()
    fig.savefig(f"{out_path}.png")
    fig.savefig(f"{out_path}.pdf")


def plot_absolute(title: str, results: Dict[str, Results], out_path: str) -> None:
    width = 0.3 / 2

    lang_names = list(results.keys())
    bench_names = set()
    for lang_results in results.values():
        for experiment in lang_results.experiments:
            bench_names.add(experiment.name)
    bench_names = list(reversed(sorted(bench_names)))
    bench_indices = {name: i for i, name in enumerate(bench_names)}

    fastest = defaultdict(lambda: float("inf"))
    for lang_results in results.values():
        for experiment in lang_results.experiments:
            fastest[experiment.name] = min(
                fastest[experiment.name],
                experiment.baseline_nanos,
                experiment.defunc_nanos,
            )

    fig, ax = plt.subplots()
    ax.set_title(title)
    ax.set_xlabel("Run Time (Normalized to Fastest)")
    ax.set_yticks(np.arange(len(bench_names)))
    ax.set_yticklabels(bench_names)

    max_ratio = max(
        max(experiment.baseline_nanos, experiment.defunc_nanos)
        / fastest[experiment.name]
        for lang_results in results.values()
        for experiment in lang_results.experiments
    )

    # if max_ratio > 10:
    #     ax.set_xlim(0.0, max_ratio * 1.15)
    # else:
    #     ax.set_xlim(0.0, max_ratio * 1.1)

    ax.set_xscale("log")

    for i, lang_name in enumerate(lang_names):
        for j, tag in enumerate(["baseline", "LSS"]):
            k = i * 2 + j
            offset = -(k * width - width * (len(lang_names) * 2 - 1) / 2)
            lang_results = results[lang_name]
            xs = []
            ys = []
            err_min = []
            err_max = []
            for experiment in lang_results.experiments:
                xs.append(bench_indices[experiment.name] + offset)
                if tag == "baseline":
                    y = experiment.baseline_nanos / fastest[experiment.name]
                    std = experiment.std_baseline_nanos / fastest[experiment.name]
                elif tag == "LSS":
                    y = experiment.defunc_nanos / fastest[experiment.name]
                    std = experiment.std_defunc_nanos / fastest[experiment.name]
                else:
                    raise ValueError(tag)
                # y = experiment.baseline_nanos / experiment.defunc_nanos
                ys.append(y)
                err_min.append(std)
                err_max.append(std)
                # err_min.append(
                #     -(experiment.min_baseline_nanos / experiment.max_defunc_nanos - y)
                # )
                # err_max.append(
                #     experiment.max_baseline_nanos / experiment.min_defunc_nanos - y
                # )
            ax.barh(
                xs,
                ys,
                width * 0.9,
                xerr=[err_min, err_max],
                label=f"{lang_name} {tag}",
                color=colors[lang_name],
                hatch="/////" if tag == "baseline" else None,
                edgecolor="white",
            )
        # # put a text label on top of each bar displaying its height
        # for x, y, e in zip(xs, ys, err_max):
        #     ax.text(
        #         y + e + max_ratio * 0.01,
        #         x,
        #         f"{y:.2f}×",
        #         ha="left",
        #         va="center",
        #         # fontsize=10,
        #     )

    plt.axvline(x=1, color="black", linestyle="--")

    # shrink the plot to make room for the legend in the y direction
    box = ax.get_position()
    ax.set_position([box.x0, box.y0 - box.height * 0.08, box.width, box.height * 1.08])
    # display the legend below the chart, and make space so it doesn't overlap with the x axis title
    fig.legend(loc="lower center", bbox_to_anchor=(0.5, 0.01), ncol=3, fontsize="small")
    fig.tight_layout()
    fig.savefig(f"{out_path}.png")
    fig.savefig(f"{out_path}.pdf")


def main() -> None:
    script_dir = os.path.dirname(os.path.realpath(__file__))
    criterion_path = os.path.join(script_dir, "..", "target", "criterion")
    out_dir = os.path.join(script_dir, "..", "figures", "out")
    os.makedirs(out_dir, exist_ok=True)

    # results_sml = parse_benchmarks("sml_typed", "sml_first_order", criterion_path)
    # results_ocaml = parse_benchmarks("ocaml_typed", "ocaml_first_order", criterion_path)
    # results_native = parse_benchmarks(
    #     "native_single", "native_specialize", criterion_path
    # )

    run_time_path = os.path.join(script_dir, "..", "target", "run_time")
    results_sml = parse_new_benchmarks("sml_typed", "sml_first_order", run_time_path)
    results_ocaml = parse_new_benchmarks(
        "ocaml_typed", "ocaml_first_order", run_time_path
    )
    results_native = parse_new_benchmarks(
        "native_single", "native_specialize", run_time_path
    )

    plt.style.use("bmh")

    plot(
        "Speedup Due to Lambda Set Specialization",
        {
            "MLton": results_sml,
            "OCaml": results_ocaml,
        },
        os.path.join(out_dir, "speedup_ml_family_2"),
    )

    plot(
        "Speedup Due to Lambda Set Specialization",
        {
            "Morphic": results_native,
        },
        os.path.join(out_dir, "speedup_native_2"),
    )

    plot_absolute(
        "Run Time (Lower is Better)",
        {
            "MLton": results_sml,
            "OCaml": results_ocaml,
            "Morphic": results_native,
        },
        os.path.join(out_dir, "absolute_run_time_2"),
    )


if __name__ == "__main__":
    main()
