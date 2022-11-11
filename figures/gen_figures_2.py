from typing import List, Dict
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
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


def plot_broken(title: str, results: Dict[str, Results], out_path: str) -> None:
    width = 0.8 / 3
    llim = 8.5

    lang_names = list(results.keys())
    bench_names = set()
    for lang_results in results.values():
        for experiment in lang_results.experiments:
            bench_names.add(experiment.name)
    bench_names = list(reversed(sorted(bench_names)))
    bench_indices = {name: i for i, name in enumerate(bench_names)}

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8, 6), gridspec_kw={"width_ratios": [2, 1]})
    fig.subplots_adjust(top=0.925, bottom=0.2)
    ax1.set_yticks(np.arange(len(bench_names)))
    ax1.set_yticklabels(bench_names)

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
        p1 = ax1.barh(
            xs,
            ys,
            width * 0.9,
            xerr=[err_min, err_max],
            label=lang_name,
            color=colors[lang_name],
        )
        p2 = ax2.barh(
            xs,
            ys,
            width * 0.9,
            xerr=[err_min, err_max],
            label=lang_name,
            color=colors[lang_name],
        )
        ax1.bar_label(p1, padding=8, labels=[f'{y:.2f}' for y in ys], zorder=200)
        ax2.bar_label(p2, padding=8, labels=[f'{y:.2f}' for y in ys], zorder=100)

    fig.subplots_adjust(wspace=0.075)
    ax1.set_xlim(0.0, llim)
    ax2.set_xlim(10.0, 110.0)
    ax1.yaxis.tick_left()
    ax1.spines['right'].set_visible(False)
    ax2.spines['left'].set_visible(False)
    ax1.tick_params(axis='y', length=0)
    ax2.tick_params(axis='y', length=0)

    ax2.set_yticklabels([])
    ax1.axvline(x=1, color="black", linestyle="--")


    # https://stackoverflow.com/questions/59305080/formatting-a-broken-y-axis-in-python-matplotlib
    d = 0.9  # proportion of vertical to horizontal extent of the slanted line
    kwargs = dict(marker=[(-1, -d), (1, d)], markersize=12,
                linestyle="none", color='k', mec='k', mew=1, clip_on=False, zorder=100)
    ax1.plot([1, 1], [1, 0], transform=ax1.transAxes, **kwargs)
    ax2.plot([0, 0], [1, 0], transform=ax2.transAxes, **kwargs)

    # # shrink the plot to make room for the legend in the y direction
    #box = ax1.get_position()
    #ax1.set_position([box.x0, box.y0 - box.height * 0.08, box.width, box.height * 1.08])
    # # display the legend below the chart, and make space so it doesn't overlap with the x axis title
    handles, labels = ax1.get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", bbox_to_anchor=(0.5, 0.055), ncol=3, fontsize="small")
    fig.suptitle(title)
    fig.text(0.5, 0.13, 'Speedup Factor', ha='center', va='center')
    fig.savefig(f"{out_path}.png")
    fig.savefig(f"{out_path}.pdf")


def plot_log(title: str, results: Dict[str, Results], out_path: str) -> None:
    width = 0.8 / 3

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

    ax.set_xscale("log")
    ax.set_xlim(right=100)
    ax.xaxis.set_major_formatter(mticker.ScalarFormatter())

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
        p1 = ax.barh(
            xs,
            ys,
            width * 0.9,
            xerr=[err_min, err_max],
            label=lang_name,
            color=colors[lang_name],
        )
        ax.bar_label(p1, padding=8, labels=[f'{y:.2f}' for y in ys])
        print(f'{lang_name}: {ys}')

    ax.tick_params(axis='y', length=0)
    plt.axvline(x=1, color="black", linestyle="--")

    # shrink the plot to make room for the legend in the y direction
    box = ax.get_position()
    ax.set_position([box.x0, box.y0 - box.height * 0.08, box.width, box.height * 1.08])
    # display the legend below the chart, and make space so it doesn't overlap with the x axis title
    fig.legend(loc="lower center", bbox_to_anchor=(0.5, 0.01), ncol=3, fontsize="small")
    fig.tight_layout()
    fig.savefig(f"{out_path}.png")
    fig.savefig(f"{out_path}.pdf")


def plot(title: str, results: Dict[str, Results], out_path: str) -> None:
    width = 0.8 / 3

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

    plot_log(
        "Speedup Due to Lambda Set Specialization",
        {
            "MLton": results_sml,
            "OCaml": results_ocaml,
            "Morphic": results_native,
        },
        os.path.join(out_dir, "speedup_all_2"),
    )

    plot_broken(
        "Speedup Due to Lambda Set Specialization",
        {
            "MLton": results_sml,
            "OCaml": results_ocaml,
            "Morphic": results_native,
        },
        os.path.join(out_dir, "speedup_all_broken_2"),
    )


if __name__ == "__main__":
    main()
