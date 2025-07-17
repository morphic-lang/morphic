#!/usr/bin/env python3
# %%


from pathlib import Path
from matplotlib.container import BarContainer
import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.font_manager import FontProperties
import seaborn as sns
from typing import cast


ROOT_DIR = Path(__file__).resolve().parent.parent
IN_DIR = ROOT_DIR / "results-07-07-25"
OUT_DIR = ROOT_DIR / "figure_out"


MORPHIC_COLOR: str = "#1a85ff"
SML_COLOR: str = "#dc566d"
OCAML_COLOR: str = "#ee6a1a"


CONFIGS = [
    "ocaml-typed",
    "ocaml-first_order",
    "sml-typed",
    "sml-first_order",
    "llvm-record_time-default-bdw-persistent",
    "llvm-record_time-default-rc-persistent",
    "llvm-record_time-perceus-rc-cow",
    "llvm-record_time-default-rc-cow",
]


def zip_with_configs(items: list[str]) -> dict[str, str]:
    assert len(items) == len(CONFIGS)
    return dict(zip(CONFIGS, items))


NAMES = zip_with_configs(
    [
        "OCaml",
        "OCaml (first order)",
        "SML",
        "SML (first order)",
        "Morphic (BDWGC)",
        "Morphic (persistent)",
        "Morphic (perceus)",
        "Morphic",
    ],
)


def is_interactive() -> bool:
    return "__file__" not in globals()


def clean_benchmark_name(name: str) -> str:
    name = name[len("bench_") :]
    name = name[: -len(".mor")]
    return name.replace("_", "\\_")


def load_df(name: str) -> pd.DataFrame:
    print(f"Reading data from {IN_DIR / f'{name}.csv'}")
    df = pd.read_csv(IN_DIR / f"{name}.csv")
    df["name"] = df["config"].map(lambda x: NAMES[x])
    # Underscores are special characters in LaTeX. We must escape them if we output PGF.
    df["benchmark"] = df["benchmark"].apply(clean_benchmark_name)
    return df


OUT_DIR.mkdir(exist_ok=True)

rt_df = load_df("run_times")
rt_df["time (ms)"] = rt_df["time (ns)"] / 1e6

summary_df = (
    rt_df.groupby(["benchmark", "name"])["time (ms)"].agg(["mean", "std"]).reset_index()
)

print(f"Writing summary to {OUT_DIR / 'summary_df.csv'}")
summary_df.to_csv(OUT_DIR / "summary_df.csv", index=False)

sns.set_style("whitegrid")
sns.set_style({"axes.edgecolor": "black"})

####################
# OCaml vs. SML vs. Morphic (BDWGC) - Mean Runtime
####################


def make_plot1():
    g_configs = [
        "ocaml-first_order",
        "sml-first_order",
        "llvm-record_time-default-bdw-persistent",
    ]
    g = sns.catplot(
        kind="bar",
        data=rt_df.loc[rt_df["config"].isin(g_configs)].reset_index(),
        col="benchmark",
        col_wrap=7,
        sharey=False,
        height=2.5,
        aspect=1,
        ##########
        x="name",
        y="time (ms)",
        order=[NAMES[config] for config in g_configs],
        estimator="mean",
        errorbar="sd",
        capsize=0.15,
        err_kws={"linewidth": 1.5},
        palette=[OCAML_COLOR, SML_COLOR, MORPHIC_COLOR],
        hue="name",
        hue_order=[NAMES[config] for config in g_configs],
        legend="full",
    )

    g.tick_params(labelbottom=False)
    g.tick_params(axis="x", width=0)
    g.set_titles(col_template="{col_name}", fontweight="bold")
    g.set_axis_labels("", "Mean Runtime (ms)")
    sns.move_legend(
        g,
        loc="upper left",
        title="Legend",
        alignment="left",
        bbox_to_anchor=(0.78, 0.4),
        title_fontproperties=FontProperties(weight="bold", size=12),
        fontsize=12,
    )

    ax = g.facet_axis(0, 0)
    for c in ax.containers:
        ax.bar_label(cast(BarContainer, c), fmt="%.2f")

    g.tight_layout()

    print(f"Saving figure to {OUT_DIR / 'plot.pgf'}")
    plt.savefig(OUT_DIR / "plot.pgf", bbox_inches="tight")


# make_plot1()

####################
# Morphic (BDWGC) vs. Morphic (persistent) - Median Runtime Ratio
####################


def make_plot2():
    gc_config = "llvm-record_time-default-bdw-persistent"
    rc_config = "llvm-record_time-default-rc-persistent"

    stats = (
        rt_df[rt_df["config"].isin([gc_config, rc_config])]
        .groupby(["benchmark", "config"])["time (ms)"]
        .agg(["median", "min", "max"])
        .unstack("config")
    )

    ratios = pd.DataFrame(
        {
            "benchmark": stats.index,
            "gc_median": stats[("median", gc_config)],
            "rc_median": stats[("median", rc_config)],
            "ratio": stats[("median", gc_config)] / stats[("median", rc_config)],
            "upper_bound": stats[("max", gc_config)] / stats[("min", rc_config)],
            "lower_bound": stats[("min", gc_config)] / stats[("max", rc_config)],
        }
    ).round(4)

    # Calculate error bar values
    upper_error = ratios["upper_bound"] - ratios["ratio"]
    lower_error = ratios["ratio"] - ratios["lower_bound"]

    g = sns.barplot(
        data=ratios,
        x="benchmark",
        y="ratio",
        yerr=[lower_error, upper_error],
        capsize=0.15,
        err_kws={"linewidth": 1.5},
        color=MORPHIC_COLOR,
    )
    # g.bar_label(cast(BarContainer, g.containers[0]), fmt="%.2f")
    g.set_xticklabels(
        g.get_xticklabels(), rotation=45, ha="right", rotation_mode="anchor"
    )
    g.axhline(1, color="black", linestyle="--", linewidth=1)


make_plot2()
