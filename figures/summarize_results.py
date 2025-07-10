#!/usr/bin/env python3
# %%


from pathlib import Path
import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.font_manager import FontProperties
import seaborn as sns


ROOT_DIR = Path(__file__).resolve().parent.parent
IN_DIR = ROOT_DIR / "results-07-07-25"
OUT_DIR = ROOT_DIR / "figure_out"


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


OUT_DIR.mkdir(exist_ok=True)

print(f"Reading data from {IN_DIR / 'run_times.csv'}")
df = pd.read_csv(IN_DIR / "run_times.csv")
df["name"] = df["config"].map(lambda x: NAMES[x])
df["time (ms)"] = df["time (ns)"] / 1e6

summary_df = (
    df.groupby(["benchmark", "name"])["time (ms)"].agg(["mean", "std"]).reset_index()
)

print(f"Writing summary to {OUT_DIR / 'summary_df.csv'}")
summary_df.to_csv(OUT_DIR / "summary_df.csv", index=False)

sns.set_style("whitegrid")
sns.set_style({"axes.edgecolor": "black"})

g = sns.catplot(
    kind="bar",
    data=df,
    col="benchmark",
    col_wrap=5,
    sharey=False,
    aspect=1,
    ##########
    x="name",
    y="time (ms)",
    order=list(NAMES.values()),
    estimator="mean",
    errorbar="sd",
    capsize=0.15,
    err_kws={"linewidth": 1.5},
    palette="husl",
    hue="name",
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
    bbox_to_anchor=(0.6, 0.3),
    title_fontproperties=FontProperties(weight="bold", size=12),
    fontsize=12,
)

g.tight_layout()

print(f"Saving figure to {OUT_DIR / 'plot.pgf'}")
plt.savefig(OUT_DIR / "plot.pgf", bbox_inches="tight")

if is_interactive():
    plt.show()
