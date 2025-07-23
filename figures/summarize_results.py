#!/usr/bin/env python3
# %%

# In the acmart.cls with acmsmall we have font sizes:
# - normal = 10pt
# - scriptsize = 7pt
#
# You can test this with: \fontname\font\ at \the\fontdimen6\font

from pathlib import Path
import matplotlib
from matplotlib.container import BarContainer
import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.font_manager import FontProperties
import seaborn as sns
from typing import cast

OUTPUT_FORMAT = "pgf"

# Configure matplotlib for PGF output to fix spacing issues
if OUTPUT_FORMAT == "pgf":
    matplotlib.rcParams.update({
        'pgf.rcfonts': False,  # Don't setup fonts from rc parameters
        'font.family': 'serif',
        'text.usetex': True,
        # 'pgf.preamble': [
        #     r'\usepackage{amsmath}',
        #     r'\usepackage{amssymb}',
        # ]
    })

ROOT_DIR = Path(__file__).resolve().parent.parent
IN_DIR = ROOT_DIR / "target"
# IN_DIR = Path("/home/ben/code/morphic-results-07-16-25")
OUT_DIR = ROOT_DIR / "figure_out"


MORPHIC_COLOR: str = "#1a85ff"
SML_COLOR: str = "#dc566d"
OCAML_COLOR: str = "#ee6a1a"

TIME_CONFIG_NAMES = {
    "ocaml-typed": "OCaml",
    "ocaml-first_order": "OCaml (first order)",
    "sml-typed": "SML",
    "sml-first_order": "SML (first order)",
    "llvm-record_time-default-bdw-persistent": "Morphic (GC; persistent)",
    "llvm-record_time-perceus-bdw-persistent": "Morphic (GC; persistent; no spec)",
    "llvm-record_time-default-rc-persistent": "Morphic (borrows; persistent)",
    "llvm-record_time-perceus-rc-persistent": "Morphic (Perceus; persistent)",
    "llvm-record_time-perceus-rc-cow": "Morphic (Perceus; COW)",
    "llvm-record_time-default-rc-cow": "Morphic (borrows; COW)",
}

TIME_NAMES = list(TIME_CONFIG_NAMES.keys())


def is_interactive() -> bool:
    return "__file__" not in globals()


def clean_benchmark_name(name: str) -> str:
    # Remove 'bench_' prefix if present
    if name.startswith("bench_"):
        name = name[len("bench_"):]
    
    # Remove '.mor' suffix if present
    if name.endswith(".mor"):
        name = name[:-len(".mor")]
    
    # Underscores are special characters in LaTeX. We must escape them if we output PGF.
    if OUTPUT_FORMAT == "pgf":
        name = name.replace("_", "\\_")
    
    return name


def load_rt_df() -> pd.DataFrame:
    name = "run_times"
    print(f"Reading data from {IN_DIR / f'{name}.csv'}")
    df = pd.read_csv(IN_DIR / f"{name}.csv")
    df["name"] = df["config"].map(lambda x: TIME_CONFIG_NAMES[x])
    df["benchmark"] = df["benchmark"].apply(clean_benchmark_name)
    return df

RETAIN_CONFIG_NAMES = {
    "llvm-record_rc-default-bdw-persistent": "Morphic (BDWGC)",
    "llvm-record_rc-default-rc-persistent": "Morphic (persistent)",
    "llvm-record_rc-perceus-rc-cow": "Morphic (perceus)",
    "llvm-record_rc-default-rc-cow": "Morphic",
    "llvm-record_rc-perceus-rc-persistent": "Perceus (persistent)",
    "llvm-record_rc-perceus-bdw-persistent": "Perceus (BDWGC)",
}

RETAIN_NAMES = list(RETAIN_CONFIG_NAMES.keys())

def load_retains_df() -> pd.DataFrame:
    name = "rc_counts"
    print(f"Reading data from {IN_DIR / f'{name}.csv'}")
    df = pd.read_csv(IN_DIR / f"{name}.csv")
    df["name"] = df["config"].map(lambda x: RETAIN_CONFIG_NAMES[x])
    # Underscores are special characters in LaTeX. We must escape them if we output PGF.
    df["benchmark"] = df["benchmark"].apply(clean_benchmark_name)
    return df


OUT_DIR.mkdir(exist_ok=True)

rt_df = load_rt_df()
rt_df["time (ms)"] = rt_df["time (ns)"] / 1e6

summary_df = (
    rt_df.groupby(["benchmark", "name"])["time (ms)"].agg(["mean", "std"]).reset_index()
)

retains_df = load_retains_df()

print(f"Writing summary to {OUT_DIR / 'summary_df.csv'}")
summary_df.to_csv(OUT_DIR / "summary_df.csv", index=False)

####################
# OCaml vs. SML vs. Morphic (BDWGC) - Mean Runtime
####################


# %%

def make_ocaml_sml_gc():
    sns.set_style("whitegrid")
    sns.set_style({"axes.edgecolor": "black"})
    plt.figure()
    g_configs = [
        "ocaml-first_order",
        "sml-first_order",
        "llvm-record_time-default-bdw-persistent",
    ]
    g = sns.catplot(
        kind="bar",
        data=rt_df.loc[rt_df["config"].isin(g_configs)].reset_index(),
        col="benchmark",
        col_wrap=5,
        sharey=False,
        height=0.75,
        aspect=1.5,
        ##########
        x="name",
        y="time (ms)",
        order=[TIME_CONFIG_NAMES[config] for config in g_configs],
        estimator="mean",
        errorbar="se",
        # capsize=0.15,
        # err_kws={"linewidth": 1.5},
        palette=[OCAML_COLOR, SML_COLOR, MORPHIC_COLOR],
        hue="name",
        hue_order=[TIME_CONFIG_NAMES[config] for config in g_configs],
        legend="full",
    )

    g.tick_params(labelbottom=False)
    g.tick_params(axis="x", width=0)
    g.set_titles(col_template="{col_name}", fontweight="normal")
    g.set_axis_labels("", "")
    
    # # Fix PGF y-axis label spacing issue by setting a consistent formatter
    # if OUTPUT_FORMAT == "pgf":
    #     def y_formatter(x, pos):
    #         if x == 0:
    #             return "0"
    #         elif x >= 1000:
    #             return f"{x/1000:.0f}k"
    #         elif x >= 100:
    #             return f"{x:.0f}"
    #         elif x >= 10:
    #             return f"{x:.1f}"
    #         else:
    #             return f"{x:.2f}"
        
    #     for ax in g.axes.flat:
    #         ax.yaxis.set_major_formatter(FuncFormatter(y_formatter))
    #         # Alternative: Use string method formatter if the above doesn't work
    #         # from matplotlib.ticker import StrMethodFormatter
    #         # ax.yaxis.set_major_formatter(StrMethodFormatter("{x:.1f}"))
    
    sns.move_legend(
        g,
        loc="upper left",
        title="Legend",
        alignment="left",
        bbox_to_anchor=(0.5, 0.39),
        title_fontproperties=FontProperties(weight="normal", size=8),
        fontsize=8,
    )

    g.tight_layout()

    print(f"Saving figure to {OUT_DIR / f'ocaml_sml_gc.{OUTPUT_FORMAT}'}")
    plt.savefig(OUT_DIR / f"ocaml_sml_gc.{OUTPUT_FORMAT}", bbox_inches="tight")

make_ocaml_sml_gc()

####################
# Morphic (BDWGC) vs. Morphic (persistent) - Median Runtime Ratio
####################

# %%


def plot_speedup(numer_name: str, numer_config: str, denom_name: str, denom_config: str):
    sns.set_style("whitegrid")
    plt.figure()

    stats = (
        rt_df[rt_df["config"].isin([numer_config, denom_config])]
        .groupby(["benchmark", "config"])["time (ms)"]
        .agg(["median", "min", "max", ("q25", lambda x: x.quantile(0.25)), ("q75", lambda x: x.quantile(0.75))])
        .unstack("config")
    )

    ratios = pd.DataFrame(
        {
            "benchmark": stats.index,
            "ratio": stats[("median", numer_config)] / stats[("median", denom_config)],
            "upper_bound": stats[("max", numer_config)] / stats[("min", denom_config)],
            "lower_bound": stats[("min", numer_config)] / stats[("max", denom_config)],
        }
    )

    # Calculate error bar values
    upper_error = ratios["upper_bound"] - ratios["ratio"]
    lower_error = ratios["ratio"] - ratios["lower_bound"]

    LABEL_FONT_SIZE = 7
    TITLE_FONT_SIZE = 7

    fig, ax = plt.subplots(figsize=(3, 2.5))
    ax.tick_params(axis="x", labelsize=LABEL_FONT_SIZE)
    g = sns.barplot(
        ax=ax,
        data=ratios,
        x="benchmark",
        y="ratio",
        yerr=[lower_error, upper_error],
        capsize=0.15,
        err_kws={"linewidth": 1.5},
        color=MORPHIC_COLOR,
    )

    g.bar_label(cast(BarContainer, g.containers[1]), fmt="%.2f$\\times$", fontsize=LABEL_FONT_SIZE)
    
    g.set_xticklabels(
        g.get_xticklabels(), rotation=45, ha="right", rotation_mode="anchor"
    )
    g.axhline(1, color="black", linestyle="--", linewidth=1)
    g.set_ylabel(f"Ratio of Runtimes", fontsize=LABEL_FONT_SIZE)
    g.set_xlabel("")
    g.set_title(f"Speedup: {numer_name} / {denom_name}", fontweight="bold", fontsize=TITLE_FONT_SIZE)
    
    # Remove the top spine/line
    g.spines['top'].set_visible(False)
    g.spines['right'].set_visible(False)

    plt.tight_layout()

    filename = f"{numer_name.replace(' ', '-')}_vs_{denom_name.replace(' ', '-')}.{OUTPUT_FORMAT}"
    print(f"Saving figure to {OUT_DIR / filename}")
    plt.savefig(OUT_DIR / filename, bbox_inches="tight")


plot_speedup(
    "GC",
    "llvm-record_time-default-bdw-persistent",
    "Borrow Inference",
    "llvm-record_time-default-rc-persistent",
)

####################
# Speedup vs. Perceus (COW) - Median Runtime Ratio
####################


# %% 

plot_speedup(
    "Perceus COW",
    "llvm-record_time-perceus-rc-cow",
    "Morphic COW",
    "llvm-record_time-default-rc-cow",
)

####################
# Speedup vs. Perceus (Persistent) - Median Runtime Ratio
####################

# %%

plot_speedup(
    "Perceus Persistent",
    "llvm-record_time-perceus-rc-persistent",
    "Morphic Persistent",
    "llvm-record_time-default-rc-persistent",
)

####################
# Data Table with Absolute Values for All Configurations
####################

def create_absolute_values_table():
    sns.set_style("whitegrid")
    # Create a comprehensive table with all configurations
    table_data = []
    
    # Get median values for all config/benchmark combinations
    medians = (
        rt_df.groupby(["benchmark", "config"])["time (ms)"]
        .median()
        .reset_index()
        .pivot(index="benchmark", columns="config", values="time (ms)")
    )
    
    # Add configuration names for better readability
    medians.columns = [TIME_CONFIG_NAMES.get(col, col) for col in medians.columns]
    
    # Round to 2 decimal places
    medians = medians.round(2)
    
    print(f"Writing absolute values table to {OUT_DIR / 'absolute_values_table.csv'}")
    medians.to_csv(OUT_DIR / "absolute_values_table.csv")
    
    # Create a visualization of the table
    fig, ax = plt.subplots(figsize=(16, 10))
    ax.axis('tight')
    ax.axis('off')
    
    # Create the table
    table = ax.table(
        cellText=medians.values.astype(str).tolist(),
        rowLabels=list(medians.index),
        colLabels=list(medians.columns),
        cellLoc='center',
        loc='center'
    )
    
    # Style the table
    table.auto_set_font_size(False)
    table.set_fontsize(8)
    table.scale(1, 2)
    
    # Color the header row
    for i in range(len(medians.columns)):
        table[(0, i)].set_facecolor('#4CAF50')
        table[(0, i)].set_text_props(weight='bold', color='white')
    
    # Color the row labels
    for i in range(len(medians.index)):
        table[(i+1, -1)].set_facecolor('#E8F5E8')
        table[(i+1, -1)].set_text_props(weight='bold')
    
    # Add alternating row colors for better readability
    for i in range(len(medians.index)):
        if i % 2 == 0:
            for j in range(len(medians.columns)):
                table[(i+1, j)].set_facecolor('#F5F5F5')
    
    plt.title('Absolute Runtime Values (Median in ms)', fontsize=16, fontweight='bold', pad=20)
    plt.tight_layout()
    
    print(f"Saving table visualization to {OUT_DIR / f'absolute_values_table.{OUTPUT_FORMAT}'}")
    plt.savefig(OUT_DIR / f"absolute_values_table.{OUTPUT_FORMAT}", bbox_inches="tight", dpi=300)
    
    # Also create a formatted version for display
    print("\nAbsolute Values Table (Median Runtime in ms):")
    print("=" * 80)
    print(medians.to_string())
    print("=" * 80)
    
    return medians

# create_absolute_values_table()

####################
# Retains Eliminated vs. Perceus (COW)
####################

# %%

def plot_retains_eliminated(
    baseline_name: str,
    baseline_config: str,
    other_name: str,
    other_config: str,
    label_offsets: dict[str, float] = {},
):
    sns.set_style("whitegrid")
    plt.figure()

    # Process the retains data
    retain_data = retains_df[retains_df["config"].isin([baseline_config, other_config])].copy()
    
    # Pivot to get side-by-side comparison
    retain_pivot = retain_data.pivot(index="benchmark", columns="config", values="retain count")
    
    # Calculate percentage of retains eliminated
    # Formula: (Perceus_retains - Default_retains) / Perceus_retains * 100
    # When Perceus_retains = 0, set to 0% (no retains to eliminate)
    perceus_retains = retain_pivot[baseline_config]
    default_retains = retain_pivot[other_config]
    
    retains_eliminated_pct = []
    benchmark_names = []
    
    for i in range(len(perceus_retains)):
        benchmark = str(retain_pivot.index[i])
        p_retains = perceus_retains.iloc[i]
        d_retains = default_retains.iloc[i]
        
        if pd.isna(p_retains) or pd.isna(d_retains):
            continue  # Skip benchmarks with missing data
            
        if p_retains == 0:
            # No retains in Perceus, so 0% eliminated (nothing to eliminate)
            pct = 0.0
        else:
            # Calculate percentage eliminated
            pct = (p_retains - d_retains) / p_retains * 100
            pct = max(0.0, pct)  # Cap at 0% minimum
        
        retains_eliminated_pct.append(pct)
        benchmark_names.append(benchmark)  # Use the name as-is since it's already cleaned
        print(f"{benchmark}: Perceus={p_retains}, Default={d_retains}, Eliminated={pct:.1f}%")
    
    # Create DataFrame for plotting
    plot_data = pd.DataFrame({
        "benchmark": benchmark_names,
        "retains_eliminated_pct": retains_eliminated_pct
    })

    LABEL_FONT_SIZE = 7
    TITLE_FONT_SIZE = 7
    
    fig, ax = plt.subplots(figsize=(3, 2.5))
    ax.tick_params(axis="x", labelsize=LABEL_FONT_SIZE)
    ax.tick_params(axis="y", labelsize=LABEL_FONT_SIZE)
    g = sns.barplot(
        ax=ax,
        data=plot_data,
        x="benchmark",
        y="retains_eliminated_pct",
        color=MORPHIC_COLOR,
    )

    fmt = "%.1f%%" if OUTPUT_FORMAT == "pgf" else "%.1f\\%%"
    
    # Get the bars and their positions
    bars = g.containers[0]
    
    # Add labels with offset for the specific bar
    for i, (bar, pct) in enumerate(zip(bars, plot_data["retains_eliminated_pct"])):
        x_offset = label_offsets.get(i, 0)
        label = fmt % pct
        g.annotate(label, 
                  xy=(bar.get_x() + bar.get_width()/2 + x_offset, bar.get_height()),
                  xytext=(0, 0.5),
                  textcoords="offset points",
                  ha='center', va='bottom',
                  fontsize=LABEL_FONT_SIZE)

    
    g.set_xticklabels(
        g.get_xticklabels(), rotation=45, ha="right", rotation_mode="anchor"
    )
    g.set_ylabel("Retains Eliminated (%)", fontsize=LABEL_FONT_SIZE)
    g.set_xlabel("")
    g.set_title(f"Retains Eliminated: {baseline_name} vs. {other_name}", fontweight="bold", fontsize=TITLE_FONT_SIZE)
    g.set_ylim(0, 105)  # Set y-axis from 0% to 105% for better visibility
    
    # Remove the top spine/line
    g.spines['top'].set_visible(False)
    g.spines['right'].set_visible(False)
    
    plt.tight_layout()

    filename = f"retains_eliminated_{baseline_name.replace(' ', '-')}_vs_{other_name.replace(' ', '-')}.{OUTPUT_FORMAT}"
    print(f"Saving figure to {OUT_DIR / filename}")
    plt.savefig(OUT_DIR / filename, bbox_inches="tight")

plot_retains_eliminated(
    "Perceus COW",
    "llvm-record_rc-perceus-rc-cow",
    "Morphic COW",
    "llvm-record_rc-default-rc-cow",
    {8: -0.5},
)

####################
# Retains Eliminated vs. Perceus (Persistent)
####################

# %%

plot_retains_eliminated(
    "Perceus Persistent",
    "llvm-record_rc-perceus-rc-persistent",
    "Morphic Persistent",
    "llvm-record_rc-default-rc-persistent",
)