#!/usr/bin/env python3
# %%


from pathlib import Path
from matplotlib.container import BarContainer
from matplotlib.patches import Rectangle
from matplotlib.ticker import FuncFormatter
import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.font_manager import FontProperties
import seaborn as sns
from typing import cast


ROOT_DIR = Path(__file__).resolve().parent.parent
IN_DIR = ROOT_DIR / "results"
OUT_DIR = ROOT_DIR / "figure_out"


MORPHIC_COLOR: str = "#1a85ff"
SML_COLOR: str = "#dc566d"
OCAML_COLOR: str = "#ee6a1a"

TIME_CONFIG_NAMES = {
    "ocaml-typed": "OCaml",
    "ocaml-first_order": "OCaml (first order)",
    "sml-typed": "SML",
    "sml-first_order": "SML (first order)",
    "llvm-record_time-default-bdw-persistent": "Morphic (BDWGC)",
    "llvm-record_time-default-rc-persistent": "Morphic (persistent)",
    "llvm-record_time-perceus-rc-cow": "Morphic (perceus)",
    "llvm-record_time-default-rc-cow": "Morphic",
    "llvm-record_time-perceus-rc-persistent": "Perceus (persistent)",
    "llvm-record_time-perceus-bdw-persistent": "Perceus (BDWGC)",
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
    
    return name


def load_rt_df() -> pd.DataFrame:
    name = "run_times"
    print(f"Reading data from {IN_DIR / f'{name}.csv'}")
    df = pd.read_csv(IN_DIR / f"{name}.csv")
    df["name"] = df["config"].map(lambda x: TIME_CONFIG_NAMES[x])
    # Underscores are special characters in LaTeX. We must escape them if we output PGF.
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

sns.set_style("whitegrid")
sns.set_style({"axes.edgecolor": "black"})

####################
# OCaml vs. SML vs. Morphic (BDWGC) - Mean Runtime
####################


# %%

def make_ocaml_sml_gc():
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
        col_wrap=7,
        sharey=False,
        height=2.5,
        aspect=1,
        ##########
        x="name",
        y="time (ms)",
        order=[TIME_CONFIG_NAMES[config] for config in g_configs],
        estimator="mean",
        errorbar="sd",
        # capsize=0.15,
        # err_kws={"linewidth": 1.5},
        palette=[OCAML_COLOR, SML_COLOR, MORPHIC_COLOR],
        hue="name",
        hue_order=[TIME_CONFIG_NAMES[config] for config in g_configs],
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

    g.tight_layout()

    print(f"Saving figure to {OUT_DIR / 'ocaml_sml_gc.png'}")
    plt.savefig(OUT_DIR / "ocaml_sml_gc.png", bbox_inches="tight")

make_ocaml_sml_gc()

####################
# Morphic (BDWGC) vs. Morphic (persistent) - Median Runtime Ratio
####################

# %%


def plot_gc_vs_rc():
    plt.figure()
    gc_config = "llvm-record_time-default-bdw-persistent"
    rc_config = "llvm-record_time-default-rc-persistent"

    stats = (
        rt_df[rt_df["config"].isin([gc_config, rc_config])]
        .groupby(["benchmark", "config"])["time (ms)"]
        .agg(["median", "min", "max", lambda x: x.quantile(0.25), lambda x: x.quantile(0.75)])
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

    g.bar_label(cast(BarContainer, g.containers[1]), fmt="%.2f")
    
    g.set_xticklabels(
        g.get_xticklabels(), rotation=45, ha="right", rotation_mode="anchor"
    )
    g.axhline(1, color="black", linestyle="--", linewidth=1)
    plt.tight_layout()

    print(f"Saving figure to {OUT_DIR / 'gc_vs_rc.png'}")
    plt.savefig(OUT_DIR / "gc_vs_rc.png", bbox_inches="tight")


plot_gc_vs_rc()

####################
# Speedup vs. Perceus (COW) - Median Runtime Ratio
####################


# %% 
def plot_speedup_vs_perceus_cow():
    plt.figure()
    baseline_config = "llvm-record_time-perceus-rc-cow"
    comparison_config = "llvm-record_time-default-rc-cow"

    # Get all individual samples for each benchmark/config combination
    baseline_data = rt_df[rt_df["config"] == baseline_config].groupby("benchmark")["time (ms)"].apply(list)
    comparison_data = rt_df[rt_df["config"] == comparison_config].groupby("benchmark")["time (ms)"].apply(list)
    
    ratios_list = []
    
    for benchmark in baseline_data.index:
        if benchmark in comparison_data.index:
            baseline_samples = baseline_data[benchmark]
            comparison_samples = comparison_data[benchmark]
            
            # Calculate all possible ratios (baseline_sample / comparison_sample)
            all_ratios = []
            for baseline_val in baseline_samples:
                for comparison_val in comparison_samples:
                    all_ratios.append(baseline_val / comparison_val)
            
            # Calculate mean and standard deviation
            import numpy as np
            mean_ratio = np.mean(all_ratios)
            std_ratio = np.std(all_ratios)
            
            ratios_list.append({
                "benchmark": benchmark,
                "speedup": mean_ratio,
                "std_ratio": std_ratio,
            })
    
    ratios = pd.DataFrame(ratios_list)

    # Calculate error bar values using standard deviation
    upper_error = ratios["std_ratio"]
    lower_error = ratios["std_ratio"]

    g = sns.barplot(
        data=ratios,
        x="benchmark",
        y="speedup",
        yerr=[lower_error, upper_error],
        capsize=0.15,
        err_kws={"linewidth": 1.5},
        color=MORPHIC_COLOR,
    )

    g.bar_label(cast(BarContainer, g.containers[1]), fmt="%.2fx")
    
    g.set_xticklabels(
        g.get_xticklabels(), rotation=45, ha="right", rotation_mode="anchor"
    )
    g.axhline(1, color="black", linestyle="--", linewidth=1)
    g.set_ylabel("Speedup (Perceus COW / Morphic COW)")
    g.set_title("Speedup vs. Perceus (COW)", fontweight="bold")
    plt.tight_layout()

    print(f"Saving figure to {OUT_DIR / 'speedup_vs_perceus_cow.png'}")
    plt.savefig(OUT_DIR / "speedup_vs_perceus_cow.png", bbox_inches="tight")

plot_speedup_vs_perceus_cow()

####################
# Speedup vs. Perceus (Persistent) - Median Runtime Ratio
####################

# %%

def plot_speedup_vs_perceus_persistent():
    plt.figure()
    baseline_config = "llvm-record_time-perceus-rc-persistent"
    comparison_config = "llvm-record_time-default-rc-persistent"

    # Get all individual samples for each benchmark/config combination
    baseline_data = rt_df[rt_df["config"] == baseline_config].groupby("benchmark")["time (ms)"].apply(list)
    comparison_data = rt_df[rt_df["config"] == comparison_config].groupby("benchmark")["time (ms)"].apply(list)
    
    ratios_list = []
    
    for benchmark in baseline_data.index:
        if benchmark in comparison_data.index:
            baseline_samples = baseline_data[benchmark]
            comparison_samples = comparison_data[benchmark]
            
            # Calculate all possible ratios (baseline_sample / comparison_sample)
            all_ratios = []
            for baseline_val in baseline_samples:
                for comparison_val in comparison_samples:
                    all_ratios.append(baseline_val / comparison_val)
            
            # Calculate mean and standard deviation
            import numpy as np
            mean_ratio = np.mean(all_ratios)
            std_ratio = np.std(all_ratios)
            
            ratios_list.append({
                "benchmark": benchmark,
                "speedup": mean_ratio,
                "std_ratio": std_ratio,
            })
    
    ratios = pd.DataFrame(ratios_list)

    print(ratios)

    # Calculate error bar values
    upper_error = ratios["std_ratio"]
    lower_error = ratios["std_ratio"]

    g = sns.barplot(
        data=ratios,
        x="benchmark",
        y="speedup",
        yerr=[lower_error, upper_error],
        capsize=0.15,
        err_kws={"linewidth": 1.5},
        color=MORPHIC_COLOR,
    )
    
    g.bar_label(cast(BarContainer, g.containers[1]), fmt="%.2fx")
    
    g.set_xticklabels(
        g.get_xticklabels(), rotation=45, ha="right", rotation_mode="anchor"
    )
    g.axhline(1, color="black", linestyle="--", linewidth=1)
    g.set_ylabel("Speedup (Perceus Persistent / Morphic Persistent)")
    g.set_title("Speedup vs. Perceus (Persistent)", fontweight="bold")
    plt.tight_layout()

    print(f"Saving figure to {OUT_DIR / 'speedup_vs_perceus_persistent.png'}")
    plt.savefig(OUT_DIR / "speedup_vs_perceus_persistent.png", bbox_inches="tight")

plot_speedup_vs_perceus_persistent()

####################
# Data Table with Absolute Values for All Configurations
####################

def create_absolute_values_table():
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
    
    print(f"Saving table visualization to {OUT_DIR / 'absolute_values_table.png'}")
    plt.savefig(OUT_DIR / "absolute_values_table.png", bbox_inches="tight", dpi=300)
    
    # Also create a formatted version for display
    print("\nAbsolute Values Table (Median Runtime in ms):")
    print("=" * 80)
    print(medians.to_string())
    print("=" * 80)
    
    return medians

create_absolute_values_table()

####################
# Retains Eliminated vs. Perceus (COW)
####################

# %%

def plot_retains_eliminated_vs_perceus_cow():
    plt.figure()
    perceus_config = "llvm-record_rc-perceus-rc-cow"
    default_config = "llvm-record_rc-default-rc-cow"

    # Process the retains data
    retain_data = retains_df[retains_df["config"].isin([perceus_config, default_config])].copy()
    
    # Pivot to get side-by-side comparison
    retain_pivot = retain_data.pivot(index="benchmark", columns="config", values="retain count")
    
    # Calculate percentage of retains eliminated
    # Formula: (Perceus_retains - Default_retains) / Perceus_retains * 100
    # When Perceus_retains = 0, set to 0% (no retains to eliminate)
    perceus_retains = retain_pivot[perceus_config]
    default_retains = retain_pivot[default_config]
    
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
    
    g = sns.barplot(
        data=plot_data,
        x="benchmark",
        y="retains_eliminated_pct",
        color=MORPHIC_COLOR,
    )

    g.bar_label(cast(BarContainer, g.containers[0]), fmt="%.1f%%")
    
    g.set_xticklabels(
        g.get_xticklabels(), rotation=45, ha="right", rotation_mode="anchor"
    )
    g.set_ylabel("Retains Eliminated (%)")
    g.set_title("Retains Eliminated vs. Perceus (COW)", fontweight="bold")
    g.set_ylim(0, 105)  # Set y-axis from 0% to 105% for better visibility
    
    plt.tight_layout()

    print(f"Saving figure to {OUT_DIR / 'retains_eliminated_vs_perceus_cow.png'}")
    plt.savefig(OUT_DIR / "retains_eliminated_vs_perceus_cow.png", bbox_inches="tight")

plot_retains_eliminated_vs_perceus_cow()

####################
# Retains Eliminated vs. Perceus (Persistent)
####################

# %%

def plot_retains_eliminated_vs_perceus_persistent():
    plt.figure()
    perceus_config = "llvm-record_rc-perceus-rc-persistent"
    default_config = "llvm-record_rc-default-rc-persistent"

    # Process the retains data
    retain_data = retains_df[retains_df["config"].isin([perceus_config, default_config])].copy()
    
    # Pivot to get side-by-side comparison
    retain_pivot = retain_data.pivot(index="benchmark", columns="config", values="retain count")
    
    # Calculate percentage of retains eliminated
    # Formula: (Perceus_retains - Default_retains) / Perceus_retains * 100
    # When Perceus_retains = 0, set to 0% (no retains to eliminate)
    perceus_retains = retain_pivot[perceus_config]
    default_retains = retain_pivot[default_config]
    
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
    
    # Create DataFrame for plotting
    plot_data = pd.DataFrame({
        "benchmark": benchmark_names,
        "retains_eliminated_pct": retains_eliminated_pct
    })
    
    g = sns.barplot(
        data=plot_data,
        x="benchmark",
        y="retains_eliminated_pct",
        color=MORPHIC_COLOR,
    )
    
    g.bar_label(cast(BarContainer, g.containers[0]), fmt="%.1f%%")
    
    g.set_xticklabels(
        g.get_xticklabels(), rotation=45, ha="right", rotation_mode="anchor"
    )
    g.set_ylabel("Retains Eliminated (%)")
    g.set_title("Retains Eliminated vs. Perceus (Persistent)", fontweight="bold")
    g.set_ylim(0, 105)  # Set y-axis from 0% to 105% for better visibility
    
    plt.tight_layout()

    print(f"Saving figure to {OUT_DIR / 'retains_eliminated_vs_perceus_persistent.png'}")
    plt.savefig(OUT_DIR / "retains_eliminated_vs_perceus_persistent.png", bbox_inches="tight")

plot_retains_eliminated_vs_perceus_persistent()
