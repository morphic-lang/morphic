#!/usr/bin/env python3

from dataclasses import dataclass
import sys
from enum import StrEnum
import json
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path
import seaborn as sns
from collections import defaultdict
import pandas as pd
import argparse


ROOT_DIR = Path(__file__).resolve().parent.parent
IN_DIR = ROOT_DIR / "target"
OUT_DIR = ROOT_DIR / "figure_out"


class RcStrategy(StrEnum):
    DEFAULT = "default"
    PERCEUS = "perceus"


class ProfileMode(StrEnum):
    RECORD_RC = "record_rc"
    NO_RECORD_RC = "record_time"


class GcKind(StrEnum):
    RC = "rc"
    BDW = "bdw"


class ArrayKind(StrEnum):
    COW = "cow"
    PERSISTENT = "persistent"


class MlVariant(StrEnum):
    SML = "sml"
    OCAML = "ocaml"


class Stage(StrEnum):
    TYPED = "typed"
    FIRST_ORDER = "first_order"


@dataclass(frozen=True)
class LlvmExperiment:
    rc_strat: RcStrategy
    profile_mode: ProfileMode
    gc_kind: GcKind
    array_kind: ArrayKind


@dataclass(frozen=True)
class MlExperiment:
    variant: MlVariant
    stage: Stage


Experiment = LlvmExperiment | MlExperiment


MORPHIC_COLOR: str = "#1a85ff"
MORPHIC_BDW_COLOR: str = "#2f207e"
SML_COLOR: str = "#dc566d"
OCAML_COLOR: str = "#ee6a1a"


EXPERIMENTS: list[Experiment] = [
    MlExperiment(variant=MlVariant.OCAML, stage=Stage.TYPED),
    MlExperiment(variant=MlVariant.OCAML, stage=Stage.FIRST_ORDER),
    MlExperiment(variant=MlVariant.SML, stage=Stage.TYPED),
    MlExperiment(variant=MlVariant.SML, stage=Stage.FIRST_ORDER),
    LlvmExperiment(
        rc_strat=RcStrategy.DEFAULT,
        profile_mode=ProfileMode.NO_RECORD_RC,
        gc_kind=GcKind.BDW,
        array_kind=ArrayKind.PERSISTENT,
    ),
    LlvmExperiment(
        rc_strat=RcStrategy.DEFAULT,
        profile_mode=ProfileMode.NO_RECORD_RC,
        gc_kind=GcKind.RC,
        array_kind=ArrayKind.PERSISTENT,
    ),
    LlvmExperiment(
        rc_strat=RcStrategy.PERCEUS,
        profile_mode=ProfileMode.NO_RECORD_RC,
        gc_kind=GcKind.RC,
        array_kind=ArrayKind.COW,
    ),
    LlvmExperiment(
        rc_strat=RcStrategy.DEFAULT,
        profile_mode=ProfileMode.NO_RECORD_RC,
        gc_kind=GcKind.RC,
        array_kind=ArrayKind.COW,
    ),
]


def style(e: Experiment) -> dict[str, str | None]:
    # possible hatch patterns: ["/", "\\", "|", "-", "+", "x", "o", "O", ".", "*"]
    match e:
        case LlvmExperiment(rc_strat, profile_mode, gc_kind, array_kind):
            color = MORPHIC_COLOR if gc_kind == GcKind.RC else MORPHIC_BDW_COLOR
            hatch = "/" if array_kind == ArrayKind.COW else None
            return {
                "color": color,
                "hatch": hatch,
            }
        case MlExperiment(variant, stage):
            hatch = "/" if stage == Stage.FIRST_ORDER else None
            match variant:
                case MlVariant.SML:
                    return {
                        "color": SML_COLOR,
                        "hatch": hatch,
                    }
                case MlVariant.OCAML:
                    return {
                        "color": OCAML_COLOR,
                        "hatch": hatch,
                    }


def tag(e: Experiment) -> str:
    match e:
        case LlvmExperiment(rc_strat, profile_mode, gc_kind, array_kind):
            return f"llvm-{profile_mode}-{rc_strat}-{gc_kind}-{array_kind}"
        case MlExperiment(variant, stage):
            return f"{variant}-{stage}"


def parse_filename(filename: str) -> tuple[str, Experiment]:
    """
    Formats: [bench_name]-llvm-[profile_mode]-[rc_strat]-[gc_kind]-[array_kind].txt
             [bench_name]-[sml|ocaml]-[stage].txt
    """
    name, *config_parts = filename.removesuffix(".txt").split("-")

    if config_parts[0] == "llvm":
        assert len(config_parts) == 5
        _, profile_mode, rc_strat, gc_kind, array_kind = config_parts

        experiment = LlvmExperiment(
            rc_strat=RcStrategy(rc_strat),
            profile_mode=ProfileMode(profile_mode),
            gc_kind=GcKind(gc_kind),
            array_kind=ArrayKind(array_kind),
        )
    else:
        assert len(config_parts) == 2
        variant, stage = config_parts

        experiment = MlExperiment(variant=MlVariant(variant), stage=Stage(stage))

    return name, experiment


def load_runtime_data() -> dict[str, dict[Experiment, list[int]]]:
    """Load all runtime data from target/run_time directory"""
    data: dict[str, dict[Experiment, list[int]]] = defaultdict(dict)
    runtime_dir = IN_DIR / "run_time"

    if not runtime_dir.exists():
        print(f"Error: {runtime_dir} directory not found")
        sys.exit(1)

    for file_path in runtime_dir.glob("*.txt"):
        try:
            with open(file_path, "r") as f:
                content = f.read().strip()
                if content:
                    times_ns: list[int] = json.loads(content)
                    benchmark, experiment = parse_filename(file_path.name)
                    match experiment:
                        case LlvmExperiment(profile_mode=ProfileMode.NO_RECORD_RC):
                            data[benchmark][experiment] = times_ns
                        case MlExperiment():
                            data[benchmark][experiment] = times_ns
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
            sys.exit(1)

    for k, v in data.items():
        print(f"k: {k}, v: {v.keys()}")
    return data


def convert_to_ms(times_ns: list[int]) -> list[float]:
    """Convert nanoseconds to milliseconds"""
    return [t / 1_000_000.0 for t in times_ns]


def plot_runtime_comparison(data: dict[str, dict[Experiment, list[int]]]) -> None:
    """Create comparison plots for runtime data"""

    # Set up the plotting style
    plt.style.use("default")
    sns.set_palette("husl")

    # Create figure with subplots for each benchmark
    benchmarks: list[str] = sorted(data.keys())
    n_benchmarks: int = len(benchmarks)

    if n_benchmarks == 0:
        print("No benchmark data found")
        return

    # Calculate grid dimensions
    cols: int = min(3, n_benchmarks)
    rows: int = (n_benchmarks + cols - 1) // cols

    fig, axes = plt.subplots(rows, cols, figsize=(5 * cols, 4 * rows))
    if n_benchmarks == 1:
        axes = [axes]
    elif rows == 1:
        axes = axes
    else:
        axes = axes.flatten()

    for i, benchmark in enumerate(benchmarks):
        ax = axes[i] if i < len(axes) else plt.subplot(rows, cols, i + 1)

        experiments: dict[Experiment, list[int]] = data[benchmark]
        config_names: list[str] = []
        means: list[float] = []
        stds: list[float] = []
        styles: list[dict[str, str | None]] = []

        # Sort experiments for consistent ordering
        sorted_experiments: list[tuple[str, Experiment, list[int]]] = sorted(
            [(tag(exp), exp, times_ns) for exp, times_ns in experiments.items()],
            key=lambda x: EXPERIMENTS.index(x[1]),
        )

        for config_name, experiment, times_ns in sorted_experiments:
            times_ms: list[float] = convert_to_ms(times_ns)
            config_names.append(
                config_name.replace("-", "\n")
            )  # Multi-line for readability
            means.append(float(np.mean(times_ms)))
            stds.append(float(np.std(times_ms)))
            styles.append(style(experiment))

        # Create bar plot with individual styling
        bars = ax.bar(
            range(len(config_names)),
            means,
            yerr=stds,
            capsize=5,
            alpha=0.7,
        )

        # Apply styling to each bar
        for bar, style_dict in zip(bars, styles):
            if style_dict["color"]:
                bar.set_color(style_dict["color"])
                bar.set_edgecolor("black")
            if style_dict["hatch"]:
                bar.set_hatch(style_dict["hatch"])

        # Customize the plot
        ax.set_title(
            benchmark.replace("bench_", "").replace(".mor", ""),
            fontsize=12,
            fontweight="bold",
        )
        ax.set_ylabel("Runtime (ms)")
        ax.set_xticks(range(len(config_names)))
        ax.set_xticklabels(config_names, rotation=45, ha="right", fontsize=8)
        ax.grid(True, alpha=0.3)

        # Add value labels on bars
        for bar, mean_val in zip(bars, means):
            height = bar.get_height()
            ax.text(
                bar.get_x() + bar.get_width() / 2.0,
                height + max(stds) * 0.1,
                f"{mean_val:.1f}",
                ha="center",
                va="bottom",
                fontsize=8,
            )

    # Hide empty subplots
    for i in range(n_benchmarks, len(axes)):
        axes[i].set_visible(False)

    plt.tight_layout()

    path = OUT_DIR / "plot.png"
    plt.savefig(path, dpi=300, bbox_inches="tight")
    print(f"Saved runtime comparison plot to {path}")


def create_summary_table(
    data: dict[str, dict[Experiment, list[int]]],
) -> pd.DataFrame:
    """Create a summary table of all runtime data"""
    rows = []

    for benchmark, experiments in data.items():
        for experiment, times_ns in experiments.items():
            row = {
                "Benchmark": benchmark,
                "Configuration": tag(experiment),
                "Mean Runtime (ns)": np.mean(times_ns),
                "Std Dev (ns)": np.std(times_ns),
                "Min Runtime (ns)": np.min(times_ns),
                "Max Runtime (ns)": np.max(times_ns),
                "Outer Loop Iters": len(times_ns),
            }
            rows.append(row)

    df: pd.DataFrame = pd.DataFrame(rows)
    return df


def plot_heatmap(
    data: dict[str, dict[Experiment, list[int]]],
) -> None:
    """Create a plot comparing configurations across all benchmarks"""
    # Collect all unique configurations
    all_configs: set[Experiment] = set()
    for experiments in data.values():
        all_configs.update(experiments.keys())

    all_configs_list: list[Experiment] = sorted(
        all_configs, key=lambda e: EXPERIMENTS.index(e)
    )
    benchmarks: list[str] = sorted(data.keys())

    # Create matrix of mean runtimes
    matrix: list[list[float]] = []
    config_labels: list[str] = []
    benchmark_labels: list[str] = []

    for experiment in all_configs_list:
        row: list[float] = []
        for benchmark in benchmarks:
            if experiment in data[benchmark]:
                times_ms: list[float] = convert_to_ms(data[benchmark][experiment])
                row.append(float(np.mean(times_ms)))
            else:
                row.append(np.nan)
        matrix.append(row)
        config_labels.append(tag(experiment).replace("-", "\n"))

    benchmark_labels = [b.replace("bench_", "").replace(".mor", "") for b in benchmarks]

    # Create heatmap
    plt.figure(figsize=(12, 8))

    # Use log scale for better visualization of different magnitude values
    matrix_array: np.ndarray = np.array(matrix)
    mask: np.ndarray = np.isnan(matrix_array)

    # Create heatmap with log scale
    im = plt.imshow(np.log10(matrix_array + 1), cmap="YlOrRd", aspect="auto")

    # Add colorbar
    cbar = plt.colorbar(im)
    cbar.set_label("Log10(Runtime in ms + 1)", rotation=270, labelpad=20)

    # Set ticks and labels
    plt.xticks(range(len(benchmark_labels)), benchmark_labels, rotation=45, ha="right")
    plt.yticks(range(len(config_labels)), config_labels, fontsize=8)

    # Add text annotations
    for i in range(len(config_labels)):
        for j in range(len(benchmark_labels)):
            if not mask[i, j]:
                text = f"{matrix_array[i, j]:.1f}"
                plt.text(
                    j,
                    i,
                    text,
                    ha="center",
                    va="center",
                    fontsize=8,
                    color=(
                        "white"
                        if matrix_array[i, j] > np.nanmax(matrix_array) / 2
                        else "black"
                    ),
                )

    plt.title("Runtime Comparison Across All Configurations and Benchmarks")
    plt.xlabel("Benchmarks")
    plt.ylabel("Configurations")
    plt.tight_layout()

    path = OUT_DIR / "heatmap.png"
    plt.savefig(path, dpi=300, bbox_inches="tight")
    print(f"Saved configuration heatmap to {path}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate benchmark plots and summaries"
    )
    parser.add_argument(
        "--interactive",
        "-i",
        action="store_true",
        help="show plots interactively",
    )
    args = parser.parse_args()

    print("Loading runtime data...")
    data: dict[str, dict[Experiment, list[int]]] = load_runtime_data()

    if not data:
        print("No runtime data found. Make sure to run the benchmarks first.")
        return

    print(f"Found data for {len(data)} benchmarks")

    # Create summary table
    print("\nCreating summary table...")
    summary_df: pd.DataFrame = create_summary_table(data)
    print(summary_df.to_string(index=False))

    # Create output directory if it doesn't exist
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    # Save summary to CSV
    path = OUT_DIR / "runtime_summary.csv"
    summary_df.to_csv(path, index=False)
    print(f"\nSaved summary table to {path}")

    # Create plots
    print("\nCreating runtime plot...")
    plot_runtime_comparison(data)

    print("\nCreating runtime heatmap...")
    plot_heatmap(data)

    print("\nDone! Check the generated PNG files and CSV for detailed results.")

    if args.interactive:
        plt.show()


if __name__ == "__main__":
    main()
