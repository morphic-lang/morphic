#!/usr/bin/env python3
"""
Graph visualization script for constraint data from `annot_modes.rs` (borrow inference).
"""

import matplotlib.pyplot as plt
import networkx as nx
import re


def parse_graph_data(data_str: str) -> tuple[dict[int, set[int]], dict[int, str]]:
    graph = {}
    constraints = {}

    lines = data_str.strip().split("\n")
    for line in lines:
        line = line.strip()
        if not line:
            continue

        # Match pattern like "0: lb_vars={6}, lb_const=&" or "1: lb_vars={2, 15}, lb_const=●"
        match = re.match(r"(\d+):\s*lb_vars=\{([^}]*)\},\s*lb_const=([^,\s]+)", line)
        if match:
            node = int(match.group(1))
            edges_str = match.group(2).strip()
            constraint = match.group(3).strip()

            if edges_str:
                edges = {int(x.strip()) for x in edges_str.split(",") if x.strip()}
            else:
                edges = set()

            graph[node] = edges
            constraints[node] = constraint

    return graph, constraints


def create_directed_graph(graph_data: dict[int, set[int]]) -> nx.DiGraph:
    G = nx.DiGraph()

    all_nodes = set(graph_data.keys())
    for edges in graph_data.values():
        all_nodes.update(edges)

    G.add_nodes_from(all_nodes)

    for node, edges in graph_data.items():
        for target in edges:
            G.add_edge(node, target)

    return G


def visualize_graph(
    G: nx.DiGraph,
    constraints: dict[int, str] | None = None,
    title: str = "Graph Visualization",
    figsize: tuple[int, int] = (12, 8),
    node_size: int = 1000,
    font_size: int = 12,
    arrow_size: int = 20,
    separate_components: bool = True,
):
    if separate_components:
        visualize_graph_components(
            G, constraints, title, figsize, node_size, font_size, arrow_size
        )
    else:
        visualize_graph_single(
            G, constraints, title, figsize, node_size, font_size, arrow_size
        )


def visualize_graph_single(
    G: nx.DiGraph,
    constraints: dict[int, str] | None = None,
    title: str = "Graph Visualization",
    figsize: tuple[int, int] = (12, 8),
    node_size: int = 1000,
    font_size: int = 12,
    arrow_size: int = 20,
):
    plt.figure(figsize=figsize)

    pos = nx.spring_layout(G, k=1, iterations=50)

    if constraints:
        node_colors = []
        for node in G.nodes():
            if node in constraints:
                if constraints[node] == "&":
                    node_colors.append("lightblue")
                elif constraints[node] == "●":
                    node_colors.append("lightcoral")
                else:
                    node_colors.append("lightgray")
            else:
                node_colors.append("lightgray")
    else:
        node_colors = ["lightblue"] * len(G.nodes())

    nx.draw(
        G,
        pos,
        with_labels=True,
        node_color=node_colors,
        node_size=node_size,
        font_size=font_size,
        font_weight="bold",
        arrows=True,
        arrowsize=arrow_size,
        arrowstyle="->",
        edge_color="gray",
        width=2,
    )

    if constraints:
        from matplotlib.patches import Patch

        legend_elements = [
            Patch(facecolor="lightblue", label="lb_const = &"),
            Patch(facecolor="lightcoral", label="lb_const = ●"),
        ]
        plt.legend(handles=legend_elements, loc="upper right")

    plt.title(title, fontsize=16, fontweight="bold")
    plt.tight_layout()
    plt.show()


def visualize_graph_components(
    G: nx.DiGraph,
    constraints: dict[int, str] | None = None,
    title: str = "Graph Visualization",
    figsize: tuple[int, int] = (12, 8),
    node_size: int = 1000,
    font_size: int = 12,
    arrow_size: int = 20,
):
    components = list(nx.weakly_connected_components(G))

    print(f"Found {len(components)} connected components:")
    for i, component in enumerate(components):
        print(f"  Component {i+1}: {sorted(component)} ({len(component)} nodes)")

    component_graphs = []
    for component in components:
        subgraph = G.subgraph(component).copy()
        component_graphs.append(subgraph)

    n_components = len(component_graphs)
    if n_components <= 3:
        cols = n_components
        rows = 1
    elif n_components <= 6:
        cols = 3
        rows = 2
    else:
        cols = 4
        rows = (n_components + 3) // 4

    fig, axes = plt.subplots(
        rows, cols, figsize=(figsize[0], figsize[1] * max(1, rows / 2))
    )
    if n_components == 1:
        axes = [axes]
    elif rows == 1:
        axes = axes
    else:
        axes = axes.flatten()

    for i, (component, subgraph) in enumerate(zip(components, component_graphs)):
        ax = axes[i]

        pos = nx.spring_layout(subgraph, k=1, iterations=50)

        if constraints:
            node_colors = []
            for node in subgraph.nodes():
                if node in constraints:
                    if constraints[node] == "&":
                        node_colors.append("lightblue")
                    elif constraints[node] == "●":
                        node_colors.append("lightcoral")
                    else:
                        node_colors.append("lightgray")
                else:
                    node_colors.append("lightgray")
        else:
            node_colors = ["lightblue"] * len(subgraph.nodes())

        nx.draw(
            subgraph,
            pos,
            ax=ax,
            with_labels=True,
            node_color=node_colors,
            node_size=node_size // 2,
            font_size=font_size - 2,
            font_weight="bold",
            arrows=True,
            arrowsize=arrow_size // 2,
            arrowstyle="->",
            edge_color="gray",
            width=1.5,
        )

        ax.set_title(
            f"Component {i+1} ({len(component)} nodes)", fontsize=12, fontweight="bold"
        )

    for i in range(n_components, len(axes)):
        axes[i].set_visible(False)

    if constraints:
        from matplotlib.patches import Patch

        legend_elements = [
            Patch(facecolor="lightblue", label="lb_const = &"),
            Patch(facecolor="lightcoral", label="lb_const = ●"),
        ]
        fig.legend(
            handles=legend_elements, loc="upper right", bbox_to_anchor=(0.98, 0.98)
        )

    plt.suptitle(
        f"{title} - {n_components} Connected Components", fontsize=16, fontweight="bold"
    )
    plt.tight_layout()
    plt.show()


def analyze_graph(G: nx.DiGraph):
    print(f"Graph Analysis:")
    print(f"  Number of nodes: {G.number_of_nodes()}")
    print(f"  Number of edges: {G.number_of_edges()}")
    print(f"  Nodes: {sorted(G.nodes())}")
    print(f"  Edges: {sorted(G.edges())}")

    sources = [n for n in G.nodes() if G.in_degree(n) == 0]
    print(f"  Source nodes (no incoming edges): {sources}")

    sinks = [n for n in G.nodes() if G.out_degree(n) == 0]
    print(f"  Sink nodes (no outgoing edges): {sinks}")

    try:
        cycles = list(nx.simple_cycles(G))
        if cycles:
            print(f"  Cycles found: {cycles}")
        else:
            print("  No cycles found (DAG)")
    except:
        print("  Cycle detection failed")


def main():
    datasets = {
        "eval#0": """
  0: lb_vars={6}, lb_const=&
  1: lb_vars={2, 15}, lb_const=&
  2: lb_vars={11}, lb_const=&
  3: lb_vars={7, 12}, lb_const=&
  4: lb_vars={8, 13}, lb_const=&
  5: lb_vars={9, 14}, lb_const=&
  6: lb_vars={0, 8}, lb_const=&
  7: lb_vars={10}, lb_const=&
  8: lb_vars={4, 6}, lb_const=&
  9: lb_vars={5}, lb_const=&
  10: lb_vars={7}, lb_const=&
  11: lb_vars={}, lb_const=&
  12: lb_vars={3}, lb_const=●
  13: lb_vars={4}, lb_const=&
  14: lb_vars={5}, lb_const=●
  15: lb_vars={1}, lb_const=●
""",
        "map#0": """
  0: lb_vars={4, 15}, lb_const=&
  1: lb_vars={6}, lb_const=&
  2: lb_vars={7}, lb_const=&
  3: lb_vars={8}, lb_const=&
  4: lb_vars={5, 13}, lb_const=&
  5: lb_vars={9}, lb_const=&
  6: lb_vars={1, 10}, lb_const=&
  7: lb_vars={2, 11}, lb_const=&
  8: lb_vars={3, 12}, lb_const=&
  9: lb_vars={}, lb_const=&
  10: lb_vars={6}, lb_const=●
  11: lb_vars={7}, lb_const=&
  12: lb_vars={8}, lb_const=●
  13: lb_vars={14}, lb_const=&
  14: lb_vars={13}, lb_const=&
  15: lb_vars={}, lb_const=&
  16: lb_vars={}, lb_const=&
""",
        "map_rec#0": """
  0: lb_vars={4, 35, 36}, lb_const=&
  1: lb_vars={5, 15}, lb_const=&
  2: lb_vars={6, 16}, lb_const=&
  3: lb_vars={7, 17}, lb_const=&
  4: lb_vars={14, 29}, lb_const=&
  5: lb_vars={1, 8, 31}, lb_const=&
  6: lb_vars={2, 9, 32}, lb_const=&
  7: lb_vars={3, 10, 33}, lb_const=&
  8: lb_vars={5, 11, 19}, lb_const=&
  9: lb_vars={6, 12, 20}, lb_const=&
  10: lb_vars={7, 13, 21}, lb_const=&
  11: lb_vars={8}, lb_const=&
  12: lb_vars={9}, lb_const=&
  13: lb_vars={10}, lb_const=&
  14: lb_vars={0}, lb_const=&
  15: lb_vars={1, 22}, lb_const=&
  16: lb_vars={2, 23}, lb_const=&
  17: lb_vars={3, 24}, lb_const=&
  18: lb_vars={25, 28}, lb_const=&
  19: lb_vars={8, 27}, lb_const=&
  20: lb_vars={9, 23}, lb_const=&
  21: lb_vars={10, 24}, lb_const=&
  22: lb_vars={26}, lb_const=&
  23: lb_vars={16, 20}, lb_const=&
  24: lb_vars={17, 21, 25}, lb_const=&
  25: lb_vars={18, 24}, lb_const=&
  26: lb_vars={22}, lb_const=●
  27: lb_vars={19}, lb_const=●
  28: lb_vars={18}, lb_const=●
  29: lb_vars={30}, lb_const=&
  30: lb_vars={29}, lb_const=&
  31: lb_vars={5, 34}, lb_const=&
  32: lb_vars={6}, lb_const=&
  33: lb_vars={7}, lb_const=&
  34: lb_vars={31}, lb_const=●
  35: lb_vars={}, lb_const=&
  36: lb_vars={}, lb_const=&
  37: lb_vars={}, lb_const=&
""",
    }

    dataset_name = "map_rec#0"
    sample_data = datasets[dataset_name]

    print(f"Visualizing dataset: {dataset_name}")
    print("Parsing graph data...")
    graph_data, constraints = parse_graph_data(sample_data)
    print(f"Parsed graph data: {graph_data}")
    print(f"Parsed constraints: {constraints}")
    print()

    print("Creating directed graph...")
    G = create_directed_graph(graph_data)

    print("Analyzing graph...")
    analyze_graph(G)
    print()

    print("Visualizing graph...")
    visualize_graph(
        G, constraints=constraints, title=f"Constraint Graph - {dataset_name}"
    )

    # plt.savefig('graph_visualization.png', dpi=300, bbox_inches='tight')
    # print("Graph saved as 'graph_visualization.png'")


if __name__ == "__main__":
    main()
