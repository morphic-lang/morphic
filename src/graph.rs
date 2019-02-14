#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeId(pub usize);

#[derive(Clone, Debug)]
pub struct Graph {
    pub edges_out: Vec<Vec<NodeId>>, // Indexed by NodeId
}

// Reversal

fn reverse(graph: &Graph) -> Graph {
    let mut edges_in = vec![vec![]; graph.edges_out.len()];

    for (src, edges) in graph.edges_out.iter().enumerate() {
        for &NodeId(dest) in edges {
            edges_in[dest].push(NodeId(src));
        }
    }

    Graph {
        edges_out: edges_in,
    }
}

// Depth-First Exploration

fn dfs_postorder<I: Iterator<Item = NodeId>>(graph: &Graph, roots: I) -> Vec<NodeId> {
    let mut visited = vec![false; graph.edges_out.len()];
    let mut traversal = Vec::new();

    #[derive(Debug)]
    enum Action {
        Push(NodeId),
        Done(NodeId),
    }

    let mut stack = roots.map(Action::Push).collect::<Vec<_>>();

    while let Some(action) = stack.pop() {
        match action {
            Action::Push(NodeId(to_push)) => {
                if visited[to_push] {
                    continue;
                }

                visited[to_push] = true;

                stack.push(Action::Done(NodeId(to_push)));

                for &NodeId(neighbor) in &graph.edges_out[to_push] {
                    if visited[neighbor] {
                        continue;
                    }

                    stack.push(Action::Push(NodeId(neighbor)));
                }
            }

            Action::Done(NodeId(id)) => {
                traversal.push(NodeId(id));
            }
        }
    }

    traversal
}

// Strongly-Connected Components

pub fn strongly_connected(graph: &Graph) -> Vec<Vec<NodeId>> {
    let reversed = reverse(graph);

    let scc_order = dfs_postorder(&reversed, (0..reversed.edges_out.len()).map(NodeId));

    let mut visited = vec![false; graph.edges_out.len()];

    let mut sccs = Vec::new();

    for &scc_root in scc_order.iter().rev() {
        if visited[scc_root.0] {
            continue;
        }

        let mut scc = Vec::new();

        let mut to_visit = vec![scc_root];

        while let Some(scc_node) = to_visit.pop() {
            if visited[scc_node.0] {
                continue;
            }

            visited[scc_node.0] = true;

            scc.push(scc_node);

            for &neighbor in &graph.edges_out[scc_node.0] {
                if visited[neighbor.0] {
                    continue;
                }

                to_visit.push(neighbor);
            }
        }

        sccs.push(scc);
    }

    sccs
}

// Simple generative property-based testing

#[cfg(test)]
mod test {
    use super::*;

    fn nodes_exactly_once(graph: &Graph, sccs: &[Vec<NodeId>]) -> bool {
        let mut seen = vec![false; graph.edges_out.len()];

        for scc in sccs {
            for &NodeId(node) in scc {
                if seen[node] {
                    return false;
                }

                seen[node] = true;
            }
        }

        seen.iter().all(|&flag| flag)
    }

    fn sccs_linearized(graph: &Graph, sccs: &[Vec<NodeId>]) -> bool {
        let mut seen = vec![false; graph.edges_out.len()];

        for scc in sccs {
            for &NodeId(node) in scc {
                seen[node] = true;
            }

            for &NodeId(node) in scc {
                for &NodeId(out_neighbor) in &graph.edges_out[node] {
                    if !seen[out_neighbor] {
                        return false;
                    }
                }
            }
        }

        true
    }

    fn is_root(graph: &Graph, subgraph: &[NodeId], root: NodeId) -> bool {
        use std::collections::BTreeSet;

        let subgraph_set: BTreeSet<_> = subgraph.iter().cloned().collect();

        let mut visited = BTreeSet::new();
        visited.insert(root);

        let mut fringe = vec![root];
        visited.insert(root);

        while let Some(node) = fringe.pop() {
            assert!(subgraph_set.contains(&node));
            assert!(visited.contains(&node));

            for &neighbor in &graph.edges_out[node.0] {
                if subgraph_set.contains(&neighbor) && !visited.contains(&neighbor) {
                    fringe.push(neighbor);
                    visited.insert(neighbor);
                }
            }
        }

        subgraph_set == visited
    }

    fn sccs_strongly_connected(graph: &Graph, sccs: &[Vec<NodeId>]) -> bool {
        for scc in sccs {
            // NOTE: This intentionally runs in quadratic time
            for &node in scc {
                if !is_root(graph, scc, node) {
                    return false;
                }
            }
        }

        true
    }

    fn assert_valid_sccs(graph: &Graph, sccs: &[Vec<NodeId>]) {
        assert!(nodes_exactly_once(graph, sccs));
        assert!(sccs_linearized(graph, sccs));
        assert!(sccs_strongly_connected(graph, sccs));
    }

    #[test]
    fn test_random() {
        use rand::distributions::{Distribution, Exp, Uniform};
        use rand::SeedableRng;
        use rand_pcg::Pcg64Mcg;

        // Seed generated once for deterministic tests
        let mut gen = Pcg64Mcg::seed_from_u64(0xe2662e13b18f515);

        const NUM_NODES: usize = 20;
        const NUM_TESTS_PER_CFG: u32 = 50;

        for &mean_edges in &[0.01, 1.0, 5.0, 10.0] {
            for _ in 0..NUM_TESTS_PER_CFG {
                let mut graph = Graph {
                    edges_out: vec![Vec::new(); NUM_NODES],
                };

                for node_edges in graph.edges_out.iter_mut() {
                    for _ in 0..(Exp::new(mean_edges).sample(&mut gen) as u32) {
                        node_edges.push(NodeId(Uniform::new(0, NUM_NODES).sample(&mut gen)));
                    }
                }

                let sccs = strongly_connected(&graph);

                assert_valid_sccs(&graph, &sccs);
            }
        }
    }
}
