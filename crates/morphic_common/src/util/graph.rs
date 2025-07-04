use id_collections::{Id, IdVec};

#[derive(Clone, Debug)]
pub struct Graph<NodeId: Id> {
    pub edges_out: IdVec<NodeId, Vec<NodeId>>, // Indexed by NodeId
}

// Reversal

fn reverse<NodeId: Id>(graph: &Graph<NodeId>) -> Graph<NodeId> {
    let mut edges_in = IdVec::from_vec((0..graph.edges_out.len()).map(|_| Vec::new()).collect());

    for (src, edges) in &graph.edges_out {
        for dest in edges {
            edges_in[dest].push(src.clone());
        }
    }

    Graph {
        edges_out: edges_in,
    }
}

// Depth-First Exploration

fn dfs_postorder<NodeId: Id, I: Iterator<Item = NodeId>>(
    graph: &Graph<NodeId>,
    roots: I,
) -> Vec<NodeId> {
    let mut visited: IdVec<NodeId, _> = IdVec::from_vec(vec![false; graph.edges_out.len()]);
    let mut traversal = Vec::new();

    enum Action<NodeId> {
        Push(NodeId),
        Done(NodeId),
    }

    let mut stack = roots.map(Action::Push).collect::<Vec<_>>();

    while let Some(action) = stack.pop() {
        match action {
            Action::Push(to_push) => {
                if visited[&to_push] {
                    continue;
                }

                visited[&to_push] = true;

                stack.push(Action::Done(to_push.clone()));

                for neighbor in &graph.edges_out[&to_push] {
                    if visited[neighbor] {
                        continue;
                    }

                    stack.push(Action::Push(neighbor.clone()));
                }
            }

            Action::Done(id) => {
                traversal.push(id);
            }
        }
    }

    traversal
}

// Strongly-Connected Components

pub fn strongly_connected<NodeId: Id>(graph: &Graph<NodeId>) -> Vec<Vec<NodeId>> {
    let reversed = reverse(graph);

    let scc_order = dfs_postorder(&reversed, reversed.edges_out.count().into_iter());

    let mut visited: IdVec<NodeId, _> = IdVec::from_vec(vec![false; graph.edges_out.len()]);

    let mut sccs = Vec::new();

    for scc_root in scc_order.iter().rev() {
        if visited[scc_root] {
            continue;
        }

        let mut scc = Vec::new();

        let mut to_visit = vec![scc_root.clone()];

        while let Some(scc_node) = to_visit.pop() {
            if visited[&scc_node] {
                continue;
            }

            visited[&scc_node] = true;

            scc.push(scc_node.clone());

            for neighbor in &graph.edges_out[&scc_node] {
                if visited[neighbor] {
                    continue;
                }

                to_visit.push(neighbor.clone());
            }
        }

        sccs.push(scc);
    }

    sccs
}

#[derive(Clone, Debug)]
pub enum Scc<NodeId> {
    Acyclic(NodeId),
    Cyclic(Vec<NodeId>),
}

impl<NodeId> Scc<NodeId> {
    pub fn iter(&self) -> SccIter<NodeId> {
        self.into_iter()
    }
}

#[derive(Clone, Debug)]
enum SccIterImpl<'a, NodeId> {
    Acyclic(std::iter::Once<&'a NodeId>),
    Cyclic(std::slice::Iter<'a, NodeId>),
}

#[derive(Clone, Debug)]
pub struct SccIter<'a, NodeId> {
    inner: SccIterImpl<'a, NodeId>,
}

impl<'a, NodeId> Iterator for SccIter<'a, NodeId> {
    type Item = &'a NodeId;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            SccIterImpl::Acyclic(iter) => iter.next(),
            SccIterImpl::Cyclic(iter) => iter.next(),
        }
    }
}

impl<'a, NodeId> IntoIterator for &'a Scc<NodeId> {
    type Item = &'a NodeId;
    type IntoIter = SccIter<'a, NodeId>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Scc::Acyclic(node) => SccIter {
                inner: SccIterImpl::Acyclic(std::iter::once(node)),
            },
            Scc::Cyclic(nodes) => SccIter {
                inner: SccIterImpl::Cyclic(nodes.iter()),
            },
        }
    }
}

pub fn acyclic_and_cyclic_sccs<NodeId: Id + Eq>(graph: &Graph<NodeId>) -> Vec<Scc<NodeId>> {
    let sccs = strongly_connected(graph);

    sccs.into_iter()
        .map(|mut scc| {
            if scc.len() == 1 {
                let singleton = &scc[0];
                if !graph.edges_out[singleton].contains(singleton) {
                    return Scc::Acyclic(singleton.clone());
                }
            }
            // Reverse the SCC to get a more favorable ordering for fixed point iteration. This is
            // purely a performance optimization, and has no bearing on correctness.
            scc.reverse();
            Scc::Cyclic(scc)
        })
        .collect()
}

// Simple generative property-based testing

#[cfg(test)]
mod test {
    use super::*;

    fn nodes_exactly_once<NodeId: Id>(graph: &Graph<NodeId>, sccs: &[Vec<NodeId>]) -> bool {
        let mut seen: IdVec<NodeId, _> = IdVec::from_vec(vec![false; graph.edges_out.len()]);

        for scc in sccs {
            for node in scc {
                if seen[node] {
                    return false;
                }

                seen[node] = true;
            }
        }

        seen.iter().all(|(_, &flag)| flag)
    }

    fn sccs_linearized<NodeId: Id>(graph: &Graph<NodeId>, sccs: &[Vec<NodeId>]) -> bool {
        let mut seen: IdVec<NodeId, _> = IdVec::from_vec(vec![false; graph.edges_out.len()]);

        for scc in sccs {
            for node in scc {
                seen[node] = true;
            }

            for node in scc {
                for out_neighbor in &graph.edges_out[node] {
                    if !seen[out_neighbor] {
                        return false;
                    }
                }
            }
        }

        true
    }

    fn is_root<NodeId: Id + Ord>(
        graph: &Graph<NodeId>,
        subgraph: &[NodeId],
        root: &NodeId,
    ) -> bool {
        use std::collections::BTreeSet;

        let subgraph_set: BTreeSet<_> = subgraph.iter().cloned().collect();

        let mut visited = BTreeSet::new();
        visited.insert(root.clone());

        let mut fringe = vec![root.clone()];
        visited.insert(root.clone());

        while let Some(node) = fringe.pop() {
            assert!(subgraph_set.contains(&node));
            assert!(visited.contains(&node));

            for neighbor in &graph.edges_out[&node] {
                if subgraph_set.contains(&neighbor) && !visited.contains(&neighbor) {
                    fringe.push(neighbor.clone());
                    visited.insert(neighbor.clone());
                }
            }
        }

        subgraph_set == visited
    }

    fn sccs_strongly_connected<NodeId: Id + Ord>(
        graph: &Graph<NodeId>,
        sccs: &[Vec<NodeId>],
    ) -> bool {
        for scc in sccs {
            // NOTE: This intentionally runs in quadratic time
            for node in scc {
                if !is_root(graph, scc, node) {
                    return false;
                }
            }
        }

        true
    }

    fn assert_valid_sccs<NodeId: Id + Ord>(graph: &Graph<NodeId>, sccs: &[Vec<NodeId>]) {
        assert!(nodes_exactly_once(graph, sccs));
        assert!(sccs_linearized(graph, sccs));
        assert!(sccs_strongly_connected(graph, sccs));
    }

    #[test]
    fn test_random() {
        use id_collections::id_type;
        use rand::SeedableRng;
        use rand_distr::{Distribution, Exp, Uniform};
        use rand_pcg::Pcg64Mcg;

        #[id_type]
        struct TestNodeId(usize);

        // Seed generated once for deterministic tests
        let mut gen = Pcg64Mcg::seed_from_u64(0xe2662e13b18f515);

        const NUM_NODES: usize = 20;
        const NUM_TESTS_PER_CFG: u32 = 50;

        for &mean_edges in &[0.01, 1.0, 5.0, 10.0] {
            for _ in 0..NUM_TESTS_PER_CFG {
                let mut graph = Graph {
                    edges_out: IdVec::from_vec(vec![Vec::new(); NUM_NODES]),
                };

                for (_, node_edges) in graph.edges_out.iter_mut() {
                    for _ in 0..(Exp::new(mean_edges).unwrap().sample(&mut gen) as u32) {
                        node_edges.push(TestNodeId(
                            Uniform::new(0, NUM_NODES).unwrap().sample(&mut gen),
                        ));
                    }
                }

                let sccs = strongly_connected(&graph);

                assert_valid_sccs(&graph, &sccs);
            }
        }
    }
}

// Connected components

#[derive(Clone, Debug)]
pub struct Undirected<NodeId: Id>(Graph<NodeId>);

impl<NodeId: Id> Undirected<NodeId> {
    pub fn from_directed_unchecked(graph: Graph<NodeId>) -> Self {
        Undirected(graph)
    }

    pub fn into_directed(self) -> Graph<NodeId> {
        self.0
    }
}

pub fn connected_components<NodeId: Id>(graph: &Undirected<NodeId>) -> Vec<Vec<NodeId>> {
    let mut components = Vec::new();

    let mut visited: IdVec<NodeId, _> = IdVec::from_vec(vec![false; graph.0.edges_out.len()]);

    for root_id in graph.0.edges_out.count().into_iter() {
        if visited[&root_id] {
            continue;
        }

        let mut component = Vec::new();

        let mut to_visit = vec![root_id];

        while let Some(node) = to_visit.pop() {
            if visited[&node] {
                continue;
            }

            component.push(node.clone());

            for neighbor in &graph.0.edges_out[&node] {
                to_visit.push(neighbor.clone());
            }

            visited[&node] = true;
        }

        components.push(component);
    }

    components
}
