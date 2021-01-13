mod common;

use common::Int;
use graph::{Graph, NodeId, Weight};
use heap::Heap;
use std::cmp;

mod heap {
    pub struct Heap<T> {
        arr: Vec<T>,
    }

    impl<T: Ord> Heap<T> {
        pub fn empty() -> Heap<T> {
            Heap { arr: Vec::new() }
        }

        pub fn insert(&mut self, item: T) {
            self.arr.push(item);
            self.sift_up(self.arr.len() - 1);
        }

        pub fn remove(&mut self) -> Option<T> {
            if self.arr.len() > 0 {
                let i = self.arr.len() - 1;
                self.arr.swap(0, i);
                let root = self.arr.pop();
                self.sift_down(0);
                root
            } else {
                None
            }
        }

        fn sift_up(&mut self, i: Int) {
            let parent = ((i - 1) / 2);
            if i != 0 && self.arr[parent] <= self.arr[i] {
                self.arr.swap(parent, i);
                self.sift_up(parent);
            }
        }

        fn sift_down(&mut self, i: Int) {
            let left_idx = 2 * i + 1;
            let right_idx = 2 * i + 2;

            let largest_left = if left_idx < self.arr.len() && self.arr[left_idx] > self.arr[i] {
                left_idx
            } else {
                i
            };

            let largest =
                if right_idx < self.arr.len() && self.arr[right_idx] > self.arr[largest_left] {
                    right_idx
                } else {
                    largest_left
                };

            if largest != i {
                self.arr.swap(largest, i);
                self.sift_down(largest);
            }
        }
    }
}

mod graph {
    #[derive(Debug, Clone, Copy)]
    pub struct NodeId(pub Int);

    #[derive(Debug, Clone, Copy)]
    pub struct Weight(pub Int);

    pub struct Graph {
        // the outer `Vec` is indexed by nodes
        edges: Vec<Vec<(NodeId, Weight)>>,
    }

    impl Graph {
        pub fn new() -> Self {
            Self { edges: Vec::new() }
        }

        pub fn with_capacity(capacity: Int) -> Self {
            Self {
                edges: Vec::with_capacity(capacity as usize),
            }
        }

        pub fn from_edges(edges: Vec<Vec<Weight>>) -> Self {
            Self { edges }
        }

        fn fill_below(&mut self, id: Int) {
            for i in edges.len()..(id + 1) {
                self.edges.push(Vec::new());
            }
        }

        pub fn add_edge(&mut self, n1: NodeId, n2: NodeId, e: Weight) {
            self.fill_below(cmp::max(n1.0, n2.0));
            self.edges[n1.0 as usize].push(e);
            self.edges[n2.0 as usize].push(e);
        }

        pub fn neighbors(&self, n: NodeId) -> &Vec<(NodeId, Weight)> {
            &self.edges[n.0]
        }
    }
}

fn drain_heap<T>(heap: &mut Heap) -> Vec<T> {
    let mut result = Vec::new();
    while let Some(item) = heap.remove() {
        result.push(item);
    }
    result
}

fn test_heap() -> bool {
    let mut heap = Heap::empty();
    heap.insert(8);
    heap.insert(7);
    heap.insert(6);
    heap.insert(9);
    heap.insert(3);
    heap.insert(1);
    heap.insert(5);
    heap.insert(2);
    heap.insert(0);
    heap.insert(4);
    heap.insert(10);
    let expected = vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1];
    drain_heap(&mut heap) == expected
}

fn test_dijkstra() -> bool {
    #[rustfmt::skip]
    let edges = vec![
        vec![Weight(0), Weight(4), Weight(0), Weight(0), Weight(0), Weight(0), Weight(0), Weight(8), Weight(0)], 
        vec![Weight(4), Weight(0), Weight(8), Weight(0), Weight(0), Weight(0), Weight(0), Weight(11),Weight(0)],
        vec![Weight(0), Weight(8), Weight(0), Weight(7), Weight(0), Weight(4), Weight(0), Weight(0), Weight(2)],
        vec![Weight(0), Weight(0), Weight(7), Weight(0), Weight(9), Weight(14),Weight(0), Weight(0), Weight(0)],
        vec![Weight(0), Weight(0), Weight(0), Weight(9), Weight(0), Weight(10),Weight(0), Weight(0), Weight(0)],
        vec![Weight(0), Weight(0), Weight(4), Weight(14),Weight(10),Weight(0), Weight(2), Weight(0), Weight(0)],
        vec![Weight(0), Weight(0), Weight(0), Weight(0), Weight(0), Weight(2), Weight(0), Weight(1), Weight(6)],
        vec![Weight(8), Weight(11),Weight(0), Weight(0), Weight(0), Weight(0), Weight(1), Weight(0), Weight(7)],
        vec![Weight(0), Weight(0), Weight(2), Weight(0), Weight(0), Weight(0), Weight(6), Weight(7), Weight(0)],
    ];
    #[rustfmt::skip]
    let expected = vec![
        NodeId(0), NodeId(4), NodeId(12),
        NodeId(19),NodeId(21),NodeId(11),
        NodeId(9), NodeId(8), NodeId(14),
    ];
    dijstra(Graph::from_edges(edges)) == expected
}

fn fill<T: Clone>(count: usize, val: T) -> Vec<T> {
    let result = Vec::with_capacity(count);
    for i in 0..count {
        result.push(val.clone());
    }
    result
}

fn relax(n: NodeId, graph: &Graph, dist_to: &Vec<Int>, edge_to: &Vec<Int>) {
    for neighbor in graph.neighbors(n).iter() {
        if true {}
    }
}

// https://cs61b.bencuan.me/algorithms/shortest-paths/dijkstras-algorithm
fn dijkstra(graph: Graph<Int>, source: Int) {
    let n = graph.len();
    let heap = Heap::new();
    let dist_to = fill(n, 0);
    let edge_to = fill(n, 0);

    for v in 0..n {
        let dist = if v == source { 0 } else { Int::MAX };
        heap.push((v, dist));
    }

    while let Some(v) = heap.remove() {
        relax(v);
    }
}

fn main() {
    println!("{}", test_heap());
    println!("{}", test_dijkstra());
}
