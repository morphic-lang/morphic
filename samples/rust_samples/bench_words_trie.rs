use std::marker::PhantomData;

trait TrieKey<'a> {
    type Components: Iterator<Item = usize> + 'a;

    fn alph_size() -> usize;

    fn components(&'a self) -> Self::Components;
}

#[derive(Clone, Debug)]
struct SparseArray<K, T> {
    key_phantom: PhantomData<K>,
    store: Option<(Vec<Option<T>>, usize)>,
}

impl<K: for<'a> TrieKey<'a>, T> SparseArray<K, T> {
    fn new() -> Self {
        SparseArray {
            key_phantom: PhantomData,
            store: None,
        }
    }

    fn is_empty(&self) -> bool {
        self.store.is_none()
    }

    fn get(&self, i: usize) -> Option<&T> {
        match &self.store {
            Some((arr, _)) => arr[i].as_ref(),
            None => {
                if i < K::alph_size() {
                    None
                } else {
                    panic!("Sparse array index out of bounds")
                }
            }
        }
    }

    fn update(&mut self, i: usize, func: impl for<'a> FnOnce(&'a mut Option<T>)) {
        match &mut self.store {
            Some((arr, num_pop)) => {
                let val = &mut arr[i];
                let num_pop_without_val = if val.is_some() {
                    *num_pop - 1
                } else {
                    *num_pop
                };
                func(val);
                if val.is_some() {
                    *num_pop = num_pop_without_val + 1;
                } else if num_pop_without_val > 0 {
                    *num_pop = num_pop_without_val;
                } else {
                    self.store = None;
                }
            }

            None => {
                let mut val = None;
                func(&mut val);
                if val.is_some() {
                    let mut init_arr = Vec::with_capacity(K::alph_size());
                    init_arr.resize_with(K::alph_size(), || None);
                    init_arr[i] = val;
                    self.store = Some((init_arr, 1));
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
struct Node<K, V> {
    leaf: Option<V>,
    children: SparseArray<K, Node<K, V>>,
}

impl<K: for<'a> TrieKey<'a>, V> Node<K, V> {
    fn new() -> Self {
        Node {
            leaf: None,
            children: SparseArray::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.leaf.is_none() && self.children.is_empty()
    }

    fn get<'a, 'b>(&'a self, key: &mut <K as TrieKey<'b>>::Components) -> Option<&'a V> {
        match key.next() {
            Some(index) => self.children.get(index).and_then(|child| child.get(key)),
            None => self.leaf.as_ref(),
        }
    }

    fn update<'a>(
        &mut self,
        key: &mut <K as TrieKey<'a>>::Components,
        func: impl for<'b> FnOnce(&'b mut Option<V>),
    ) {
        match key.next() {
            Some(index) => {
                self.children.update(index, |opt_child| {
                    match opt_child {
                        Some(child) => {
                            child.update(key, func);
                        }
                        None => {
                            // Instead of calling `func` and doing this match, it would also be
                            // semantically correct to write:
                            //
                            //   let mut new_child = Node::new();
                            //   new_child.update(key, func);
                            //   *opt_child = Some(new_child);
                            //
                            // However, we know that `func` will eventually be called with `None` at
                            // the end of the chain, and if `func(None)` leaves its argument as
                            // `None` then the code proposed above would create a chain of new
                            // intermediate nodes and then immediately destroy them.  It's more
                            // efficient to compute `func(None)` here, and avoid creating the chain
                            // in the first place when `func` takes `None` to `None`.
                            let mut val = None;
                            func(&mut val);
                            match val {
                                Some(new_val) => {
                                    // We need to 'outline' this to avoid infinite polymorphic
                                    // recursion in the following recursive call.
                                    fn const_assign_closure<V>(
                                        new_val: V,
                                    ) -> impl for<'a> FnOnce(&'a mut Option<V>)
                                    {
                                        |leaf_val| {
                                            *leaf_val = Some(new_val);
                                        }
                                    }

                                    let mut new_child = Node::new();
                                    new_child.update(key, const_assign_closure(new_val));
                                    *opt_child = Some(new_child);
                                }
                                None => {}
                            }
                        }
                    }

                    if let Some(child) = opt_child {
                        if child.is_empty() {
                            *opt_child = None;
                        }
                    }
                });
            }

            None => {
                func(&mut self.leaf);
            }
        }
    }
}

#[derive(Clone, Debug)]
struct Trie<K, V> {
    root: Node<K, V>,
}

impl<K: for<'a> TrieKey<'a>, V> Trie<K, V> {
    fn new() -> Self {
        Trie { root: Node::new() }
    }

    #[allow(dead_code)]
    fn is_empty(&self) -> bool {
        self.root.is_empty()
    }

    fn get<'a>(&'a self, key: &K) -> Option<&'a V> {
        self.root.get(&mut key.components())
    }

    fn update(&mut self, key: &K, func: impl for<'a> FnOnce(&'a mut Option<V>)) {
        self.root.update(&mut key.components(), func);
    }

    #[allow(dead_code)]
    fn set(&mut self, key: &K, opt_val: Option<V>) {
        self.root.update(&mut key.components(), |leaf_val| {
            *leaf_val = opt_val;
        })
    }
}

#[derive(Clone, Debug)]
struct BytesComponents<'a> {
    iter: std::slice::Iter<'a, u8>,
}

impl<'a> Iterator for BytesComponents<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        self.iter.next().map(|&byte| byte as usize)
    }
}

#[derive(Clone, Debug)]
struct BytesKey(Vec<u8>);

impl<'a> TrieKey<'a> for BytesKey {
    type Components = BytesComponents<'a>;

    fn alph_size() -> usize {
        256
    }

    fn components(&'a self) -> Self::Components {
        BytesComponents {
            iter: self.0.iter(),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Nybble {
    Lo,
    Hi,
}

#[derive(Clone, Debug)]
struct NybblesComponents<'a> {
    iter: std::slice::Iter<'a, u8>,
    nybble: Nybble,
}

impl<'a> Iterator for NybblesComponents<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        match self.nybble {
            Nybble::Lo => {
                let result = self
                    .iter
                    .as_slice()
                    .first()
                    .map(|&byte| (byte & 0x0f) as usize);
                self.nybble = Nybble::Hi;
                result
            }

            Nybble::Hi => {
                let result = self.iter.next().map(|&byte| ((byte & 0xf0) >> 4) as usize);
                self.nybble = Nybble::Lo;
                result
            }
        }
    }
}

#[derive(Clone, Debug)]
struct NybblesKey(Vec<u8>);

impl<'a> TrieKey<'a> for NybblesKey {
    type Components = NybblesComponents<'a>;

    fn alph_size() -> usize {
        16
    }

    fn components(&'a self) -> Self::Components {
        NybblesComponents {
            iter: self.0.iter(),
            nybble: Nybble::Lo,
        }
    }
}

mod common;

use common::{read_line, repeat, write_report, ProfileInfo};

static COUNT_WORDS_INFO: ProfileInfo = ProfileInfo::new();

fn read_words() -> Vec<NybblesKey> {
    let mut words = Vec::new();
    loop {
        let line = read_line().into_bytes();
        if line.is_empty() {
            break;
        }
        words.push(NybblesKey(line));
    }
    words
}

fn count_words(tokens: &[NybblesKey], queries: &[NybblesKey]) -> Vec<u64> {
    COUNT_WORDS_INFO.record_call(|| {
        let mut counts: Trie<NybblesKey, u64> = Trie::new();
        for token in tokens {
            counts.update(token, |count| {
                *count = Some(count.unwrap_or(0) + 1);
            });
        }

        queries
            .iter()
            .map(|query| counts.get(query).cloned().unwrap_or(0))
            .collect()
    })
}

fn main() {
    match read_line().parse::<u64>() {
        Ok(iters) => {
            let tokens = read_words();
            let queries = read_words();
            if let Some(query_counts) = repeat(iters, || count_words(&tokens, &queries)) {
                for count in query_counts {
                    println!("{}", count);
                }
            }
        }

        Err(_) => eprintln!("Please enter an iteration count"),
    }

    write_report(&COUNT_WORDS_INFO);
}
