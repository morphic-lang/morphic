use id_collections::{Id, IdVec};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct InternTable<K: Id, V> {
    map: IdVec<K, V>,
    rev_map: BTreeMap<V, K>,
}

impl<K: Id, V: Clone + Ord> InternTable<K, V> {
    pub fn new() -> Self {
        InternTable {
            map: IdVec::new(),
            rev_map: BTreeMap::new(),
        }
    }

    pub fn get(&self, key: K) -> &V {
        &self.map[key]
    }

    pub fn intern(&mut self, value: V) -> K {
        if self.rev_map.contains_key(&value) {
            self.rev_map[&value]
        } else {
            let key = self.map.push(value.clone());
            self.rev_map.insert(value, key);
            key
        }
    }
}
