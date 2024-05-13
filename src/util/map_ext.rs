use id_collections::{Id, IdMap, IdVec};
use std::collections::BTreeMap;

pub trait Map {
    type K;
    type V;

    fn get(&self, k: &Self::K) -> Option<&Self::V>;
}

impl<K: Ord, V> Map for BTreeMap<K, V> {
    type K = K;
    type V = V;

    fn get(&self, k: &K) -> Option<&V> {
        self.get(k)
    }
}

impl<I: Id, V> Map for IdVec<I, V> {
    type K = I;
    type V = V;

    fn get(&self, k: &I) -> Option<&V> {
        self.get(*k)
    }
}

impl<I: Id, V> Map for IdMap<I, V> {
    type K = I;
    type V = V;

    fn get(&self, k: &I) -> Option<&V> {
        self.get(*k)
    }
}

pub trait MapExt<K, V> {
    fn insert_vacant(&mut self, key: K, value: V);
}

impl<K: Ord, V> MapExt<K, V> for BTreeMap<K, V> {
    fn insert_vacant(&mut self, key: K, value: V) {
        let old = self.insert(key, value);
        if old.is_some() {
            panic!("insert_vacant: key already exists");
        }
    }
}

pub fn btree_map_refs<K, V, U>(x: &BTreeMap<K, V>, mut f: impl FnMut(&K, &V) -> U) -> BTreeMap<K, U>
where
    K: Clone + Ord,
{
    x.iter().map(|(k, v)| (k.clone(), f(k, v))).collect()
}
