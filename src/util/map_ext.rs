use std::collections::BTreeMap;

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
