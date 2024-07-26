use id_collections::{Id, IdMap, IdVec};
use std::collections::BTreeMap;
use std::marker::PhantomData;

/// An abstraction over references to map-like data structures.
pub trait MapRef<'a, K, V>: Copy {
    fn get(self, k: &K) -> Option<&'a V>;
}

impl<'a, K: Ord, V> MapRef<'a, K, V> for &'a BTreeMap<K, V> {
    fn get(self, k: &K) -> Option<&'a V> {
        self.get(k)
    }
}

impl<'a, I: Id, V> MapRef<'a, I, V> for &'a IdVec<I, V> {
    fn get(self, k: &I) -> Option<&'a V> {
        self.get(*k)
    }
}

impl<'a, I: Id, V> MapRef<'a, I, V> for &'a IdMap<I, V> {
    fn get(self, k: &I) -> Option<&'a V> {
        self.get(*k)
    }
}

/// A wrapper for functions which implements `MapRef`. Rust's type inference around closures is
/// quite sketchy and trying to implement `MapRef` directly on closures produces weird type errors
/// at usage sites.
pub struct FnWrap<'a, K, V, F>(F, PhantomData<(K, &'a V)>);

impl<'a, K, V, F> FnWrap<'a, K, V, F>
where
    // `FnWrap` only exists to help the type checker. To that end, the key is this bound.
    F: Fn(&K) -> Option<&'a V> + Copy + 'a,
{
    pub fn wrap(f: F) -> Self {
        Self(f, PhantomData)
    }
}

// `#[derive(Copy)]` isn't smart enough to produce this because `K` needn't be `Copy`.
impl<'a, K, V, F: Copy> Copy for FnWrap<'a, K, V, F> {}

// `#[derive(Clone)]` isn't smart enough to produce this because `K` needn't be `Clone`.
impl<'a, K, V, F: Clone> Clone for FnWrap<'a, K, V, F> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<'a, K, V, F> MapRef<'a, K, V> for FnWrap<'a, K, V, F>
where
    F: Fn(&K) -> Option<&'a V> + Copy + 'a,
{
    fn get(self, k: &K) -> Option<&'a V> {
        (self.0)(k)
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

#[allow(unused_macros)]
macro_rules! map {
    ($($key:expr => $value:expr),* $(,)?) => {
        {
            let mut map = BTreeMap::new();
            $(map.insert($key, $value);)*
            map
        }
    };
}

#[allow(unused_imports)]
pub(crate) use map;

#[allow(unused_macros)]
macro_rules! set {
    ($($elem:expr),* $(,)?) => {
        {
            use std::collections::BTreeSet;
            #[allow(unused_mut)] // compiler bug (?)
            let mut set = BTreeSet::new();
            $(set.insert($elem);)*
            set
        }
    };
}

#[allow(unused_imports)]
pub(crate) use set;
