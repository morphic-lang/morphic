use id_collections::{Id, IdMap, IdVec};
use std::collections::BTreeMap;
use std::marker::PhantomData;

/// An abstraction over references to map-like data structures.
pub trait MapRef<'a, K, V>: Copy {
    fn get(self, k: &K) -> &'a V;
}

impl<'a, K: Ord, V> MapRef<'a, K, V> for &'a BTreeMap<K, V> {
    fn get(self, k: &K) -> &'a V {
        &self[k]
    }
}

impl<'a, I: Id, V> MapRef<'a, I, V> for &'a IdVec<I, V> {
    fn get(self, k: &I) -> &'a V {
        &self[k]
    }
}

impl<'a, I: Id, V> MapRef<'a, I, V> for &'a IdMap<I, V> {
    fn get(self, k: &I) -> &'a V {
        &self[k]
    }
}

/// Implementing `MapRef` directly on closures stress tests Rust's type inference at call sites.
/// `FnWrap` is a lightweight mechanism to help inference.
pub struct FnWrap<'a, K, V, F>(F, PhantomData<(K, &'a V)>);

impl<'a, K, V, F> FnWrap<'a, K, V, F>
where
    // This bound helps inference.
    F: Fn(&K) -> Option<&'a V> + Copy + 'a,
{
    pub fn wrap(f: F) -> Self {
        Self(f, PhantomData)
    }
}

impl<'a, K, V, F: Clone> Clone for FnWrap<'a, K, V, F> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<'a, K, V, F: Copy> Copy for FnWrap<'a, K, V, F> {}

impl<'a, K, V, F> MapRef<'a, K, V> for FnWrap<'a, K, V, F>
where
    F: Fn(&K) -> &'a V + Copy + 'a,
{
    fn get(self, k: &K) -> &'a V {
        (self.0)(k)
    }
}

pub trait BTreeMapExt<K, V> {
    fn insert_vacant(&mut self, key: K, value: V);

    fn map_refs<U>(&self, f: impl FnMut(&K, &V) -> U) -> BTreeMap<K, U>
    where
        K: Clone;
}

impl<K: Ord, V> BTreeMapExt<K, V> for BTreeMap<K, V> {
    fn insert_vacant(&mut self, key: K, value: V) {
        let old = self.insert(key, value);
        if old.is_some() {
            panic!("insert_vacant: key already exists");
        }
    }

    fn map_refs<U>(&self, mut f: impl FnMut(&K, &V) -> U) -> BTreeMap<K, U>
    where
        K: Clone,
    {
        self.iter().map(|(k, v)| (k.clone(), f(k, v))).collect()
    }
}

pub trait VecExt<T> {
    fn map_refs<U>(&self, f: impl FnMut(&T) -> U) -> Vec<U>
    where
        T: Clone;
}

impl<T> VecExt<T> for Vec<T> {
    fn map_refs<U>(&self, f: impl FnMut(&T) -> U) -> Vec<U>
    where
        T: Clone,
    {
        self.iter().map(f).collect()
    }
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
            #[allow(unused_mut)] // false positive
            let mut set = BTreeSet::new();
            $(set.insert($elem);)*
            set
        }
    };
}

#[allow(unused_imports)]
pub(crate) use set;
