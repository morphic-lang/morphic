use std::collections::{btree_set, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct NonEmptySet<T>(BTreeSet<T>);

impl<T> NonEmptySet<T> {
    pub fn new(value: T) -> Self
    where
        T: Ord,
    {
        Self(std::iter::once(value).collect())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter<'a>(&'a self) -> btree_set::Iter<'a, T> {
        self.0.iter()
    }
}

impl<T: Ord> Extend<T> for NonEmptySet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.0.extend(iter);
    }
}

impl<T: Ord + Clone> std::ops::BitOr for &NonEmptySet<T> {
    type Output = NonEmptySet<T>;

    fn bitor(self, rhs: &NonEmptySet<T>) -> Self::Output {
        NonEmptySet(&self.0 | &rhs.0)
    }
}

impl<T> TryFrom<BTreeSet<T>> for NonEmptySet<T> {
    type Error = ();

    fn try_from(set: BTreeSet<T>) -> Result<Self, Self::Error> {
        if !set.is_empty() {
            Ok(Self(set))
        } else {
            Err(())
        }
    }
}

impl<'a, T> IntoIterator for &'a NonEmptySet<T> {
    type Item = &'a T;
    type IntoIter = btree_set::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
