use id_collections::{Id, IdVec};

pub struct ZipEq<I, J> {
    lhs: I,
    rhs: J,
}

impl<I, J> Iterator for ZipEq<I, J>
where
    I: Iterator,
    J: Iterator,
{
    type Item = (I::Item, J::Item);

    fn next(&mut self) -> Option<Self::Item> {
        match (self.lhs.next(), self.rhs.next()) {
            (Some(a), Some(b)) => Some((a, b)),
            (None, None) => None,
            (Some(_), None) => panic!(".zip_eq(): rhs iterator is shorter"),
            (None, Some(_)) => panic!(".zip_eq(): lhs iterator is shorter"),
        }
    }
}

pub trait IterExt {
    fn zip_eq<T>(self, other: T) -> ZipEq<Self, T::IntoIter>
    where
        Self: Sized,
        T: IntoIterator;
}

impl<I> IterExt for I {
    fn zip_eq<T>(self, other: T) -> ZipEq<Self, T::IntoIter>
    where
        Self: Sized,
        T: IntoIterator,
    {
        ZipEq {
            lhs: self,
            rhs: other.into_iter(),
        }
    }
}

pub fn try_zip_eq<'a, K: Id, V, U>(
    lhs: &'a IdVec<K, V>,
    rhs: &'a IdVec<K, U>,
) -> Option<impl Iterator<Item = (K, &'a V, &'a U)>> {
    if lhs.len() != rhs.len() {
        None
    } else {
        Some(lhs.iter().zip(rhs.values()).map(|((k, v), u)| (k, v, u)))
    }
}
