use id_collections::{Id, IdVec};

pub struct ZipEq<I, J> {
    a: I,
    b: J,
}

impl<I, J> Iterator for ZipEq<I, J>
where
    I: Iterator,
    J: Iterator,
{
    type Item = (I::Item, J::Item);

    fn next(&mut self) -> Option<Self::Item> {
        match (self.a.next(), self.b.next()) {
            (Some(a), Some(b)) => Some((a, b)),
            (None, None) => None,
            (Some(_), None) => panic!(".zip_eq(): rhs iterator is shorter"),
            (None, Some(_)) => panic!(".zip_eq(): lhs iterator is shorter"),
        }
    }
}

pub trait IterExt {
    fn try_zip_eq<T, J>(self, other: T) -> Option<std::iter::Zip<Self, J>>
    where
        Self: Sized + ExactSizeIterator,
        J: Sized + ExactSizeIterator,
        T: IntoIterator<IntoIter = J>;

    fn zip_eq<T>(self, other: T) -> ZipEq<Self, T::IntoIter>
    where
        Self: Sized,
        T: IntoIterator;
}

impl<I> IterExt for I {
    fn try_zip_eq<T, J>(self, other: T) -> Option<std::iter::Zip<Self, J>>
    where
        Self: Sized + ExactSizeIterator,
        J: Sized + ExactSizeIterator,
        T: IntoIterator<IntoIter = J>,
    {
        let other = other.into_iter();
        if self.len() == other.len() {
            Some(self.zip(other))
        } else {
            None
        }
    }

    fn zip_eq<T>(self, other: T) -> ZipEq<Self, T::IntoIter>
    where
        Self: Sized,
        T: IntoIterator,
    {
        ZipEq {
            a: self,
            b: other.into_iter(),
        }
    }
}

pub fn try_zip_eq<'a, K: Id, V, U>(
    lhs: &'a IdVec<K, V>,
    rhs: &'a IdVec<K, U>,
) -> Option<impl Iterator<Item = (K, &'a V, &'a U)>> {
    lhs.iter()
        .try_zip_eq(rhs)
        .map(|zip| zip.map(|((id, lhs), (_, rhs))| (id, lhs, rhs)))
}
