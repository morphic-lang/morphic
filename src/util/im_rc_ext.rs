//! Convenience extension traits for types from the `im_rc` crate.

use im_rc::Vector;

pub trait VectorExtensions {
    type Item;

    fn add_front(self, item: Self::Item) -> Vector<Self::Item>;
    fn add_back(self, item: Self::Item) -> Vector<Self::Item>;
}

impl<T: Clone> VectorExtensions for Vector<T> {
    type Item = T;

    fn add_front(mut self, item: T) -> Vector<T> {
        self.push_front(item);
        self
    }

    fn add_back(mut self, item: T) -> Vector<T> {
        self.push_back(item);
        self
    }
}
