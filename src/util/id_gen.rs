use crate::util::id_type::Id;

#[derive(Clone, Debug)]
pub struct IdGen<T> {
    next: T,
}

impl<T: Id> IdGen<T> {
    pub fn new() -> IdGen<T> {
        IdGen {
            next: T::from_index(0),
        }
    }

    pub fn fresh(&mut self) -> T {
        let result = self.next.clone();
        self.next = T::from_index(result.to_index() + 1);
        result
    }

    pub fn count(&self) -> usize {
        self.next.to_index()
    }
}
