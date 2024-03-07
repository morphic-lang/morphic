use id_collections::{Count, Id};

#[derive(Clone, Debug)]
pub struct IdGen<T: Id> {
    next: Count<T>,
}

impl<T: Id> IdGen<T> {
    pub fn new() -> IdGen<T> {
        IdGen { next: Count::new() }
    }

    pub fn fresh(&mut self) -> T {
        self.next.inc()
    }

    pub fn count(&self) -> Count<T> {
        self.next.clone()
    }
}
