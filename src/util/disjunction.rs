use im_rc::OrdSet;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Disj<T: Ord + Clone> {
    Any(OrdSet<T>),
    True,
}

impl<T: Ord + Clone> Disj<T> {
    pub fn new() -> Self {
        Disj::Any(OrdSet::new())
    }

    pub fn or(self, other: Self) -> Self {
        match (self, other) {
            (Disj::True, _) => Disj::True,
            (_, Disj::True) => Disj::True,
            (Disj::Any(clauses1), Disj::Any(clauses2)) => Disj::Any(clauses1.union(clauses2)),
        }
    }

    pub fn or_mut(&mut self, other: Self) {
        *self = self.clone().or(other);
    }
}

impl<T: Ord + Clone> Default for Disj<T> {
    fn default() -> Self {
        Disj::new()
    }
}
