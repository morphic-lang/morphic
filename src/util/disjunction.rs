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

    pub fn is_const_false(&self) -> bool {
        match self {
            Disj::True => false,
            Disj::Any(conds) => conds.is_empty(),
        }
    }

    pub fn map<U: Ord + Clone>(self, transform: impl Fn(T) -> U) -> Disj<U> {
        match self {
            Disj::True => Disj::True,
            Disj::Any(clauses) => Disj::Any(clauses.into_iter().map(transform).collect()),
        }
    }

    pub fn flat_map<U: Ord + Clone>(&self, transform: impl Fn(&T) -> Disj<U>) -> Disj<U> {
        match self {
            Disj::True => Disj::True,

            Disj::Any(clauses) => {
                let mut result = Disj::new();
                for clause in clauses {
                    result.or_mut(transform(clause));
                }
                result
            }
        }
    }
}

impl<T: Ord + Clone> Default for Disj<T> {
    fn default() -> Self {
        Disj::new()
    }
}
