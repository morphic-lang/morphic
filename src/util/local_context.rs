use crate::util::id_type::Id;
use crate::util::id_vec::IdVec;

#[derive(Clone, Debug)]
pub struct LocalContext<Var: Id, T> {
    stack: IdVec<Var, T>,
}

impl<Var: Id, T> LocalContext<Var, T> {
    pub fn new() -> Self {
        LocalContext {
            stack: IdVec::new(),
        }
    }

    pub fn add_local(&mut self, binding: T) -> Var {
        self.stack.push(binding)
    }

    pub fn truncate(&mut self, len: usize) {
        self.stack.truncate(len);
    }

    pub fn local_binding(&self, local: Var) -> &T
    where
        T: Clone,
    {
        &self.stack[local]
    }

    pub fn with_scope<R, F: for<'a> FnOnce(&'a mut LocalContext<Var, T>) -> R>(
        &mut self,
        body: F,
    ) -> R {
        let old_len = self.stack.len();
        let result = body(self);
        debug_assert!(self.stack.len() >= old_len);
        self.stack.items.truncate(old_len);
        result
    }

    pub fn len(&self) -> usize {
        self.stack.len()
    }
}
