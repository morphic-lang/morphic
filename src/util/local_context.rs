use id_collections::{Count, Id, IdVec};

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

    pub fn inner(&self) -> &IdVec<Var, T> {
        &self.stack
    }

    pub fn add_local(&mut self, binding: T) -> Var {
        self.stack.push(binding)
    }

    pub fn pop_local(&mut self) -> (Var, T) {
        self.stack.pop().unwrap()
    }

    pub fn truncate(&mut self, count: Count<Var>) {
        self.stack.truncate(count);
    }

    pub fn local_binding(&self, local: Var) -> &T {
        &self.stack[local]
    }

    pub fn local_binding_mut(&mut self, local: Var) -> &mut T {
        &mut self.stack[local]
    }

    pub fn with_scope<R, F: for<'a> FnOnce(&'a mut LocalContext<Var, T>) -> R>(
        &mut self,
        body: F,
    ) -> R {
        let old_count = self.stack.count();
        let result = body(self);
        debug_assert!(self.stack.count() >= old_count);
        self.stack.truncate(old_count);
        result
    }

    pub fn len(&self) -> usize {
        self.stack.len()
    }

    pub fn count(&self) -> Count<Var> {
        self.stack.count()
    }
}
