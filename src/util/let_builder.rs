use id_collections::{Count, Id};

pub trait FromBindings {
    type LocalId: Id;
    type Binding;

    fn from_bindings(bindings: Vec<Self::Binding>, ret: Self::LocalId) -> Self;
}

#[derive(Clone, Debug)]
pub struct LetManyBuilder<E: FromBindings> {
    num_locals: Count<E::LocalId>,
    bindings: Vec<E::Binding>,
}

impl<E: FromBindings> LetManyBuilder<E> {
    pub fn new(num_locals: Count<E::LocalId>) -> Self {
        LetManyBuilder {
            num_locals,
            bindings: Vec::new(),
        }
    }

    pub fn add_binding(&mut self, binding: E::Binding) -> E::LocalId {
        let id = self.num_locals.inc();
        self.bindings.push(binding);
        id
    }

    pub fn to_expr(self, ret: E::LocalId) -> E {
        debug_assert!(ret.to_index() < self.num_locals.to_value());
        E::from_bindings(self.bindings, ret)
    }

    pub fn child(&self) -> LetManyBuilder<E> {
        LetManyBuilder::new(self.num_locals)
    }
}
