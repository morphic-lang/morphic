use id_collections::{Count, Id};

pub trait FromBindings: Sized {
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

pub trait BuildMatch: FromBindings {
    type VariantId: Id;
    type Type: Clone;

    fn bool_type() -> Self::Type;

    fn build_binding(
        builder: &mut LetManyBuilder<Self>,
        ty: Self::Type,
        expr: Self,
    ) -> Self::LocalId;

    fn build_if(cond: Self::LocalId, then_expr: Self, else_expr: Self) -> Self;
    fn build_unwrap_variant(variant: Self::VariantId, local: Self::LocalId) -> Self;
    fn build_check_variant(variant: Self::VariantId, local: Self::LocalId) -> Self;
    fn build_unreachable(ty: Self::Type) -> Self;

    /// Builds a series of nested if expressions to simulate matching on a sum
    /// type. Returns `unreachable` if no match is found.
    fn build_match<I, F>(
        builder: &mut LetManyBuilder<Self>,
        local: Self::LocalId,
        mut variants: I,
        ret_ty: &Self::Type,
        mut build_case: F,
    ) -> Self
    where
        I: Iterator<Item = (Self::VariantId, Self::Type)>,
        F: FnMut(&mut LetManyBuilder<Self>, Self::VariantId, Self::LocalId) -> Self::LocalId,
    {
        if let Some((variant_id, variant_ty)) = variants.next() {
            let cond = Self::build_binding(
                builder,
                Self::bool_type(),
                Self::build_check_variant(variant_id, local),
            );

            let mut then_builder = builder.child();
            let unwrapped = Self::build_binding(
                &mut then_builder,
                variant_ty,
                Self::build_unwrap_variant(variant_id, local),
            );

            let then_result = build_case(&mut then_builder, variant_id, unwrapped);
            let then_case = then_builder.to_expr(then_result);

            let mut else_builder = builder.child();
            let else_case =
                Self::build_match(&mut else_builder, local, variants, ret_ty, build_case);

            Self::build_if(cond, then_case, else_case)
        } else {
            Self::build_unreachable(ret_ty.clone())
        }
    }
}
