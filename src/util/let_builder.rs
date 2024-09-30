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

fn build_match_helper<E: BuildMatch, I, F>(
    builder: &mut LetManyBuilder<E>,
    local: E::LocalId,
    variant_id: E::VariantId,
    variant_ty: E::Type,
    variants: I,
    ret_ty: &E::Type,
    mut build_case: F,
) -> E::LocalId
where
    I: Iterator<Item = (E::VariantId, E::Type)>,
    F: FnMut(&mut LetManyBuilder<E>, E::VariantId, E::LocalId) -> E::LocalId,
{
    let cond = E::build_binding(
        builder,
        E::bool_type(),
        E::build_check_variant(variant_id, local),
    );

    let mut then_builder = builder.child();
    let unwrapped = E::build_binding(
        &mut then_builder,
        variant_ty,
        E::build_unwrap_variant(variant_id, local),
    );
    let then_result = build_case(&mut then_builder, variant_id, unwrapped);
    let then_case = then_builder.to_expr(then_result);

    let else_builder = builder.child();
    let else_case = build_nested_match(else_builder, local, variants, ret_ty, build_case);

    let if_ = E::build_if(cond, then_case, else_case);
    E::build_binding(builder, ret_ty.clone(), if_)
}

fn build_nested_match<E: BuildMatch, I, F>(
    mut builder: LetManyBuilder<E>,
    local: E::LocalId,
    mut variants: I,
    ret_ty: &E::Type,
    build_case: F,
) -> E
where
    I: Iterator<Item = (E::VariantId, E::Type)>,
    F: FnMut(&mut LetManyBuilder<E>, E::VariantId, E::LocalId) -> E::LocalId,
{
    if let Some((variant_id, variant_ty)) = variants.next() {
        let result = build_match_helper(
            &mut builder,
            local,
            variant_id,
            variant_ty,
            variants,
            ret_ty,
            build_case,
        );

        // Unlike at the top level, the 'if' we built is the return value of the scope
        builder.to_expr(result)
    } else {
        E::build_unreachable(ret_ty.clone())
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

    /// Builds a series of nested 'if' expressions to simulate matching on a sum.
    fn build_match<I, F>(
        builder: &mut LetManyBuilder<Self>,
        local: Self::LocalId,
        mut variants: I,
        ret_ty: &Self::Type,
        build_case: F,
    ) -> Self::LocalId
    where
        I: Iterator<Item = (Self::VariantId, Self::Type)>,
        F: FnMut(&mut LetManyBuilder<Self>, Self::VariantId, Self::LocalId) -> Self::LocalId,
    {
        if let Some((variant_id, variant_ty)) = variants.next() {
            build_match_helper(
                builder, local, variant_id, variant_ty, variants, ret_ty, build_case,
            )
        } else {
            Self::build_binding(
                builder,
                ret_ty.clone(),
                Self::build_unreachable(ret_ty.clone()),
            )
        }
    }
}
