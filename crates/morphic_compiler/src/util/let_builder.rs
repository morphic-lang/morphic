use crate::data::metadata::Metadata;
use id_collections::{Count, Id};

pub trait FromBindings: Sized {
    type LocalId: Id;
    type Type: Clone;

    fn from_bindings(bindings: Vec<(Self::Type, Self, Metadata)>, ret: Self::LocalId) -> Self;
}

#[derive(Clone, Debug)]
pub struct LetManyBuilder<E: FromBindings> {
    num_locals: Count<E::LocalId>,
    bindings: Vec<(E::Type, E, Metadata)>,
}

impl<E: FromBindings> LetManyBuilder<E> {
    pub fn new(num_locals: Count<E::LocalId>) -> Self {
        LetManyBuilder {
            num_locals,
            bindings: Vec::new(),
        }
    }

    pub fn add_binding(&mut self, ty: E::Type, expr: E) -> E::LocalId {
        self.add_binding_with_metadata(ty, expr, Metadata::default())
    }

    pub fn add_binding_with_metadata(
        &mut self,
        ty: E::Type,
        expr: E,
        metadata: Metadata,
    ) -> E::LocalId {
        let id = self.num_locals.inc();
        self.bindings.push((ty, expr, metadata));
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

fn build_match_helper<E: BuildMatch, I, D, C>(
    builder: &mut LetManyBuilder<E>,
    discrim: E::LocalId,
    variant_id: E::VariantId,
    variant_ty: E::Type,
    variants: I,
    ret_ty: &E::Type,
    build_default: D,
    mut build_case: C,
) -> E::LocalId
where
    I: Iterator<Item = (E::VariantId, E::Type)>,
    D: Fn() -> E,
    C: FnMut(&mut LetManyBuilder<E>, E::VariantId, E::LocalId) -> E::LocalId,
{
    let cond = E::build_binding(
        builder,
        E::bool_type(),
        E::build_check_variant(variant_id, discrim),
    );

    let mut then_builder = builder.child();
    let unwrapped = E::build_binding(
        &mut then_builder,
        variant_ty,
        E::build_unwrap_variant(variant_id, discrim),
    );
    let then_result = build_case(&mut then_builder, variant_id, unwrapped);
    let then_case = then_builder.to_expr(then_result);

    let else_builder = builder.child();
    let else_case = build_nested_match(
        else_builder,
        discrim,
        variants,
        ret_ty,
        build_default,
        build_case,
    );

    let if_ = E::build_if(cond, then_case, else_case);
    E::build_binding(builder, ret_ty.clone(), if_)
}

fn build_nested_match<E: BuildMatch, I, D, C>(
    mut builder: LetManyBuilder<E>,
    discrim: E::LocalId,
    mut variants: I,
    ret_ty: &E::Type,
    build_default: D,
    build_case: C,
) -> E
where
    I: Iterator<Item = (E::VariantId, E::Type)>,
    D: Fn() -> E,
    C: FnMut(&mut LetManyBuilder<E>, E::VariantId, E::LocalId) -> E::LocalId,
{
    if let Some((variant_id, variant_ty)) = variants.next() {
        let result = build_match_helper(
            &mut builder,
            discrim,
            variant_id,
            variant_ty,
            variants,
            ret_ty,
            build_default,
            build_case,
        );

        // Unlike at the top level, the 'if' we built is the return value of the scope
        builder.to_expr(result)
    } else {
        build_default()
    }
}

pub trait BuildMatch: FromBindings {
    type VariantId: Id;

    fn bool_type() -> Self::Type;
    fn build_binding(
        builder: &mut LetManyBuilder<Self>,
        ty: Self::Type,
        expr: Self,
    ) -> Self::LocalId;
    fn build_if(cond: Self::LocalId, then_expr: Self, else_expr: Self) -> Self;
    fn build_unwrap_variant(variant: Self::VariantId, local: Self::LocalId) -> Self;
    fn build_check_variant(variant: Self::VariantId, local: Self::LocalId) -> Self;

    /// Builds a series of nested 'if' expressions to simulate matching on a sum.
    fn build_match<I, D, C>(
        builder: &mut LetManyBuilder<Self>,
        discrim: Self::LocalId,
        mut variants: I,
        ret_ty: &Self::Type,
        build_default: D,
        build_case: C,
    ) -> Self::LocalId
    where
        I: Iterator<Item = (Self::VariantId, Self::Type)>,
        D: Fn() -> Self,
        C: FnMut(&mut LetManyBuilder<Self>, Self::VariantId, Self::LocalId) -> Self::LocalId,
    {
        if let Some((variant_id, variant_ty)) = variants.next() {
            build_match_helper(
                builder,
                discrim,
                variant_id,
                variant_ty,
                variants,
                ret_ty,
                build_default,
                build_case,
            )
        } else {
            Self::build_binding(builder, ret_ty.clone(), build_default())
        }
    }
}
