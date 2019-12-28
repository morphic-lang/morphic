use crate::data::first_order_ast as first_ord;
use crate::data::mutation_annot_ast as mutation;
use crate::data::repr_unified_ast as unif;
use crate::util::disjunction::Disj;
use crate::util::id_vec::IdVec;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RepChoice {
    OptimizedMut,
    FallbackImmut,
}

#[derive(Clone, Debug)]
pub struct ParamConstraints {
    pub fallback_immut_if: Disj<mutation::MutationCondition>,
}

#[derive(Clone, Debug)]
pub struct FuncRepConstraints {
    pub param_constraints: IdVec<unif::RepParamId, ParamConstraints>,
    pub internal_vars: IdVec<unif::InternalRepVarId, RepChoice>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<first_ord::CustomTypeId, unif::TypeDef>,
    pub funcs: IdVec<first_ord::CustomFuncId, unif::FuncDef>,
    pub rep_constraints: IdVec<first_ord::CustomFuncId, FuncRepConstraints>,
    pub main: first_ord::CustomFuncId,
}
