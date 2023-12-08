use crate::data::first_order_ast as first_ord;
use crate::data::mutation_annot_ast as mutation;
use crate::data::profile as prof;
use crate::data::rc_specialized_ast as rc;
use crate::data::repr_unified_ast as unif;
use crate::data::resolved_ast as res;
use crate::util::disjunction::Disj;
use id_collections::IdVec;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RepChoice {
    OptimizedMut,
    FallbackImmut,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
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
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<first_ord::CustomTypeId, unif::TypeDef>,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<rc::CustomFuncId, unif::FuncDef>,
    pub func_symbols: IdVec<rc::CustomFuncId, first_ord::FuncSymbols>,
    pub rep_constraints: IdVec<rc::CustomFuncId, FuncRepConstraints>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: rc::CustomFuncId,
}
