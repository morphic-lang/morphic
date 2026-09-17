use crate::data::profile as prof;
use crate::data::resolved_ast as res;
use id_collections::IdVec;
use std::collections::BTreeSet;

/// `Kind(vec![])`, rendered `Type`, is the kind of ordinary types, and `Kind(vec![Kind::TYPE])`,
/// rendered `Type -> Type`, is the kind of a constructor taking one ordinary type, such as `Array`.
/// Kinds are simple: there is no kind polymorphism, and a constructor always ultimately produces
/// an ordinary type.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Kind(pub Vec<Kind>);

impl Kind {
    /// The kind of ordinary types.
    pub const TYPE: Kind = Kind(Vec::new());

    pub fn is_type(&self) -> bool {
        self.0.is_empty()
    }
}

/// The resolved program after kind inference.  It differs from `res::Program` only in that every
/// parameter list records the kinds of its parameters.
#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<res::CustomTypeId, TypeDef>,
    pub custom_type_symbols: IdVec<res::CustomTypeId, res::TypeSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub vals: IdVec<res::CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<res::CustomGlobalId, res::ValSymbols>,
    pub traits: IdVec<res::CustomTraitId, TraitDef>,
    pub trait_symbols: IdVec<res::CustomTraitId, res::TraitSymbols>,
    pub impls: IdVec<res::CustomImplId, ImplDef>,
    pub impl_symbols: IdVec<res::CustomImplId, res::ImplSymbols>,
    pub impl_scope: IdVec<res::ModId, BTreeSet<res::ImplId>>,
    pub main: res::CustomGlobalId,
}

#[derive(Clone, Debug)]
pub struct TraitDef {
    pub param_kinds: IdVec<res::TypeParamId, Kind>,
    pub supers: IdVec<res::SuperId, res::TraitApp>,
    pub funcs: IdVec<res::TraitFuncId, TraitFuncSig>,
}

impl TraitDef {
    pub fn func_layout(&self, func: res::TraitFuncId) -> res::TraitFuncLayout {
        res::TraitFuncLayout {
            num_trait_params: self.param_kinds.count(),
            num_own_params: self.funcs[func].own_param_kinds.count(),
        }
    }
}

/// See `res::TraitFuncSig`.
#[derive(Clone, Debug)]
pub struct TraitFuncSig {
    pub own_param_kinds: IdVec<res::TraitFuncParamId, Kind>,
    pub own_constrs: IdVec<res::TraitFuncConstrId, res::TraitApp>,
    pub body: res::Type,
}

#[derive(Clone, Debug)]
pub struct ImplDef {
    pub trait_: res::TraitId,
    pub param_kinds: IdVec<res::TypeParamId, Kind>,
    pub head: Vec<res::Type>,
    pub trait_constrs: IdVec<res::TraitConstrId, res::TraitApp>,
    pub funcs: IdVec<res::TraitFuncId, res::CustomGlobalId>,
}

impl ImplDef {
    pub fn func_layout(&self) -> res::ImplFuncLayout {
        res::ImplFuncLayout {
            num_impl_params: self.param_kinds.count(),
            num_impl_constrs: self.trait_constrs.count(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub param_kinds: IdVec<res::TypeParamId, Kind>,
    pub variants: IdVec<res::VariantId, Option<res::Type>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeScheme {
    pub param_kinds: IdVec<res::TypeParamId, Kind>,
    pub trait_constrs: IdVec<res::TraitConstrId, res::TraitApp>,
    pub body: res::Type,
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: TypeScheme,
    pub body: res::Expr,
}
