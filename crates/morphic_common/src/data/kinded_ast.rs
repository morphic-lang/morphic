use crate::data::profile as prof;
use crate::data::resolved_ast as res;
use id_collections::IdVec;

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
    pub main: res::CustomGlobalId,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub param_kinds: IdVec<res::TypeParamId, Kind>,
    pub variants: IdVec<res::VariantId, Option<res::Type>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeScheme {
    pub param_kinds: IdVec<res::TypeParamId, Kind>,
    pub body: res::Type,
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: TypeScheme,
    pub body: res::Expr,
}
