use crate::data::kinded_ast as kinded;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::{id_type, IdVec};
use std::collections::BTreeSet;

/// The program after type inference.  Every reference to a constrained global carries one
/// obligation per trait constraint of the global's scheme, instantiated at the reference's type
/// arguments. Discharging them will be the job of the trait solver.
#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<res::CustomTypeId, kinded::TypeDef>,
    pub custom_type_symbols: IdVec<res::CustomTypeId, res::TypeSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub vals: IdVec<res::CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<res::CustomGlobalId, res::ValSymbols>,
    pub traits: IdVec<res::CustomTraitId, kinded::TraitDef>,
    pub trait_symbols: IdVec<res::CustomTraitId, res::TraitSymbols>,
    pub impls: IdVec<res::CustomImplId, kinded::ImplDef>,
    pub impl_symbols: IdVec<res::CustomImplId, res::ImplSymbols>,
    pub impl_scope: IdVec<res::ModId, BTreeSet<res::ImplId>>,
    pub main: res::CustomGlobalId,
}

#[id_type]
pub struct ObligationId(pub usize);

/// A trait constraint that some reference in a definition's body requires to hold over the
/// definition's type parameters.
#[derive(Clone, Debug)]
pub struct Obligation {
    pub trait_constr: res::TraitApp,
    pub span: Option<(usize, usize)>,
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: kinded::TypeScheme,
    pub body: Expr,
    pub obligations: IdVec<ObligationId, Obligation>,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Global(
        res::GlobalId,
        IdVec<res::TypeParamId, res::Type>,
        IdVec<res::TraitConstrId, ObligationId>,
    ),
    TraitFunc(
        res::TraitId,
        res::TraitFuncId,
        res::TraitFuncInst<ObligationId>,
    ),
    Local(res::LocalId),
    Tuple(Vec<Expr>),
    Lam(
        Purity,
        res::Type, // Argument type
        res::Type, // Return type
        Pattern,
        Box<Expr>,
        Option<prof::ProfilePointId>,
    ),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, res::Type),
    LetMany(Vec<(Pattern, Expr)>, Box<Expr>),

    ArrayLit(res::Type, Vec<Expr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),

    Span(usize, usize, Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any(res::Type),
    Var(res::Type),
    Tuple(Vec<Pattern>),
    Ctor(
        res::TypeId,
        Vec<res::Type>,
        res::VariantId,
        Option<Box<Pattern>>,
    ),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),

    Span(usize, usize, Box<Pattern>),
}
