use crate::data::elaborated_ast as elab;
use crate::data::num_type::NumLit;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::IdVec;

/// The program after trait solving.  It differs from the typed program in that every obligation
/// has been replaced by its derivation.
#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<res::CustomTypeId, elab::TypeDef>,
    pub custom_type_symbols: IdVec<res::CustomTypeId, res::TypeSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub vals: IdVec<res::CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<res::CustomGlobalId, res::ValSymbols>,
    pub traits: IdVec<res::CustomTraitId, elab::TraitDef>,
    pub trait_symbols: IdVec<res::CustomTraitId, res::TraitSymbols>,
    pub impls: IdVec<res::CustomImplId, elab::ImplDef>,
    pub impl_symbols: IdVec<res::CustomImplId, res::ImplSymbols>,
    pub main: res::CustomGlobalId,
}

/// Evidence that a trait constraint holds, relative to the enclosing definition's own trait
/// constraints.
pub type Derivation = elab::Derivation;

pub type Type = elab::Type;

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: elab::TypeScheme,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Global(
        res::GlobalId,
        IdVec<res::TypeParamId, Type>,
        IdVec<res::TraitConstrId, Derivation>,
    ),
    TraitFunc(
        res::TraitId,
        res::TraitFuncId,
        elab::TraitFuncInst<Derivation>,
    ),
    Local(res::LocalId),
    Tuple(Vec<Expr>),
    Lam(
        Purity,
        Type, // Argument type
        Type, // Return type
        Pattern,
        Box<Expr>,
        Option<prof::ProfilePointId>,
    ),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, Type),
    LetMany(Vec<(Pattern, Expr)>, Box<Expr>),

    ArrayLit(Type, Vec<Expr>),
    NumLit(NumLit),

    Span(usize, usize, Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any(Type),
    Var(Type),
    Tuple(Vec<Pattern>),
    Ctor(res::TypeId, Vec<Type>, res::VariantId, Option<Box<Pattern>>),
    NumConst(NumLit),

    Span(usize, usize, Box<Pattern>),
}
