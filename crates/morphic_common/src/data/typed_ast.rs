use crate::data::elaborated_ast as elab;
use crate::data::num_type::NumLit;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::{id_type, IdVec};
use std::collections::BTreeSet;

/// The program after type inference.  Every reference to a constrained global, and every
/// occurrence of a constrained type in a body, carries obligations: trait constraints over the
/// definition's type parameters that the trait solver has yet to discharge, except where
/// unification already determined their evidence.
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
    pub impl_scope: IdVec<res::ModId, BTreeSet<res::ImplId>>,
    pub main: res::CustomGlobalId,
}

#[id_type]
pub struct ObligationId(pub usize);

/// A trait constraint that some part of a definition's body requires to hold over the
/// definition's type parameters.  The evidence inside its goal is other obligations of the same
/// definition.
#[derive(Clone, Debug)]
pub struct Obligation {
    pub goal: elab::TraitApp<ObligationId>,
    /// The innermost expression enclosing where the obligation arose, or the whole definition
    /// for an obligation instantiated from its own signature.
    pub span: (usize, usize),
    pub origin: Origin,
    pub evidence: Evidence,
}

/// Where an obligation arose, for explaining its evidence in error messages.
#[derive(Clone, Debug)]
pub enum Origin {
    /// One of the enclosing definition's own trait constraints.
    OwnConstr(res::TraitConstrId),
    /// A trait constraint of the scheme of a referenced global.
    GlobalConstr(res::GlobalId, res::TraitConstrId),
    /// The trait's own constraint, at a reference to one of its funcs.
    TraitFuncTrait(res::TraitId, res::TraitFuncId),
    /// One of a trait func's own constraints, at a reference to it.
    TraitFuncConstr(res::TraitId, res::TraitFuncId, res::TraitFuncConstrId),
    /// Evidence that a type in a signature carries, at a reference to what the signature
    /// declares.
    Carried(Signature),
    /// A constraint of a constrained type written in the body.
    Annotation(res::CustomTypeId, res::TraitConstrId),
    /// A constraint of a constrained type whose constructor a pattern matches.
    Pattern(res::CustomTypeId, res::TraitConstrId),
}

/// A signature whose types carry evidence.
#[derive(Clone, Copy, Debug)]
pub enum Signature {
    /// The enclosing definition's own.
    Own,
    Global(res::GlobalId),
    TraitFunc(res::TraitId, res::TraitFuncId),
    /// A type declaration, whose variants and constraints carry evidence.
    TypeDecl(res::CustomTypeId),
}

/// What inference determined about an obligation's evidence, by unifying the evidence of
/// constrained types.  Everything undetermined is solved afterwards in the definition's scope.
#[derive(Clone, Debug)]
pub enum Evidence {
    Unknown,
    /// One of the enclosing definition's own trait constraints.
    Given(res::TraitConstrId),
    Impl(
        res::ImplId,
        IdVec<res::TypeParamId, elab::Type<ObligationId>>,
        IdVec<res::TraitConstrId, ObligationId>,
    ),
    Super(ObligationId, res::SuperId),
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: elab::TypeScheme,
    pub body: Expr,
    pub obligations: IdVec<ObligationId, Obligation>,
    /// Pairs of obligations whose evidence unification required to be equal but did not
    /// identify: either the two sides already differ, or at least one is a superclass
    /// projection, which inference cannot compare.  Projection is not injective (two `Ord I64`
    /// impls may share their `Eq I64` superclass evidence), so whether such sides agree is only
    /// known once trait solving has resolved both to derivations.  The body solver checks each
    /// equation then and reports a conflict that explains, through the origins of the
    /// obligations, where each side's evidence came from.  Nothing in inference depends on the
    /// answer: the two obligations belong to types that already unified, so their goals agree,
    /// and the equation cannot determine the evidence a projection is taken from.
    pub evidence_equations: Vec<(ObligationId, ObligationId)>,
}

/// A type in a body: its evidence is obligations of the definition.
pub type Type = elab::Type<ObligationId>;

#[derive(Clone, Debug)]
pub enum Expr {
    Global(
        res::GlobalId,
        IdVec<res::TypeParamId, Type>,
        IdVec<res::TraitConstrId, ObligationId>,
    ),
    TraitFunc(
        res::TraitId,
        res::TraitFuncId,
        elab::TraitFuncInst<ObligationId>,
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
