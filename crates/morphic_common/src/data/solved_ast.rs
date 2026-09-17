use crate::data::kinded_ast as kinded;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::IdVec;

/// The program after trait solving.  It differs from the typed program in that every obligation
/// has been replaced by its derivation, and every impl records the derivations of its trait's
/// superclasses.
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
    pub impls: IdVec<res::CustomImplId, ImplDef>,
    pub impl_symbols: IdVec<res::CustomImplId, res::ImplSymbols>,
    pub main: res::CustomGlobalId,
}

/// Evidence that a trait constraint holds, relative to the trait constraints ("givens") of the
/// enclosing definition or impl.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Derivation {
    /// The constraint is one of the enclosing scheme's own trait constraints.
    Given(res::TraitConstrId),
    /// The constraint is discharged by an impl, instantiated at the given type arguments, whose
    /// own constraints are discharged by the sub-derivations.
    Impl(
        res::ImplId,
        IdVec<res::TypeParamId, res::Type>,
        IdVec<res::TraitConstrId, Derivation>,
    ),
    /// The constraint is a superclass of the trait of the inner derivation.
    Super(Box<Derivation>, res::SuperId),
}

#[derive(Clone, Debug)]
pub struct ImplDef {
    pub trait_: res::TraitId,
    pub param_kinds: IdVec<res::TypeParamId, kinded::Kind>,
    pub head: Vec<res::Type>,
    pub trait_constrs: IdVec<res::TraitConstrId, res::TraitApp>,
    /// A derivation of each superclass of the trait for the head, relative to the impl's own
    /// trait constraints.
    pub supers: IdVec<res::SuperId, Derivation>,
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
pub struct ValDef {
    pub scheme: kinded::TypeScheme,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Global(
        res::GlobalId,
        IdVec<res::TypeParamId, res::Type>,
        IdVec<res::TraitConstrId, Derivation>,
    ),
    TraitFunc(
        res::TraitId,
        res::TraitFuncId,
        res::TraitFuncInst<Derivation>,
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
