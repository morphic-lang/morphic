use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::IdVec;

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<res::CustomTypeId, res::TypeDef>,
    pub custom_type_symbols: IdVec<res::CustomTypeId, res::TypeSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub vals: IdVec<res::CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<res::CustomGlobalId, res::ValSymbols>,
    pub main: res::CustomGlobalId,
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: res::TypeScheme,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Global(res::GlobalId, IdVec<res::TypeParamId, res::Type>),
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
