use crate::data::purity::Purity;
use crate::data::resolved_ast as res;

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: Vec<res::TypeDef>,
    pub vals: Vec<ValDef>,
    pub main: res::CustomGlobalId,
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: res::TypeScheme,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Global(res::GlobalId, Vec<res::Type>),
    Local(res::LocalId),
    Tuple(Vec<Expr>),
    Lam(
        Purity,
        Pattern,
        res::Type, // Return type
        Box<Expr>,
    ),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    Let(Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(res::Type, Vec<Expr>),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),
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
    IntConst(i64),
    FloatConst(f64),
    TextConst(String),
}
