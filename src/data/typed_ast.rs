use crate::data::resolved_ast as res;

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: Vec<res::TypeDef>,
    pub vals: Vec<ValDef>,
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
    Lam(res::Pattern, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(res::Pattern, Expr)>),
    Let(res::Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(Vec<Expr>),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),
}
