#[derive(Clone, Debug)]
pub struct TypeName(String);

#[derive(Clone, Debug)]
pub struct CtorName(String);

#[derive(Clone, Debug)]
pub struct TypeParam(String);

#[derive(Clone, Debug)]
pub struct ValName(String);

#[derive(Clone, Debug)]
pub enum Item {
    TypeDef(TypeName, Vec<TypeParam>, Vec<(CtorName, Vec<Type>)>),
    ValDef(ValName, Expr),
}

#[derive(Clone, Debug)]
pub enum Type {
    Var(TypeParam),
    App(TypeName, Vec<Type>),
    Tuple(Vec<Type>),
    Func(Box<Type>, Box<Type>),

    Array(Box<Type>),
    Int,
    Float,
    Text,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Var(ValName),
    Tuple(Vec<Expr>),
    Lam(Pattern, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    Let(Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(Vec<Expr>),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any,
    Var(ValName),
    Tuple(Vec<Pattern>),
    Ctor(CtorName, Vec<Pattern>),

    IntConst(i64),
    FloatConst(i64),
    TextConst(String),
}
