#[derive(Clone, Debug)]
pub struct TypeName(pub String);

#[derive(Clone, Debug)]
pub struct CtorName(pub String);

#[derive(Clone, Debug)]
pub struct TypeParam(pub String);

#[derive(Clone, Debug)]
pub struct ValName(pub String);

#[derive(Clone, Debug)]
pub struct Program(pub Vec<Item>);

#[derive(Clone, Debug)]
pub enum Item {
    TypeDef(TypeName, Vec<TypeParam>, Vec<(CtorName, Type)>),
    ValDef(ValName, Type, Expr),
}

#[derive(Clone, Debug)]
pub enum Type {
    Var(TypeParam),
    App(TypeName, Vec<Type>),
    Tuple(Vec<Type>),
    Func(Box<Type>, Box<Type>),
}

#[derive(Clone, Debug)]
pub enum Expr {
    Var(ValName),
    Op(Op),
    Ctor(CtorName),
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
pub enum Op {
    AddInt,
    SubInt,
    MulInt,
    DivInt,
    NegInt,

    EqInt,
    LtInt,
    LteInt,

    AddFloat,
    SubFloat,
    MulFloat,
    DivFloat,
    NegFloat,

    EqFloat,
    LtFloat,
    LteFloat,
}

pub fn binop(op: Op, left: Expr, right: Expr) -> Expr {
    Expr::App(
        Box::new(Expr::Op(op)),
        Box::new(Expr::Tuple(vec![left, right])),
    )
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any,
    Var(ValName),
    Tuple(Vec<Pattern>),
    Ctor(CtorName, Box<Pattern>),

    IntConst(i64),
    FloatConst(f64),
    TextConst(String),
}
