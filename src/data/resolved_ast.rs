use crate::data::raw_ast::Op;

#[derive(Clone, Debug)]
pub struct TypeId(pub usize);

#[derive(Clone, Debug)]
pub struct VariantId(pub usize);

#[derive(Clone, Debug)]
pub struct TypeParamId(pub usize);

#[derive(Clone, Debug)]
pub struct GlobalId(pub usize);

#[derive(Clone, Debug)]
pub struct LocalId(pub usize);

#[derive(Clone, Debug)]
pub struct Program {
    types: Vec<TypeDef>,
    vals: Vec<ValDef>,
}

#[derive(Clone, Debug)]
pub enum TypeDef {
    Int,
    Float,
    Text,
    Array,
    Custom {
        num_params: usize,
        variants: Vec<Type>,
    },
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Item,
    Len,
    Push,
    Pop,
}

#[derive(Clone, Debug)]
pub enum ValDef {
    ArithOp(Op),
    ArrayOp(Op),
    Ctor {
        type_: TypeId,
        variant: VariantId,
    },
    Custom {
        scheme_params: usize,
        scheme: Type,
        body: Expr,
    },
}

#[derive(Clone, Debug)]
pub enum Type {
    Var(TypeParamId),
    App(TypeId, Vec<Type>),
    Tuple(Vec<Type>),
    Func(Box<Type>, Box<Type>),
}

#[derive(Clone, Debug)]
pub struct TypeScheme {
    num_params: usize,
    body: Type,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Global(GlobalId),
    Local(LocalId),
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
pub struct Pattern {
    num_vars: usize,
    body: PatternBody,
}

#[derive(Clone, Debug)]
pub enum PatternBody {
    Any,
    Var,
    Tuple(Vec<Pattern>),
    Ctor(TypeId, VariantId, Box<Pattern>),
    IntConst(i64),
    FloatConst(f64),
    TextConst(String),
}
