use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RepVarId(pub usize);

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub num_params: usize,
    pub variants: Vec<Option<Type>>,
}

#[derive(Clone, Debug)]
pub enum Type {
    Bool,
    Int,
    Float,
    Text,
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Func(Purity, RepVarId, Box<Type>, Box<Type>),
    Custom(mono::CustomTypeId, Vec<RepVarId>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AliasId(pub usize);

#[derive(Clone, Debug)]
pub enum Requirement {
    Lam(lifted::LamId, Vec<RepVarId>),
    Alias(AliasId, Vec<RepVarId>),
    ArithOp(Op),
    ArrayOp(ArrayOp, Type),
    ArrayReplace(Type),
    Ctor(mono::CustomTypeId, Vec<RepVarId>, res::VariantId),
}

#[derive(Clone, Debug)]
pub struct Alias {
    pub num_params: usize,
    // Invariant: each internal var's requirements are expressed entirely in terms of external vars.
    pub internal_vars: Vec<Vec<Requirement>>,
    pub reqs: Vec<Requirement>,
}

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(Op),
    ArrayOp(ArrayOp, Type),
    Ctor(mono::CustomTypeId, Vec<RepVarId>, res::VariantId),
    Global(mono::CustomGlobalId, Vec<RepVarId>),
    Local(lifted::LocalId),
    Capture(lifted::CaptureId),
    Tuple(Vec<Expr>),
    Lam(
        lifted::LamId,
        Vec<RepVarId>, // Parameters on the lambda
        RepVarId,      // Representation of the lambda expression
        Vec<Expr>,     // Captures
    ),
    App(
        Purity,
        RepVarId, // Representation being called
        Box<Expr>,
        Box<Expr>,
    ),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, Type),
    Let(Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(
        Type, // Item type
        Vec<Expr>,
    ),
    BoolLit(bool),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any(Type),
    Var(Type),
    Tuple(Vec<Pattern>),
    Ctor(
        mono::CustomTypeId,
        Vec<RepVarId>,
        res::VariantId,
        Option<Box<Pattern>>,
    ),
    BoolConst(bool),
    IntConst(i64),
    FloatConst(f64),
    TextConst(String),
}

#[derive(Clone, Debug)]
pub struct TypeScheme {
    pub params: Vec<Vec<Requirement>>,
    // Invariant: mentions only external vars (vars with id < params.len())
    pub body: Type,
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub type_: TypeScheme,
    // Invariant: each internal var's requirements are expressed entirely in terms of external vars.
    pub internal_vars: Vec<Vec<Requirement>>,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct LamDef {
    pub purity: Purity,
    pub params: Vec<Vec<Requirement>>,
    // Invariant: mentions only external vars (vars with id < num_params)
    pub captures: Vec<Type>,
    // Same as above
    pub arg: Type,
    // Same as above
    pub ret: Type,
    // Invariant: each internal var's requirements are expressed entirely in terms of external vars.
    pub internal_vars: Vec<Vec<Requirement>>,
    pub arg_pat: Pattern,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: Vec<TypeDef>,
    pub vals: Vec<ValDef>,
    pub lams: Vec<LamDef>,
    pub aliases: Vec<Alias>,
    pub main: mono::CustomGlobalId,
}
