use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RepParamId(pub usize);

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub num_params: usize,
    pub variants: Vec<Option<Type<RepParamId>>>,
}

#[derive(Clone, Debug)]
pub enum Type<Rep> {
    Bool,
    Int,
    Float,
    Text,
    Array(Box<Type<Rep>>),
    Tuple(Vec<Type<Rep>>),
    Func(Purity, Rep, Box<Type<Rep>>, Box<Type<Rep>>),
    Custom(mono::CustomTypeId, Vec<Rep>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TemplateId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InCycle {
    NoCycle,
    Cycle,
}

#[derive(Clone, Debug)]
pub struct Template {
    pub in_cycle: InCycle,
    pub num_params: usize,
    pub requirements: Vec<Requirement>,
}

#[derive(Clone, Debug)]
pub enum Requirement {
    Lam(lifted::LamId, Vec<Solution>),
    Template(TemplateId, Vec<Solution>),
    ArithOp(Op),
    ArrayOp(ArrayOp, Type<Solution>),
    ArrayReplace(Type<Solution>),
    Ctor(mono::CustomTypeId, Vec<Solution>, res::VariantId),
}

#[derive(Clone, Debug)]
pub enum Solution {
    Param(RepParamId),
    MinSolutionTo(TemplateId, Vec<RepParamId>),
}

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(
        Op,
        Solution, // Representation of this function expression
    ),
    ArrayOp(
        ArrayOp,
        Type<Solution>,
        Solution, // Representation of this function expression
    ),
    NullaryCtor(mono::CustomTypeId, Vec<Solution>, res::VariantId),
    Ctor(
        mono::CustomTypeId,
        Vec<Solution>,
        res::VariantId,
        Solution, // Representation of this function expressionn
    ),
    Global(mono::CustomGlobalId, Vec<Solution>),
    Local(lifted::LocalId),
    Capture(lifted::CaptureId),
    Tuple(Vec<Expr>),
    Lam(
        lifted::LamId,
        Vec<Solution>, // Parameters on the lambda
        Solution,      // Representation of the lambda expression
        Vec<Expr>,     // Captures
    ),
    App(
        Purity,
        Solution, // Representation being called
        Box<Expr>,
        Box<Expr>,
    ),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, Type<Solution>),
    Let(Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(
        Type<Solution>, // Item type
        Vec<Expr>,
    ),
    BoolLit(bool),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any(Type<Solution>),
    Var(Type<Solution>),
    Tuple(Vec<Pattern>),
    Ctor(
        mono::CustomTypeId,
        Vec<Solution>,
        res::VariantId,
        Option<Box<Pattern>>,
    ),
    BoolConst(bool),
    IntConst(i64),
    FloatConst(f64),
    TextConst(String),
}

#[derive(Clone, Debug)]
pub struct Params {
    // Indexed by RepParamId
    // Number of parameters is implicit in the length of this vector
    pub requirements: Vec<(TemplateId, Vec<RepParamId>)>,
}

impl Params {
    pub fn num_params(&self) -> usize {
        self.requirements.len()
    }
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub params: Params,
    pub type_: Type<RepParamId>,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct LamDef {
    pub purity: Purity,
    pub params: Params,
    pub captures: Vec<Type<RepParamId>>,
    pub arg: Type<RepParamId>,
    pub ret: Type<RepParamId>,
    pub arg_pat: Pattern,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: Vec<TypeDef>,
    pub templates: Vec<Template>,
    pub vals: Vec<ValDef>,
    pub lams: Vec<LamDef>,
    pub main: mono::CustomGlobalId,
}
