use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp, IOOp};
use crate::util::id_vec::IdVec;

id_type!(pub RepParamId);

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub num_params: usize,
    pub variants: IdVec<res::VariantId, Option<Type<RepParamId>>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type<Rep> {
    Bool,
    Byte,
    Int,
    Float,
    Array(Box<Type<Rep>>),
    Tuple(Vec<Type<Rep>>),
    Func(Purity, Rep, Box<Type<Rep>>, Box<Type<Rep>>),
    Custom(mono::CustomTypeId, IdVec<RepParamId, Rep>),
}

id_type!(pub TemplateId);

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
    Lam(lifted::LamId, IdVec<RepParamId, Solution>),
    Template(TemplateId, IdVec<RepParamId, Solution>),
    ArithOp(Op),
    ArrayOp(ArrayOp, Type<Solution>),
    ArrayReplace(Type<Solution>),
    IOOp(IOOp),
    Ctor(
        mono::CustomTypeId,
        IdVec<RepParamId, Solution>,
        res::VariantId,
    ),
}

#[derive(Clone, Debug)]
pub enum Solution {
    Param(RepParamId),
    MinSolutionTo(TemplateId, IdVec<RepParamId, RepParamId>),
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
    IOOp(IOOp, Solution),
    NullaryCtor(
        mono::CustomTypeId,
        IdVec<RepParamId, Solution>,
        res::VariantId,
    ),
    Ctor(
        mono::CustomTypeId,
        IdVec<RepParamId, Solution>,
        res::VariantId,
        Solution, // Representation of this function expressionn
    ),
    Global(mono::CustomGlobalId, IdVec<RepParamId, Solution>),
    Local(lifted::LocalId),
    Capture(lifted::CaptureId),
    Tuple(Vec<Expr>),
    Lam(
        lifted::LamId,
        IdVec<RepParamId, Solution>,    // Parameters on the lambda
        Solution,                       // Representation of the lambda expression
        IdVec<lifted::CaptureId, Expr>, // Captures
    ),
    App(
        Purity,
        Solution, // Representation being called
        Box<Expr>,
        Box<Expr>,
        Type<Solution>, // Argument type
        Type<Solution>, // Return type
    ),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, Type<Solution>),
    LetMany(Vec<(Pattern, Expr)>, Box<Expr>),

    ArrayLit(
        Type<Solution>, // Item type
        Vec<Expr>,
    ),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any(Type<Solution>),
    Var(Type<Solution>),
    Tuple(Vec<Pattern>),
    Ctor(
        mono::CustomTypeId,
        IdVec<RepParamId, Solution>,
        res::VariantId,
        Option<Box<Pattern>>,
    ),
    BoolConst(bool),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

#[derive(Clone, Debug)]
pub struct Params {
    // Number of parameters is implicit in the length of this vector
    pub requirements: IdVec<RepParamId, (TemplateId, IdVec<RepParamId, RepParamId>)>,
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
    pub captures: IdVec<lifted::CaptureId, Type<RepParamId>>,
    pub arg: Type<RepParamId>,
    pub ret: Type<RepParamId>,
    pub arg_pat: Pattern,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<mono::CustomTypeId, TypeDef>,
    pub custom_type_symbols: IdVec<mono::CustomTypeId, mono::TypeSymbols>,
    pub templates: IdVec<TemplateId, Template>,
    pub vals: IdVec<mono::CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<mono::CustomGlobalId, mono::ValSymbols>,
    pub lams: IdVec<lifted::LamId, LamDef>,
    pub lam_symbols: IdVec<lifted::LamId, lifted::LamSymbols>,
    pub main: mono::CustomGlobalId,
}
