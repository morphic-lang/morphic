use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ClosureParamId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Polarity {
    Positive,
    Negative,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub param_polarities: Vec<Polarity>,
    pub variants: Vec<Option<PType>>,
}

// Closure-parameterized type terms, for use in typedefs
#[derive(Clone, Debug)]
pub enum PType {
    Bool,
    Int,
    Float,
    Text,
    Array(Box<PType>),
    Tuple(Vec<PType>),
    Func(Purity, ClosureParamId, Box<PType>, Box<PType>),
    Custom(mono::CustomTypeId, Vec<ClosureParamId>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum InstId {
    Lam(lifted::LamId),
    Alias(AliasId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AliasId(pub usize);

#[derive(Clone, Debug)]
pub enum InstArg {
    Param(ClosureParamId),
    Inst(InstId, Vec<Union>),
}

#[derive(Clone, Debug)]
pub struct Union(pub Vec<InstArg>);

#[derive(Clone, Debug)]
pub struct AliasDef {
    pub num_params: usize,
    pub inst: InstId,
    pub args: Vec<Union>,
}

#[derive(Clone, Debug)]
pub enum IType {
    Bool,
    Int,
    Float,
    Text,
    Array(Box<IType>),
    Tuple(Vec<IType>),
    Func(Purity, Union, Box<IType>, Box<IType>),
    Custom(mono::CustomTypeId, Vec<Union>),
}

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(Op),
    ArrayOp(ArrayOp, IType),
    Ctor(mono::CustomTypeId, Vec<Union>, res::VariantId),
    Global(mono::CustomGlobalId, Vec<Union>),
    Local(lifted::LocalId),
    Capture(lifted::CaptureId),
    Tuple(Vec<Expr>),
    Lam(lifted::LamId, Vec<Union>, Vec<Expr>),
    App(Purity, Union, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    Let(Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(IType, Vec<Expr>),
    BoolLit(bool),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any(IType),
    Var(IType),
    Tuple(Vec<Pattern>),
    Ctor(
        mono::CustomTypeId,
        Vec<Union>,
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
    pub num_params: usize,
    pub body: IType,
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub type_: TypeScheme,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct LamDef {
    pub purity: Purity,
    pub num_params: usize,
    pub captures: Vec<IType>,
    pub arg: IType,
    pub ret: IType,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: Vec<TypeDef>,
    pub vals: Vec<ValDef>,
    pub lams: Vec<LamDef>,
    pub main: mono::CustomGlobalId,
}
