use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp};

use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RepParamId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TemplateVarId(pub usize);

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

#[derive(Clone, Debug)]
pub enum Constraint {
    Lam(
        TemplateVarId, // Representation which must support the given lambda
        lifted::LamId,
        Vec<TemplateVarId>, // Parameters of the lambda
    ),
    Template(Vec<TemplateVarId>),
    ArithOp(
        TemplateVarId, // Representation which must support the given operation
        Op,
    ),
    ArrayOp(
        TemplateVarId, // Representation which must support the given operation
        ArrayOp,
        Type<TemplateVarId>, // Array item type
    ),
    ArrayReplace(
        TemplateVarId,       // Representation which must support the given operation
        Type<TemplateVarId>, // Array item type
    ),
    Ctor(
        TemplateVarId, // Representation which must support the given operation
        mono::CustomTypeId,
        Vec<TemplateVarId>, // Parameters of the type being constructed
        res::VariantId,
    ),
}

#[derive(Clone, Debug)]
pub struct Template {
    pub num_vars: usize,
    pub params: Vec<TemplateVarId>, // Indexed by RepParamId
    pub constraints: Vec<Constraint>,

    pub deps: Vec<BTreeSet<TemplateVarId>>, // Indexed by TemplateVarId
    pub param_deps: Vec<BTreeSet<RepParamId>>, // Indexed by RepParamId
}

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(Op),
    ArrayOp(ArrayOp, Type<TemplateVarId>),
    Ctor(mono::CustomTypeId, Vec<TemplateVarId>, res::VariantId),
    Global(mono::CustomGlobalId, Vec<TemplateVarId>),
    Local(lifted::LocalId),
    Capture(lifted::CaptureId),
    Tuple(Vec<Expr>),
    Lam(
        lifted::LamId,
        Vec<TemplateVarId>, // Parameters on the lambda
        TemplateVarId,      // Representation of the lambda expression
        Vec<Expr>,          // Captures
    ),
    App(
        Purity,
        TemplateVarId, // Representation being called
        Box<Expr>,
        Box<Expr>,
    ),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, Type<TemplateVarId>),
    Let(Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(
        Type<TemplateVarId>, // Item type
        Vec<Expr>,
    ),
    BoolLit(bool),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any(Type<TemplateVarId>),
    Var(Type<TemplateVarId>),
    Tuple(Vec<Pattern>),
    Ctor(
        mono::CustomTypeId,
        Vec<TemplateVarId>,
        res::VariantId,
        Option<Box<Pattern>>,
    ),
    BoolConst(bool),
    IntConst(i64),
    FloatConst(f64),
    TextConst(String),
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub template: TemplateId,
    pub type_: Type<RepParamId>,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct LamDef {
    pub purity: Purity,
    pub template: TemplateId,
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
