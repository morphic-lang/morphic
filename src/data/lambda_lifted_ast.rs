use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LamId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CaptureId(pub usize);

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(Op),
    ArrayOp(ArrayOp, mono::Type),
    Ctor(mono::CustomTypeId, res::VariantId),
    Global(mono::CustomGlobalId),
    Local(LocalId),
    Capture(CaptureId),
    Tuple(Vec<Expr>),
    Lam(LamId, Vec<Expr>),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(mono::Pattern, Expr)>, mono::Type),
    Let(mono::Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(mono::Type, Vec<Expr>),
    BoolLit(bool),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub type_: mono::Type,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct LamDef {
    pub purity: Purity,
    pub captures: Vec<mono::Type>,
    pub arg: mono::Pattern,
    pub ret: mono::Type,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: Vec<mono::TypeDef>,
    pub vals: Vec<ValDef>,
    pub lams: Vec<LamDef>,
    pub main: mono::CustomGlobalId,
}
