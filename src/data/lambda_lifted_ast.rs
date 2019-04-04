use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp, IOOp};

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
    IOOp(IOOp),
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
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
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
    pub arg_type: mono::Type,
    pub ret_type: mono::Type,
    pub arg: mono::Pattern,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct LamData {
    pub lifted_from: mono::CustomGlobalId,
}
#[derive(Clone)]
pub struct Program {
    pub custom_types: Vec<mono::TypeDef>,
    pub custom_type_data: Vec<mono::TypeData>,
    pub vals: Vec<ValDef>,
    pub val_data: Vec<mono::ValData>,
    pub lams: Vec<LamDef>,
    pub lam_data: Vec<LamData>,
    pub main: mono::CustomGlobalId,
}
