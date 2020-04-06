use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp, IoOp};
use crate::util::id_vec::IdVec;

id_type!(pub LamId);

id_type!(pub LocalId);

impl LocalId {
    pub const ARG: Self = LocalId(0);
}

id_type!(pub CaptureId);

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(Op),
    ArrayOp(ArrayOp, mono::Type),
    IoOp(IoOp),
    Ctor(mono::CustomTypeId, res::VariantId),
    Global(mono::CustomGlobalId),
    Local(LocalId),
    Capture(CaptureId),
    Tuple(Vec<Expr>),
    Lam(LamId, IdVec<CaptureId, Expr>),
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
    pub captures: IdVec<CaptureId, mono::Type>,
    pub arg_type: mono::Type,
    pub ret_type: mono::Type,
    pub arg: mono::Pattern,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct LamSymbols {
    pub lifted_from: mono::CustomGlobalId,
}

#[derive(Clone)]
pub struct Program {
    pub custom_types: IdVec<mono::CustomTypeId, mono::TypeDef>,
    pub custom_type_symbols: IdVec<mono::CustomTypeId, mono::TypeSymbols>,
    pub vals: IdVec<mono::CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<mono::CustomGlobalId, mono::ValSymbols>,
    pub lams: IdVec<LamId, LamDef>,
    pub lam_symbols: IdVec<LamId, LamSymbols>,
    pub main: mono::CustomGlobalId,
}
