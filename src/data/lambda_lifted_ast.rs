use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp, IOOp};
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
    IOOp(IOOp),
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
pub struct LamData {
    pub lifted_from: mono::CustomGlobalId,
}

#[derive(Clone)]
pub struct Program {
    pub custom_types: IdVec<mono::CustomTypeId, mono::TypeDef>,
    pub custom_type_data: IdVec<mono::CustomTypeId, mono::TypeData>,
    pub vals: IdVec<mono::CustomGlobalId, ValDef>,
    pub val_data: IdVec<mono::CustomGlobalId, mono::ValData>,
    pub lams: IdVec<LamId, LamDef>,
    pub lam_data: IdVec<LamId, LamData>,
    pub main: mono::CustomGlobalId,
}
