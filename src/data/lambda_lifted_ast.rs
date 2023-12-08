use crate::data::intrinsics::Intrinsic;
use crate::data::mono_ast as mono;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast::{self as res, ArrayOp, IoOp};
use id_collections::{id_type, IdVec};

#[id_type]
pub struct LamId(pub usize);

#[id_type]
pub struct LocalId(pub usize);

impl LocalId {
    pub const ARG: Self = LocalId(0);
}

#[id_type]
pub struct CaptureId(pub usize);

#[derive(Clone, Debug)]
pub enum Expr {
    Intrinsic(Intrinsic),
    ArrayOp(ArrayOp, mono::Type),
    IoOp(IoOp),
    Panic(mono::Type),
    Ctor(mono::CustomTypeId, res::VariantId),
    Global(mono::CustomGlobalId),
    Local(LocalId),
    Capture(CaptureId),
    Tuple(Vec<Expr>),
    Lam(LamId, IdVec<CaptureId, Expr>),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(mono::Pattern, Expr)>, mono::Type),
    LetMany(Vec<(mono::Pattern, Expr)>, Box<Expr>),

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
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct LamSymbols {
    pub lifted_from: mono::ValSymbols,
}

#[derive(Clone)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<mono::CustomTypeId, mono::TypeDef>,
    pub custom_type_symbols: IdVec<mono::CustomTypeId, mono::TypeSymbols>,
    pub vals: IdVec<mono::CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<mono::CustomGlobalId, mono::ValSymbols>,
    pub lams: IdVec<LamId, LamDef>,
    pub lam_symbols: IdVec<LamId, LamSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: mono::CustomGlobalId,
}
