use std::collections::BTreeSet;

use crate::data::intrinsics::Intrinsic;
use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp, IoOp};
use crate::util::id_vec::IdVec;

id_type!(pub CustomTypeId);

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub variants: IdVec<res::VariantId, Option<Type>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FuncRep(pub BTreeSet<FuncCase>);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Byte,
    Int,
    Float,
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Func(FuncRep),
    Custom(CustomTypeId),
}

id_type!(pub OpaqueFuncRepId);

id_type!(pub LamId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FuncCase {
    Lam(LamId),
    Opaque(OpaqueFuncRepId),
    ArithOp(Op),
    Intrinsic(Intrinsic),
    ArrayOp(ArrayOp, Type),
    ArrayReplace(Type),
    IoOp(IoOp),
    Panic(Type),
    Ctor(CustomTypeId, res::VariantId),
}

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(Op, FuncRep),
    Intrinsic(Intrinsic, FuncRep),
    ArrayOp(ArrayOp, Type, FuncRep),
    IoOp(IoOp, FuncRep),
    Panic(Type, FuncRep),
    NullaryCtor(CustomTypeId, res::VariantId),
    Ctor(CustomTypeId, res::VariantId, FuncRep),
    Global(CustomGlobalId),
    Local(lifted::LocalId),
    Capture(lifted::CaptureId),
    Tuple(Vec<Expr>),
    Lam(LamId, FuncRep, IdVec<lifted::CaptureId, Expr>),
    App(
        Purity,
        FuncRep,
        Box<Expr>,
        Box<Expr>,
        Type, // Argument type
        Type, // Return type
    ),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, Type),
    LetMany(Vec<(Pattern, Expr)>, Box<Expr>),

    ArrayLit(Type, Vec<Expr>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

id_type!(pub CustomGlobalId);

#[derive(Clone, Debug)]
pub enum Pattern {
    Any(Type),
    Var(Type),
    Tuple(Vec<Pattern>),
    Ctor(CustomTypeId, res::VariantId, Option<Box<Pattern>>),
    BoolConst(bool),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub type_: Type,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct LamDef {
    pub purity: Purity,
    pub captures: IdVec<lifted::CaptureId, Type>,
    pub arg: Type,
    pub ret: Type,
    pub arg_pat: Pattern,
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<CustomTypeId, TypeDef>,
    pub custom_type_symbols: IdVec<CustomTypeId, mono::TypeSymbols>,
    pub opaque_reps: IdVec<OpaqueFuncRepId, FuncRep>,
    pub vals: IdVec<CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<CustomGlobalId, mono::ValSymbols>,
    pub lams: IdVec<LamId, LamDef>,
    pub lam_symbols: IdVec<LamId, lifted::LamSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomGlobalId,
}
