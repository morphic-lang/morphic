use std::collections::BTreeSet;

use crate::data::lambda_lifted_ast as lifted;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CustomTypeId(pub usize);

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub variants: Vec<Option<Type>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FuncRep(pub BTreeSet<FuncCase>);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Int,
    Float,
    Text,
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Func(FuncRep),
    Custom(CustomTypeId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct OpaqueFuncRepId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LamId(pub usize);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FuncCase {
    Lam(LamId),
    Opaque(OpaqueFuncRepId),
    ArithOp(Op),
    ArrayOp(ArrayOp, Type),
    ArrayReplace(Type),
    Ctor(CustomTypeId, res::VariantId),
}

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(Op, FuncRep),
    ArrayOp(ArrayOp, Type, FuncRep),
    NullaryCtor(CustomTypeId, res::VariantId),
    Ctor(CustomTypeId, res::VariantId, FuncRep),
    Global(CustomGlobalId),
    Local(lifted::LocalId),
    Capture(lifted::CaptureId),
    Tuple(Vec<Expr>),
    Lam(LamId, FuncRep, Vec<Expr>),
    App(Purity, FuncRep, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, Type),
    Let(Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(Type, Vec<Expr>),
    BoolLit(bool),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CustomGlobalId(pub usize);

#[derive(Clone, Debug)]
pub enum Pattern {
    Any(Type),
    Var(Type),
    Tuple(Vec<Pattern>),
    Ctor(CustomTypeId, res::VariantId, Option<Box<Pattern>>),
    BoolConst(bool),
    IntConst(i64),
    FloatConst(f64),
    TextConst(String),
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub type_: Type,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct LamDef {
    pub purity: Purity,
    pub captures: Vec<Type>,
    pub arg: Type,
    pub ret: Type,
    pub arg_pat: Pattern,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: Vec<TypeDef>,
    pub opaque_reps: Vec<FuncRep>, // Indexed by OpaqueFuncRepId
    pub vals: Vec<ValDef>,         // Indexed by CustomGlobalId
    pub lams: Vec<LamDef>,         // Indexed by LamId
    pub main: CustomGlobalId,
}
