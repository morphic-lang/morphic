use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp, IoOp};
use crate::util::id_vec::IdVec;

id_type!(pub CustomTypeId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Byte,
    Int,
    Float,
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Func(Purity, Box<Type>, Box<Type>),
    Custom(CustomTypeId),
}

#[derive(Clone, Debug)]
pub struct TypeSymbols {
    pub type_name: raw::TypeName,
    pub type_mono: IdVec<res::TypeParamId, Type>,
    pub variant_symbols: IdVec<res::VariantId, res::VariantSymbols>,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub variants: IdVec<res::VariantId, Option<Type>>,
}

id_type!(pub CustomGlobalId);

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(Op),
    ArrayOp(ArrayOp, Type),
    IoOp(IoOp),
    Ctor(CustomTypeId, res::VariantId),
    Global(CustomGlobalId),
    Local(res::LocalId),
    Tuple(Vec<Expr>),
    Lam(
        Purity,
        Type, // Argument type
        Type, // Return type
        Pattern,
        Box<Expr>,
    ),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, Type),
    LetMany(Vec<(Pattern, Expr)>, Box<Expr>),

    ArrayLit(Type, Vec<Expr>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

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
pub enum ValSymbols {
    Wrapper(ValSymbolsKind),
    Normal(ValSymbolsKind),
}

#[derive(Clone, Debug)]
pub struct ValSymbolsKind {
    pub val_name: raw::ValName,
    pub type_mono: IdVec<res::TypeParamId, Type>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<CustomTypeId, TypeDef>,
    pub custom_type_symbols: IdVec<CustomTypeId, TypeSymbols>,
    pub vals: IdVec<CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<CustomGlobalId, ValSymbols>,
    pub main: CustomGlobalId,
}
