use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use crate::data::resolved_ast::{self as res, ArrayOp, IoOp};
use id_collections::{id_type, IdVec};

#[id_type]
pub struct CustomTypeId(pub usize);

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
    pub variant_symbols: IdVec<res::VariantId, res::VariantSymbols>,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub variants: IdVec<res::VariantId, Option<Type>>,
}

#[id_type]
pub struct CustomGlobalId(pub usize);

#[derive(Clone, Debug)]
pub enum Expr {
    Intrinsic(Intrinsic),
    ArrayOp(ArrayOp, Type),
    IoOp(IoOp),
    Panic(Type),
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
        Option<prof::ProfilePointId>,
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
    Wrapper(ValSymbolsInner),
    Normal(ValSymbolsInner),
}

#[derive(Clone, Debug)]
pub struct ValSymbolsInner {
    pub val_name: raw::ValName,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<CustomTypeId, TypeDef>,
    pub custom_type_symbols: IdVec<CustomTypeId, TypeSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub vals: IdVec<CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<CustomGlobalId, ValSymbols>,
    pub main: CustomGlobalId,
}
