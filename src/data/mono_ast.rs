use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CustomTypeId(pub usize);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Int,
    Float,
    Text,
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Func(Purity, Box<Type>, Box<Type>),
    Custom(CustomTypeId),
}

#[derive(Clone, Debug)]
pub struct TypeData {
    pub type_name: raw::TypeName,
    pub mono_with: Vec<Type>,
    pub variant_data: Vec<res::VariantData>,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub variants: Vec<Option<Type>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CustomGlobalId(pub usize);

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(Op),
    ArrayOp(ArrayOp, Type),
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
    Let(Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(Type, Vec<Expr>),
    BoolLit(bool),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),
}

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
pub struct ValData {
    pub val_name: raw::ValName,
    pub mono_with: Vec<Type>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: Vec<TypeDef>,
    pub custom_type_data: Vec<TypeData>,
    pub vals: Vec<ValDef>,
    pub val_data: Vec<ValData>,
    pub main: CustomGlobalId,
}
