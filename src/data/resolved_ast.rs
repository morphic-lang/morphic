use crate::data::purity::Purity;
use crate::data::raw_ast::{self as raw, Op};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeId {
    Bool,
    Byte,
    Int,
    Float,
    Array,
    Custom(CustomTypeId),
}

id_type!(pub CustomTypeId);

id_type!(pub VariantId);

id_type!(pub TypeParamId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum GlobalId {
    ArithOp(Op),
    ArrayOp(ArrayOp),
    IOOp(IOOp),
    Ctor(TypeId, VariantId),
    Custom(CustomGlobalId),
}

id_type!(pub CustomGlobalId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum IOOp {
    Input,
    Output,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArrayOp {
    Item,
    Len,
    Push,
    Pop,
    Concat,
}

id_type!(pub LocalId);

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: Vec<TypeDef>,
    pub custom_type_data: Vec<TypeData>,
    pub vals: Vec<ValDef>,
    pub val_data: Vec<ValData>,
    pub main: CustomGlobalId,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub num_params: usize,
    pub variants: Vec<Option<Type>>,
}

#[derive(Clone, Debug)]
pub struct VariantData {
    pub variant_name: raw::CtorName,
}

#[derive(Clone, Debug)]
pub struct TypeData {
    // TODO: Include filename/module info
    pub type_name: raw::TypeName,
    pub variant_data: Vec<VariantData>,
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: TypeScheme,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct ValData {
    // TODO: Include filename/module info
    pub val_name: raw::ValName,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Var(TypeParamId),
    App(TypeId, Vec<Type>),
    Tuple(Vec<Type>),
    Func(Purity, Box<Type>, Box<Type>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeScheme {
    pub num_params: usize,
    pub body: Type,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Global(GlobalId),
    Local(LocalId),
    Tuple(Vec<Expr>),
    Lam(Purity, Pattern, Box<Expr>),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    Let(Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(Vec<Expr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any,
    Var,
    Tuple(Vec<Pattern>),
    Ctor(TypeId, VariantId, Option<Box<Pattern>>),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}
