use std::path::PathBuf;

use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use id_collections::{id_type, IdVec};

// 'ModId' is used only for the purposes of reporting human-readable module information to the user,
// for example during error reporting. After the initial name resolution pass is complete, the
// module from which a particular type or value originated is semantically irrelevant.
#[id_type]
pub struct ModId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeId {
    Bool,
    Byte,
    Int,
    Float,
    Array,
    Custom(CustomTypeId),
}

#[id_type]
pub struct CustomTypeId(pub usize);

#[id_type]
pub struct VariantId(pub usize);

#[id_type]
pub struct TypeParamId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum GlobalId {
    Intrinsic(Intrinsic),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic,
    Ctor(TypeId, VariantId),
    Custom(CustomGlobalId),
}

#[id_type]
pub struct CustomGlobalId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum IoOp {
    Input,
    Output,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArrayOp {
    Get,
    Extract,
    Len,
    Push,
    Pop,
    Reserve,
}

#[id_type]
pub struct LocalId(pub usize);

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<ModId, ModSymbols>,
    pub custom_types: IdVec<CustomTypeId, TypeDef>,
    pub custom_type_symbols: IdVec<CustomTypeId, TypeSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub vals: IdVec<CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<CustomGlobalId, ValSymbols>,
    pub main: CustomGlobalId,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModDeclLoc {
    Root,
    ChildOf { parent: ModId, name: raw::ModName },
}

#[derive(Clone, Debug)]
pub struct ModSymbols {
    pub file: PathBuf,
    pub decl_loc: ModDeclLoc,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub num_params: usize,
    pub variants: IdVec<VariantId, Option<Type>>,
}

#[derive(Clone, Debug)]
pub struct VariantSymbols {
    pub variant_name: raw::CtorName,
}

#[derive(Clone, Debug)]
pub struct TypeSymbols {
    pub mod_: ModId,
    pub type_name: raw::TypeName,
    pub variant_symbols: IdVec<VariantId, VariantSymbols>,
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: TypeScheme,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct ValSymbols {
    pub mod_: ModId,
    pub type_param_names: IdVec<TypeParamId, raw::TypeParam>,
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
    Lam(Purity, Pattern, Box<Expr>, Option<prof::ProfilePointId>),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    LetMany(Vec<(Pattern, Expr)>, Box<Expr>),

    ArrayLit(Vec<Expr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),

    Span(usize, usize, Box<Expr>),
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

    Span(usize, usize, Box<Pattern>),
}
