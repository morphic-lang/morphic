// The 'anonymous-sum AST' differs from the first-order AST in that all sum types are anonymous, and
// all custom types are simple 'newtypes'.  First-order custom types with multiple variants are
// transformed into newtypes over anonymous sum types.  This simplifies some aspects of alias
// analysis, because it separates handling of sum types from handling of recursive types (via custom
// types).
//
// This AST is also the first to include explicit "boxing" (pointer indirection) constructs where
// necessary to prevent recursive types from having infinite size.
//
// Note that even in the presence of anonymous sum types, custom types are still absolutely
// necessary, because they provide the only mechanism for expressing recursive types.

use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::IdVec;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Num(first_ord::NumType),
    Array(Box<Type>),
    HoleArray(Box<Type>),
    // TODO: If sum type fields are indexed by typed ids, should products types be as well?
    Tuple(Vec<Type>),
    Variants(IdVec<first_ord::VariantId, Type>),
    Boxed(Box<Type>),
    Custom(first_ord::CustomTypeId),
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input,
    Output(Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Get(
        Type,      // Item type
        Box<Expr>, // Array
        Box<Expr>, // Index
    ), // Returns item
    Extract(
        Type,      // Item type
        Box<Expr>, // Array
        Box<Expr>, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        Type,      // Item type
        Box<Expr>, // Array
    ), // Returns int
    Push(
        Type,      // Item type
        Box<Expr>, // Array
        Box<Expr>, // Item
    ), // Returns new array
    Pop(
        Type,      // Item type
        Box<Expr>, // Array
    ), // Returns tuple (array, item)
    Replace(
        Type,
        Box<Expr>, // Hole array
        Box<Expr>, // Item
    ), // Returns new array
    Reserve(
        Type,
        Box<Expr>, // Array
        Box<Expr>, // Capacity
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(first_ord::LocalId),
    Call(Purity, first_ord::CustomFuncId, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, Type),
    LetMany(Vec<(Pattern, Expr)>, Box<Expr>),

    Tuple(Vec<Expr>),
    WrapVariant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        Box<Expr>,
    ),
    WrapBoxed(
        Box<Expr>,
        Type, // Inner type
    ),
    WrapCustom(first_ord::CustomTypeId, Box<Expr>),

    Intrinsic(Intrinsic, Box<Expr>),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(Type, Box<Expr>),

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
    Variant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        Box<Pattern>,
    ),
    Boxed(
        Box<Pattern>,
        Type, // Inner type
    ),
    Custom(first_ord::CustomTypeId, Box<Pattern>),
    BoolConst(bool),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: Type,
    pub ret_type: Type,
    pub arg: Pattern,
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,

    pub custom_types: IdVec<first_ord::CustomTypeId, Type>,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<first_ord::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: first_ord::CustomFuncId,
}
