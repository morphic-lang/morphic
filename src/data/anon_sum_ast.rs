// The 'anonymous-sum AST' differs from the first-order AST in that all sum types are anonymous, and
// all custom types are simple 'newtypes'.  First-order custom types with multiple variants are
// transformed into newtypes over anonymous sum types.  This simplifies some aspects of alias
// analysis, because it separates handling of sum types from handling of recursive types (via custom
// types).
//
// Note that even in the presence of anonymous sum types, custom types are still absolutely
// necessary, because they provide the only mechanism for expressing recursive types.

use crate::data::first_order_ast as first_ord;
use crate::data::purity::Purity;
use crate::util::id_vec::IdVec;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Bool,
    Num(first_ord::NumType),
    Array(Box<Type>),
    HoleArray(Box<Type>),
    // TODO: If sum type fields are indexed by typed ids, should products types be as well?
    Tuple(Vec<Type>),
    Variants(IdVec<first_ord::VariantId, Type>),
    Custom(first_ord::CustomTypeId),
}

#[derive(Clone, Debug)]
pub enum IOOp {
    Input,
    Output(Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum ArithOp {
    Op(first_ord::NumType, first_ord::BinOp, Box<Expr>, Box<Expr>),
    Cmp(
        first_ord::NumType,
        first_ord::Comparison,
        Box<Expr>,
        Box<Expr>,
    ),
    Negate(first_ord::NumType, Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Item(
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
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(first_ord::LocalId),
    Call(Purity, first_ord::CustomFuncId, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, Type),
    Let(
        Pattern,   // lhs
        Box<Expr>, // rhs
        Box<Expr>, // body
    ),

    Tuple(Vec<Expr>),
    WrapVariant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        Box<Expr>,
    ),
    WrapCustom(first_ord::CustomTypeId, Box<Expr>),

    ArithOp(ArithOp),
    ArrayOp(ArrayOp),
    IOOp(IOOp),

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
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<first_ord::CustomTypeId, Type>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub main: first_ord::CustomFuncId,
}
