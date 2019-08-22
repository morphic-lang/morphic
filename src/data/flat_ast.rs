use crate::data::first_order_ast::{self as first_ord};
use crate::data::purity::Purity;
use crate::util::id_vec::IdVec;

id_type!(pub LocalId);

#[derive(Clone, Debug)]
pub enum ArithOp {
    Op(first_ord::NumType, first_ord::BinOp, LocalId, LocalId),
    Cmp(first_ord::NumType, first_ord::Comparison, LocalId, LocalId),
    Negate(first_ord::NumType, LocalId),
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Item(
        first_ord::Type, // Item type
        LocalId,         // Array
        LocalId,         // Index
    ), // Returns tuple of (item, hole array)
    Len(
        first_ord::Type, // Item type
        LocalId,         // Array
    ), // Returns int
    Push(
        first_ord::Type, // Item type
        LocalId,         // Array
        LocalId,         // Item
    ), // Returns new array
    Pop(
        first_ord::Type, // Item type
        LocalId,         // Array
    ), // Returns tuple (array, item)
    Replace(
        first_ord::Type, // Item type
        LocalId,         // Hole array
        LocalId,         // Item
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum IOOp {
    Input,           // Returns array of bytes
    Output(LocalId), // Takes array of bytes, returns unit
}

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(ArithOp),
    ArrayOp(ArrayOp),
    IOOp(IOOp),
    Ctor(
        first_ord::CustomTypeId,
        first_ord::VariantId,
        Option<LocalId>,
    ),
    Local(LocalId),
    Tuple(Vec<LocalId>),
    Call(Purity, first_ord::CustomFuncId, LocalId),
    Branch(LocalId, Vec<(Condition, Expr)>, first_ord::Type),
    Let(
        Box<Expr>, // rhs
        Box<Expr>, // body
    ),

    UnwrapVariant(first_ord::CustomTypeId, first_ord::VariantId, LocalId),
    TupleField(LocalId, usize),

    ArrayLit(first_ord::Type, Vec<LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub enum Condition {
    Any,
    Tuple(Vec<Condition>),
    Ctor(
        first_ord::CustomTypeId,
        first_ord::VariantId,
        Option<Box<Condition>>,
    ),
    BoolConst(bool),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

const ARG_LOCAL: LocalId = LocalId(0);

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: first_ord::Type,
    pub ret_type: first_ord::Type,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<first_ord::CustomTypeId, first_ord::TypeDef>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub main: first_ord::CustomFuncId,
}
