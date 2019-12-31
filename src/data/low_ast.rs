use crate::data::first_order_ast as first_ord;
use crate::data::repr_constrained_ast as constrain;
use crate::util::id_vec::IdVec;

// Second pass:
// (1) flatten sum types over sum types

id_type!(pub LocalId);
id_type!(pub CustomTypeId);
id_type!(pub VariantId);
id_type!(pub CustomFuncId);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Bool,
    Num(first_ord::NumType),
    Array(constrain::RepChoice, Box<Type>),
    HoleArray(constrain::RepChoice, Box<Type>),
    Tuple(Vec<Type>),
    Variants(IdVec<VariantId, Type>),
    Boxed(Box<Type>),
    Custom(CustomTypeId),
}

#[derive(Clone, Copy, Debug)]
pub enum ArithOp {
    Op(first_ord::NumType, first_ord::BinOp, LocalId, LocalId),
    Cmp(first_ord::NumType, first_ord::Comparison, LocalId, LocalId),
    Negate(first_ord::NumType, LocalId),
}

// Mutable operations on persistent arrays with refcount 1 should mutate
#[derive(Clone, Debug)]
pub enum ArrayOp {
    New(),

    // Returns tuple of (item, hole array)
    // Argument is borrowed; Return is owned
    Item(
        LocalId, // Array
        LocalId, // Index
    ),

    // Returns int
    // Argument is borrowed
    Len(
        LocalId, // Array
    ),

    // Arguments are owned; Return is owned
    Push(
        LocalId, // Array
        LocalId, // Item
    ),

    // Returns type (array, item)
    // Argument is owned; Return values are owned
    Pop(
        LocalId, // Array
    ),

    // Returns new array
    // Arguments are owned; Return is owned
    Replace(
        LocalId, // Hole array
        LocalId, // Item
    ),

    // Returns unit
    // Argument is borrowed
    Retain(
        LocalId, // Array
    ),

    // Returns unit
    // Argument is owned
    Release(
        LocalId, // Array
    ),
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input,           // Returns array of bytes
    Output(LocalId), // Takes array of bytes, returns unit
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(LocalId),
    Call(CustomFuncId, LocalId),
    If(LocalId, Box<Expr>, Box<Expr>),
    LetMany(
        Vec<(Type, Expr)>, // bound values.  Each is assigned a new sequential LocalId
        LocalId,           // body
    ),

    Tuple(Vec<LocalId>),
    TupleField(LocalId, usize),
    WrapVariant(IdVec<VariantId, Type>, VariantId, LocalId),
    UnwrapVariant(VariantId, LocalId),
    WrapCustom(CustomTypeId, LocalId),
    UnwrapCustom(CustomTypeId, LocalId),

    Retain(LocalId),  // Takes any type, returns unit
    Release(LocalId), // Takes any type, returns unit

    CheckVariant(VariantId, LocalId), // Returns a bool

    ArithOp(ArithOp),
    ArrayOp(constrain::RepChoice, Type, ArrayOp), // Type is the item type
    IoOp(IoOp),

    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

pub const ARG_LOCAL: LocalId = LocalId(0);

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub arg_type: Type,
    pub ret_type: Type,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<CustomTypeId, Type>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub main: CustomFuncId,
}
