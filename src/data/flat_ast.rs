use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::id_vec::IdVec;

id_type!(pub LocalId);

#[derive(Clone, Copy, Debug)]
pub enum ArithOp {
    Op(first_ord::NumType, first_ord::BinOp, LocalId, LocalId),
    Cmp(first_ord::NumType, first_ord::Comparison, LocalId, LocalId),
    Negate(first_ord::NumType, LocalId),
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Item(
        anon::Type, // Item type
        LocalId,    // Array
        LocalId,    // Index
    ), // Returns tuple of (item, hole array)
    Len(
        anon::Type, // Item type
        LocalId,    // Array
    ), // Returns int
    Push(
        anon::Type, // Item type
        LocalId,    // Array
        LocalId,    // Item
    ), // Returns new array
    Pop(
        anon::Type, // Item type
        LocalId,    // Array
    ), // Returns tuple (array, item)
    Replace(
        anon::Type, // Item type
        LocalId,    // Hole array
        LocalId,    // Item
    ), // Returns new array
}

#[derive(Clone, Copy, Debug)]
pub enum IoOp {
    Input,           // Returns array of bytes
    Output(LocalId), // Takes array of bytes, returns unit
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(LocalId),
    Call(Purity, first_ord::CustomFuncId, LocalId),
    Branch(LocalId, Vec<(Condition, Expr)>, anon::Type),
    LetMany(
        Vec<(anon::Type, Expr)>, // bound values.  Each is assigned a new sequential LocalId
        LocalId,                 // body
    ),

    Tuple(Vec<LocalId>),
    TupleField(LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, anon::Type>,
        first_ord::VariantId,
        LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, LocalId),
    WrapCustom(first_ord::CustomTypeId, LocalId),
    UnwrapCustom(first_ord::CustomTypeId, LocalId),

    ArithOp(ArithOp),
    ArrayOp(ArrayOp),
    IoOp(IoOp),

    ArrayLit(anon::Type, Vec<LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub enum Condition {
    Any,
    Tuple(Vec<Condition>),
    Variant(first_ord::VariantId, Box<Condition>),
    Custom(first_ord::CustomTypeId, Box<Condition>),
    BoolConst(bool),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

pub const ARG_LOCAL: LocalId = LocalId(0);

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: anon::Type,
    pub ret_type: anon::Type,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<first_ord::CustomTypeId, anon::Type>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub main: first_ord::CustomFuncId,
}
