use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::repr_constrained_ast as constrain;
use crate::data::repr_specialized_ast as special;
use crate::data::resolved_ast as res;
use crate::data::tail_rec_ast as tail;
use crate::util::id_vec::IdVec;

// Second pass:
// (1) flatten sum types over sum types

id_type!(pub LocalId);
id_type!(pub CustomFuncId);
pub type CustomTypeId = special::CustomTypeId;

pub type Type = special::Type;

// Mutable operations on persistent arrays with refcount 1 should mutate
#[derive(Clone, Debug)]
pub enum ArrayOp {
    New(),

    // Returns tuple of (item, hole array)
    // Argument is borrowed
    // Return value is borrowed
    Get(
        LocalId, // Array
        LocalId, // Index
    ),

    // Returns tuple of (item, hole array)
    // Argument is owned
    // Returned item is owned
    // Returned hole array is owned
    Extract(
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

    // Arguments are owned; Return is owned
    Reserve(
        LocalId, // Array
        LocalId, // Capacity
    ),
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input,           // Returns array of bytes
    Output(LocalId), // Takes array of bytes by borrow, returns unit
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(LocalId),
    Call(CustomFuncId, LocalId),
    TailCall(tail::TailFuncId, LocalId),
    If(LocalId, Box<Expr>, Box<Expr>),
    LetMany(
        Vec<(Type, Expr)>, // bound values.  Each is assigned a new sequential LocalId
        LocalId,           // body
    ),
    Unreachable(Type),

    Tuple(Vec<LocalId>),
    TupleField(LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        LocalId,
    ),
    UnwrapVariant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        LocalId,
    ),
    WrapCustom(CustomTypeId, LocalId),
    UnwrapCustom(CustomTypeId, LocalId),
    WrapBoxed(
        LocalId,
        Type, // Inner type
    ),
    UnwrapBoxed(
        LocalId,
        Type, // Inner type
    ), // Does not touch refcount

    // TODO: Consider using the same representation as the RC-specialized AST and subsequent passes
    Retain(LocalId, Type),  // Takes any type, returns unit
    Release(LocalId, Type), // Takes any type, returns unit

    CheckVariant(first_ord::VariantId, LocalId), // Returns a bool

    Intrinsic(Intrinsic, LocalId),
    ArrayOp(constrain::RepChoice, Type, ArrayOp), // Type is the item type
    IoOp(constrain::RepChoice, IoOp),
    // Takes message by borrow (not that it matters when the program is about to end anyway...)
    Panic(
        Type,                 // Return type
        constrain::RepChoice, // Message representation
        LocalId,              // Message
    ),

    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

pub const ARG_LOCAL: LocalId = LocalId(0);

#[derive(Clone, Debug)]
pub struct TailFunc {
    pub arg_type: Type,
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub tail_funcs: IdVec<tail::TailFuncId, TailFunc>,

    pub arg_type: Type,
    pub ret_type: Type,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<CustomTypeId, Type>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}
