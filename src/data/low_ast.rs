use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::metadata::Metadata;
use crate::data::obligation_annot_ast as ob;
use crate::data::profile as prof;
use crate::data::rc_specialized_ast2::{self as rc, ModeScheme, ModeSchemeId, RcOp};
use crate::data::resolved_ast as res;
use crate::data::tail_rec_ast as tail;
use id_collections::{id_type, IdVec};

// Second pass:
// (1) flatten sum types over sum types

#[id_type]
pub struct LocalId(pub usize);

// TODO: We can just use `tail::CustomFuncId` here
#[id_type]
pub struct CustomFuncId(pub usize);

pub type CustomTypeId = ob::CustomTypeId;

pub type Type = rc::Type;

// Mutable operations on arrays with refcount 1 should mutate
#[derive(Clone, Debug)]
pub enum ArrayOp {
    New,

    Get(
        LocalId, // Array
        LocalId, // Index
    ),

    Extract(
        LocalId, // Array
        LocalId, // Index
    ),

    // Returns int
    Len(
        LocalId, // Array
    ),

    Push(
        LocalId, // Array
        LocalId, // Item
    ),

    Pop(
        LocalId, // Array
    ),

    Replace(
        LocalId, // Hole array
        LocalId, // Item
    ),

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
    LetMany(
        Vec<(Type, Expr, Metadata)>, // bound values. Each is assigned a new sequential LocalId
        LocalId,                     // body
    ),

    If(LocalId, Box<Expr>, Box<Expr>),
    CheckVariant(first_ord::VariantId, LocalId), // Returns a bool
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
        ModeScheme, // Output type
    ),
    UnwrapBoxed(
        LocalId,
        ModeScheme, // Input type
        ModeScheme, // Output type
    ),

    RcOp(ModeScheme, RcOp, LocalId), // Takes any type, returns unit

    Intrinsic(Intrinsic, LocalId),
    ArrayOp(ModeScheme, ArrayOp),
    IoOp(IoOp),
    // Takes message by borrow (not that it matters when the program is about to end anyway...)
    Panic(
        Type,    // Return type
        LocalId, // Message
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
    pub tail_func_symbols: IdVec<tail::TailFuncId, first_ord::FuncSymbols>,

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
    pub custom_types: rc::CustomTypes,
    pub custom_type_symbols: IdVec<CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<CustomFuncId, tail::TailFuncSymbols>,
    pub schemes: IdVec<ModeSchemeId, ModeScheme>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}
