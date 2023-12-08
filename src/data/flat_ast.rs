use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::{id_type, IdVec};

#[id_type]
pub struct LocalId(pub usize);

#[id_type]
pub struct CustomTypeSccId(pub usize);

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Get(
        anon::Type, // Item type
        LocalId,    // Array
        LocalId,    // Index
    ), // Returns item
    Extract(
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
    Reserve(
        anon::Type, // Item type
        LocalId,    // Array
        LocalId,    // Capacity
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
    WrapBoxed(
        LocalId,
        anon::Type, // Inner type
    ),
    UnwrapBoxed(
        LocalId,
        anon::Type, // Inner type
    ),
    WrapCustom(first_ord::CustomTypeId, LocalId),
    UnwrapCustom(first_ord::CustomTypeId, LocalId),

    Intrinsic(Intrinsic, LocalId),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(anon::Type, LocalId),

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
    Boxed(
        Box<Condition>,
        anon::Type, // Inner type
    ),
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
    pub profile_point: Option<prof::ProfilePointId>,
}

// Annotating each custom type with an id representing the SCC it belongs to isn't particularly
// related to the main purpose of this pass, but it's convenient to do it here, because alias
// analysis needs it.

#[derive(Clone, Debug)]
pub struct CustomTypeDef {
    pub content: anon::Type,
    pub scc: CustomTypeSccId,
}

#[derive(Clone, Debug)]
pub struct CustomTypes {
    pub types: IdVec<first_ord::CustomTypeId, CustomTypeDef>,
    pub sccs: IdVec<CustomTypeSccId, Vec<first_ord::CustomTypeId>>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: CustomTypes,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<first_ord::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: first_ord::CustomFuncId,
}
