use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::mode_annot_ast2 as annot;
use crate::data::obligation_annot_ast as ob;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::rc_annot_ast::RcOp;
use crate::data::resolved_ast as res;
use id_collections::{id_type, IdVec};

#[id_type]
pub struct LocalId(pub usize);

pub const ARG_LOCAL: LocalId = LocalId(0);

#[id_type]
pub struct CustomTypeId(pub usize);

pub type CustomFuncId = ob::CustomFuncId;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Type>),
    Variants(IdVec<first_ord::VariantId, Type>),
    Custom(CustomTypeId),
    Array(annot::Mode, Box<Type>),
    HoleArray(annot::Mode, Box<Type>),
    Boxed(annot::Mode, Box<Type>),
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Get(
        Type,    // Item type
        LocalId, // Array
        LocalId, // Index
    ), // Returns item
    Extract(
        Type,    // Item type
        LocalId, // Array
        LocalId, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        Type,    // Item type
        LocalId, // Array
    ),
    Push(
        Type,    // Item type
        LocalId, // Array
        LocalId, // Item
    ),
    Pop(
        Type,    // Item type
        LocalId, // Array
    ), // Returns tuple (array, item)
    Replace(
        Type,    // Item type
        LocalId, // Hole array
        LocalId, // Item
    ), // Returns new array
    Reserve(
        Type,    // Item type
        LocalId, // Array
        LocalId, // Capacity
    ), // Returns new array
}

#[derive(Clone, Copy, Debug)]
pub enum IoOp {
    Input,
    Output(LocalId),
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(LocalId),
    Call(Purity, CustomFuncId, LocalId),
    Branch(LocalId, Vec<(Condition, Expr)>, Type),
    LetMany(Vec<(Type, Expr)>, LocalId),

    Tuple(Vec<LocalId>),
    TupleField(LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, LocalId),
    WrapBoxed(
        LocalId,
        Type, // Inner type
    ),
    UnwrapBoxed(
        LocalId,
        Type, // Inner type
    ),
    WrapCustom(CustomTypeId, LocalId),
    UnwrapCustom(CustomTypeId, LocalId),

    // `Type` is not redundant with the binding type of `LocalId`. If the operation is a retain,
    // some additional fields of the argument may be treated as borrowed, as indicated by `Type`.
    RcOp(RcOp, Type, LocalId),

    Intrinsic(Intrinsic, LocalId),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(
        Type,    // Return type
        LocalId, // Message
    ),

    ArrayLit(Type, Vec<LocalId>),
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
        Type, // Inner type
    ),
    Custom(CustomTypeId, Box<Condition>),
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
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct CustomTypes {
    pub types: IdVec<CustomTypeId, Type>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: CustomTypes,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}
