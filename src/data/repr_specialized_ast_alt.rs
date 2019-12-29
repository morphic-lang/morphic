use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::purity::Purity;
use crate::data::repr_constrained_ast as constrain;
use crate::util::id_vec::IdVec;

id_type!(pub CustomTypeId);

id_type!(pub CustomFuncId);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Bool,
    Num(first_ord::NumType),
    Array(constrain::RepChoice, Box<Type>),
    HoleArray(constrain::RepChoice, Box<Type>),
    Tuple(Vec<Type>),
    Variants(IdVec<first_ord::VariantId, Type>),
    Custom(CustomTypeId),
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    // Returns tuple of (item, hole array)
    Item(
        flat::LocalId, // Array
        flat::LocalId, // Index
    ),

    Len(flat::LocalId),

    Push(
        flat::LocalId, // Array
        flat::LocalId, // Item
    ),

    // Returns tuple of (array, item)
    Pop(constrain::RepChoice, flat::LocalId),

    // Returns new array
    Replace(
        flat::LocalId, // Hole array
        flat::LocalId, // Item
    ),
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input,
    Output(flat::LocalId),
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(flat::LocalId),
    Call(Purity, CustomFuncId, flat::LocalId),
    Branch(flat::LocalId, Vec<(Condition, Expr)>),
    LetMany(Vec<(Type, Expr)>, flat::LocalId),

    Tuple(Vec<flat::LocalId>),
    TupleField(flat::LocalId, usize),
    WrapVariant(IdVec<first_ord::VariantId, Type>),
    UnwrapVariant(first_ord::VariantId, flat::LocalId),
    WrapCustom(CustomTypeId, flat::LocalId),
    UnwrapCustom(CustomTypeId, flat::LocalId),

    ArithOp(flat::ArithOp),
    ArrayOp(
        constrain::RepChoice,
        Type, // Item type
        ArrayOp,
    ),
    IoOp(constrain::RepChoice, IoOp),

    ArrayLit(constrain::RepChoice, Type, Vec<flat::LocalId>),
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
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<CustomTypeId, Type>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub main: CustomFuncId,
}
