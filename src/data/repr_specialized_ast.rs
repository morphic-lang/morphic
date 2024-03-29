use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::rc_specialized_ast as rc;
use crate::data::repr_constrained_ast as constrain;
use crate::data::repr_unified_ast as unif;
use crate::data::resolved_ast as res;
use crate::util::id_vec::IdVec;

id_type!(pub CustomTypeId);

id_type!(pub CustomFuncId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Num(first_ord::NumType),
    Array(constrain::RepChoice, Box<Type>),
    HoleArray(constrain::RepChoice, Box<Type>),
    Tuple(Vec<Type>),
    Variants(IdVec<first_ord::VariantId, Type>),
    Boxed(Box<Type>),
    Custom(CustomTypeId),
}

#[derive(Clone, Copy, Debug)]
pub enum IoOp {
    Input,
    Output(rc::LocalId),
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(rc::LocalId),
    Call(Purity, CustomFuncId, rc::LocalId),
    Branch(rc::LocalId, Vec<(Condition, Expr)>, Type),
    LetMany(Vec<(Type, Expr)>, rc::LocalId),

    Tuple(Vec<rc::LocalId>),
    TupleField(rc::LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        rc::LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, rc::LocalId),
    WrapBoxed(
        rc::LocalId,
        Type, // Inner type
    ),
    UnwrapBoxed(
        rc::LocalId,
        Type, // Inner type
    ),
    WrapCustom(CustomTypeId, rc::LocalId),
    UnwrapCustom(CustomTypeId, rc::LocalId),

    RcOp(
        rc::RcOp,
        unif::ContainerType<constrain::RepChoice>,
        Type,
        rc::LocalId,
    ),

    Intrinsic(Intrinsic, rc::LocalId),
    ArrayOp(
        constrain::RepChoice,
        Type, // Item type
        unif::ArrayOp,
    ),
    IoOp(constrain::RepChoice, IoOp),
    Panic(
        Type,                 // Return type
        constrain::RepChoice, // Message representation
        rc::LocalId,          // Message
    ),

    ArrayLit(constrain::RepChoice, Type, Vec<rc::LocalId>),
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
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<CustomTypeId, Type>,
    pub custom_type_symbols: IdVec<CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}
