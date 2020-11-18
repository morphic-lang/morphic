use im_rc::OrdMap;

use crate::data::alias_annot_ast as alias;
use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::mutation_annot_ast as mutation;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::rc_specialized_ast as rc;
use crate::data::resolved_ast as res;
use crate::util::graph::Scc;
use crate::util::id_vec::IdVec;

id_type!(pub RepParamId);

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub num_params: usize,
    pub content: Type<RepParamId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<Rep> {
    Bool,
    Num(first_ord::NumType),
    Array(Rep, Box<Type<Rep>>),
    HoleArray(Rep, Box<Type<Rep>>),
    Tuple(Vec<Type<Rep>>),
    Variants(IdVec<first_ord::VariantId, Type<Rep>>),
    Boxed(Box<Type<Rep>>),
    Custom(first_ord::CustomTypeId, IdVec<RepParamId, Rep>),
}

#[derive(Clone, Copy, Debug)]
pub enum ArrayOp {
    Get(
        rc::LocalId, // Array
        rc::LocalId, // Index
    ), // Returns item
    Extract(
        rc::LocalId, // Array
        rc::LocalId, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        rc::LocalId, // Array
    ),
    Push(
        rc::LocalId, // Array
        rc::LocalId, // Item
    ),
    Pop(
        rc::LocalId, // Array
    ), // Returns tuple (array, item)
    Replace(
        rc::LocalId, // Hole array
        rc::LocalId, // Item
    ), // Returns new array
    Reserve(
        rc::LocalId, // Array
        rc::LocalId, // Capacity
    ), // Returns new array
}

#[derive(Clone, Copy, Debug)]
pub enum ContainerType<Rep> {
    Array(Rep),
    HoleArray(Rep),
    Boxed,
}

#[derive(Clone, Debug)]
pub enum Expr<Call, Rep> {
    Local(rc::LocalId),
    Call(Call),
    Branch(
        rc::LocalId,
        Vec<(Condition<Rep>, Expr<Call, Rep>)>,
        Type<Rep>,
    ),
    LetMany(
        Vec<(Type<Rep>, Expr<Call, Rep>)>, // bound values.  Each is assigned a new sequential LocalId
        rc::LocalId,                       // body
    ),

    Tuple(Vec<rc::LocalId>),
    TupleField(rc::LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type<Rep>>,
        first_ord::VariantId,
        rc::LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, rc::LocalId),
    WrapBoxed(
        rc::LocalId,
        Type<Rep>, // Inner type
    ),
    UnwrapBoxed(
        rc::LocalId,
        Type<Rep>, // Inner type
    ),
    WrapCustom(first_ord::CustomTypeId, IdVec<RepParamId, Rep>, rc::LocalId),
    UnwrapCustom(first_ord::CustomTypeId, IdVec<RepParamId, Rep>, rc::LocalId),

    RcOp(
        rc::RcOp,
        ContainerType<Rep>,
        Type<Rep>,                                       // Inner type inside container
        OrdMap<alias::FieldPath, mutation::LocalStatus>, // Argument statuses
        rc::LocalId,
    ),

    Intrinsic(Intrinsic, rc::LocalId),
    ArrayOp(
        Rep,                                             // Array representation
        Type<Rep>,                                       // Item type
        OrdMap<alias::FieldPath, mutation::LocalStatus>, // Array statuses
        ArrayOp,
    ),
    IoOp(Rep, rc::IoOp),
    Panic(
        Type<Rep>,             // Return type
        Rep,                   // Message representation
        mutation::LocalStatus, // Message status
        rc::LocalId,           // Message
    ),

    ArrayLit(Rep, Type<Rep>, Vec<rc::LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub enum Condition<Rep> {
    Any,
    Tuple(Vec<Condition<Rep>>),
    Variant(first_ord::VariantId, Box<Condition<Rep>>),
    Boxed(
        Box<Condition<Rep>>,
        Type<Rep>, // Inner type
    ),
    Custom(
        first_ord::CustomTypeId,
        IdVec<RepParamId, Rep>,
        Box<Condition<Rep>>,
    ),
    BoolConst(bool),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

#[derive(Clone, Debug)]
pub struct SolvedCall<Rep>(
    pub Purity,
    pub rc::CustomFuncId,
    pub IdVec<RepParamId, Rep>,
    // Aliases internal to the argument
    pub rc::ArgAliases,
    // Statuses of argument fields prior to call
    pub OrdMap<alias::FieldPath, mutation::LocalStatus>,
    pub rc::LocalId,
);

id_type!(pub InternalRepVarId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RepSolution {
    Internal(InternalRepVarId),
    Param(RepParamId),
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub num_params: usize,
    pub num_internal_vars: usize,
    pub arg_type: Type<RepParamId>,
    pub ret_type: Type<RepParamId>,
    pub body: Expr<SolvedCall<RepSolution>, RepSolution>,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<first_ord::CustomTypeId, TypeDef>,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<rc::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<rc::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: rc::CustomFuncId,

    pub sccs: Vec<Scc<rc::CustomFuncId>>,
}
