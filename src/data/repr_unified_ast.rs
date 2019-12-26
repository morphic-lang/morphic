use im_rc::OrdMap;

use crate::data::alias_annot_ast as alias;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as mutation;
use crate::data::purity::Purity;
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
    Custom(first_ord::CustomTypeId, IdVec<RepParamId, Rep>),
}

#[derive(Clone, Debug)]
pub enum ArrayOp<Rep> {
    Item(
        Rep,                   // Array representation
        Type<Rep>,             // Item type
        mutation::LocalStatus, // Array status
        flat::LocalId,         // Array
        flat::LocalId,         // Index
    ), // Returns tuple of (item, hole array)
    Len(
        Rep,                   // Array representation
        Type<Rep>,             // Item type
        mutation::LocalStatus, // Array status
        flat::LocalId,         // Array
    ),
    Push(
        Rep,                   // Array representation
        Type<Rep>,             // Item type
        mutation::LocalStatus, // Array status
        flat::LocalId,         // Array
        flat::LocalId,         // Item
    ),
    Pop(
        Rep,                   // Array representation
        Type<Rep>,             // Item type
        mutation::LocalStatus, // Array status
        flat::LocalId,         // Array
    ), // Returns tuple (array, item)
    Replace(
        Rep,                   // Hole array representation
        Type<Rep>,             // Item type
        mutation::LocalStatus, // Array status
        flat::LocalId,         // Hole array
        flat::LocalId,         // Item
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum IOOp<Rep> {
    Input(Rep), // Returns byte array
    Output(
        Rep,                   // Array representation
        mutation::LocalStatus, // Byte array status
        flat::LocalId,         // Byte array
    ),
}

#[derive(Clone, Debug)]
pub enum Expr<Call, Rep> {
    Local(flat::LocalId),
    Call(Call),
    Branch(
        flat::LocalId,
        Vec<(flat::Condition, Expr<Call, Rep>)>,
        Type<Rep>,
    ),
    LetMany(
        Vec<(Type<Rep>, Expr<Call, Rep>)>, // bound values.  Each is assigned a new sequential LocalId
        flat::LocalId,                     // body
    ),

    Tuple(Vec<flat::LocalId>),
    TupleField(flat::LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type<Rep>>,
        first_ord::VariantId,
        flat::LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, flat::LocalId),
    WrapCustom(
        first_ord::CustomTypeId,
        IdVec<RepParamId, Rep>,
        flat::LocalId,
    ),
    UnwrapCustom(
        first_ord::CustomTypeId,
        IdVec<RepParamId, Rep>,
        flat::LocalId,
    ),

    ArithOp(flat::ArithOp),
    ArrayOp(ArrayOp<Rep>),
    IOOp(IOOp<Rep>),

    ArrayLit(Type<Rep>, Vec<flat::LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub struct SolvedCall<Rep>(
    pub Purity,
    pub first_ord::CustomFuncId,
    pub IdVec<RepParamId, Rep>,
    // Aliases from argument fields (keys) to other names in scope (values) (which may
    // potentially also be fields of the argument)
    pub OrdMap<alias::FieldPath, alias::LocalAliases>,
    // Folded aliases for each argument fold point
    pub OrdMap<alias::FieldPath, alias::FoldedAliases>,
    // Statuses of argument fields prior to call
    pub OrdMap<alias::FieldPath, mutation::LocalStatus>,
    pub flat::LocalId,
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
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<first_ord::CustomTypeId, TypeDef>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub main: first_ord::CustomFuncId,

    pub sccs: Vec<Scc<first_ord::CustomFuncId>>,
}
