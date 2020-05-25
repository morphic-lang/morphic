use im_rc::OrdMap;

use crate::data::alias_annot_ast as alias;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as mutation;
use crate::data::profile as prof;
use crate::data::purity::Purity;
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
    Custom(first_ord::CustomTypeId, IdVec<RepParamId, Rep>),
}

#[derive(Clone, Copy, Debug)]
pub enum ArrayOp {
    Item(
        flat::LocalId, // Array
        flat::LocalId, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        flat::LocalId, // Array
    ),
    Push(
        flat::LocalId, // Array
        flat::LocalId, // Item
    ),
    Pop(
        flat::LocalId, // Array
    ), // Returns tuple (array, item)
    Replace(
        flat::LocalId, // Hole array
        flat::LocalId, // Item
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum Expr<Call, Rep> {
    Local(flat::LocalId),
    Call(Call),
    Branch(
        flat::LocalId,
        Vec<(Condition<Rep>, Expr<Call, Rep>)>,
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
    ArrayOp(
        Rep,                   // Array representation
        Type<Rep>,             // Item type
        mutation::LocalStatus, // Array status
        ArrayOp,
    ),
    IoOp(Rep, mutation::IoOp),

    ArrayLit(Rep, Type<Rep>, Vec<flat::LocalId>),
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
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<first_ord::CustomTypeId, TypeDef>,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<first_ord::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: first_ord::CustomFuncId,

    pub sccs: Vec<Scc<first_ord::CustomFuncId>>,
}
