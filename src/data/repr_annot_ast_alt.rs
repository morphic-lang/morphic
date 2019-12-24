use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast::MutationCondition;
use crate::data::purity::Purity;
use crate::util::disjunction::Disj;
use crate::util::id_vec::IdVec;

id_type!(pub RepParamId);

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub num_params: usize,
    pub content: Type<RepParamId>,
}

#[derive(Clone, Debug)]
pub enum Type<Rep> {
    Bool,
    Num(first_ord::NumType),
    Array(Rep, Box<Type<Rep>>),
    HoleArray(Rep, Box<Type<Rep>>),
    Tuple(Vec<Type<Rep>>),
    Variants(IdVec<first_ord::VariantId, Type<Rep>>),
    Custom(first_ord::CustomTypeId, Vec<Rep>),
}

#[derive(Clone, Debug)]
pub enum ArrayOp<Rep> {
    Item(
        Rep,           // Array representation
        Type<Rep>,     // Item type
        flat::LocalId, // Array
        flat::LocalId, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        Rep,           // Array representation
        Type<Rep>,     // Item type
        flat::LocalId, // Array
    ),
    Push(
        Rep,           // Array representation
        Type<Rep>,     // Item type
        flat::LocalId, // Array
        flat::LocalId, // Item
    ),
    Pop(
        Rep,           // Array representation
        Type<Rep>,     // Item type
        flat::LocalId, // Array
    ), // Returns tuple (array, item)
    Replace(
        Rep,           // Hole array representation
        Type<Rep>,     // Item type
        flat::LocalId, // Hole array
        flat::LocalId, // Item
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum IOOp<Rep> {
    Input(Rep), // Returns byte array
    Output(
        Rep,           // Array representation
        flat::LocalId, // Byte array
    ),
}

#[derive(Clone, Debug)]
pub enum Expr<Rep> {
    Local(first_ord::LocalId),
    Call(
        Purity,
        first_ord::CustomFuncId,
        IdVec<RepParamId, Rep>,
        flat::LocalId,
    ),
    Branch(flat::LocalId, Vec<(flat::Condition, Expr<Rep>)>, Type<Rep>),
    LetMany(
        Vec<(Type<Rep>, Expr<Rep>)>, // bound values.  Each is assigned a new sequential LocalId
        flat::LocalId,               // body
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Rep {
    Immut,
    Mut,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RepSolution {
    Const(Rep),
    Var(RepParamId),
}

#[derive(Clone, Debug)]
pub struct ParamConstraint {
    immut_cond: Disj<MutationCondition>,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub params: IdVec<RepParamId, ParamConstraint>,
    pub arg_type: Type<RepParamId>,
    pub ret_type: Type<RepParamId>,
    pub body: Expr<RepSolution>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<first_ord::CustomTypeId, TypeDef>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub main: first_ord::CustomFuncId,
}
