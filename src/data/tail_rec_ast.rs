use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::purity::Purity;
use crate::data::repr_constrained_ast as constrain;
use crate::data::repr_specialized_ast as special;
use crate::data::repr_unified_ast as unif;
use crate::util::id_vec::IdVec;

id_type!(pub CustomFuncId);

id_type!(pub TailFuncId);

#[derive(Clone, Debug)]
pub enum Expr {
    Local(flat::LocalId),
    Call(Purity, CustomFuncId, flat::LocalId),
    TailCall(TailFuncId, flat::LocalId),
    Branch(
        flat::LocalId,
        Vec<(special::Condition, Expr)>,
        special::Type,
    ),
    LetMany(Vec<(special::Type, Expr)>, flat::LocalId),

    Tuple(Vec<flat::LocalId>),
    TupleField(flat::LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, special::Type>,
        first_ord::VariantId,
        flat::LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, flat::LocalId),
    WrapCustom(special::CustomTypeId, flat::LocalId),
    UnwrapCustom(special::CustomTypeId, flat::LocalId),

    ArithOp(flat::ArithOp),
    ArrayOp(
        constrain::RepChoice,
        special::Type, // Item type
        unif::ArrayOp,
    ),
    IoOp(constrain::RepChoice, flat::IoOp),

    ArrayLit(constrain::RepChoice, special::Type, Vec<flat::LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub struct TailFunc {
    pub arg_type: special::Type,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    // "Tail functions" are functions which may only be called from within this 'FuncDef' (from
    // either the 'body' or from other tail functions), and which may be only called via tail calls.
    // In a more imperative IR like LLVM, tail functions would correspond to labeled blocks within a
    // function which may be used as the target of 'goto's.  Unlike such blocks in an imperative IR,
    // however, tail functions also take explicit arguments (this acts as an alternative to mutable
    // variables or 'phi' nodes).
    //
    // For functions which are not tail-recursive, the 'tail_funcs' vector should be empty.
    pub tail_funcs: IdVec<TailFuncId, TailFunc>,

    pub purity: Purity,
    pub arg_type: special::Type,
    pub ret_type: special::Type,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<special::CustomTypeId, special::Type>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub main: CustomFuncId,
}
