use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::rc_specialized_ast as rc;
use crate::data::repr_constrained_ast as constrain;
use crate::data::repr_specialized_ast as special;
use crate::data::repr_unified_ast as unif;
use crate::data::resolved_ast as res;
use id_collections::{id_type, IdVec};

#[id_type]
pub struct CustomFuncId(pub usize);

#[id_type]
pub struct TailFuncId(pub usize);

#[derive(Clone, Debug)]
pub enum Expr {
    Local(rc::LocalId),
    Call(Purity, CustomFuncId, rc::LocalId),
    TailCall(TailFuncId, rc::LocalId),
    Branch(rc::LocalId, Vec<(special::Condition, Expr)>, special::Type),
    LetMany(Vec<(special::Type, Expr)>, rc::LocalId),

    Tuple(Vec<rc::LocalId>),
    TupleField(rc::LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, special::Type>,
        first_ord::VariantId,
        rc::LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, rc::LocalId),
    WrapBoxed(
        rc::LocalId,
        special::Type, // Inner type
    ),
    UnwrapBoxed(
        rc::LocalId,
        special::Type, // Inner type
    ),
    WrapCustom(special::CustomTypeId, rc::LocalId),
    UnwrapCustom(special::CustomTypeId, rc::LocalId),

    RcOp(
        rc::RcOp,
        unif::ContainerType<constrain::RepChoice>,
        special::Type,
        rc::LocalId,
    ),

    Intrinsic(Intrinsic, rc::LocalId),
    ArrayOp(
        constrain::RepChoice,
        special::Type, // Item type
        unif::ArrayOp,
    ),
    IoOp(constrain::RepChoice, special::IoOp),
    Panic(special::Type, constrain::RepChoice, rc::LocalId),

    ArrayLit(constrain::RepChoice, special::Type, Vec<rc::LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub struct TailFunc {
    pub arg_type: special::Type,
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
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
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<special::CustomTypeId, special::Type>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}
