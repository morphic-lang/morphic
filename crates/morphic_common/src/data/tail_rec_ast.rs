use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::metadata::Metadata;
use crate::data::obligation_annot_ast::CustomTypeId;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::rc_specialized_ast::{self as rc, ModeScheme, ModeSchemeId, RcOp};
use crate::data::resolved_ast as res;
use crate::util::let_builder::{BuildMatch, FromBindings, LetManyBuilder};
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
    LetMany(Vec<(rc::Type, Expr, Metadata)>, rc::LocalId),

    If(rc::LocalId, Box<Expr>, Box<Expr>),
    CheckVariant(first_ord::VariantId, rc::LocalId), // Returns a bool
    Unreachable(rc::Type),

    Tuple(Vec<rc::LocalId>),
    TupleField(rc::LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, rc::Type>,
        first_ord::VariantId,
        rc::LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, rc::LocalId),
    WrapBoxed(
        rc::LocalId,
        ModeScheme, // Output type
    ),
    UnwrapBoxed(
        rc::LocalId,
        ModeScheme, // Input type
        ModeScheme, // Output type
    ),
    WrapCustom(CustomTypeId, rc::LocalId),
    UnwrapCustom(CustomTypeId, rc::LocalId),

    RcOp(ModeScheme, RcOp, rc::LocalId),

    Intrinsic(Intrinsic, rc::LocalId),
    ArrayOp(ModeScheme, rc::ArrayOp),
    IoOp(rc::IoOp),
    Panic(
        rc::Type,   // Output type
        ModeScheme, // Input type
        rc::LocalId,
    ),

    ArrayLit(
        ModeScheme,       // Scheme of *item*
        Vec<rc::LocalId>, // Elements
    ),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub struct TailFunc {
    pub arg_type: rc::Type,
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub enum TailFuncSymbols {
    Acyclic(first_ord::FuncSymbols),
    Cyclic,
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
    pub tail_func_symbols: IdVec<TailFuncId, first_ord::FuncSymbols>,

    pub purity: Purity,
    pub arg_type: rc::Type,
    pub ret_type: rc::Type,
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: rc::CustomTypes,
    pub custom_type_symbols: IdVec<CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<CustomFuncId, TailFuncSymbols>,
    pub schemes: IdVec<ModeSchemeId, ModeScheme>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}

impl FromBindings for Expr {
    type LocalId = rc::LocalId;
    type Type = rc::Type;

    fn from_bindings(bindings: Vec<(Self::Type, Self, Metadata)>, ret: Self::LocalId) -> Self {
        Expr::LetMany(bindings, ret)
    }
}

impl BuildMatch for Expr {
    type VariantId = first_ord::VariantId;

    fn bool_type() -> Self::Type {
        rc::Type::Bool
    }

    fn build_binding(
        builder: &mut LetManyBuilder<Self>,
        ty: Self::Type,
        expr: Self,
    ) -> Self::LocalId {
        builder.add_binding(ty, expr)
    }

    fn build_if(cond: Self::LocalId, then_expr: Self, else_expr: Self) -> Self {
        Expr::If(cond, Box::new(then_expr), Box::new(else_expr))
    }

    fn build_check_variant(variant: Self::VariantId, local: Self::LocalId) -> Self {
        Expr::CheckVariant(variant, local)
    }

    fn build_unwrap_variant(variant: Self::VariantId, local: Self::LocalId) -> Self {
        Expr::UnwrapVariant(variant, local)
    }
}
