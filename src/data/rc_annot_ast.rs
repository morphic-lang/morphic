use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::mode_annot_ast2::{CollectOverlay, Overlay};
use crate::data::obligation_annot_ast::{self as ob, TypeDef};
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::iter::IterExt;
use id_collections::{id_type, IdVec};

pub type Selector = Overlay<bool>;

impl std::ops::BitAnd for &Selector {
    type Output = Selector;

    fn bitand(self, other: &Selector) -> Selector {
        self.iter()
            .zip_eq(other.iter())
            .map(|(&b1, &b2)| b1 && b2)
            .collect_overlay(&self)
    }
}

impl std::ops::BitOr for &Selector {
    type Output = Selector;

    fn bitor(self, other: &Selector) -> Selector {
        self.iter()
            .zip_eq(other.iter())
            .map(|(&b1, &b2)| b1 || b2)
            .collect_overlay(&self)
    }
}

pub type CustomFuncId = ob::CustomFuncId;
pub type CustomTypeId = first_ord::CustomTypeId;
pub type Type = ob::Type;

#[id_type]
pub struct LocalId(pub usize);

pub const ARG_LOCAL: LocalId = LocalId(0);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RcOp {
    Retain,
    Release,
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Get(Type, LocalId, LocalId),
    Extract(Type, LocalId, LocalId),
    Len(Type, LocalId),
    Push(Type, LocalId, LocalId),
    Pop(Type, LocalId),
    Replace(Type, LocalId, LocalId),
    Reserve(Type, LocalId, LocalId),
}

#[derive(Clone, Debug)]
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
    WrapBoxed(LocalId, Type),
    UnwrapBoxed(LocalId, Type),
    WrapCustom(first_ord::CustomTypeId, LocalId),
    UnwrapCustom(first_ord::CustomTypeId, LocalId),

    RcOp(RcOp, Selector, LocalId),

    Intrinsic(Intrinsic, LocalId),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(Type, LocalId),

    ArrayLit(Type, Vec<LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

pub type Condition = ob::Condition;

#[derive(Clone, Debug)]

pub struct FuncDef {
    pub purity: Purity,
    pub arg_ty: Type,
    pub ret_ty: Type,

    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct CustomTypes {
    pub types: IdVec<CustomTypeId, TypeDef>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: CustomTypes,
    pub funcs: IdVec<ob::CustomFuncId, FuncDef>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: ob::CustomFuncId,
}
