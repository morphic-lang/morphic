use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::mode_annot_ast2::{self as annot, Shape, SlotId};
use crate::data::obligation_annot_ast::{self as ob, CustomTypeDef};
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::{id_type, IdVec};
use std::collections::BTreeSet;

#[derive(Clone, Debug)]
pub struct Selector {
    pub shape: annot::Shape,
    pub true_: BTreeSet<SlotId>,
}

impl Selector {
    pub fn none(shape: &Shape) -> Selector {
        Selector {
            shape: shape.clone(),
            true_: BTreeSet::new(),
        }
    }

    pub fn one(shape: &Shape, slot: SlotId) -> Selector {
        Selector {
            shape: shape.clone(),
            true_: std::iter::once(slot).collect(),
        }
    }

    pub fn insert(&mut self, slot: SlotId) {
        self.true_.insert(slot);
    }

    pub fn nonempty(&self) -> bool {
        !self.true_.is_empty()
    }
}

impl std::ops::BitAnd for &Selector {
    type Output = Selector;

    fn bitand(self, other: &Selector) -> Selector {
        debug_assert_eq!(self.shape, other.shape);
        Selector {
            shape: self.shape.clone(),
            true_: &self.true_ & &other.true_,
        }
    }
}

impl std::ops::BitOr for &Selector {
    type Output = Selector;

    fn bitor(self, other: &Selector) -> Selector {
        debug_assert_eq!(self.shape, other.shape);
        Selector {
            shape: self.shape.clone(),
            true_: &self.true_ | &other.true_,
        }
    }
}

impl std::ops::Sub for &Selector {
    type Output = Selector;

    fn sub(self, other: &Selector) -> Selector {
        debug_assert_eq!(self.shape, other.shape);
        Selector {
            shape: self.shape.clone(),
            true_: &self.true_ - &other.true_,
        }
    }
}

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
    Get(ob::Type, LocalId, LocalId),
    Extract(ob::Type, LocalId, LocalId),
    Len(ob::Type, LocalId),
    Push(ob::Type, LocalId, LocalId),
    Pop(ob::Type, LocalId),
    Replace(ob::Type, LocalId, LocalId),
    Reserve(ob::Type, LocalId, LocalId),
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input,
    Output(LocalId),
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(LocalId),
    Call(Purity, ob::CustomFuncId, LocalId),
    LetMany(Vec<(ob::Type, Expr)>, LocalId),

    If(LocalId, Box<Expr>, Box<Expr>),
    CheckVariant(first_ord::VariantId, LocalId), // Returns a bool
    Unreachable(ob::Type),

    Tuple(Vec<LocalId>),
    TupleField(LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, ob::Type>,
        first_ord::VariantId,
        LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, LocalId),
    WrapBoxed(LocalId, ob::Type),
    UnwrapBoxed(LocalId, ob::Type),
    WrapCustom(first_ord::CustomTypeId, LocalId),
    UnwrapCustom(first_ord::CustomTypeId, LocalId),

    RcOp(RcOp, Selector, LocalId),

    Intrinsic(Intrinsic, LocalId),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(ob::Type, LocalId),

    ArrayLit(ob::Type, Vec<LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]

pub struct FuncDef {
    pub purity: Purity,
    pub arg_ty: ob::Type,
    pub ret_ty: ob::Type,

    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct CustomTypes {
    pub types: IdVec<first_ord::CustomTypeId, CustomTypeDef>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: CustomTypes,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<ob::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<ob::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: ob::CustomFuncId,
}
