use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::mode_annot_ast2::CollectOverlay;
use crate::data::mode_annot_ast2::{self as annot, Lt, Mode, Overlay, SlotId};
use crate::data::obligation_annot_ast as ob;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::iter::IterExt;
use id_collections::Count;
use id_collections::{id_type, IdVec};
use std::collections::BTreeSet;

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

// Since we insert let bindings in this pass (for retains and releases), the lifetime data from the
// previous pass is no longer meaningful.
pub type Type = annot::ModeData<Mode>;

#[id_type]
pub struct LocalId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RcOp {
    Retain,
    Release,
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Get(LocalId, LocalId, Type),
    Extract(LocalId, LocalId),
    Len(LocalId),
    Push(LocalId, LocalId),
    Pop(LocalId),
    Replace(LocalId, LocalId),
    Reserve(LocalId, LocalId),
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
    Branch(LocalId, Vec<(annot::Condition<Mode, Lt>, Expr)>, Type),
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
    WrapCustom(
        first_ord::CustomTypeId,
        LocalId, // The unwrapped argument value
        Type,    // The wrapped return type (needed for lowering)
    ),
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

#[derive(Clone, Debug)]

pub struct FuncDef {
    pub purity: Purity,
    pub arg_ty: Type,
    pub ret_ty: Type,

    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    // `ov` is computable from `ty`, but kept around for convenience
    pub ty: annot::ModeData<SlotId>,
    pub ov: Overlay<SlotId>,
    pub slot_count: Count<SlotId>,
    pub ov_slots: BTreeSet<SlotId>,
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
