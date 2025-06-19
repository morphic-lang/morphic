use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast::SlotId;
use crate::data::obligation_annot_ast::{self as ob, CustomTypeDef, CustomTypeId, Shape};
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::collection_ext::{FnWrap, MapRef};
use id_collections::{id_type, IdVec};
use std::collections::BTreeSet;

#[derive(Clone, Debug)]
pub struct Selector {
    pub shape: Shape,
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
pub struct Occur {
    pub id: LocalId,
    pub ty: ob::Type,
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    // The type is the the type of the input array (not merely its item)
    Get(Occur, Occur),
    Extract(Occur, Occur),
    Len(Occur),
    Push(Occur, Occur),
    Pop(Occur),
    Replace(Occur, Occur),
    Reserve(Occur, Occur),
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input,
    Output(Occur),
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(Occur),
    Call(Purity, ob::CustomFuncId, Occur),
    LetMany(Vec<(ob::BindType, Expr, Metadata)>, Occur),

    If(Occur, Box<Expr>, Box<Expr>),
    CheckVariant(first_ord::VariantId, Occur), // Returns a bool
    Unreachable(ob::Type),

    Tuple(Vec<Occur>),
    TupleField(Occur, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, ob::Type>,
        first_ord::VariantId,
        Occur,
    ),
    UnwrapVariant(first_ord::VariantId, Occur),
    WrapBoxed(
        Occur,    // Input
        ob::Type, // Output type
    ),
    UnwrapBoxed(
        Occur,    // Input
        ob::Type, // Output type
    ),
    WrapCustom(CustomTypeId, Occur),
    UnwrapCustom(CustomTypeId, Occur),

    RcOp(RcOp, Selector, LocalId),

    Intrinsic(Intrinsic, Occur),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(
        ob::Type, // Output type
        Occur,    // Input
    ),

    ArrayLit(
        ob::Type,   // Item type
        Vec<Occur>, // Elements
    ),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]

pub struct FuncDef {
    pub purity: Purity,
    pub arg_ty: ob::BindType,
    pub ret_ty: ob::RetType,

    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct CustomTypes {
    pub types: IdVec<CustomTypeId, CustomTypeDef>,
}

impl CustomTypes {
    pub fn view_shapes(&self) -> impl MapRef<'_, CustomTypeId, Shape> {
        FnWrap::wrap(|id| &self.types[id].content)
    }
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: CustomTypes,
    pub custom_type_symbols: IdVec<CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<ob::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<ob::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: ob::CustomFuncId,
}
