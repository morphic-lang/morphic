//! This pass annotates every binding with its lifetime "obligation." This represents the lifetime
//! of the binding as one might understand it in Rust. This is in contrast to the lifetimes we
//! computed in the previous pass which were conservative because we did not know what was owned or
//! borrowed. As the previous sentence implies, to determine lifetime obligations we need to know
//! concrete modes. Therefore, this pass specializes functions with respect to modes (though it is
//! convenient to let custom types remain mode polymorphic until the next pass).

use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::mode_annot_ast2::{self as annot, CollectOverlay, Lt, Mode, Overlay, SlotId};
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::collection_ext::{FnWrap, MapRef};
use crate::util::iter::IterExt;
use id_collections::{id_type, Count, IdVec};
use std::collections::BTreeSet;

pub type StackLt = Overlay<Lt>;

impl StackLt {
    pub fn join(&self, other: &StackLt) -> StackLt {
        debug_assert_eq!(self.shape(), other.shape());
        self.iter()
            .zip_eq(other.iter())
            .map(|(lt1, lt2)| lt1.join(lt2))
            .collect_overlay(self)
    }
}

pub type CustomTypeId = first_ord::CustomTypeId;
pub type Type = annot::ModeData<Mode>;
pub type Condition = annot::Condition;

#[id_type]
pub struct CustomFuncId(usize);

#[derive(Clone, Debug)]
pub struct Occur {
    pub id: flat::LocalId,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Get(Occur, Occur, Type),
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
    Call(Purity, CustomFuncId, Occur),
    Branch(Occur, Vec<(Condition, Expr)>, Type),
    LetMany(Vec<(Type, StackLt, Expr)>, Occur),

    Tuple(Vec<Occur>),
    TupleField(Occur, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        Occur,
    ),
    UnwrapVariant(first_ord::VariantId, Occur),
    WrapBoxed(Occur, Type),
    UnwrapBoxed(Occur, Type),
    WrapCustom(first_ord::CustomTypeId, Occur),
    UnwrapCustom(first_ord::CustomTypeId, Occur),

    Intrinsic(Intrinsic, Occur),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(Type, Occur),

    ArrayLit(Type, Vec<Occur>),
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
    pub arg_obligation: StackLt,

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

impl CustomTypes {
    pub fn view_types(&self) -> impl MapRef<'_, CustomTypeId, annot::ModeData<SlotId>> {
        FnWrap::wrap(|id| self.types.get(id).map(|def| &def.ty))
    }
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: CustomTypes,
    pub custom_type_symbols: IdVec<CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}
