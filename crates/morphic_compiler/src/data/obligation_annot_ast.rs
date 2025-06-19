//! This pass annotates every binding with its lifetime "obligation." This represents the lifetime
//! of the binding as one might understand it in Rust. This is in contrast to the lifetimes we
//! computed in the previous pass which were conservative because we did not know what was owned or
//! borrowed. As the previous sentence implies, to determine lifetime obligations we need to know
//! concrete modes. Therefore, this pass specializes functions with respect to modes (though it is
//! convenient to let custom types remain mode polymorphic until the next pass).

use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::guarded_ast::UnfoldRecipe;
use crate::data::intrinsics::Intrinsic;
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast::{self as annot, Lt, LtParam, Mode};
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::non_empty_set::NonEmptySet;
use id_collections::{id_type, IdVec};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BindRes<L> {
    StackOwned(L),
    HeapOwned,
    Borrowed(L),
}

impl<L> BindRes<L> {
    pub fn mode(&self) -> Mode {
        match self {
            BindRes::StackOwned(_) => Mode::Owned,
            BindRes::HeapOwned => Mode::Owned,
            BindRes::Borrowed(_) => Mode::Borrowed,
        }
    }

    pub fn lt(&self) -> Option<&L> {
        match self {
            BindRes::StackOwned(l) => Some(l),
            BindRes::HeapOwned => None,
            BindRes::Borrowed(l) => Some(l),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueRes<L> {
    Owned,
    Borrowed(L),
}

impl<L> ValueRes<L> {
    pub fn mode(&self) -> Mode {
        match self {
            ValueRes::Owned => Mode::Owned,
            ValueRes::Borrowed(_) => Mode::Borrowed,
        }
    }
}

#[id_type]
pub struct CustomFuncId(pub usize);

pub type CustomTypeId = first_ord::CustomTypeId;
pub type CustomTypeSccId = flat::CustomTypeSccId;

pub type Shape = annot::Shape<CustomTypeId>;
pub type Type = annot::Type<ValueRes<Lt>, CustomTypeId>;
pub type BindType = annot::Type<BindRes<Lt>, CustomTypeId>;
pub type RetType = annot::Type<ValueRes<LtParam>, CustomTypeId>;
pub type Occur = annot::Occur<ValueRes<Lt>, CustomTypeId>;
pub type ArrayOp = annot::ArrayOp<ValueRes<Lt>, CustomTypeId>;
pub type IoOp = annot::IoOp<ValueRes<Lt>, CustomTypeId>;
pub type CustomTypeDef = annot::CustomTypeDef<CustomTypeId, CustomTypeSccId>;
pub type CustomTypes = annot::CustomTypes<CustomTypeId, CustomTypeSccId>;

pub fn wrap_lts(ty: &RetType) -> Type {
    let f = |res: &ValueRes<LtParam>| match res {
        ValueRes::Owned => ValueRes::Owned,
        ValueRes::Borrowed(lt) => ValueRes::Borrowed(Lt::Join(NonEmptySet::new(*lt))),
    };
    annot::Type::new(
        ty.shape().clone(),
        IdVec::from_vec(ty.iter().map(f).collect()),
    )
}

pub fn as_value_type(ty: &BindType) -> Type {
    let f = |res: &BindRes<Lt>| match res {
        BindRes::StackOwned(_) => ValueRes::Owned,
        BindRes::HeapOwned => ValueRes::Owned,
        BindRes::Borrowed(lt) => ValueRes::Borrowed(lt.clone()),
    };
    annot::Type::new(
        ty.shape().clone(),
        IdVec::from_vec(ty.iter().map(f).collect()),
    )
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(Occur),
    Call(Purity, CustomFuncId, Occur),
    LetMany(
        Vec<(BindType, Expr, Metadata)>, // Bound values. Each is assigned a new sequential `LocalId`
        Occur,                           // Result
    ),

    If(Occur, Box<Expr>, Box<Expr>),
    CheckVariant(first_ord::VariantId, Occur), // Returns a bool
    Unreachable(Type),

    Tuple(Vec<Occur>),
    TupleField(Occur, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        Occur,
    ),
    UnwrapVariant(first_ord::VariantId, Occur),
    WrapBoxed(
        Occur,
        Type, // Output type
    ),
    UnwrapBoxed(
        Occur,
        Type, // Output type
    ),
    WrapCustom(CustomTypeId, UnfoldRecipe<CustomTypeId>, Occur),
    UnwrapCustom(CustomTypeId, UnfoldRecipe<CustomTypeId>, Occur),

    Intrinsic(Intrinsic, Occur),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(
        Type, // Return type
        Occur,
    ),

    ArrayLit(Type, Vec<Occur>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]

pub struct FuncDef {
    pub purity: Purity,
    pub arg_ty: BindType,
    pub ret_ty: RetType,

    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
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
