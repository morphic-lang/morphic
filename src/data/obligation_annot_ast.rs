//! This pass annotates every binding with its lifetime "obligation." This represents the lifetime
//! of the binding as one might understand it in Rust. This is in contrast to the lifetimes we
//! computed in the previous pass which were conservative because we did not know what was owned or
//! borrowed. As the previous sentence implies, to determine lifetime obligations we need to know
//! concrete modes. Therefore, this pass specializes functions with respect to modes (though it is
//! convenient to let custom types remain mode polymorphic until the next pass).

use crate::data::first_order_ast as first_ord;
use crate::data::guarded_ast::{self as guard, UnfoldRecipe};
use crate::data::intrinsics::Intrinsic;
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast2::{self as annot, Lt, LtParam, Mode};
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::{id_type, IdVec};

#[id_type]
pub struct CustomFuncId(usize);

pub type Type = annot::Type<Mode, Lt>;

#[derive(Clone, Debug)]
pub struct Occur {
    pub id: guard::LocalId,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Get(
        Occur, // Array
        Occur, // Index
        Type,  // Return type
    ),
    Extract(
        Occur, // Array
        Occur, // Index
    ),
    Len(
        Occur, // Array
    ),
    Push(
        Occur, // Array
        Occur, // Item
    ),
    Pop(
        Occur, // Array
    ),
    Replace(
        Occur, // Hole array
        Occur, // Item
    ),
    Reserve(
        Occur, // Array
        Occur, // Capacity
    ),
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
    LetMany(Vec<(Type, Expr, Metadata)>, Occur),

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
        Type, // Input type
        Type, // Output type
    ),
    WrapCustom(first_ord::CustomTypeId, UnfoldRecipe, Occur),
    UnwrapCustom(first_ord::CustomTypeId, UnfoldRecipe, Occur),

    Intrinsic(Intrinsic, Occur),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(Type, Occur),

    ArrayLit(
        Type,       // Item type
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
    pub arg_ty: Type,
    pub ret_ty: annot::Type<Mode, LtParam>,

    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

pub type CustomTypeDef = annot::CustomTypeDef;
pub type CustomTypes = annot::CustomTypes;

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: CustomTypes,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}
