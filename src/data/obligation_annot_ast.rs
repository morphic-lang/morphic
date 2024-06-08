use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::mode_annot_ast2::{self as annot, CollectOverlay, Lt, Mode, Overlay};
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::iter::IterExt;
use id_collections::{id_type, IdVec};

// To determine lifetime obligations, we need to know concrete modes. Therefore, this pass
// specializes functions (though not types) with respect to modes.

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
pub type TypeDef = annot::TypeDef;

pub type Type = annot::Type<Mode, Lt>;
pub type ModeData = annot::ModeData<Mode>;
pub type LtData = annot::LtData<Lt>;

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
    Branch(Occur, Vec<(annot::Condition<Mode, Lt>, Expr)>, Type),
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
    WrapCustom(
        first_ord::CustomTypeId,
        Occur, // The unwrapped argument value
        Type,  // The wrapped return type (needed for lowering)
    ),
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
pub struct CustomTypes {
    pub types: IdVec<CustomTypeId, TypeDef>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: CustomTypes,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}
