use crate::data::first_order_ast::{self as first_ord};
use crate::data::intrinsics::Intrinsic;
use crate::data::low_ast as low;
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast::Mode;
use crate::data::obligation_annot_ast::{CustomFuncId, CustomTypeId};
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::collection_ext::VecExt;
use crate::util::let_builder::{BuildMatch, FromBindings, LetManyBuilder};
use crate::util::local_context::LocalContext;
use id_collections::{id_type, IdVec};

#[id_type]
pub struct LocalId(pub usize);

pub const ARG_LOCAL: LocalId = LocalId(0);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Type>),
    Variants(IdVec<first_ord::VariantId, Type>),
    Custom(CustomTypeId),
    Array(Box<Type>),
    HoleArray(Box<Type>),
    Boxed(Box<Type>),
}

#[id_type]
pub struct ModeSchemeId(pub usize);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModeScheme {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<ModeScheme>),
    Variants(IdVec<first_ord::VariantId, ModeScheme>),
    Custom(ModeSchemeId, CustomTypeId),
    Array(Mode, Box<ModeScheme>),
    HoleArray(Mode, Box<ModeScheme>),
    Boxed(Mode, Box<ModeScheme>),
}

impl ModeScheme {
    pub fn as_type(&self) -> Type {
        match self {
            ModeScheme::Bool => Type::Bool,
            ModeScheme::Num(num_type) => Type::Num(*num_type),
            ModeScheme::Tuple(schemes) => Type::Tuple(schemes.map_refs(|s| s.as_type())),
            ModeScheme::Variants(schemes) => Type::Variants(schemes.map_refs(|_, s| s.as_type())),
            ModeScheme::Custom(_, id) => Type::Custom(*id),
            ModeScheme::Array(_, scheme) => Type::Array(Box::new(scheme.as_type())),
            ModeScheme::HoleArray(_, scheme) => Type::HoleArray(Box::new(scheme.as_type())),
            ModeScheme::Boxed(_, scheme) => Type::Boxed(Box::new(scheme.as_type())),
        }
    }
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Get(
        LocalId, // Array
        LocalId, // Index
    ), // Returns item
    Extract(
        LocalId, // Array
        LocalId, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        LocalId, // Array
    ),
    Push(
        LocalId, // Array
        LocalId, // Item
    ),
    Pop(
        LocalId, // Array
    ), // Returns tuple (array, item)
    Replace(
        LocalId, // Hole array
        LocalId, // Item
    ), // Returns new array
    Reserve(
        LocalId, // Array
        LocalId, // Capacity
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input,
    Output(
        ModeScheme, // Input
        LocalId,
    ),
}

#[derive(Copy, Clone, Debug)]
pub enum RcOp {
    Retain,
    Release,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(LocalId),
    Call(Purity, CustomFuncId, LocalId),
    LetMany(Vec<(Type, Expr, Metadata)>, LocalId),

    If(LocalId, Box<Expr>, Box<Expr>),
    CheckVariant(first_ord::VariantId, LocalId), // Returns a bool
    Unreachable(Type),

    Tuple(Vec<LocalId>),
    TupleField(LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, LocalId),
    WrapBoxed(LocalId, ModeScheme),
    UnwrapBoxed(LocalId, ModeScheme, ModeScheme),
    WrapCustom(CustomTypeId, LocalId),
    UnwrapCustom(CustomTypeId, LocalId),
    RcOp(ModeScheme, RcOp, LocalId),

    Intrinsic(Intrinsic, LocalId),
    ArrayOp(ModeScheme, ArrayOp),
    IoOp(IoOp),
    Panic(
        Type,       // Output
        ModeScheme, // Input
        LocalId,    // Message
    ),

    ArrayLit(
        ModeScheme,   // Scheme of *item*
        Vec<LocalId>, // Elements
    ),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: Type,
    pub ret_type: Type,
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct CustomTypes {
    pub types: IdVec<CustomTypeId, Type>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: CustomTypes,
    pub custom_type_symbols: IdVec<CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<CustomFuncId, first_ord::FuncSymbols>,
    pub schemes: IdVec<ModeSchemeId, ModeScheme>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}

impl FromBindings for Expr {
    type LocalId = LocalId;
    type Type = Type;

    fn from_bindings(bindings: Vec<(Self::Type, Self, Metadata)>, ret: Self::LocalId) -> Self {
        Expr::LetMany(bindings, ret)
    }
}

impl LocalId {
    pub fn lookup_in(&self, context: &LocalContext<LocalId, (Type, low::LocalId)>) -> low::LocalId {
        context.local_binding(*self).1
    }
}

impl BuildMatch for Expr {
    type VariantId = first_ord::VariantId;

    fn bool_type() -> Self::Type {
        Type::Bool
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
