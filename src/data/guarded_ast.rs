use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::{self as intrs, Intrinsic};
use crate::data::metadata::Metadata;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::{id_type, IdVec};
use id_graph_sccs::{SccKind, Sccs};

#[derive(Debug, Clone, Copy)]
pub enum GuardPhase {
    Structural,
    Direct(flat::CustomTypeSccId),
    Indirect(flat::CustomTypeSccId),
}

impl GuardPhase {
    pub fn should_guard(
        self,
        can_guard: CanGuard,
        kind: SccKind,
        scc: flat::CustomTypeSccId,
    ) -> bool {
        let is_candidate = match self {
            GuardPhase::Structural => true,
            GuardPhase::Direct(_) => true,
            GuardPhase::Indirect(curr_scc) => scc != curr_scc,
        };
        can_guard == CanGuard::Yes && kind == SccKind::Cyclic && is_candidate
    }

    pub fn indirect(self) -> Self {
        match self {
            GuardPhase::Structural => GuardPhase::Structural,
            GuardPhase::Direct(scc) => GuardPhase::Indirect(scc),
            GuardPhase::Indirect(scc) => GuardPhase::Indirect(scc),
        }
    }
}

#[derive(Clone, Debug)]
pub enum UnfoldRecipe {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<UnfoldRecipe>),
    Variants(IdVec<first_ord::VariantId, UnfoldRecipe>),
    LeaveCustom(first_ord::CustomTypeId),
    ProcessCustom(first_ord::CustomTypeId, GuardPhase),
    Array(Box<UnfoldRecipe>),
    HoleArray(Box<UnfoldRecipe>),
    Boxed(Box<UnfoldRecipe>),
}

#[id_type]
pub struct LocalId(pub usize);

pub const ARG_LOCAL: LocalId = LocalId(0);

// We redeclare `Type` here to ensure the guarding pass remembers to guard every type that appears
// in the output, not because of any difference in `Type` itself.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Type>),
    Variants(IdVec<first_ord::VariantId, Type>),
    Custom(first_ord::CustomTypeId),
    Array(Box<Type>),
    HoleArray(Box<Type>),
    Boxed(Box<Type>),
}

impl Type {
    pub fn from_intr(type_: &intrs::Type) -> Type {
        match type_ {
            intrs::Type::Bool => Type::Bool,
            intrs::Type::Num(num_type) => Type::Num(*num_type),
            intrs::Type::Tuple(items) => Type::Tuple(items.iter().map(Self::from_intr).collect()),
        }
    }
}
#[derive(Clone, Debug)]
pub enum ArrayOp {
    Get(
        Type,    // Item type
        LocalId, // Array
        LocalId, // Index
    ), // Returns item
    Extract(
        Type,    // Item type
        LocalId, // Array
        LocalId, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        Type,    // Item type
        LocalId, // Array
    ), // Returns int
    Push(
        Type,    // Item type
        LocalId, // Array
        LocalId, // Item
    ), // Returns new array
    Pop(
        Type,    // Item type
        LocalId, // Array
    ), // Returns tuple (array, item)
    Replace(
        Type,    // Item type
        LocalId, // Hole array
        LocalId, // Item
    ), // Returns new array
    Reserve(
        Type,    // Item type
        LocalId, // Array
        LocalId, // Capacity
    ), // Returns new array
}

#[derive(Clone, Copy, Debug)]
pub enum IoOp {
    Input,           // Returns array of bytes
    Output(LocalId), // Takes array of bytes, returns unit
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(LocalId),
    Call(Purity, first_ord::CustomFuncId, LocalId),
    LetMany(
        Vec<(Type, Expr, Metadata)>, // bound values. Each is assigned a new sequential LocalId
        LocalId,                     // body
    ),

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
    UnwrapVariant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        LocalId,
    ),
    WrapBoxed(
        LocalId,
        Type, // Inner type
    ),
    UnwrapBoxed(
        LocalId,
        Type, // Inner type
    ),
    WrapCustom(first_ord::CustomTypeId, UnfoldRecipe, LocalId),
    UnwrapCustom(first_ord::CustomTypeId, UnfoldRecipe, LocalId),

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
    pub arg_type: Type,
    pub ret_type: Type,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CanGuard {
    Yes,
    No,
}

#[derive(Clone, Debug)]
pub struct CustomTypeDef {
    pub content: Type,
    pub scc: flat::CustomTypeSccId,
    pub can_guard: CanGuard,
}

#[derive(Clone, Debug)]
pub struct CustomTypes {
    pub types: IdVec<first_ord::CustomTypeId, CustomTypeDef>,
    // Guarding can (surprisingly) change SCCs, e.g.,
    //
    // type A = Array B -guard-> type A = Array B
    // type B = A       -guard-> type B = Array B
    //
    // This field stores the SCCs of the pre-guarded customs.
    pub sccs: Sccs<flat::CustomTypeSccId, first_ord::CustomTypeId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: CustomTypes,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<first_ord::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: first_ord::CustomFuncId,
}
