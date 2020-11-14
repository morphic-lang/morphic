use im_rc::OrdMap;

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::mutation_annot_ast as mutation;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::disjunction::Disj;
use crate::util::id_vec::IdVec;
use crate::util::norm_pair::NormPair;

id_type!(pub CustomFuncId);

id_type!(pub LocalId);

pub const ARG_LOCAL: LocalId = LocalId(0);

// Local ids aren't stable between the original alias-annotated AST and the RC-specialized AST, so
// preserving original aliasing annotations (which are expressed in terms of `flat::LocalId`s) would
// be confusing.  Luckily, we don't need to preserve full variable-level aliasing information; all
// we really need past this point are the argument-internal aliases at each function call.
#[derive(Clone, Debug)]
pub struct ArgAliases {
    pub aliases: OrdMap<NormPair<alias::FieldPath>, Disj<alias::AliasCondition>>,
    pub folded_aliases: OrdMap<alias::FieldPath, alias::FoldedAliases>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ContainerType {
    Array,
    HoleArray,
    Boxed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RcOp {
    Retain,
    Release,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrayOp {
    Get(
        anon::Type,            // Item type
        mutation::LocalStatus, // Array status
        LocalId,               // Array
        LocalId,               // Index
    ), // Returns item
    Extract(
        anon::Type,            // Item type
        mutation::LocalStatus, // Array status
        LocalId,               // Array
        LocalId,               // Index
    ), // Returns tuple of (item, hole array)
    Len(
        anon::Type,            // Item type
        mutation::LocalStatus, // Array status
        LocalId,               // Array
    ),
    Push(
        anon::Type,            // Item type
        mutation::LocalStatus, // Array status
        LocalId,               // array
        LocalId,               // Item
    ),
    Pop(
        anon::Type,            // Item type
        mutation::LocalStatus, // Array status
        LocalId,               // Array
    ), // Returns tuple of (array, item)
    Replace(
        anon::Type,            // Item type
        mutation::LocalStatus, // Hole array status
        LocalId,               // Hole array
        LocalId,               // Item
    ), // Returns new array
    Reserve(
        anon::Type,            // Item type
        mutation::LocalStatus, // Array status
        LocalId,               // Array
        LocalId,               // Capacity
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input, // Returns byte array
    Output(
        mutation::LocalStatus, // Byte array statuses
        LocalId,               // Byte array
    ), // Returns unit
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(LocalId),
    Call(
        Purity,
        CustomFuncId,
        // Aliases internal to the argument
        ArgAliases,
        // Statuses of argument fields prior to call
        OrdMap<alias::FieldPath, mutation::LocalStatus>,
        LocalId, // Argument
    ),
    Branch(LocalId, Vec<(flat::Condition, Expr)>, anon::Type),
    LetMany(
        Vec<(anon::Type, Expr)>, // bound values.  Each is assigned a new sequential LocalId
        LocalId,                 // body
    ),

    Tuple(Vec<LocalId>),
    TupleField(LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, anon::Type>,
        first_ord::VariantId,
        LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, LocalId),
    WrapBoxed(
        LocalId,
        anon::Type, // Inner type
    ),
    UnwrapBoxed(
        LocalId,
        anon::Type, // Inner type
    ),
    WrapCustom(first_ord::CustomTypeId, LocalId),
    UnwrapCustom(first_ord::CustomTypeId, LocalId),

    RcOp(
        RcOp,
        ContainerType,
        anon::Type, // Inner type inside container
        LocalId,
    ),

    Intrinsic(Intrinsic, LocalId),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(
        anon::Type,            // Return type
        mutation::LocalStatus, // Message status
        LocalId,               // Message
    ),

    ArrayLit(anon::Type, Vec<LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: anon::Type,
    pub ret_type: anon::Type,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument.
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<first_ord::CustomTypeId, anon::Type>,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}
