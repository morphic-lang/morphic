use im_rc::{OrdMap, OrdSet};
use std::collections::BTreeMap;

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::mutation_annot_ast as mutation;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::graph::Scc;
use crate::util::id_vec::IdVec;

id_type!(pub CallId);

id_type!(pub OccurId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Local(pub OccurId, pub flat::LocalId);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrayOp {
    Item(
        anon::Type,            // Item type
        alias::LocalAliases,   // Array aliases
        mutation::LocalStatus, // Array status
        Local,                 // Array
        Local,                 // Index
    ), // Returns tuple of (item, hole array)
    Len(
        anon::Type,            // Item type
        alias::LocalAliases,   // Array aliases
        mutation::LocalStatus, // Array status
        Local,                 // Array
    ),
    Push(
        anon::Type,            // Item type
        alias::LocalAliases,   // Array aliases
        mutation::LocalStatus, // Array status
        Local,                 // array
        Local,                 // Item
    ),
    Pop(
        anon::Type,            // Item type
        alias::LocalAliases,   // Array aliases
        mutation::LocalStatus, // Array status
        Local,                 // Array
    ), // Returns tuple of (array, item)
    Replace(
        anon::Type,            // Item type
        alias::LocalAliases,   // Holar array aliases
        mutation::LocalStatus, // Hole array status
        Local,                 // Hole array
        Local,                 // Item
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input, // Returns byte array
    Output(
        alias::LocalAliases,   // Byte array aliases
        mutation::LocalStatus, // Byte array status
        Local,                 // Byte array
    ), // Returns unit
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(Local),
    Call(
        CallId,
        Purity,
        first_ord::CustomFuncId,
        // Aliases from argument fields (keys) to other names in scope (values) (which may
        // potentially also be fields of the argument)
        OrdMap<alias::FieldPath, alias::LocalAliases>,
        // Folded aliases for each argument fold point
        OrdMap<alias::FieldPath, alias::FoldedAliases>,
        // Statuses of argument fields prior to call
        OrdMap<alias::FieldPath, mutation::LocalStatus>,
        // Fate of *return value*
        Fate,
        Local, // Argument
    ),
    Branch(Local, Vec<(flat::Condition, Expr)>, anon::Type),
    LetMany(
        Vec<(anon::Type, Expr)>, // bound values.  Each is assigned a new sequential LocalId
        Local,                   // body
    ),

    Tuple(Vec<Local>),
    TupleField(Local, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, anon::Type>,
        first_ord::VariantId,
        Local,
    ),
    UnwrapVariant(first_ord::VariantId, Local),
    WrapBoxed(
        Local,
        anon::Type, // Inner type
    ),
    WrapUnboxed(
        Local,
        anon::Type, // Inner type
    ),
    WrapCustom(first_ord::CustomTypeId, Local),
    UnwrapCustom(first_ord::CustomTypeId, Local),

    Intrinsic(Intrinsic, Local),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(
        anon::Type,            // Return type
        mutation::LocalStatus, // Message status
        Local,                 // Message
    ),

    ArrayLit(anon::Type, Vec<Local>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

/// Represents the fate of a field path *inside the current function*.
///
/// These variants form a meaningful total order, with Unusued < Accessed < Owned.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum InternalFate {
    Unused,
    Accessed,
    Owned,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FieldFate {
    pub internal: InternalFate,
    pub ret_destinations: OrdSet<alias::RetName>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fate {
    pub fates: BTreeMap<alias::FieldPath, FieldFate>,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: anon::Type,
    pub ret_type: anon::Type,
    pub alias_sig: alias::AliasSig,
    pub mutation_sig: mutation::MutationSig,
    pub arg_fate: Fate,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument.
    pub body: Expr,
    pub fates: IdVec<OccurId, Fate>,
    pub num_calls: usize,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<first_ord::CustomTypeId, anon::Type>,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<first_ord::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: first_ord::CustomFuncId,

    pub sccs: Vec<Scc<first_ord::CustomFuncId>>,
}
