use im_rc::OrdMap;
use std::rc::Rc;

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::disjunction::Disj;
use crate::util::graph::Scc;
use id_collections::IdVec;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MutationCondition {
    AliasCondition(alias::AliasCondition),
    ArgMutated(alias::ArgName),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalStatus {
    pub mutated_cond: Disj<MutationCondition>,
}

#[derive(Clone, Debug)]
pub struct LocalInfo {
    pub type_: Rc<anon::Type>,
    pub statuses: OrdMap<alias::FieldPath, LocalStatus>,
}

#[derive(Clone, Debug)]
pub struct ContextSnapshot {
    pub locals: OrdMap<flat::LocalId, LocalInfo>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrayOp {
    Get(
        anon::Type,                            // Item type
        alias::LocalAliases,                   // Array aliases
        flat::LocalId,                         // Array
        flat::LocalId,                         // Index
        OrdMap<alias::FieldPath, LocalStatus>, // Statuses of returned item
    ), // Returns item
    Extract(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        flat::LocalId,       // Array
        flat::LocalId,       // Index
    ), // Returns tuple of (item, hole array)
    Len(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        flat::LocalId,       // Array
    ),
    Push(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        flat::LocalId,       // Array
        flat::LocalId,       // Item
    ),
    Pop(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        flat::LocalId,       // Array
    ), // Returns tuple of (array, item)
    Replace(
        anon::Type,          // Item type
        alias::LocalAliases, // Hole array aliases
        flat::LocalId,       // Hole array
        flat::LocalId,       // Item
    ), // Returns new array
    Reserve(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        flat::LocalId,       // Array
        flat::LocalId,       // Capacity
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input, // Returns byte array
    Output(
        alias::LocalAliases, // Byte array aliases
        flat::LocalId,       // Byte array
    ), // Returns unit
}

#[derive(Clone, Debug)]
pub struct Expr {
    /// Snapshot of the context before evaluating this expression
    pub prior_context: ContextSnapshot,
    pub kind: ExprKind,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Local(flat::LocalId),
    Call(
        Purity,
        first_ord::CustomFuncId,
        // Aliases from argument fields (keys) to other names in scope (values) (which may
        // potentially also be fields of the argument)
        OrdMap<alias::FieldPath, alias::LocalAliases>,
        // Folded aliases for each argument fold point
        OrdMap<alias::FieldPath, alias::FoldedAliases>,
        flat::LocalId, // Argument
    ),
    Branch(
        flat::LocalId,
        Vec<(
            flat::Condition,
            Expr,
            ContextSnapshot, // Snapshot of the context after evaluating this branch arm
        )>,
        anon::Type,
    ),
    LetMany(
        Vec<(anon::Type, Expr)>, // bound values.  Each is assigned a new sequential LocalId
        ContextSnapshot,         // Snapshot of the context after all bindings have been evaluated
        flat::LocalId,           // body
    ),

    Tuple(Vec<flat::LocalId>),
    TupleField(flat::LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, anon::Type>,
        first_ord::VariantId,
        flat::LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, flat::LocalId),
    WrapBoxed(
        flat::LocalId,
        anon::Type, // Inner type
    ),
    UnwrapBoxed(
        flat::LocalId,
        anon::Type,                            // Inner type
        OrdMap<alias::FieldPath, LocalStatus>, // Statuses of returned item
    ),
    WrapCustom(first_ord::CustomTypeId, flat::LocalId),
    UnwrapCustom(first_ord::CustomTypeId, flat::LocalId),

    Intrinsic(Intrinsic, flat::LocalId),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(
        anon::Type,    // Return type
        flat::LocalId, // Message
    ),

    ArrayLit(anon::Type, Vec<flat::LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MutationSig {
    // Conditions under which each argument field may be mutated during the call
    pub arg_mutation_conds: OrdMap<alias::ArgName, Disj<alias::AliasCondition>>,
    // Conditions under which each return value field may be mutated at the end of the call
    pub ret_statuses: OrdMap<alias::RetName, LocalStatus>,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: anon::Type,
    pub ret_type: anon::Type,
    pub alias_sig: alias::AliasSig,
    pub mutation_sig: MutationSig,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument.
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: flat::CustomTypes,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<first_ord::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: first_ord::CustomFuncId,

    pub sccs: Vec<Scc<first_ord::CustomFuncId>>,
}
