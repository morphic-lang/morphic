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
use crate::util::event_set as event;
use crate::util::graph::Scc;
use crate::util::id_vec::IdVec;

id_type!(pub CallId);

id_type!(pub OccurId);

id_type!(pub LetBlockId);

id_type!(pub BranchBlockId);

id_type!(pub RetainPointId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Local(pub OccurId, pub flat::LocalId);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrayOp {
    Get(
        anon::Type,                                      // Item type
        alias::LocalAliases,                             // Array aliases
        Local,                                           // Array
        Local,                                           // Index
        OrdMap<alias::FieldPath, mutation::LocalStatus>, // Statuses of returned item
        RetainPointId,
    ), // Returns item
    Extract(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        Local,               // Array
        Local,               // Index
    ), // Returns tuple of (item, hole array)
    Len(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        Local,               // Array
    ),
    Push(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        Local,               // array
        Local,               // Item
    ),
    Pop(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        Local,               // Array
    ), // Returns tuple of (array, item)
    Replace(
        anon::Type,          // Item type
        alias::LocalAliases, // Hole array aliases
        Local,               // Hole array
        Local,               // Item
    ), // Returns new array
    Reserve(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        Local,               // Array
        Local,               // Capacity
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input, // Returns byte array
    Output(
        alias::LocalAliases, // Byte array aliases
        Local,               // Byte array
    ), // Returns unit
}

id_type!(pub ExprId);

#[derive(Clone, Debug)]
pub struct Expr {
    pub id: ExprId,
    pub prior_context: mutation::ContextSnapshot,
    pub kind: ExprKind,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
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
        Local, // Argument
    ),
    Branch(
        Local,
        Vec<(
            BranchBlockId,
            flat::Condition,
            Expr,
            mutation::ContextSnapshot, // Snapshot of the context after evaluating this branch arm
        )>,
        anon::Type,
    ),
    LetMany(
        LetBlockId,
        Vec<(anon::Type, Expr)>, // bound values.  Each is assigned a new sequential LocalId
        mutation::ContextSnapshot, // Snapshot of the context after all bindings have been evaluated
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
    UnwrapBoxed(
        Local,
        anon::Type,                                      // Inner type
        OrdMap<alias::FieldPath, mutation::LocalStatus>, // Statuses of returned item
        RetainPointId,
    ),
    WrapCustom(first_ord::CustomTypeId, Local),
    UnwrapCustom(first_ord::CustomTypeId, Local),

    Intrinsic(Intrinsic, Local),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(
        anon::Type, // Return type
        Local,      // Message
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

#[derive(Clone, Debug)]
pub struct FieldFate {
    pub internal: InternalFate,
    // `last_internal_use` is an upper bound on the points in the function's control flow graph
    // where this value will be used (accessed or owned) last.  It does not consider accesses which
    // occur after the current function returns; instead, `ret_destinations` tracks that
    // information.
    //
    // If `internal` is `Unused`, then `last_internal_use` should be empty.
    pub last_internal_use: event::Horizon,
    // We only consider a value to escape a block if it is *used* (accessed or owned) after that
    // block.  This means we should have the invariant that if `internal` is `Unused`, then
    // `blocks_escaped` should be empty.
    //
    // For a fate attached to a syntactic construct (e.g. a variable occurrence) residing in a
    // particular block, this set might contain blocks which are neither the current block nor
    // parents of the current block.  These are harmless, but are also almost always irrelevant.
    pub blocks_escaped: OrdSet<LetBlockId>,
    pub ret_destinations: OrdSet<alias::RetName>,
}

impl FieldFate {
    pub fn new() -> Self {
        FieldFate {
            internal: InternalFate::Unused,
            last_internal_use: event::Horizon::new(),
            blocks_escaped: OrdSet::new(),
            ret_destinations: OrdSet::new(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ArgFieldFate {
    pub internal: InternalFate,
    pub ret_destinations: OrdSet<alias::RetName>,
}

#[derive(Clone, Debug)]
pub struct Fate {
    pub fates: BTreeMap<alias::FieldPath, FieldFate>,
}

impl Fate {
    pub fn new() -> Self {
        Fate {
            fates: BTreeMap::new(),
        }
    }
}

// TODO: Remove this struct.  We can remove the `fate` field here entirely (we only need it for the
// `ExprKind::Call` case), and we can merge the `event` field here into the `Expr` struct.
#[derive(Clone, Debug)]
pub struct ExprAnnot {
    pub fate: Fate,
    pub event: event::Horizon,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: anon::Type,
    pub ret_type: anon::Type,
    pub alias_sig: alias::AliasSig,
    pub mutation_sig: mutation::MutationSig,
    pub arg_fate: BTreeMap<alias::ArgName, ArgFieldFate>,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument.
    pub body: Expr,
    pub occur_fates: IdVec<OccurId, Fate>,
    pub expr_annots: IdVec<ExprId, ExprAnnot>,
    pub num_calls: usize,
    pub num_retain_points: usize,
    pub let_block_end_events: IdVec<LetBlockId, event::Horizon>,
    pub branch_block_end_events: IdVec<BranchBlockId, event::Horizon>,
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
