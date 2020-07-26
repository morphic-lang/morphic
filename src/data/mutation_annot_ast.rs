use im_rc::OrdMap;

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::disjunction::Disj;
use crate::util::graph::Scc;
use crate::util::id_vec::IdVec;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MutationCondition {
    AliasCondition(alias::AliasCondition),
    ArgMutated(alias::ArgName),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalStatus {
    pub mutated_cond: Disj<MutationCondition>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrayOp {
    Item(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        LocalStatus,         // Array status
        flat::LocalId,       // Array
        flat::LocalId,       // Index
    ), // Returns tuple of (item, hole array)
    Len(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        LocalStatus,         // Array status
        flat::LocalId,       // Array
    ),
    Push(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        LocalStatus,         // Array status
        flat::LocalId,       // array
        flat::LocalId,       // Item
    ),
    Pop(
        anon::Type,          // Item type
        alias::LocalAliases, // Array aliases
        LocalStatus,         // Array status
        flat::LocalId,       // Array
    ), // Returns tuple of (array, item)
    Replace(
        anon::Type,          // Item type
        alias::LocalAliases, // Hole array aliases
        LocalStatus,         // Hole array status
        flat::LocalId,       // Hole array
        flat::LocalId,       // Item
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input, // Returns byte array
    Output(
        alias::LocalAliases, // Byte array aliases
        LocalStatus,         // Byte array statuses
        flat::LocalId,       // Byte array
    ), // Returns unit
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(flat::LocalId),
    Call(
        Purity,
        first_ord::CustomFuncId,
        // Aliases from argument fields (keys) to other names in scope (values) (which may
        // potentially also be fields of the argument)
        OrdMap<alias::FieldPath, alias::LocalAliases>,
        // Folded aliases for each argument fold point
        OrdMap<alias::FieldPath, alias::FoldedAliases>,
        // Statuses of argument fields prior to call
        OrdMap<alias::FieldPath, LocalStatus>,
        flat::LocalId, // Argument
    ),
    Branch(flat::LocalId, Vec<(flat::Condition, Expr)>, anon::Type),
    LetMany(
        Vec<(anon::Type, Expr)>, // bound values.  Each is assigned a new sequential LocalId
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
        anon::Type, // Inner type
    ),
    WrapCustom(first_ord::CustomTypeId, flat::LocalId),
    UnwrapCustom(first_ord::CustomTypeId, flat::LocalId),

    ArithOp(flat::ArithOp),
    ArrayOp(ArrayOp),
    IoOp(IoOp),

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
    pub mutation_sig: MutationSig,
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
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<first_ord::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: first_ord::CustomFuncId,

    pub sccs: Vec<Scc<first_ord::CustomFuncId>>,
}
