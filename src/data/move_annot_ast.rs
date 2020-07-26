use im_rc::OrdMap;
use std::collections::BTreeMap;

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::fate_annot_ast::{CallId, OccurId};
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as mutation;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::graph::Scc;
use crate::util::id_vec::IdVec;

id_type!(pub FuncVersionId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Local(pub OccurId, pub flat::LocalId);

#[derive(Clone, Copy, Debug)]
pub enum ArithOp {
    Op(first_ord::NumType, first_ord::BinOp, Local, Local),
    Cmp(first_ord::NumType, first_ord::Comparison, Local, Local),
    Negate(first_ord::NumType, Local),
}

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
        Purity,
        first_ord::CustomFuncId,
        CallId,
        // Aliases from argument fields (keys) to other names in scope (values) (which may
        // potentially also be fields of the argument)
        OrdMap<alias::FieldPath, alias::LocalAliases>,
        // Folded aliases for each argument fold point
        OrdMap<alias::FieldPath, alias::FoldedAliases>,
        // Statuses of argument fields prior to call
        OrdMap<alias::FieldPath, mutation::LocalStatus>,
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
    WrapBoxed(Local, anon::Type),
    UnwrapBoxed(Local, anon::Type),
    WrapCustom(first_ord::CustomTypeId, Local),
    UnwrapCustom(first_ord::CustomTypeId, Local),

    ArithOp(ArithOp),
    ArrayOp(ArrayOp),
    IoOp(IoOp),

    ArrayLit(anon::Type, Vec<Local>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum OccurMode {
    Move,
    MightBorrow,
}

#[derive(Clone, Debug)]
pub struct OccurModes {
    pub occur_modes: BTreeMap<alias::FieldPath, OccurMode>,
}

#[derive(Clone, Debug)]
pub struct FuncVersion {
    pub occurs: IdVec<OccurId, OccurModes>,
    pub calls: IdVec<CallId, FuncVersionId>,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: anon::Type,
    pub ret_type: anon::Type,
    pub mutation_sig: mutation::MutationSig,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument.
    pub body: Expr,
    pub versions: IdVec<FuncVersionId, FuncVersion>,
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
