use im_rc::{OrdMap, OrdSet, Vector};

use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::purity::Purity;
use crate::util::id_vec::IdVec;
use crate::util::norm_pair::NormPair;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Field {
    Field(usize),
    Variant(first_ord::VariantId),
    Custom(first_ord::CustomTypeId),
    ArrayMembers,
}

pub type FieldPath = Vector<Field>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ArgName(pub FieldPath);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RetName(pub FieldPath);

/// Every name has a 'precision status' indicating whether alias analysis was able to precisely
/// analyze its aliasing relationships.
///
/// Alias analysis guarantees that if it is possible for two names to alias at runtime (assuming no
/// aliasing among argument names), and if at least one of those names is marked 'precise', then the
/// alias graph will include an edge between those names.
///
/// However, alias analysis makes *no guarantees* about the existence of edges between names both of
/// which are marked 'imprecise'.  This means that even if there is no edge between two 'imprecise'
/// names, it is still possible they may alias at runtime.
///
/// We include this flag as an 'escape hatch' to cope with uncommon edge cases where a more precise
/// analysis would be prohibitively complex.  In particular, we mark names as imprecise when it
/// would otherwise be necessary to model aliasing relationships *between* elements of an array or a
/// recursive data structure.  For example, when analyzing this expression:
///
///     let inner = [1, 2, 3] in
///     let outer = [inner, inner] in
///     ...
///
/// we mark the name `outer.ArrayMembers` as 'imprecise' to avoid needing to explicitly model the
/// edge between the first and second elements of `outer`.
///
/// Imprecision statuses are represented symbolically, as they may depend on contextual information
/// from outside the current function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Precision {
    // An unconditionally precise status is represented by an empty ImpreciseIfAny set.
    ImpreciseIfAny(OrdSet<ImprecisionClause>),
    UnconditionallyImprecise,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ImprecisionClause {
    ImpreciseIfAliased(NormPair<ArgName>),
    ImpreciseIfArgImprecise(ArgName),
}

/// Represents the aliasing edges incident on an abstract heap cell, in a scope, under the condition
/// that none of the fields within the argument to the current function alias each other.
#[derive(Clone, Debug)]
pub struct LocalAliases {
    pub edges: OrdSet<(flat::LocalId, FieldPath)>,
    pub precision: Precision,
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Item(
        first_ord::Type, // Item type
        LocalAliases,    // Array aliases
        flat::LocalId,   // Array
        flat::LocalId,   // Index
    ), // Returns tuple of (item, hole array)
    Len(
        first_ord::Type, // Item type
        LocalAliases,    // Array aliases
        flat::LocalId,   // Array
    ),
    Push(
        first_ord::Type, // Item type
        LocalAliases,    // Array aliases
        flat::LocalId,   // Array
        flat::LocalId,   // Item
    ), // Returns new array
    Pop(
        first_ord::Type, // Item type
        LocalAliases,    // Array aliases
        flat::LocalId,   // Array
    ), // Returns tuple (array, item)
    Replace(
        first_ord::Type, // Item type
        LocalAliases,    // Hole array aliases
        flat::LocalId,   // Hole array
        flat::LocalId,   // Item
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum IOOp {
    Input, // Returns byte array
    Output(
        LocalAliases,  // Byte array aliases
        flat::LocalId, // Byte array
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
        OrdMap<FieldPath, LocalAliases>,
        flat::LocalId, // Argument
    ),
    Branch(flat::LocalId, Vec<(flat::Condition, Expr)>, first_ord::Type),
    LetMany(
        Vec<(first_ord::Type, Expr)>, // bound values.  Each is assigned a new sequential LocalId
        flat::LocalId,                // body
    ),

    Tuple(Vec<flat::LocalId>),
    TupleField(first_ord::LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, anon::Type>,
        first_ord::VariantId,
        flat::LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, flat::LocalId),
    WrapCustom(first_ord::CustomTypeId, flat::LocalId),
    UnwrapCustom(first_ord::CustomTypeId, flat::LocalId),

    ArithOp(flat::ArithOp),
    ArrayOp(ArrayOp),
    IOOp(IOOp),

    ArrayLit(first_ord::Type, Vec<flat::LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

/// Represents the aliasing edges incident on an abstract heap cell within the return value of a
/// function, under the condition that none of the fields within the argument to the function alias
/// each other.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnAliases {
    pub arg_edges: OrdSet<ArgName>,
    pub ret_edges: OrdSet<RetName>,
    pub precision: Precision,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: first_ord::Type,
    pub ret_type: first_ord::Type,
    // Aliases from return value fields (keys) to argument and return value fields (values)
    pub ret_field_aliases: OrdMap<RetName, ReturnAliases>,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument.
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<first_ord::CustomTypeId, anon::Type>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub main: first_ord::CustomFuncId,
}
