use im_rc::{OrdMap, Vector};

use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::purity::Purity;
use crate::util::disjunction::Disj;
use crate::util::graph::Scc;
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SubPath(pub FieldPath);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldedAliases {
    pub inter_elem_aliases: OrdMap<NormPair<SubPath>, Disj<AliasCondition>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AliasCondition {
    AliasInArg(NormPair<ArgName>),
    FoldedAliasInArg(
        ArgName, // Path to fold point
        NormPair<SubPath>,
    ),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalAliases {
    pub aliases: OrdMap<(flat::LocalId, FieldPath), Disj<AliasCondition>>,
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Item(
        anon::Type,    // Item type
        LocalAliases,  // Array aliases
        flat::LocalId, // Array
        flat::LocalId, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        anon::Type,    // Item type
        LocalAliases,  // Array aliases
        flat::LocalId, // Array
    ),
    Push(
        anon::Type,    // Item type
        LocalAliases,  // Array aliases
        flat::LocalId, // Array
        flat::LocalId, // Item
    ), // Returns new array
    Pop(
        anon::Type,    // Item type
        LocalAliases,  // Array aliases
        flat::LocalId, // Array
    ), // Returns tuple (array, item)
    Replace(
        anon::Type,    // Item type
        LocalAliases,  // Hole array aliases
        flat::LocalId, // Hole array
        flat::LocalId, // Item
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
        // Folded aliases for each argument fold point
        OrdMap<FieldPath, FoldedAliases>,
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
    WrapCustom(first_ord::CustomTypeId, flat::LocalId),
    UnwrapCustom(first_ord::CustomTypeId, flat::LocalId),

    ArithOp(flat::ArithOp),
    ArrayOp(ArrayOp),
    IOOp(IOOp),

    ArrayLit(anon::Type, Vec<flat::LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AliasSig {
    // Aliases from return value fields (keys) to argument and return value fields (values)
    pub ret_arg_aliases: OrdMap<RetName, OrdMap<ArgName, Disj<AliasCondition>>>,
    // Aliases between return value fields
    pub ret_ret_aliases: OrdMap<NormPair<RetName>, Disj<AliasCondition>>,
    // Folded aliases at each return value fold point
    pub ret_folded_aliases: OrdMap<RetName, FoldedAliases>,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: anon::Type,
    pub ret_type: anon::Type,
    pub alias_sig: AliasSig,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument.
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<first_ord::CustomTypeId, anon::Type>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub main: first_ord::CustomFuncId,

    // It is not strictly necessary to store the SCCs here, as they can be recomputed from `funcs`.
    // However, we will need the SCCs again in several subsequent compiler passes (during which the
    // call graph topology does not change), so it is easiest and most efficient to cache them here.
    pub sccs: Vec<Scc<first_ord::CustomFuncId>>,
}
