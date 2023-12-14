use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::{id_type, IdVec};
use std::cmp::{Ordering, PartialOrd};
use std::collections::HashSet;
use std::hash::Hash;

#[id_type]
pub struct LifetimeVar(pub usize);
#[id_type]
pub struct LifetimeParam(pub usize);
#[id_type]
pub struct ModeVar(pub usize);
#[id_type]
pub struct ModeParam(pub usize);

/// We compute the least solution to our constraints where `Borrowed` < `Owned`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModeTerm {
    Owned,
    Borrowed,
    Join(NonemptySet<ModeVar>),
}

impl ModeTerm {
    pub fn var(v: ModeVar) -> Self {
        Self::Join(NonemptySet::new(v))
    }
}

/// A constraint of the form `self.0 <= self.1`
#[derive(Debug, Clone, Copy)]
pub struct ModeConstr(pub ModeVar, pub ModeVar);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LocalLifetime {
    Final,
    Let(Box<LocalLifetime>),
    In(Box<LocalLifetime>),
    Match(Box<LocalLifetime>, Box<LocalLifetime>),
    Matchl(Box<LocalLifetime>),
    Matchr(Box<LocalLifetime>),
}

impl LocalLifetime {
    fn join(&self, other: &Self) -> Self {
        use LocalLifetime::*;
        match (self, other) {
            (Final, Final) => Final,
            (Let(l1), Let(l2)) => Let(Box::new(l1.join(l2))),
            (In(l1), In(l2)) => In(Box::new(l1.join(l2))),
            (Let(_), In(_)) => other.clone(),
            (In(_), Let(_)) => self.clone(),
            (Match(l1, r1), Match(l2, r2)) => Match(Box::new(l1.join(l2)), Box::new(r1.join(r2))),
            (Matchl(l1), Matchl(l2)) => Matchl(Box::new(l1.join(l2))),
            (Matchr(l1), Matchr(l2)) => Matchr(Box::new(l1.join(l2))),
            _ => Final,
        }
    }
}

impl PartialOrd for LocalLifetime {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use LocalLifetime::*;
        match (self, other) {
            (Final, Final) => Some(Ordering::Equal),
            (Let(l1), Let(l2)) => l1.partial_cmp(l2),
            (In(l1), In(l2)) => l1.partial_cmp(l2),
            (Let(_), In(_)) => Some(Ordering::Less),
            (In(_), Let(_)) => Some(Ordering::Greater),
            (Match(l1, r1), Match(l2, r2)) => l1.partial_cmp(l2).and_then(|o| {
                if o == Ordering::Equal {
                    r1.partial_cmp(r2)
                } else {
                    Some(o)
                }
            }),
            (Matchl(l1), Matchl(l2)) => l1.partial_cmp(l2),
            (Matchr(l1), Matchr(l2)) => l1.partial_cmp(l2),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lifetime {
    Empty,
    Local(LocalLifetime),
    Join(NonemptySet<LifetimeVar>),
}

impl Lifetime {
    pub fn var(v: LifetimeVar) -> Self {
        Self::Join(NonemptySet::new(v))
    }
}

impl PartialOrd for Lifetime {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Lifetime::*;
        match (self, other) {
            (Empty, Empty) => Some(Ordering::Equal),
            (Local(l1), Local(l2)) => l1.partial_cmp(l2),
            (Join(ltvs1), Join(ltvs2)) => {
                if ltvs1.is_subset(ltvs2) {
                    Some(Ordering::Less)
                } else if ltvs2.is_subset(ltvs1) {
                    Some(Ordering::Greater)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub enum ArrayOp<Mode, Lt> {
    Get(
        Type<Mode, Lt>, // Item type
        flat::LocalId,  // Array
        flat::LocalId,  // Index
    ), // Returns item
    Extract(
        Type<Mode, Lt>, // Item type
        flat::LocalId,  // Array
        flat::LocalId,  // Index
    ), // Returns tuple of (item, hole array)
    Len(
        Type<Mode, Lt>, // Item type
        flat::LocalId,  // Array
    ), // Returns int
    Push(
        Type<Mode, Lt>, // Item type
        flat::LocalId,  // Array
        flat::LocalId,  // Item
    ), // Returns new array
    Pop(
        Type<Mode, Lt>, // Item type
        flat::LocalId,  // Array
    ), // Returns tuple (array, item)
    Replace(
        Type<Mode, Lt>, // Item type
        flat::LocalId,  // Hole array
        flat::LocalId,  // Item
    ), // Returns new array
    Reserve(
        Type<Mode, Lt>, // Item type
        flat::LocalId,  // Array
        flat::LocalId,  // Capacity
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum Expr<Mode, Lt> {
    Local(flat::LocalId),
    Call(Purity, first_ord::CustomFuncId, flat::LocalId),
    Branch(
        flat::LocalId,
        Vec<(Condition<Mode, Lt>, Expr<Mode, Lt>)>,
        Type<Mode, Lt>,
    ),
    LetMany(
        Vec<(Type<Mode, Lt>, Expr<Mode, Lt>)>, // bound values.  Each is assigned a new sequential flat::LocalId
        flat::LocalId,                         // body
    ),

    Tuple(Vec<flat::LocalId>),
    TupleField(flat::LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type<Mode, Lt>>,
        first_ord::VariantId,
        flat::LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, flat::LocalId),
    WrapBoxed(
        flat::LocalId,
        Type<Mode, Lt>, // Inner type
    ),
    UnwrapBoxed(
        flat::LocalId,
        Type<Mode, Lt>, // Inner type
    ),
    WrapCustom(first_ord::CustomTypeId, flat::LocalId),
    UnwrapCustom(first_ord::CustomTypeId, flat::LocalId),

    Intrinsic(Intrinsic, flat::LocalId),
    ArrayOp(ArrayOp<Mode, Lt>),
    IoOp(flat::IoOp),
    Panic(Type<Mode, Lt>, flat::LocalId),

    ArrayLit(Type<Mode, Lt>, Vec<flat::LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub enum Condition<Mode, Lt> {
    Any,
    Tuple(Vec<Condition<Mode, Lt>>),
    Variant(first_ord::VariantId, Box<Condition<Mode, Lt>>),
    Boxed(
        Box<Condition<Mode, Lt>>,
        Type<Mode, Lt>, // Inner type
    ),
    Custom(first_ord::CustomTypeId, Box<Condition<Mode, Lt>>),
    BoolConst(bool),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Annot<Mode, Lt> {
    pub lifetime: Lt,
    pub mode: Mode,
    pub intrinsic_ty: IntrinsicType<Mode>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<Mode, Lt> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Type<Mode, Lt>>),
    Variants(IdVec<first_ord::VariantId, Type<Mode, Lt>>),
    Custom(
        first_ord::CustomTypeId,
        IdVec<ModeParam, Mode>,   // Substitution for mode parameters
        IdVec<LifetimeParam, Lt>, // Substitution for lifetime parameters
    ),

    // Types with mode variables
    Array(Box<Type<Mode, Lt>>, Annot<Mode, Lt>),
    HoleArray(Box<Type<Mode, Lt>>, Annot<Mode, Lt>),
    Boxed(Box<Type<Mode, Lt>>, Annot<Mode, Lt>),
}

/// "Intrinsic" as opposed to "extrinsic", not "intrinsic" as in a "compiler built-in"
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntrinsicType<Mode> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<IntrinsicType<Mode>>),
    Variants(IdVec<first_ord::VariantId, IntrinsicType<Mode>>),
    Custom(first_ord::CustomTypeId, IdVec<ModeParam, Mode>),

    // Types with mode variables
    Array(Box<IntrinsicType<Mode>>, Mode),
    HoleArray(Box<IntrinsicType<Mode>>, Mode),
    Boxed(Box<IntrinsicType<Mode>>, Mode),
}

pub type SolverType = Type<ModeVar, LifetimeVar>;
pub type SolverIntrinsicType = IntrinsicType<ModeVar>;
pub type SolverExpr = Expr<ModeVar, LifetimeVar>;

pub type ExternalType = Type<ModeParam, LifetimeParam>;
pub type ExternalIntrinsicType = IntrinsicType<ModeParam>;
pub type ExternalExpr = Expr<ModeParam, LifetimeParam>;

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,

    // The total number of mode (resp. lifetime) parameters in `arg_type` and `ret_type`
    pub num_mode_params: usize,
    pub num_lifetime_params: usize,
    pub arg_type: ExternalType,
    pub ret_type: ExternalType,
    pub constrs: Vec<ModeConstr>,

    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument
    pub body: flat::Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct CustomTypeDef {
    pub num_mode_params: usize,
    pub num_lifetime_params: usize,
    pub content: ExternalType,
    pub scc: flat::CustomTypeSccId,
}

#[derive(Clone, Debug)]
pub struct CustomTypes {
    pub types: IdVec<first_ord::CustomTypeId, CustomTypeDef>,
    pub sccs: IdVec<flat::CustomTypeSccId, Vec<first_ord::CustomTypeId>>,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NonemptySet<T: Eq + Hash>(HashSet<T>);

impl<T: Eq + Hash> NonemptySet<T> {
    pub fn new(x: T) -> Self {
        Self(std::iter::once(x).collect())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        self.0.is_subset(&other.0)
    }

    pub fn insert(&mut self, x: T) {
        self.0.insert(x);
    }
}
