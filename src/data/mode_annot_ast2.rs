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
    Join(NonEmptySet<ModeVar>),
}

impl ModeTerm {
    pub fn var(v: ModeVar) -> Self {
        Self::Join(NonEmptySet::new(v))
    }
}

/// A constraint of the form `self.0 <= self.1`.
#[derive(Debug, Clone, Copy)]
pub struct ModeConstr(pub ModeVar, pub ModeVar);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lt {
    Empty,
    Local(LtLocal),
    Join(NonEmptySet<LifetimeVar>),
}

impl Lt {
    pub fn var(v: LifetimeVar) -> Self {
        Self::Join(NonEmptySet::new(v))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LtLocal {
    Nil,
    Seq(Box<LtLocal>, usize),
    Par(LtPar),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LtPar(Vec<Option<LtLocal>>);

impl LtPar {
    fn new(l: LtLocal, i: usize, n: usize) -> Self {
        let mut v = vec![None; n];
        v[i] = Some(l);
        Self(v)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NonEmptySet<T: Eq + Hash>(HashSet<T>);

impl<T: Eq + Hash> NonEmptySet<T> {
    fn new(x: T) -> Self {
        let mut s = HashSet::new();
        s.insert(x);
        Self(s)
    }

    fn insert(&mut self, t: T) {
        self.0.insert(t);
    }

    fn union(&mut self, other: Self) {
        self.0.extend(other.0);
    }

    fn is_subset(&self, other: &Self) -> bool {
        self.0.is_subset(&other.0)
    }
}

impl Lt {
    /// A lattice join compatible with the `PartialOrd` implementation for `Lt`.
    fn join(&mut self, other: Self) {
        match (self, other) {
            (me @ Lt::Empty, other) => *me = other,
            (_, Lt::Empty) => {}
            (Lt::Local(l1), Lt::Local(l2)) => l1.join(l2),
            (me @ Lt::Local(_), other @ Lt::Join(_)) => *me = other,
            (Lt::Join(_), Lt::Local(_)) => {}
            (Lt::Join(s1), Lt::Join(s2)) => s1.union(s2),
        }
    }

    /// `l1 <= l2` iff, for every leaf in `l1`, there is a leaf in `l2` that occurs "later in time".
    /// Defines a partial order.
    fn is_subsumed_by(&self, other: &Self) -> bool {
        match (self, other) {
            (Lt::Empty, _) => true,
            (_, Lt::Empty) => false,
            (Lt::Local(l1), Lt::Local(l2)) => l1.is_subsumed_by(l2),
            (Lt::Local(_), Lt::Join(_)) => true,
            (Lt::Join(_), Lt::Local(_)) => false,
            (Lt::Join(s1), Lt::Join(s2)) => s1.is_subset(s2),
        }
    }

    /// True iff no leaf in `self` occurs "later in time" than any leaf in `other`. This condition
    /// is non-transitive.
    fn does_not_exceed(&self, other: &Self) -> bool {
        match (self, other) {
            (Lt::Empty, _) => true,
            (_, Lt::Empty) => true,
            (Lt::Local(l1), Lt::Local(l2)) => l1.does_not_exceed(l2),
            (Lt::Local(_), Lt::Join(_)) => true,
            (Lt::Join(_), Lt::Local(_)) => false,
            (Lt::Join(s1), Lt::Join(s2)) => s1.is_subset(s2),
        }
    }
}

impl LtLocal {
    fn join(&mut self, other: Self) {
        match (self, other) {
            (me @ LtLocal::Nil, other) => *me = other,
            (_, LtLocal::Nil) => {}
            (me @ LtLocal::Seq(_, _), other @ LtLocal::Seq(_, _)) => {
                let i1 = if let LtLocal::Seq(_, i) = me {
                    *i
                } else {
                    unreachable!()
                };
                let i2 = if let LtLocal::Seq(_, i) = &other {
                    *i
                } else {
                    unreachable!()
                };
                if i1 < i2 {
                    *me = other;
                } else if i1 == i2 {
                    me.join(other);
                }
            }
            (LtLocal::Seq(_, _), LtLocal::Par(_)) => {
                panic!("expected structurally compatible lifetimes")
            }
            (LtLocal::Par(_), LtLocal::Seq(_, _)) => {
                panic!("expected structurally compatible lifetimes")
            }
            (LtLocal::Par(p1), LtLocal::Par(p2)) => p1.join(p2),
        }
    }

    fn is_subsumed_by(&self, other: &Self) -> bool {
        match (self, other) {
            (LtLocal::Nil, _) => false,
            (_, LtLocal::Nil) => true,
            (LtLocal::Seq(l1, i1), LtLocal::Seq(l2, i2)) => {
                if i1 < i2 {
                    true
                } else if i1 > i2 {
                    false
                } else {
                    l1.is_subsumed_by(l2)
                }
            }
            (LtLocal::Seq(_, _), LtLocal::Par(_)) => {
                panic!("expected structurally compatible lifetimes")
            }
            (LtLocal::Par(_), LtLocal::Seq(_, _)) => {
                panic!("expected structurally compatible lifetimes")
            }
            (LtLocal::Par(p1), LtLocal::Par(p2)) => p1.is_subsumed_by(p2),
        }
    }

    fn does_not_exceed(&self, other: &Self) -> bool {
        match (self, other) {
            (LtLocal::Nil, _) => false,
            (_, LtLocal::Nil) => true,
            (LtLocal::Seq(l1, i1), LtLocal::Seq(l2, i2)) => {
                if i1 < i2 {
                    true
                } else if i1 > i2 {
                    false
                } else {
                    l1.does_not_exceed(l2)
                }
            }
            (LtLocal::Seq(_, _), LtLocal::Par(_)) => {
                panic!("expected structurally compatible lifetimes")
            }
            (LtLocal::Par(_), LtLocal::Seq(_, _)) => {
                panic!("expected structurally compatible lifetimes")
            }
            (LtLocal::Par(p1), LtLocal::Par(p2)) => p1.does_not_exceed(p2),
        }
    }
}

impl LtPar {
    fn join(&mut self, other: Self) {
        if self.0.len() != other.0.len() {
            panic!("expected structurally compatible lifetimes");
        }
        for (l1, l2) in self.0.iter_mut().zip(other.0.into_iter()) {
            match (l1, l2) {
                (None, None) => {}
                (me @ None, other @ Some(_)) => *me = other,
                (Some(_), None) => {}
                (Some(l1), Some(l2)) => l1.join(l2),
            }
        }
    }

    fn is_subsumed_by(&self, other: &Self) -> bool {
        if self.0.len() != other.0.len() {
            panic!("expected structurally compatible lifetimes");
        }
        for (l1, l2) in self.0.iter().zip(other.0.iter()) {
            match (l1, l2) {
                (Some(_), None) => {
                    return false;
                }
                (Some(l1), Some(l2)) => {
                    if !l1.is_subsumed_by(l2) {
                        return false;
                    }
                }
                _ => {}
            }
        }
        true
    }

    fn does_not_exceed(&self, other: &Self) -> bool {
        if self.0.len() != other.0.len() {
            panic!("expected structurally compatible lifetimes");
        }
        for (l1, l2) in self.0.iter().zip(other.0.iter()) {
            if let (Some(l1), Some(l2)) = (l1, l2) {
                if !l1.does_not_exceed(l2) {
                    return false;
                }
            }
        }
        true
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
