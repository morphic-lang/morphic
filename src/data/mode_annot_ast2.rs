use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::Count;
use id_collections::{id_type, IdVec};
use std::collections::HashSet;
use std::hash::Hash;

#[id_type]
pub struct LtVar(pub usize);

#[id_type]
pub struct LtParam(pub usize);

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
    /// Non-empty to ensure lifetime representations are unique.
    Join(NonEmptySet<LtVar>),
}

impl Lt {
    pub fn var(v: LtVar) -> Self {
        Self::Join(NonEmptySet::new(v))
    }
}

/// `Seq` corresponds to a set of ordered operations, for instance the binding and body of a let.
/// `Par` corresponds to a set of unordered operations, for instance the arms of a match.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LtLocal {
    Final,
    Seq(Box<LtLocal>, usize),
    Par(LtPar),
}

// Must be non-empty to ensure lifetime representations are unique.
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
    /// A join over the following lattice: `l1 <= l2` iff, for every leaf of `l1`, there is a leaf
    /// of `l2` that occurs "later in time".
    ///
    /// Panics if `self` and `other` are not structurally compatible.
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

    /// True iff no leaf in `self` occurs "later in time" than any leaf in `other`. This condition
    /// is non-transitive.
    ///
    /// Panics if `self` and `other` are not structurally compatible.
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
            (LtLocal::Final, _) => {}
            (me, LtLocal::Final) => *me = LtLocal::Final,
            (me @ LtLocal::Seq(_, _), other @ LtLocal::Seq(_, _)) => {
                // We need to set `me` to `other` if `i1 < i2`, which means we can't destructure
                // `me` and `other` in the match arm.
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

    fn does_not_exceed(&self, other: &Self) -> bool {
        match (self, other) {
            (LtLocal::Final, _) => false,
            (_, LtLocal::Final) => true,
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
pub enum ArrayOp<M, L> {
    Get(
        Type<M, L>,    // Item type
        flat::LocalId, // Array
        flat::LocalId, // Index
    ), // Returns item
    Extract(
        Type<M, L>,    // Item type
        flat::LocalId, // Array
        flat::LocalId, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        Type<M, L>,    // Item type
        flat::LocalId, // Array
    ), // Returns int
    Push(
        Type<M, L>,    // Item type
        flat::LocalId, // Array
        flat::LocalId, // Item
    ), // Returns new array
    Pop(
        Type<M, L>,    // Item type
        flat::LocalId, // Array
    ), // Returns tuple (array, item)
    Replace(
        Type<M, L>,    // Item type
        flat::LocalId, // Hole array
        flat::LocalId, // Item
    ), // Returns new array
    Reserve(
        Type<M, L>,    // Item type
        flat::LocalId, // Array
        flat::LocalId, // Capacity
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum Expr<M, L> {
    Local(flat::LocalId),
    Call(Purity, first_ord::CustomFuncId, flat::LocalId),
    Branch(
        flat::LocalId,
        Vec<(Condition<M, L>, Expr<M, L>)>,
        Type<M, L>,
    ),
    LetMany(
        Vec<(Type<M, L>, Expr<M, L>)>, // bound values.  Each is assigned a new sequential flat::LocalId
        flat::LocalId,                 // body
    ),

    Tuple(Vec<flat::LocalId>),
    TupleField(flat::LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type<M, L>>,
        first_ord::VariantId,
        flat::LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, flat::LocalId),
    WrapBoxed(
        flat::LocalId,
        Type<M, L>, // Inner type
    ),
    UnwrapBoxed(
        flat::LocalId,
        Type<M, L>, // Inner type
    ),
    WrapCustom(first_ord::CustomTypeId, flat::LocalId),
    UnwrapCustom(first_ord::CustomTypeId, flat::LocalId),

    Intrinsic(Intrinsic, flat::LocalId),
    ArrayOp(ArrayOp<M, L>),
    IoOp(flat::IoOp),
    Panic(Type<M, L>, flat::LocalId),

    ArrayLit(Type<M, L>, Vec<flat::LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub enum Condition<M, L> {
    Any,
    Tuple(Vec<Condition<M, L>>),
    Variant(first_ord::VariantId, Box<Condition<M, L>>),
    Boxed(
        Box<Condition<M, L>>,
        Type<M, L>, // Inner type
    ),
    Custom(first_ord::CustomTypeId, Box<Condition<M, L>>),
    BoolConst(bool),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModeAnnot<M, L> {
    pub lifetime: L,
    pub mode: M,
    pub intrinsic_type: IntrinsicType<M, L>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<M, L> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Type<M, L>>),
    Variants(IdVec<first_ord::VariantId, Type<M, L>>),
    Custom(
        first_ord::CustomTypeId,
        IdVec<ModeParam, M>, // Substitution for mode parameters
        IdVec<LtParam, L>,   // Substitution for lifetime parameters
    ),

    // Types with attached modes
    Array(Box<Type<M, L>>, ModeAnnot<M, L>),
    HoleArray(Box<Type<M, L>>, ModeAnnot<M, L>),
    Boxed(Box<Type<M, L>>, ModeAnnot<M, L>),
}

// "Intrinsic" as in describing the contents of the heap itself, rather than its relation to other
// objects (not "intrinsic" as in "builtin")
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntrinsicType<M, L> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<IntrinsicType<M, L>>),
    Variants(IdVec<first_ord::VariantId, IntrinsicType<M, L>>),
    Custom(
        first_ord::CustomTypeId,
        IdVec<ModeParam, M>, // Substitution for mode parameters
        IdVec<LtParam, L>,   // Substitution for lifetime parameters
    ),

    // Types with attached modes
    Array(Box<IntrinsicType<M, L>>, M),
    HoleArray(Box<IntrinsicType<M, L>>, M),
    Boxed(Box<IntrinsicType<M, L>>, M),
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,

    // The total number of mode (resp. lifetime) parameters in `arg_type` and `ret_type`
    pub num_mode_params: Count<ModeParam>,
    pub num_lt_params: Count<LtParam>,
    pub arg_type: Type<ModeParam, LtParam>,
    pub ret_type: Type<ModeParam, LtParam>,
    pub constrs: Vec<ModeConstr>,

    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument
    pub body: Expr<ModeParam, LtParam>,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct CustomTypeDef {
    pub num_mode_params: Count<ModeParam>,
    pub num_lt_params: Count<LtParam>,
    pub content: Type<ModeParam, LtParam>,
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
