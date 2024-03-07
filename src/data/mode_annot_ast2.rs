use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::{id_type, Count, Id, IdVec};
use std::collections::BTreeSet;
use std::hash::Hash;

// Notes:
// - have instantiate return a dictionary of updates?
// - for let-many, make sure to clone Gamma(x) at the right time

#[id_type]
pub struct LtParam(pub usize);

#[id_type]
pub struct ModeParam(pub usize);

/// We compute the least solution to our constraints where `Borrowed` < `Owned`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModeTerm<M: Id> {
    Owned,
    Borrowed,
    Join(BTreeSet<M>), // Always non-empty
}

impl<M: Id> ModeTerm<M> {
    pub fn var(x: M) -> Self {
        let mut set = BTreeSet::new();
        set.insert(x);
        ModeTerm::Join(set)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum PathElem {
    Seq(usize),
    Par { i: usize, n: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Path(im_rc::Vector<PathElem>);

impl Path {
    pub fn new() -> Self {
        Self(im_rc::Vector::new())
    }

    pub fn push_seq(&self, i: usize) -> Self {
        let mut elems = self.0.clone();
        elems.push_back(PathElem::Seq(i));
        Self(elems)
    }

    pub fn push_par(&self, i: usize, n: usize) -> Self {
        let mut elems = self.0.clone();
        elems.push_back(PathElem::Par { i, n });
        Self(elems)
    }

    pub fn as_lt<L>(&self) -> Lt<L> {
        let mut res = LocalLt::Final;
        for elem in self.0.iter().rev() {
            match elem {
                PathElem::Seq(i) => {
                    res = LocalLt::Seq(Box::new(res), *i);
                }
                PathElem::Par { i, n } => {
                    let mut par = vec![None; *n];
                    par[*i] = Some(res);
                    res = LocalLt::Par(par);
                }
            }
        }
        Lt::Local(res)
    }
}

/// A constraint of the form `self.0 <= self.1`.
#[derive(Debug, Clone, Copy)]
pub struct ModeLteConstr(pub ModeParam, pub ModeParam);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lt<L> {
    Empty,
    Local(LocalLt),
    Join(BTreeSet<L>), // Always non-empty
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LocalLt {
    Final,
    // For ordered "events", e.g. the binding and body of a let.
    Seq(Box<LocalLt>, usize),
    // For unordered "events", e.g. the arms of a match.
    // Always contains at lest one `Some`.
    Par(Vec<Option<LocalLt>>),
}

impl<L> Lt<L>
where
    L: Ord + Eq + Clone,
{
    pub fn var(x: L) -> Self {
        let mut set = BTreeSet::new();
        set.insert(x);
        Lt::Join(set)
    }

    /// A join over the following lattice: `l1 <= l2` iff, for every leaf of `l1`, there is a leaf
    /// of `l2` that occurs "later in time".
    ///
    /// Panics if `self` and `other` are not structurally compatible.
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Lt::Empty, l) => l.clone(),
            (l, Lt::Empty) => l.clone(),
            (Lt::Local(l1), Lt::Local(l2)) => Lt::Local(l1.join(l2)),
            (Lt::Local(_), Lt::Join(s)) => Lt::Join(s.clone()),
            (Lt::Join(s), Lt::Local(_)) => Lt::Join(s.clone()),
            (Lt::Join(s1), Lt::Join(s2)) => Lt::Join(s1 | s2),
        }
    }

    /// True iff no leaf of `self` occurs "later in time" than any leaf of `other`. This condition
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

impl LocalLt {
    pub fn join(&self, rhs: &Self) -> Self {
        match (self, rhs) {
            (LocalLt::Final, _) => LocalLt::Final,
            (_, LocalLt::Final) => LocalLt::Final,
            (LocalLt::Seq(l1, i1), LocalLt::Seq(l2, i2)) => {
                if i1 < i2 {
                    LocalLt::Seq(l2.clone(), *i2)
                } else if i2 > i1 {
                    LocalLt::Seq(l1.clone(), *i1)
                } else {
                    LocalLt::Seq(Box::new(l1.join(&**l2)), *i1)
                }
            }
            (LocalLt::Par(p1), LocalLt::Par(p2)) => {
                if p1.len() != p2.len() {
                    panic!("expected structurally compatible lifetimes");
                }
                LocalLt::Par(
                    p1.iter()
                        .zip(p2.iter())
                        .map(|(l1, l2)| match (l1, l2) {
                            (None, None) => None,
                            (None, Some(l2)) => Some(l2.clone()),
                            (Some(l1), None) => Some(l1.clone()),
                            (Some(l1), Some(l2)) => Some(l1.join(l2)),
                        })
                        .collect(),
                )
            }
            (LocalLt::Seq(_, _), LocalLt::Par(_)) | (LocalLt::Par(_), LocalLt::Seq(_, _)) => {
                panic!("expected structurally compatible lifetimes");
            }
        }
    }

    fn seq_idx(&self) -> usize {
        match self {
            LocalLt::Seq(_, i) => *i,
            _ => panic!("expected Seq"),
        }
    }

    fn does_not_exceed(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (LocalLt::Final, _) => false,
            (_, LocalLt::Final) => true,
            (LocalLt::Seq(l1, i1), LocalLt::Seq(l2, i2)) => {
                if i1 < i2 {
                    true
                } else if i1 > i2 {
                    false
                } else {
                    l1.does_not_exceed(l2)
                }
            }
            (LocalLt::Par(p1), LocalLt::Par(p2)) => {
                if p1.len() != p2.len() {
                    panic!("expected structurally compatible lifetimes");
                }
                for (l1, l2) in p1.iter().zip(p2.iter()) {
                    if let (Some(l1), Some(l2)) = (l1, l2) {
                        if !l1.does_not_exceed(l2) {
                            return false;
                        }
                    }
                }
                return true;
            }
            _ => {
                panic!("expected structurally compatible lifetimes");
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum ArrayOp<M: Id, L> {
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
pub enum Expr<M: Id, L> {
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
pub enum Condition<M: Id, L> {
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
pub enum Overlay<M: Id> {
    Unmanaged,  // For types which are alwayed copied, e.g. Bool
    Managed(M), // For types which are rc'ed, e.g. Array
    Custom(IdVec<ModeParam, M>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<M: Id, L> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Type<M, L>>),
    Variants(IdVec<first_ord::VariantId, Type<M, L>>),
    Custom {
        id: first_ord::CustomTypeId,
        mode_subst: IdVec<ModeParam, M>,
        lt_subst: IdVec<LtParam, L>,
        overlay: Overlay<M>,
    },
    Array {
        content: Box<Type<M, L>>,
        mode: ModeTerm<M>,
        lt: Lt<L>,
        overlay: Overlay<M>,
    },
    HoleArray {
        content: Box<Type<M, L>>,
        mode: ModeTerm<M>,
        lt: Lt<L>,
        overlay: Overlay<M>,
    },
    Boxed {
        content: Box<Type<M, L>>,
        mode: ModeTerm<M>,
        lt: Lt<L>,
        overlay: Overlay<M>,
    },
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,

    // Total number of params in `arg_type` and `ret_type`
    pub num_mode_params: Count<ModeParam>,
    pub num_lt_params: Count<LtParam>,
    pub arg_type: Type<ModeParam, LtParam>,
    pub ret_type: Type<ModeParam, LtParam>,
    pub constrs: Vec<ModeLteConstr>,

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
