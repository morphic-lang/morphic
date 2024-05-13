//! The output AST for the specializing variant of the borrow inference pass.
//!
//! There are a few notable differences from the paper:
//! - The AST is in A-normal form.
//! - We use nomial types ("custom" types) instead of mu types.
//! - In addition to the `Boxed` type (which is a plain reference counted allocation), we have the
//!   `Array` and `HoleArray` types, which require similar treatment during borrow inference because
//!   they have embedded reference counts.

use crate::data::first_order_ast::{self as first_ord, CustomTypeId};
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::inequality_graph2 as in_eq;
use crate::util::iter::IterExt;
use crate::util::map_ext::{btree_map_refs, Map};
use crate::util::non_empty_set::NonEmptySet;
use id_collections::{id_type, Count, IdVec};
use std::collections::BTreeMap;
use std::hash::Hash;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    Borrowed,
    Owned,
}

impl in_eq::BoundedSemilattice for Mode {
    fn join_mut(&mut self, other: &Self) {
        *self = (*self).max(*other);
    }

    fn least() -> Self {
        Mode::Borrowed
    }
}

/// During constraint generation, modes are represented using `ModeVar`s.
#[id_type]
pub struct ModeVar(pub usize);

/// Solved constraints written in terms of `ModeParam`s.
#[id_type]
pub struct ModeParam(pub usize);

/// Solution `lb` for variable `solver_var` (the latter of which we keep around for debugging).
#[derive(Debug, Clone)]
pub struct ModeSolution {
    pub lb: in_eq::LowerBound<ModeParam, Mode>,
    pub solver_var: ModeVar,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PathElem {
    Seq(usize),
    Par { i: usize, n: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Path(im_rc::Vector<PathElem>);

impl Path {
    pub fn root() -> Self {
        Self(im_rc::Vector::new())
    }

    pub fn seq(&self, i: usize) -> Self {
        let mut elems = self.0.clone();
        elems.push_back(PathElem::Seq(i));
        Self(elems)
    }

    pub fn par(&self, i: usize, n: usize) -> Self {
        let mut elems = self.0.clone();
        elems.push_back(PathElem::Par { i, n });
        Self(elems)
    }

    /// An iterator over the elements of path from root to leaf.
    fn elems(&self) -> impl Iterator<Item = PathElem> + '_ {
        self.0.iter().copied().rev()
    }

    pub fn as_local_lt(&self) -> LocalLt {
        let mut result = LocalLt::Final;
        for elem in self.elems() {
            match elem {
                PathElem::Seq(i) => {
                    result = LocalLt::Seq(Box::new(result), i);
                }
                PathElem::Par { i, n } => {
                    let mut par = vec![None; n];
                    par[i] = Some(result);
                    result = LocalLt::Par(par);
                }
            }
        }
        result
    }

    pub fn as_lt(&self) -> Lt {
        Lt::Local(self.as_local_lt())
    }
}

#[id_type]
pub struct LtParam(pub usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lt {
    Empty,
    Local(LocalLt),
    Join(NonEmptySet<LtParam>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LocalLt {
    Final,
    // Represents ordered "events", e.g. the binding and body of a let.
    Seq(Box<LocalLt>, usize),
    // Represents unordered "events", e.g. the arms of a match. Always contains at least one `Some`.
    Par(Vec<Option<LocalLt>>),
}

impl Lt {
    pub fn var(x: LtParam) -> Self {
        Lt::Join(NonEmptySet::new(x))
    }

    /// A join over the lifetime lattice: `l1 <= l2` iff, for every leaf of `l1`, there is a leaf of
    /// `l2` that occurs "later in time".
    ///
    /// Panics if `self` and `other` are not structurally compatible.
    pub fn join(&mut self, other: &Self) {
        match (self, other) {
            (_, Lt::Empty) => {}
            (l1 @ Lt::Empty, l2) => *l1 = l2.clone(),
            (Lt::Local(l1), Lt::Local(l2)) => l1.join(l2),
            (Lt::Join(_), Lt::Local(_)) => {}
            (l1 @ Lt::Local(_), Lt::Join(s)) => *l1 = Lt::Join(s.clone()),
            (Lt::Join(s1), Lt::Join(s2)) => s1.extend(s2.iter().copied()),
        }
    }

    /// True iff no leaf of `self` occurs "later in time" than `other`. This condition is
    /// reflexive, but non-transitive.
    ///
    /// Panics if `self` and `other` are not structurally compatible.
    pub fn does_not_exceed(&self, other: &Path) -> bool {
        match (self, other) {
            (Lt::Empty, _) => true,
            (Lt::Local(l), p) => l.does_not_exceed(p),
            (Lt::Join(_), _) => false,
        }
    }
}

impl LocalLt {
    pub fn join(&mut self, other: &Self) {
        match (self, other) {
            (LocalLt::Final, _) => {}
            (l1, LocalLt::Final) => *l1 = LocalLt::Final,
            (LocalLt::Seq(l1, i1), LocalLt::Seq(l2, i2)) => {
                if *i1 < *i2 {
                    *l1 = l2.clone();
                    *i1 = *i2;
                } else if i1 == i2 {
                    l1.join(l2);
                }
            }
            (LocalLt::Par(p1), LocalLt::Par(p2)) => {
                for (l1, l2) in p1.iter_mut().zip_eq(p2) {
                    match (l1, l2) {
                        (None, None) => {}
                        (Some(_), None) => {}
                        (l1 @ None, Some(l2)) => *l1 = Some(l2.clone()),
                        (Some(l1), Some(l2)) => l1.join(l2),
                    }
                }
            }
            _ => panic!("incompatible lifetimes"),
        }
    }

    pub fn does_not_exceed(&self, rhs: &Path) -> bool {
        let mut lhs = self;
        for elem in rhs.elems() {
            match (lhs, elem) {
                (LocalLt::Final, _) => {
                    return false;
                }
                (LocalLt::Seq(inner, i1), PathElem::Seq(i2)) => {
                    if *i1 < i2 {
                        return true;
                    } else if *i1 > i2 {
                        return false;
                    } else {
                        lhs = inner;
                        continue;
                    }
                }
                (LocalLt::Par(par), PathElem::Par { i, n }) => {
                    if par.len() != n {
                        panic!("incompatible lifetimes");
                    }
                    match &par[i] {
                        None => {
                            return true;
                        }
                        Some(inner) => {
                            lhs = inner;
                            continue;
                        }
                    }
                }
                _ => {
                    panic!("incompatible lifetimes");
                }
            }
        }
        // If we reach the end of `rhs`, then `rhs` is a prefix of or equal to `self` along the
        // relevant branch. Hence, `self` points to a subscope of the scope pointed to by `rhs`.
        true
    }
}

#[id_type]
pub struct CustomSlotId(pub usize);

#[id_type]
pub struct SlotId(pub usize);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Overlay<I> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Overlay<I>>),
    Variants(IdVec<first_ord::VariantId, Overlay<I>>),
    SelfCustom(CustomTypeId),
    Custom(CustomTypeId, BTreeMap<CustomSlotId, I>),
    Array(I),
    HoleArray(I),
    Boxed(I),
}

pub fn remap_ov(
    ov: &Overlay<CustomSlotId>,
    map: &impl Map<K = CustomSlotId, V = SlotId>,
) -> Overlay<SlotId> {
    match ov {
        Overlay::Bool => Overlay::Bool,
        Overlay::Num(n) => Overlay::Num(*n),
        Overlay::Tuple(ovs) => Overlay::Tuple(ovs.iter().map(|ov| remap_ov(ov, map)).collect()),
        Overlay::Variants(ovs) => Overlay::Variants(ovs.map_refs(|_, ov| remap_ov(ov, map))),
        Overlay::SelfCustom(id) => Overlay::SelfCustom(*id),
        Overlay::Custom(id, ovs) => {
            Overlay::Custom(*id, btree_map_refs(ovs, |_, slot| *map.get(slot).unwrap()))
        }
        Overlay::Array(slot) => Overlay::Array(*map.get(slot).unwrap()),
        Overlay::HoleArray(slot) => Overlay::HoleArray(*map.get(slot).unwrap()),
        Overlay::Boxed(slot) => Overlay::Boxed(*map.get(slot).unwrap()),
    }
}

#[derive(Clone, Debug)]
pub struct AnnotOverlay<A> {
    pub ov: Overlay<SlotId>,
    pub data: BTreeMap<SlotId, A>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<I> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Type<I>>),
    Variants(IdVec<first_ord::VariantId, Type<I>>),
    SelfCustom(CustomTypeId),
    Custom(
        CustomTypeId,
        BTreeMap<CustomSlotId, I>, // Overlay
        IdVec<CustomSlotId, I>,    // Substitution
    ),
    Array(I, Overlay<I>, Box<Type<I>>),
    HoleArray(I, Overlay<I>, Box<Type<I>>),
    Boxed(I, Overlay<I>, Box<Type<I>>),
}

impl<I: Copy> Type<I> {
    pub fn as_ov(&self, customs: &CustomTypes) -> Overlay<I> {
        match self {
            Type::Bool => Overlay::Bool,
            Type::Num(n) => Overlay::Num(*n),
            Type::Tuple(tys) => Overlay::Tuple(tys.iter().map(|ty| ty.as_ov(customs)).collect()),
            Type::Variants(tys) => Overlay::Variants(tys.map_refs(|_, ty| ty.as_ov(customs))),
            Type::SelfCustom(id) => Overlay::SelfCustom(*id),
            Type::Custom(id, ov_subst, _) => Overlay::Custom(*id, ov_subst.clone()),
            Type::Array(slot, _, _) => Overlay::Array(*slot),
            Type::HoleArray(slot, _, _) => Overlay::HoleArray(*slot),
            Type::Boxed(slot, _, _) => Overlay::Boxed(*slot),
        }
    }
}

pub fn remap_ty(ty: &Type<CustomSlotId>, map: &IdVec<CustomSlotId, SlotId>) -> Type<SlotId> {
    match ty {
        Type::Bool => Type::Bool,
        Type::Num(n) => Type::Num(*n),
        Type::Tuple(tys) => Type::Tuple(tys.iter().map(|ty| remap_ty(ty, map)).collect()),
        Type::Variants(tys) => Type::Variants(tys.map_refs(|_, ty| remap_ty(ty, map))),
        Type::SelfCustom(id) => Type::SelfCustom(*id),
        Type::Custom(id, ov_subst, ty_subst) => {
            let ty_subst = ty_subst.map_refs(|_, slot| map[*slot]);
            let ov_subst = btree_map_refs(ov_subst, |_, slot| map[*slot]);
            Type::Custom(*id, ov_subst, ty_subst)
        }
        Type::Array(slot, ov, ty) => {
            Type::Array(map[*slot], remap_ov(ov, map), Box::new(remap_ty(ty, map)))
        }
        Type::HoleArray(slot, ov, ty) => {
            Type::HoleArray(map[*slot], remap_ov(ov, map), Box::new(remap_ty(ty, map)))
        }
        Type::Boxed(slot, ov, ty) => {
            Type::Boxed(map[*slot], remap_ov(ov, map), Box::new(remap_ty(ty, map)))
        }
    }
}

#[derive(Clone, Debug)]
pub struct AnnotType<A, B> {
    pub ty: Type<SlotId>,
    pub ms: BTreeMap<SlotId, A>,
    pub ls: BTreeMap<SlotId, B>,
}

/// Returns the meet of two types over the lifetime lattice. This meet is "left" in the sense that
/// the modes of the first argument are retained.
pub fn left_meet<M>(this: &mut AnnotType<M, Lt>, other: &AnnotType<M, Lt>) {
    debug_assert_eq!(this.ty, other.ty);
    for (l1, l2) in this.ls.values_mut().zip_eq(other.ls.values()) {
        l1.join(l2);
    }
}

#[derive(Clone, Debug)]
pub struct Occur<M, L> {
    pub id: flat::LocalId,
    pub ty: AnnotType<M, L>,
}

#[derive(Clone, Debug)]
pub enum ArrayOp<M, L> {
    Get(
        AnnotType<M, L>, // Item type (of input)
        Occur<M, L>,     // Array
        Occur<M, L>,     // Index
        AnnotType<M, L>, // Return type; needed for retain/release insertion
    ), // Returns item
    Extract(
        AnnotType<M, L>, // Item type (of input)
        Occur<M, L>,     // Array
        Occur<M, L>,     // Index
    ), // Returns tuple of (item, hole array)
    Len(
        AnnotType<M, L>, // Item type (of input)
        Occur<M, L>,     // Array
    ), // Returns int
    Push(
        AnnotType<M, L>, // Item type (of input)
        Occur<M, L>,     // Array
        Occur<M, L>,     // Item
    ), // Returns new array
    Pop(
        AnnotType<M, L>, // Item type (of input)
        Occur<M, L>,     // Array
    ), // Returns tuple (array, item)
    Replace(
        AnnotType<M, L>, // Item type (of input)
        Occur<M, L>,     // Hole array
        Occur<M, L>,     // Item
    ), // Returns new array
    Reserve(
        AnnotType<M, L>, // Item type (of input)
        Occur<M, L>,     // Array
        Occur<M, L>,     // Capacity
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum IoOp<M, L> {
    Input,               // Returns array of bytes
    Output(Occur<M, L>), // Takes array of bytes, returns unit
}

#[derive(Clone, Debug)]
pub enum Expr<M, L> {
    Local(Occur<M, L>),
    Call(Purity, first_ord::CustomFuncId, Occur<M, L>),
    Branch(
        Occur<M, L>,
        Vec<(Condition<M, L>, Expr<M, L>)>,
        AnnotType<M, L>,
    ),
    LetMany(
        Vec<(AnnotType<M, L>, Expr<M, L>)>, // Bound values; each is assigned a new sequential `LocalId`
        Occur<M, L>,                        // Result
    ),

    Tuple(Vec<Occur<M, L>>),
    TupleField(Occur<M, L>, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, AnnotType<M, L>>,
        first_ord::VariantId,
        Occur<M, L>,
    ),
    UnwrapVariant(first_ord::VariantId, Occur<M, L>),
    WrapBoxed(
        Occur<M, L>,
        AnnotType<M, L>, // Inner type
    ),
    UnwrapBoxed(
        Occur<M, L>,
        AnnotType<M, L>, // Inner type
    ),
    WrapCustom(CustomTypeId, Occur<M, L>),
    UnwrapCustom(CustomTypeId, Occur<M, L>),

    Intrinsic(Intrinsic, Occur<M, L>),
    ArrayOp(ArrayOp<M, L>),
    IoOp(IoOp<M, L>),
    Panic(AnnotType<M, L>, Occur<M, L>),

    ArrayLit(AnnotType<M, L>, Vec<Occur<M, L>>),
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
        AnnotType<M, L>, // Inner type
    ),
    Custom(CustomTypeId, Box<Condition<M, L>>),
    BoolConst(bool),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

/// `sig` stores all the constraints on the mode parameters of the function signature. We also keep
/// around a copy of all constraints generated during inference in `all` for debugging.
#[derive(Clone, Debug)]
pub struct Constrs {
    pub sig: IdVec<ModeParam, in_eq::LowerBound<ModeParam, Mode>>,
    pub all: in_eq::ConstrGraph<ModeVar, Mode>,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_ty: AnnotType<ModeParam, Lt>,
    pub ret_ty: AnnotType<ModeParam, LtParam>,
    pub constrs: Constrs,

    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument
    pub body: Expr<ModeSolution, Lt>,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    // `ov` is computable from `ty`, but kept around for convenience
    pub ty: Type<CustomSlotId>,
    pub ov: Overlay<CustomSlotId>,
    pub num_slots: Count<CustomSlotId>,
    pub num_overlay_slots: Count<CustomSlotId>,
}

#[derive(Clone, Debug)]
pub struct CustomTypes {
    pub types: IdVec<CustomTypeId, TypeDef>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: CustomTypes,
    pub custom_type_symbols: IdVec<CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<first_ord::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: first_ord::CustomFuncId,
}
