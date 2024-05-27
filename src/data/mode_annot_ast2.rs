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
use id_collections::{id_type, Count, Id, IdVec};
use std::collections::{BTreeMap, BTreeSet};
use std::hash::Hash;
use std::iter;

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
    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Lt::Empty, l) | (l, Lt::Empty) => l.clone(),
            (Lt::Local(l1), Lt::Local(l2)) => Lt::Local(l1.join(l2)),
            (Lt::Join(s), Lt::Local(_)) | (Lt::Local(_), Lt::Join(s)) => Lt::Join(s.clone()),
            (Lt::Join(s1), Lt::Join(s2)) => Lt::Join(s1 | s2),
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
    pub fn join(&self, rhs: &Self) -> Self {
        match (self, rhs) {
            (LocalLt::Final, _) | (_, LocalLt::Final) => LocalLt::Final,
            (LocalLt::Seq(l1, i1), LocalLt::Seq(l2, i2)) => {
                if i1 < i2 {
                    LocalLt::Seq(l2.clone(), *i2)
                } else if i2 > i1 {
                    LocalLt::Seq(l1.clone(), *i1)
                } else {
                    LocalLt::Seq(Box::new(l1.join(l2)), *i1)
                }
            }
            (LocalLt::Par(p1), LocalLt::Par(p2)) => LocalLt::Par(
                p1.iter()
                    .zip_eq(p2.iter())
                    .map(|(l1, l2)| match (l1, l2) {
                        (None, None) => None,
                        (None, Some(l)) | (Some(l), None) => Some(l.clone()),
                        (Some(l1), Some(l2)) => Some(l1.join(l2)),
                    })
                    .collect(),
            ),
            (LocalLt::Seq(_, _), LocalLt::Par(_)) | (LocalLt::Par(_), LocalLt::Seq(_, _)) => {
                panic!("incompatible lifetimes");
            }
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
pub struct SlotId(pub usize);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OverlayShape<I> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<OverlayShape<I>>),
    Variants(IdVec<first_ord::VariantId, OverlayShape<I>>),
    SelfCustom(I),
    Custom(I, BTreeSet<SlotId>),
    Array,
    HoleArray,
    Boxed,
}

#[derive(Clone, Debug)]
pub enum Overlay2<I, T> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Overlay2<I, T>>),
    Variants(IdVec<first_ord::VariantId, Overlay2<I, T>>),
    SelfCustom(I),
    Custom(I, BTreeMap<SlotId, T>),
    Array(T),
    HoleArray(T),
    Boxed(T),
}

pub type Overlay<T> = Overlay2<CustomTypeId, T>;

impl<I: Id> Overlay2<I, SlotId> {
    pub fn hydrate<T: Clone>(&self, subst: &impl Map<K = SlotId, V = T>) -> Overlay2<I, T> {
        match self {
            Overlay2::Bool => Overlay2::Bool,
            Overlay2::Num(n) => Overlay2::Num(*n),
            Overlay2::Tuple(ovs) => {
                Overlay2::Tuple(ovs.iter().map(|ov| ov.hydrate(subst)).collect())
            }
            Overlay2::Variants(ovs) => Overlay2::Variants(ovs.map_refs(|_, ov| ov.hydrate(subst))),
            Overlay2::SelfCustom(id) => Overlay2::SelfCustom(*id),
            Overlay2::Custom(id, old_subst) => Overlay2::Custom(
                *id,
                btree_map_refs(old_subst, |_, slot| subst.get(slot).unwrap().clone()),
            ),
            Overlay2::Array(slot) => Overlay2::Array(subst.get(slot).unwrap().clone()),
            Overlay2::HoleArray(slot) => Overlay2::HoleArray(subst.get(slot).unwrap().clone()),
            Overlay2::Boxed(slot) => Overlay2::Boxed(subst.get(slot).unwrap().clone()),
        }
    }
}

impl<I: Id, T> Overlay2<I, T> {
    // Must produce the order expected by `collect_overlay`
    pub fn iter(&self) -> Box<dyn Iterator<Item = &T> + '_> {
        match self {
            Overlay2::Bool => Box::new(iter::empty()),
            Overlay2::Num(_) => Box::new(iter::empty()),
            Overlay2::Tuple(ovs) => Box::new(ovs.iter().flat_map(Overlay2::iter)),
            Overlay2::Variants(ovs) => Box::new(ovs.values().flat_map(Overlay2::iter)),
            Overlay2::SelfCustom(_) => Box::new(iter::empty()),
            Overlay2::Custom(_, ov) => Box::new(ov.values()),
            Overlay2::Array(x) => Box::new(iter::once(x)),
            Overlay2::HoleArray(x) => Box::new(iter::once(x)),
            Overlay2::Boxed(x) => Box::new(iter::once(x)),
        }
    }

    pub fn shape(&self) -> OverlayShape<I> {
        match self {
            Overlay2::Bool => OverlayShape::Bool,
            Overlay2::Num(n) => OverlayShape::Num(*n),
            Overlay2::Tuple(ovs) => OverlayShape::Tuple(ovs.iter().map(Overlay2::shape).collect()),
            Overlay2::Variants(ovs) => OverlayShape::Variants(ovs.map_refs(|_, ov| ov.shape())),
            Overlay2::SelfCustom(id) => OverlayShape::SelfCustom(*id),
            Overlay2::Custom(id, subst) => {
                OverlayShape::Custom(*id, subst.keys().copied().collect())
            }
            Overlay2::Array(_) => OverlayShape::Array,
            Overlay2::HoleArray(_) => OverlayShape::HoleArray,
            Overlay2::Boxed(_) => OverlayShape::Boxed,
        }
    }

    pub fn is_zero_sized_or_self(&self, customs: &IdVec<I, TypeDef2<I>>) -> bool {
        match self {
            Overlay2::Bool => false,
            Overlay2::Num(_) => false,
            Overlay2::Tuple(ovs) => ovs.iter().all(|ov| ov.is_zero_sized_or_self(customs)),
            Overlay2::Variants(ovs) => ovs.values().all(|ov| ov.is_zero_sized_or_self(customs)),
            Overlay2::SelfCustom(_) => true,
            Overlay2::Custom(id, _) => customs[*id].ov.is_zero_sized_or_self(customs),
            Overlay2::Array(_) => false,
            Overlay2::HoleArray(_) => false,
            Overlay2::Boxed(_) => false,
        }
    }
}

pub trait CollectOverlay<T> {
    fn collect_overlay<I: Id, U>(self, orig: &Overlay2<I, U>) -> Overlay2<I, T>;
}

impl<T, J: Iterator<Item = T>> CollectOverlay<T> for J {
    fn collect_overlay<I: Id, U>(mut self, orig: &Overlay2<I, U>) -> Overlay2<I, T> {
        collect_overlay(&mut self, orig)
    }
}

// Must expect the order produced by `Overlay::iter`
fn collect_overlay<I: Id, T, U>(
    iter: &mut impl Iterator<Item = T>,
    orig: &Overlay2<I, U>,
) -> Overlay2<I, T> {
    match orig {
        Overlay2::Bool => Overlay2::Bool,
        Overlay2::Num(n) => Overlay2::Num(*n),
        Overlay2::Tuple(ovs) => {
            Overlay2::Tuple(ovs.iter().map(|ov| collect_overlay(iter, ov)).collect())
        }
        Overlay2::Variants(ovs) => {
            Overlay2::Variants(ovs.map_refs(|_, ov| collect_overlay(iter, ov)))
        }
        Overlay2::SelfCustom(id) => Overlay2::SelfCustom(*id),
        Overlay2::Custom(id, subst) => {
            Overlay2::Custom(*id, btree_map_refs(subst, |_, _| iter.next().unwrap()))
        }
        Overlay2::Array(_) => Overlay2::Array(iter.next().unwrap()),
        Overlay2::HoleArray(_) => Overlay2::HoleArray(iter.next().unwrap()),
        Overlay2::Boxed(_) => Overlay2::Boxed(iter.next().unwrap()),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Shape<I> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Shape<I>>),
    Variants(IdVec<first_ord::VariantId, Shape<I>>),
    SelfCustom(I),
    Custom(I, BTreeSet<SlotId>),
    Array(Box<Shape<I>>),
    HoleArray(Box<Shape<I>>),
    Boxed(Box<Shape<I>>),
}

#[derive(Clone, Debug)]
pub enum LtData2<I, T> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<LtData2<I, T>>),
    Variants(IdVec<first_ord::VariantId, LtData2<I, T>>),
    SelfCustom(I),
    Custom(I, BTreeMap<SlotId, T>),
    Array(T, Box<LtData2<I, T>>),
    HoleArray(T, Box<LtData2<I, T>>),
    Boxed(T, Box<LtData2<I, T>>),
}

pub type LtData<T> = LtData2<CustomTypeId, T>;

impl<I: Id> LtData2<I, SlotId> {
    pub fn hydrate<T: Clone>(&self, subst: &impl Map<K = SlotId, V = T>) -> LtData2<I, T> {
        match self {
            LtData2::Bool => LtData2::Bool,
            LtData2::Num(n) => LtData2::Num(*n),
            LtData2::Tuple(lts) => LtData2::Tuple(lts.iter().map(|lt| lt.hydrate(subst)).collect()),
            LtData2::Variants(lts) => LtData2::Variants(lts.map_refs(|_, lt| lt.hydrate(subst))),
            LtData2::SelfCustom(id) => LtData2::SelfCustom(*id),
            LtData2::Custom(id, old_subst) => LtData2::Custom(
                *id,
                btree_map_refs(old_subst, |_, slot| subst.get(slot).unwrap().clone()),
            ),
            LtData2::Array(slot, lt) => LtData2::Array(
                subst.get(slot).unwrap().clone(),
                Box::new(lt.hydrate(subst)),
            ),
            LtData2::HoleArray(slot, lt) => LtData2::HoleArray(
                subst.get(slot).unwrap().clone(),
                Box::new(lt.hydrate(subst)),
            ),
            LtData2::Boxed(slot, lt) => LtData2::Boxed(
                subst.get(slot).unwrap().clone(),
                Box::new(lt.hydrate(subst)),
            ),
        }
    }
}

impl<I: Id> LtData2<I, Lt> {
    pub fn join(&self, other: &LtData2<I, Lt>) -> LtData2<I, Lt> {
        debug_assert!(self.shape() == other.shape());
        self.iter()
            .zip_eq(other.iter())
            .map(|(lt1, lt2)| lt1.join(lt2))
            .collect_lt_data(self)
    }
}

impl<I: Id, T> LtData2<I, T> {
    // Must produce the order expected by `collect_lt_data`
    pub fn iter(&self) -> Box<dyn Iterator<Item = &T> + '_> {
        match self {
            LtData2::Bool => Box::new(iter::empty()),
            LtData2::Num(_) => Box::new(iter::empty()),
            LtData2::Tuple(lts) => Box::new(lts.iter().flat_map(LtData2::iter)),
            LtData2::Variants(lts) => Box::new(lts.values().flat_map(LtData2::iter)),
            LtData2::SelfCustom(_) => Box::new(iter::empty()),
            LtData2::Custom(_, subst) => Box::new(subst.values()),
            LtData2::Array(lt, item) => Box::new(iter::once(lt).chain(item.iter())),
            LtData2::HoleArray(lt, item) => Box::new(iter::once(lt).chain(item.iter())),
            LtData2::Boxed(lt, item) => Box::new(iter::once(lt).chain(item.iter())),
        }
    }

    pub fn iter_overlay<'a>(
        &'a self,
        customs: &'a IdVec<I, TypeDef2<I>>,
    ) -> Box<dyn Iterator<Item = &'a T> + 'a> {
        match self {
            LtData2::Bool => Box::new(iter::empty()),
            LtData2::Num(_) => Box::new(iter::empty()),
            LtData2::Tuple(lts) => Box::new(lts.iter().flat_map(|lt| lt.iter_overlay(customs))),
            LtData2::Variants(lts) => {
                Box::new(lts.values().flat_map(|lt| lt.iter_overlay(customs)))
            }
            LtData2::SelfCustom(_) => Box::new(iter::empty()),
            LtData2::Custom(id, subst) => Box::new(
                customs[*id]
                    .ty
                    .lts()
                    .iter_overlay(customs)
                    .map(|slot| &subst[slot]),
            ),
            LtData2::Array(lt, _) => Box::new(iter::once(lt)),
            LtData2::HoleArray(lt, _) => Box::new(iter::once(lt)),
            LtData2::Boxed(lt, _) => Box::new(iter::once(lt)),
        }
    }

    pub fn shape(&self) -> Shape<I> {
        match self {
            LtData2::Bool => Shape::Bool,
            LtData2::Num(n) => Shape::Num(*n),
            LtData2::Tuple(lts) => Shape::Tuple(lts.iter().map(LtData2::shape).collect()),
            LtData2::Variants(lts) => Shape::Variants(lts.map_refs(|_, lt| lt.shape())),
            LtData2::SelfCustom(id) => Shape::SelfCustom(*id),
            LtData2::Custom(id, subst) => Shape::Custom(*id, subst.keys().copied().collect()),
            LtData2::Array(_, lt) => Shape::Array(Box::new(lt.shape())),
            LtData2::HoleArray(_, lt) => Shape::HoleArray(Box::new(lt.shape())),
            LtData2::Boxed(_, lt) => Shape::Boxed(Box::new(lt.shape())),
        }
    }
}

pub trait CollectLtData<T> {
    fn collect_lt_data<I: Id, U>(self, orig: &LtData2<I, U>) -> LtData2<I, T>;
}

impl<T, J: Iterator<Item = T>> CollectLtData<T> for J {
    fn collect_lt_data<I: Id, U>(mut self, orig: &LtData2<I, U>) -> LtData2<I, T> {
        collect_lt_data(&mut self, orig)
    }
}

// Must expect the order produced by `LtData::iter`
fn collect_lt_data<I: Id, T, U>(
    iter: &mut impl Iterator<Item = T>,
    orig: &LtData2<I, U>,
) -> LtData2<I, T> {
    match orig {
        LtData2::Bool => LtData2::Bool,
        LtData2::Num(n) => LtData2::Num(*n),
        LtData2::Tuple(items) => LtData2::Tuple(
            items
                .iter()
                .map(|item| collect_lt_data(iter, item))
                .collect(),
        ),
        LtData2::Variants(items) => {
            LtData2::Variants(items.map_refs(|_, item| collect_lt_data(iter, item)))
        }
        LtData2::SelfCustom(id) => LtData2::SelfCustom(*id),
        LtData2::Custom(id, subst) => {
            LtData2::Custom(*id, btree_map_refs(subst, |_, _| iter.next().unwrap()))
        }
        LtData2::Array(_, item) => {
            LtData2::Array(iter.next().unwrap(), Box::new(collect_lt_data(iter, item)))
        }
        LtData2::HoleArray(_, item) => {
            LtData2::HoleArray(iter.next().unwrap(), Box::new(collect_lt_data(iter, item)))
        }
        LtData2::Boxed(_, item) => {
            LtData2::Boxed(iter.next().unwrap(), Box::new(collect_lt_data(iter, item)))
        }
    }
}

#[derive(Clone, Debug)]
pub enum ModeData2<I, T> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<ModeData2<I, T>>),
    Variants(IdVec<first_ord::VariantId, ModeData2<I, T>>),
    SelfCustom(I),
    Custom(
        I,
        BTreeMap<SlotId, T>, // Overlay
        IdVec<SlotId, T>,    // Substitution
    ),
    Array(T, Overlay2<I, T>, Box<ModeData2<I, T>>),
    HoleArray(T, Overlay2<I, T>, Box<ModeData2<I, T>>),
    Boxed(T, Overlay2<I, T>, Box<ModeData2<I, T>>),
}

pub type ModeData<T> = ModeData2<CustomTypeId, T>;

impl<I: Id> ModeData2<I, SlotId> {
    pub fn hydrate<T: Clone>(&self, subst: &IdVec<SlotId, T>) -> ModeData2<I, T> {
        match self {
            ModeData2::Bool => ModeData2::Bool,
            ModeData2::Num(n) => ModeData2::Num(*n),
            ModeData2::Tuple(tys) => {
                ModeData2::Tuple(tys.iter().map(|ty| ty.hydrate(subst)).collect())
            }
            ModeData2::Variants(tys) => {
                ModeData2::Variants(tys.map_refs(|_, ty| ty.hydrate(subst)))
            }
            ModeData2::SelfCustom(id) => ModeData2::SelfCustom(*id),
            ModeData2::Custom(id, osub, tsub) => ModeData2::Custom(
                *id,
                btree_map_refs(osub, |_, slot| subst[*slot].clone()),
                tsub.map_refs(|_, slot| subst[*slot].clone()),
            ),
            ModeData2::Array(m, ov, ty) => ModeData2::Array(
                subst[*m].clone(),
                ov.hydrate(subst),
                Box::new(ty.hydrate(subst)),
            ),
            ModeData2::HoleArray(m, ov, ty) => ModeData2::HoleArray(
                subst[*m].clone(),
                ov.hydrate(subst),
                Box::new(ty.hydrate(subst)),
            ),
            ModeData2::Boxed(m, ov, ty) => ModeData2::Boxed(
                subst[*m].clone(),
                ov.hydrate(subst),
                Box::new(ty.hydrate(subst)),
            ),
        }
    }

    pub fn extract_lts(&self, customs: &impl Map<K = I, V = TypeDef2<I>>) -> LtData2<I, SlotId> {
        match self {
            ModeData2::Bool => LtData2::Bool,
            ModeData2::Num(n) => LtData2::Num(*n),
            ModeData2::Tuple(tys) => {
                LtData2::Tuple(tys.iter().map(|ty| ty.extract_lts(customs)).collect())
            }
            ModeData2::Variants(tys) => {
                LtData2::Variants(tys.map_refs(|_, ty| ty.extract_lts(customs)))
            }
            ModeData2::SelfCustom(id) => LtData2::SelfCustom(*id),
            ModeData2::Custom(id, _, subst) => {
                let custom = customs.get(id).unwrap();
                let subst = custom
                    .lt_slots
                    .iter()
                    .map(|&key| (key, subst[key]))
                    .collect();
                LtData2::Custom(*id, subst)
            }
            ModeData2::Array(slot, _, ty) => {
                LtData2::Array(*slot, Box::new(ty.extract_lts(customs)))
            }
            ModeData2::HoleArray(slot, _, ty) => {
                LtData2::HoleArray(*slot, Box::new(ty.extract_lts(customs)))
            }
            ModeData2::Boxed(slot, _, ty) => {
                LtData2::Boxed(*slot, Box::new(ty.extract_lts(customs)))
            }
        }
    }
}

impl<I: Id, T> ModeData2<I, T> {
    // Must produce the order expected by `collect_mode_data`
    pub fn iter(&self) -> Box<dyn Iterator<Item = &T> + '_> {
        match self {
            ModeData2::Bool => Box::new(iter::empty()),
            ModeData2::Num(_) => Box::new(iter::empty()),
            ModeData2::Tuple(tys) => Box::new(tys.iter().flat_map(ModeData2::iter)),
            ModeData2::Variants(tys) => Box::new(tys.values().flat_map(ModeData2::iter)),
            ModeData2::SelfCustom(_) => Box::new(iter::empty()),
            ModeData2::Custom(_, ov, tys) => Box::new(ov.values().chain(tys.values())),
            ModeData2::Array(m, ov, ty) => {
                Box::new(iter::once(m).chain(ov.iter()).chain(ty.iter()))
            }
            ModeData2::HoleArray(m, ov, ty) => {
                Box::new(iter::once(m).chain(ov.iter()).chain(ty.iter()))
            }
            ModeData2::Boxed(m, ov, ty) => {
                Box::new(iter::once(m).chain(ov.iter()).chain(ty.iter()))
            }
        }
    }

    pub fn iter_lts<'a>(
        &'a self,
        customs: &'a IdVec<I, TypeDef2<I>>,
    ) -> Box<dyn Iterator<Item = &'a T> + 'a> {
        match self {
            ModeData2::Bool => Box::new(iter::empty()),
            ModeData2::Num(_) => Box::new(iter::empty()),
            ModeData2::Tuple(tys) => Box::new(tys.iter().flat_map(|ty| ty.iter_lts(customs))),
            ModeData2::Variants(tys) => Box::new(tys.values().flat_map(|ty| ty.iter_lts(customs))),
            ModeData2::SelfCustom(_) => Box::new(iter::empty()),
            ModeData2::Custom(id, _, subst) => {
                let custom = customs[*id].ty.modes();
                Box::new(custom.iter_lts(customs).map(|slot| &subst[*slot]))
            }
            ModeData2::Array(m, _, ty) => Box::new(iter::once(m).chain(ty.iter_lts(customs))),
            ModeData2::HoleArray(m, _, ty) => Box::new(iter::once(m).chain(ty.iter_lts(customs))),
            ModeData2::Boxed(m, _, ty) => Box::new(iter::once(m).chain(ty.iter_lts(customs))),
        }
    }

    pub fn iter_overlay<'a>(&'a self) -> Box<dyn Iterator<Item = &'a T> + 'a> {
        match self {
            ModeData2::Bool => Box::new(iter::empty()),
            ModeData2::Num(_) => Box::new(iter::empty()),
            ModeData2::Tuple(tys) => Box::new(tys.iter().flat_map(|ty| ty.iter_overlay())),
            ModeData2::Variants(tys) => Box::new(tys.values().flat_map(|ty| ty.iter_overlay())),
            ModeData2::SelfCustom(_) => Box::new(iter::empty()),
            ModeData2::Custom(_, ov, _) => Box::new(ov.values()),
            ModeData2::Array(m, _, _) => Box::new(iter::once(m)),
            ModeData2::HoleArray(m, _, _) => Box::new(iter::once(m)),
            ModeData2::Boxed(m, _, _) => Box::new(iter::once(m)),
        }
    }

    pub fn apply_overlay(&self, ov: &Overlay2<I, T>) -> ModeData2<I, T>
    where
        T: Clone,
    {
        match (self, ov) {
            (ModeData2::Bool, Overlay2::Bool) => ModeData2::Bool,
            (ModeData2::Num(n1), Overlay2::Num(n2)) if n1 == n2 => ModeData2::Num(*n1),
            (ModeData2::Tuple(tys), Overlay2::Tuple(ovs)) => ModeData2::Tuple(
                tys.iter()
                    .zip_eq(ovs)
                    .map(|(ty, ov)| ty.apply_overlay(ov))
                    .collect(),
            ),
            (ModeData2::Variants(tys), Overlay2::Variants(ovs)) => {
                ModeData2::Variants(IdVec::from_vec(
                    tys.values()
                        .zip_eq(ovs.values())
                        .map(|(ty, ov)| ty.apply_overlay(ov))
                        .collect(),
                ))
            }
            (ModeData2::SelfCustom(id1), Overlay2::SelfCustom(id2)) if id1 == id2 => {
                ModeData2::SelfCustom(*id1)
            }
            (ModeData2::Custom(id1, ov1, subst), Overlay2::Custom(id2, ov2)) if id1 == id2 => {
                debug_assert!(ov1.keys().zip_eq(ov2.keys()).all(|(k1, k2)| k1 == k2));
                ModeData2::Custom(*id1, ov2.clone(), subst.clone())
            }
            (ModeData2::Array(_, _, ty), Overlay2::Array(m)) => {
                ModeData2::Array(m.clone(), ov.clone(), ty.clone())
            }
            (ModeData2::HoleArray(_, ov, ty), Overlay2::HoleArray(m)) => {
                ModeData2::HoleArray(m.clone(), ov.clone(), ty.clone())
            }
            (ModeData2::Boxed(_, ov, ty), Overlay2::Boxed(m)) => {
                ModeData2::Boxed(m.clone(), ov.clone(), ty.clone())
            }
            _ => panic!("type/overlay mismatch"),
        }
    }

    pub fn unapply_overlay(&self) -> Overlay2<I, T>
    where
        T: Clone,
    {
        match self {
            ModeData2::Bool => Overlay2::Bool,
            ModeData2::Num(n) => Overlay2::Num(*n),
            ModeData2::Tuple(tys) => {
                Overlay2::Tuple(tys.iter().map(ModeData2::unapply_overlay).collect())
            }
            ModeData2::Variants(tys) => {
                Overlay2::Variants(tys.map_refs(|_, ty| ty.unapply_overlay()))
            }
            ModeData2::SelfCustom(id) => Overlay2::SelfCustom(*id),
            ModeData2::Custom(id, ov, _) => Overlay2::Custom(*id, ov.clone()),
            ModeData2::Array(m, _, _) => Overlay2::Array(m.clone()),
            ModeData2::HoleArray(m, _, _) => Overlay2::HoleArray(m.clone()),
            ModeData2::Boxed(m, _, _) => Overlay2::Boxed(m.clone()),
        }
    }

    pub fn shape(&self) -> Shape<I> {
        match self {
            ModeData2::Bool => Shape::Bool,
            ModeData2::Num(n) => Shape::Num(*n),
            ModeData2::Tuple(tys) => Shape::Tuple(tys.iter().map(ModeData2::shape).collect()),
            ModeData2::Variants(tys) => Shape::Variants(tys.map_refs(|_, ty| ty.shape())),
            ModeData2::SelfCustom(id) => Shape::SelfCustom(*id),
            ModeData2::Custom(id, subst, _) => Shape::Custom(*id, subst.keys().copied().collect()),
            ModeData2::Array(_, _, ty) => Shape::Array(Box::new(ty.shape())),
            ModeData2::HoleArray(_, _, ty) => Shape::HoleArray(Box::new(ty.shape())),
            ModeData2::Boxed(_, _, ty) => Shape::Boxed(Box::new(ty.shape())),
        }
    }
}

pub trait CollectModeData<T> {
    fn collect_mode_data<I: Id, U>(self, orig: &ModeData2<I, U>) -> ModeData2<I, T>;
}

impl<T, J: Iterator<Item = T>> CollectModeData<T> for J {
    fn collect_mode_data<I: Id, U>(mut self, orig: &ModeData2<I, U>) -> ModeData2<I, T> {
        collect_mode_data(&mut self, orig)
    }
}

// Must expect the order produced by `ModeData::iter`
fn collect_mode_data<I: Id, T, U>(
    iter: &mut impl Iterator<Item = T>,
    orig: &ModeData2<I, U>,
) -> ModeData2<I, T> {
    match orig {
        ModeData2::Bool => ModeData2::Bool,
        ModeData2::Num(n) => ModeData2::Num(*n),
        ModeData2::Tuple(items) => ModeData2::Tuple(
            items
                .iter()
                .map(|item| collect_mode_data(iter, item))
                .collect(),
        ),
        ModeData2::Variants(items) => {
            ModeData2::Variants(items.map_refs(|_, item| collect_mode_data(iter, item)))
        }
        ModeData2::SelfCustom(id) => ModeData2::SelfCustom(*id),
        ModeData2::Custom(id, ov, subst) => ModeData2::Custom(
            *id,
            btree_map_refs(ov, |_, _| iter.next().unwrap()),
            subst.map_refs(|_, _| iter.next().unwrap()),
        ),
        ModeData2::Array(_, ov, item) => ModeData2::Array(
            iter.next().unwrap(),
            collect_overlay(iter, ov),
            Box::new(collect_mode_data(iter, item)),
        ),
        ModeData2::HoleArray(_, ov, item) => ModeData2::HoleArray(
            iter.next().unwrap(),
            collect_overlay(iter, ov),
            Box::new(collect_mode_data(iter, item)),
        ),
        ModeData2::Boxed(_, ov, item) => ModeData2::Boxed(
            iter.next().unwrap(),
            collect_overlay(iter, ov),
            Box::new(collect_mode_data(iter, item)),
        ),
    }
}

// We need to carry around an extra `I` parameter for RC specialization, which substitutes a fresh
// ID type to prevent the use of stale IDs.
#[derive(Clone, Debug)]
pub struct Type2<I, M, L> {
    lts: LtData2<I, L>,
    modes: ModeData2<I, M>,
}

pub type Type<M, L> = Type2<CustomTypeId, M, L>;

impl<I: Id> Type2<I, SlotId, SlotId> {
    pub fn hydrate<M: Clone, L: Clone>(
        &self,
        lt_subst: &BTreeMap<SlotId, L>,
        mode_subst: &IdVec<SlotId, M>,
    ) -> Type2<I, M, L> {
        Type2 {
            lts: self.lts.hydrate(lt_subst),
            modes: self.modes.hydrate(mode_subst),
        }
    }
}

impl<I: Id, M: Clone> Type2<I, M, Lt> {
    pub fn left_meet(&self, other: &Type2<I, M, Lt>) -> Type2<I, M, Lt> {
        Type2 {
            lts: self.lts.join(&other.lts),
            modes: self.modes.clone(),
        }
    }
}

impl<I: Id, M, L> Type2<I, M, L> {
    pub fn new(lts: LtData2<I, L>, modes: ModeData2<I, M>) -> Self {
        debug_assert!(lts.shape() == modes.shape());
        Self { lts, modes }
    }

    pub fn shape(&self) -> Shape<I> {
        self.modes.shape()
    }

    pub fn lts(&self) -> &LtData2<I, L> {
        &self.lts
    }

    pub fn lts_mut(&mut self) -> &mut LtData2<I, L> {
        &mut self.lts
    }

    pub fn modes(&self) -> &ModeData2<I, M> {
        &self.modes
    }

    pub fn modes_mut(&mut self) -> &mut ModeData2<I, M> {
        &mut self.modes
    }

    pub fn map_modes<N>(&self, f: impl Fn(&M) -> N) -> Type2<I, N, L>
    where
        L: Clone,
    {
        let lts = self.lts.clone();
        let modes = self.modes.iter().map(f).collect_mode_data(&self.modes);
        Type2 { lts, modes }
    }

    /// If `self` is `Array`, `HoleArray`, or `Boxed`, return the modes of the inner type.
    pub fn unwrap_item_modes(&self) -> &ModeData2<I, M> {
        match self.modes() {
            ModeData2::Array(_, _, item)
            | ModeData2::HoleArray(_, _, item)
            | ModeData2::Boxed(_, _, item) => item,
            _ => panic!("expected an array, hole array, or boxed type"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Occur<M, L> {
    pub id: flat::LocalId,
    pub ty: Type<M, L>,
}

#[derive(Clone, Debug)]
pub enum ArrayOp<M, L> {
    Get(
        Occur<M, L>, // Array
        Occur<M, L>, // Index
        Type<M, L>,  // Return type; needed for retain/release insertion
    ), // Returns item
    Extract(
        Occur<M, L>, // Array
        Occur<M, L>, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        Occur<M, L>, // Array
    ), // Returns int
    Push(
        Occur<M, L>, // Array
        Occur<M, L>, // Item
    ), // Returns new array
    Pop(
        Occur<M, L>, // Array
    ), // Returns tuple (array, item)
    Replace(
        Occur<M, L>, // Hole array
        Occur<M, L>, // Item
    ), // Returns new array
    Reserve(
        Occur<M, L>, // Array
        Occur<M, L>, // Capacity
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
    Branch(Occur<M, L>, Vec<(Condition<M, L>, Expr<M, L>)>, Type<M, L>),
    LetMany(
        Vec<(Type<M, L>, Expr<M, L>)>, // Bound values; each is assigned a new sequential `LocalId`
        Occur<M, L>,                   // Result
    ),

    Tuple(Vec<Occur<M, L>>),
    TupleField(Occur<M, L>, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type<M, L>>,
        first_ord::VariantId,
        Occur<M, L>,
    ),
    UnwrapVariant(first_ord::VariantId, Occur<M, L>),
    WrapBoxed(
        Occur<M, L>,
        Type<M, L>, // Inner type
    ),
    UnwrapBoxed(
        Occur<M, L>,
        Type<M, L>, // Inner type
    ),
    WrapCustom(CustomTypeId, Occur<M, L>),
    UnwrapCustom(CustomTypeId, Occur<M, L>),

    Intrinsic(Intrinsic, Occur<M, L>),
    ArrayOp(ArrayOp<M, L>),
    IoOp(IoOp<M, L>),
    Panic(
        Type<M, L>, // Return type
        Occur<M, L>,
    ),

    ArrayLit(Type<M, L>, Vec<Occur<M, L>>),
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
    pub arg_ty: Type<ModeParam, Lt>,
    pub ret_ty: Type<ModeParam, LtParam>,
    pub constrs: Constrs,

    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument
    pub body: Expr<ModeSolution, Lt>,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct TypeDef2<I> {
    // `ov` is computable from `ty`, but kept around for convenience
    pub ty: Type2<I, SlotId, SlotId>,
    pub ov: Overlay2<I, SlotId>,
    pub slot_count: Count<SlotId>,
    pub ov_slots: BTreeSet<SlotId>,
    pub lt_slots: BTreeSet<SlotId>,
}

pub type TypeDef = TypeDef2<CustomTypeId>;

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
