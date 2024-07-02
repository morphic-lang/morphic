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
use crate::util::map_ext::{btree_map_refs, MapRef};
use crate::util::non_empty_set::NonEmptySet;
use id_collections::{id_type, Count, IdVec};
use std::collections::{BTreeMap, BTreeSet};
use std::hash::Hash;
use std::iter;

#[allow(non_snake_case)]
pub fn ARG_SCOPE() -> Path {
    Path::root().seq(1)
}

#[allow(non_snake_case)]
pub fn FUNC_BODY_PATH() -> Path {
    Path::root().seq(0) // Must have `FUNC_BODY_PATH` < `ARG_SCOPE`
}

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
    Alt { i: usize, n: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Path(im_rc::Vector<PathElem>);

impl Path {
    // Private because the analysis passes should always start from `FUNC_BODY_PATH` or `ARG_SCOPE`.
    fn root() -> Self {
        Self(im_rc::Vector::new())
    }

    pub fn seq(&self, i: usize) -> Self {
        let mut elems = self.0.clone();
        elems.push_back(PathElem::Seq(i));
        Self(elems)
    }

    pub fn alt(&self, i: usize, n: usize) -> Self {
        let mut elems = self.0.clone();
        elems.push_back(PathElem::Alt { i, n });
        Self(elems)
    }

    pub fn as_local_lt(&self) -> LocalLt {
        let mut result = LocalLt::Final;
        for elem in self.0.iter().copied().rev() {
            match elem {
                PathElem::Seq(i) => {
                    result = LocalLt::Seq(Box::new(result), i);
                }
                PathElem::Alt { i, n } => {
                    let mut alt = vec![None; n];
                    alt[i] = Some(result);
                    result = LocalLt::Alt(alt);
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
    Alt(Vec<Option<LocalLt>>),
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

    pub fn contains(&self, other: &Path) -> bool {
        match (self, other) {
            (Lt::Empty, _) => false,
            (Lt::Local(l), p) => l.contains(p),
            (Lt::Join(_), _) => true,
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
    pub fn zoom(&self, path: &Path) -> Option<&Self> {
        let mut res = self;
        for elem in &path.0 {
            match (res, elem) {
                (LocalLt::Seq(inner, i1), PathElem::Seq(i2)) => {
                    if i1 == i2 {
                        res = inner;
                    } else {
                        return None;
                    }
                }
                (LocalLt::Alt(alt), PathElem::Alt { i, n }) => {
                    if alt.len() != *n {
                        panic!("incompatible lifetimes");
                    }
                    res = alt[*i].as_ref()?;
                }
                _ => {
                    panic!("incompatible lifetimes");
                }
            }
        }
        Some(res)
    }

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
            (LocalLt::Alt(p1), LocalLt::Alt(p2)) => LocalLt::Alt(
                p1.iter()
                    .zip_eq(p2.iter())
                    .map(|(l1, l2)| match (l1, l2) {
                        (None, None) => None,
                        (None, Some(l)) | (Some(l), None) => Some(l.clone()),
                        (Some(l1), Some(l2)) => Some(l1.join(l2)),
                    })
                    .collect(),
            ),
            (LocalLt::Seq(_, _), LocalLt::Alt(_)) | (LocalLt::Alt(_), LocalLt::Seq(_, _)) => {
                panic!("incompatible lifetimes");
            }
        }
    }

    pub fn contains(&self, rhs: &Path) -> bool {
        let mut lhs = self;
        for elem in &rhs.0 {
            match (lhs, elem) {
                (LocalLt::Final, _) => {
                    panic!(
                        "compared lifetimes of different lengths (while technically well-defined, \
                         this is almost certainly a bug)"
                    )
                }
                (LocalLt::Seq(inner, i1), PathElem::Seq(i2)) => {
                    if i1 < i2 {
                        return false;
                    } else if i1 > i2 {
                        return true;
                    } else {
                        lhs = inner;
                        continue;
                    }
                }
                (LocalLt::Alt(alt), PathElem::Alt { i, n }) => {
                    if alt.len() != *n {
                        panic!("incompatible lifetimes");
                    }
                    match &alt[*i] {
                        None => {
                            return false;
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
        assert!(
            *lhs == LocalLt::Final,
            "compared lifetimes of different lengths (while technically well-defined, this is \
             almost certainly a bug)"
        );
        true
    }

    pub fn does_not_exceed(&self, rhs: &Path) -> bool {
        let mut lhs = self;
        for elem in &rhs.0 {
            match (lhs, elem) {
                (LocalLt::Final, _) => {
                    panic!(
                        "compared lifetimes of different lengths (while technically well-defined, \
                         this is almost certainly a bug)"
                    )
                }
                (LocalLt::Seq(inner, i1), PathElem::Seq(i2)) => {
                    if i1 < i2 {
                        return true;
                    } else if i1 > i2 {
                        return false;
                    } else {
                        lhs = inner;
                        continue;
                    }
                }
                (LocalLt::Alt(alt), PathElem::Alt { i, n }) => {
                    if alt.len() != *n {
                        panic!("incompatible lifetimes");
                    }
                    match &alt[*i] {
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
        assert!(
            *lhs == LocalLt::Final,
            "compared lifetimes of different lengths (while technically well-defined, this is \
             almost certainly a bug)"
        );
        true
    }
}

#[id_type]
pub struct SlotId(pub usize);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OverlayShape {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<OverlayShape>),
    Variants(IdVec<first_ord::VariantId, OverlayShape>),
    SelfCustom(CustomTypeId),
    Custom(CustomTypeId),
    Array,
    HoleArray,
    Boxed,
}

#[derive(Clone, Debug)]
pub enum Overlay<T> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Overlay<T>>),
    Variants(IdVec<first_ord::VariantId, Overlay<T>>),
    SelfCustom(CustomTypeId),
    Custom(CustomTypeId, BTreeMap<SlotId, T>),
    Array(T),
    HoleArray(T),
    Boxed(T),
}

impl Overlay<SlotId> {
    pub fn hydrate<'a, T: Clone + 'a>(&self, subst: impl MapRef<'a, SlotId, T>) -> Overlay<T> {
        match self {
            Overlay::Bool => Overlay::Bool,
            Overlay::Num(n) => Overlay::Num(*n),
            Overlay::Tuple(ovs) => Overlay::Tuple(ovs.iter().map(|ov| ov.hydrate(subst)).collect()),
            Overlay::Variants(ovs) => Overlay::Variants(ovs.map_refs(|_, ov| ov.hydrate(subst))),
            Overlay::SelfCustom(id) => Overlay::SelfCustom(*id),
            Overlay::Custom(id, old_subst) => Overlay::Custom(
                *id,
                btree_map_refs(old_subst, |_, slot| subst.get(slot).unwrap().clone()),
            ),
            Overlay::Array(slot) => Overlay::Array(subst.get(slot).unwrap().clone()),
            Overlay::HoleArray(slot) => Overlay::HoleArray(subst.get(slot).unwrap().clone()),
            Overlay::Boxed(slot) => Overlay::Boxed(subst.get(slot).unwrap().clone()),
        }
    }
}

impl<T> Overlay<T> {
    pub fn from_const<U>(shape: &Overlay<U>, c: T) -> Overlay<T>
    where
        T: Clone,
    {
        shape.iter().map(|_| c.clone()).collect_overlay(shape)
    }

    // Must produce the order expected by `collect_overlay`
    pub fn iter(&self) -> Box<dyn Iterator<Item = &T> + '_> {
        match self {
            Overlay::Bool => Box::new(iter::empty()),
            Overlay::Num(_) => Box::new(iter::empty()),
            Overlay::Tuple(ovs) => Box::new(ovs.iter().flat_map(Overlay::iter)),
            Overlay::Variants(ovs) => Box::new(ovs.values().flat_map(Overlay::iter)),
            Overlay::SelfCustom(_) => Box::new(iter::empty()),
            Overlay::Custom(_, ov) => Box::new(ov.values()),
            Overlay::Array(x) => Box::new(iter::once(x)),
            Overlay::HoleArray(x) => Box::new(iter::once(x)),
            Overlay::Boxed(x) => Box::new(iter::once(x)),
        }
    }

    pub fn shape(&self) -> OverlayShape {
        match self {
            Overlay::Bool => OverlayShape::Bool,
            Overlay::Num(n) => OverlayShape::Num(*n),
            Overlay::Tuple(ovs) => OverlayShape::Tuple(ovs.iter().map(Overlay::shape).collect()),
            Overlay::Variants(ovs) => OverlayShape::Variants(ovs.map_refs(|_, ov| ov.shape())),
            Overlay::SelfCustom(id) => OverlayShape::SelfCustom(*id),
            Overlay::Custom(id, _) => OverlayShape::Custom(*id),
            Overlay::Array(_) => OverlayShape::Array,
            Overlay::HoleArray(_) => OverlayShape::HoleArray,
            Overlay::Boxed(_) => OverlayShape::Boxed,
        }
    }

    /// Returns true if the overlay is zero-sized, i.e. it does not contain any data.
    pub fn is_zero_sized<'a>(
        &self,
        customs: impl MapRef<'a, CustomTypeId, Overlay<SlotId>>,
    ) -> bool {
        fn visit<'a, T>(
            customs: impl MapRef<'a, CustomTypeId, Overlay<SlotId>>,
            visited: &mut BTreeSet<CustomTypeId>,
            this: &Overlay<T>,
        ) -> bool {
            match this {
                Overlay::Bool => false,
                Overlay::Num(_) => false,
                Overlay::Tuple(ovs) => ovs.iter().all(|ov| visit(customs, visited, ov)),
                Overlay::Variants(ovs) => ovs.values().all(|ov| visit(customs, visited, ov)),
                Overlay::SelfCustom(id) | Overlay::Custom(id, _) => {
                    if visited.contains(id) {
                        // It's OK to return true here because if the answer was false, we caught it
                        // when we actually visited the type.
                        true
                    } else {
                        visited.insert(*id);
                        visit(customs, visited, customs.get(id).unwrap())
                    }
                }
                Overlay::Array(_) => false,
                Overlay::HoleArray(_) => false,
                Overlay::Boxed(_) => false,
            }
        }

        // TODO: maybe it would be cleaner to track type SCCs in `CustomTypes`
        let mut visited = BTreeSet::new();
        visit(customs, &mut visited, self)
    }
}

pub trait CollectOverlay<T> {
    fn collect_overlay<U>(self, orig: &Overlay<U>) -> Overlay<T>;
}

impl<T, J: Iterator<Item = T>> CollectOverlay<T> for J {
    fn collect_overlay<U>(mut self, orig: &Overlay<U>) -> Overlay<T> {
        collect_overlay(&mut self, orig)
    }
}

// Must expect the order produced by `Overlay::iter`
fn collect_overlay<T, U>(iter: &mut impl Iterator<Item = T>, orig: &Overlay<U>) -> Overlay<T> {
    match orig {
        Overlay::Bool => Overlay::Bool,
        Overlay::Num(n) => Overlay::Num(*n),
        Overlay::Tuple(ovs) => {
            Overlay::Tuple(ovs.iter().map(|ov| collect_overlay(iter, ov)).collect())
        }
        Overlay::Variants(ovs) => {
            Overlay::Variants(ovs.map_refs(|_, ov| collect_overlay(iter, ov)))
        }
        Overlay::SelfCustom(id) => Overlay::SelfCustom(*id),
        Overlay::Custom(id, subst) => {
            Overlay::Custom(*id, btree_map_refs(subst, |_, _| iter.next().unwrap()))
        }
        Overlay::Array(_) => Overlay::Array(iter.next().unwrap()),
        Overlay::HoleArray(_) => Overlay::HoleArray(iter.next().unwrap()),
        Overlay::Boxed(_) => Overlay::Boxed(iter.next().unwrap()),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Shape {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Shape>),
    Variants(IdVec<first_ord::VariantId, Shape>),
    SelfCustom(CustomTypeId),
    Custom(CustomTypeId),
    Array(Box<Shape>),
    HoleArray(Box<Shape>),
    Boxed(Box<Shape>),
}

#[derive(Clone, Debug)]
pub enum LtData<T> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<LtData<T>>),
    Variants(IdVec<first_ord::VariantId, LtData<T>>),
    SelfCustom(CustomTypeId),
    Custom(CustomTypeId, BTreeMap<SlotId, T>),
    Array(T, Box<LtData<T>>),
    HoleArray(T, Box<LtData<T>>),
    Boxed(T, Box<LtData<T>>),
}

impl LtData<SlotId> {
    pub fn hydrate<'a, T: Clone + 'a>(&self, subst: impl MapRef<'a, SlotId, T>) -> LtData<T> {
        match self {
            LtData::Bool => LtData::Bool,
            LtData::Num(n) => LtData::Num(*n),
            LtData::Tuple(lts) => LtData::Tuple(lts.iter().map(|lt| lt.hydrate(subst)).collect()),
            LtData::Variants(lts) => LtData::Variants(lts.map_refs(|_, lt| lt.hydrate(subst))),
            LtData::SelfCustom(id) => LtData::SelfCustom(*id),
            LtData::Custom(id, old_subst) => LtData::Custom(
                *id,
                btree_map_refs(old_subst, |_, slot| subst.get(slot).unwrap().clone()),
            ),
            LtData::Array(slot, lt) => LtData::Array(
                subst.get(slot).unwrap().clone(),
                Box::new(lt.hydrate(subst)),
            ),
            LtData::HoleArray(slot, lt) => LtData::HoleArray(
                subst.get(slot).unwrap().clone(),
                Box::new(lt.hydrate(subst)),
            ),
            LtData::Boxed(slot, lt) => LtData::Boxed(
                subst.get(slot).unwrap().clone(),
                Box::new(lt.hydrate(subst)),
            ),
        }
    }
}

impl LtData<Lt> {
    pub fn join(&self, other: &LtData<Lt>) -> LtData<Lt> {
        debug_assert!(self.shape() == other.shape());
        self.iter()
            .zip_eq(other.iter())
            .map(|(lt1, lt2)| lt1.join(lt2))
            .collect_lt_data(self)
    }
}

impl LtData<LtParam> {
    pub fn wrap_params(&self) -> LtData<Lt> {
        self.iter().copied().map(Lt::var).collect_lt_data(self)
    }
}

impl<T> LtData<T> {
    // Must produce the order expected by `collect_lt_data`
    pub fn iter(&self) -> Box<dyn Iterator<Item = &T> + '_> {
        match self {
            LtData::Bool => Box::new(iter::empty()),
            LtData::Num(_) => Box::new(iter::empty()),
            LtData::Tuple(lts) => Box::new(lts.iter().flat_map(LtData::iter)),
            LtData::Variants(lts) => Box::new(lts.values().flat_map(LtData::iter)),
            LtData::SelfCustom(_) => Box::new(iter::empty()),
            LtData::Custom(_, subst) => Box::new(subst.values()),
            LtData::Array(lt, item) => Box::new(iter::once(lt).chain(item.iter())),
            LtData::HoleArray(lt, item) => Box::new(iter::once(lt).chain(item.iter())),
            LtData::Boxed(lt, item) => Box::new(iter::once(lt).chain(item.iter())),
        }
    }

    pub fn iter_stack<'a>(
        &'a self,
        customs: impl MapRef<'a, CustomTypeId, TypeDef> + 'a,
    ) -> Box<dyn Iterator<Item = &'a T> + 'a> {
        match self {
            LtData::Bool => Box::new(iter::empty()),
            LtData::Num(_) => Box::new(iter::empty()),
            LtData::Tuple(lts) => Box::new(lts.iter().flat_map(move |lt| lt.iter_stack(customs))),
            LtData::Variants(lts) => {
                Box::new(lts.values().flat_map(move |lt| lt.iter_stack(customs)))
            }
            LtData::SelfCustom(_) => Box::new(iter::empty()),
            LtData::Custom(id, subst) => Box::new(
                customs
                    .get(id)
                    .unwrap()
                    .ty
                    .lts()
                    .iter_stack(customs)
                    .map(|slot| &subst[slot]),
            ),
            LtData::Array(lt, _) => Box::new(iter::once(lt)),
            LtData::HoleArray(lt, _) => Box::new(iter::once(lt)),
            LtData::Boxed(lt, _) => Box::new(iter::once(lt)),
        }
    }

    pub fn shape(&self) -> Shape {
        match self {
            LtData::Bool => Shape::Bool,
            LtData::Num(n) => Shape::Num(*n),
            LtData::Tuple(lts) => Shape::Tuple(lts.iter().map(LtData::shape).collect()),
            LtData::Variants(lts) => Shape::Variants(lts.map_refs(|_, lt| lt.shape())),
            LtData::SelfCustom(id) => Shape::SelfCustom(*id),
            LtData::Custom(id, _) => Shape::Custom(*id),
            LtData::Array(_, lt) => Shape::Array(Box::new(lt.shape())),
            LtData::HoleArray(_, lt) => Shape::HoleArray(Box::new(lt.shape())),
            LtData::Boxed(_, lt) => Shape::Boxed(Box::new(lt.shape())),
        }
    }
}

pub trait CollectLtData<T> {
    fn collect_lt_data<U>(self, orig: &LtData<U>) -> LtData<T>;
}

impl<T, J: Iterator<Item = T>> CollectLtData<T> for J {
    fn collect_lt_data<U>(mut self, orig: &LtData<U>) -> LtData<T> {
        collect_lt_data(&mut self, orig)
    }
}

// Must expect the order produced by `LtData::iter`
fn collect_lt_data<T, U>(iter: &mut impl Iterator<Item = T>, orig: &LtData<U>) -> LtData<T> {
    match orig {
        LtData::Bool => LtData::Bool,
        LtData::Num(n) => LtData::Num(*n),
        LtData::Tuple(items) => LtData::Tuple(
            items
                .iter()
                .map(|item| collect_lt_data(iter, item))
                .collect(),
        ),
        LtData::Variants(items) => {
            LtData::Variants(items.map_refs(|_, item| collect_lt_data(iter, item)))
        }
        LtData::SelfCustom(id) => LtData::SelfCustom(*id),
        LtData::Custom(id, subst) => {
            LtData::Custom(*id, btree_map_refs(subst, |_, _| iter.next().unwrap()))
        }
        LtData::Array(_, item) => {
            LtData::Array(iter.next().unwrap(), Box::new(collect_lt_data(iter, item)))
        }
        LtData::HoleArray(_, item) => {
            LtData::HoleArray(iter.next().unwrap(), Box::new(collect_lt_data(iter, item)))
        }
        LtData::Boxed(_, item) => {
            LtData::Boxed(iter.next().unwrap(), Box::new(collect_lt_data(iter, item)))
        }
    }
}

#[derive(Clone, Debug)]
pub enum ModeData<T> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<ModeData<T>>),
    Variants(IdVec<first_ord::VariantId, ModeData<T>>),
    SelfCustom(CustomTypeId),
    Custom(
        CustomTypeId,
        BTreeMap<SlotId, T>, // Overlay
        IdVec<SlotId, T>,    // Substitution
    ),
    Array(T, Overlay<T>, Box<ModeData<T>>),
    HoleArray(T, Overlay<T>, Box<ModeData<T>>),
    Boxed(T, Overlay<T>, Box<ModeData<T>>),
}

impl ModeData<SlotId> {
    pub fn hydrate<T: Clone>(&self, subst: &IdVec<SlotId, T>) -> ModeData<T> {
        match self {
            ModeData::Bool => ModeData::Bool,
            ModeData::Num(n) => ModeData::Num(*n),
            ModeData::Tuple(tys) => {
                ModeData::Tuple(tys.iter().map(|ty| ty.hydrate(subst)).collect())
            }
            ModeData::Variants(tys) => ModeData::Variants(tys.map_refs(|_, ty| ty.hydrate(subst))),
            ModeData::SelfCustom(id) => ModeData::SelfCustom(*id),
            ModeData::Custom(id, osub, tsub) => ModeData::Custom(
                *id,
                btree_map_refs(osub, |_, slot| subst[*slot].clone()),
                tsub.map_refs(|_, slot| subst[*slot].clone()),
            ),
            ModeData::Array(m, ov, ty) => ModeData::Array(
                subst[*m].clone(),
                ov.hydrate(subst),
                Box::new(ty.hydrate(subst)),
            ),
            ModeData::HoleArray(m, ov, ty) => ModeData::HoleArray(
                subst[*m].clone(),
                ov.hydrate(subst),
                Box::new(ty.hydrate(subst)),
            ),
            ModeData::Boxed(m, ov, ty) => ModeData::Boxed(
                subst[*m].clone(),
                ov.hydrate(subst),
                Box::new(ty.hydrate(subst)),
            ),
        }
    }

    pub fn extract_lts<'a>(
        &self,
        customs: impl MapRef<'a, CustomTypeId, TypeDef>,
    ) -> LtData<SlotId> {
        match self {
            ModeData::Bool => LtData::Bool,
            ModeData::Num(n) => LtData::Num(*n),
            ModeData::Tuple(tys) => {
                LtData::Tuple(tys.iter().map(|ty| ty.extract_lts(customs)).collect())
            }
            ModeData::Variants(tys) => {
                LtData::Variants(tys.map_refs(|_, ty| ty.extract_lts(customs)))
            }
            ModeData::SelfCustom(id) => LtData::SelfCustom(*id),
            ModeData::Custom(id, _, subst) => {
                let custom = customs.get(id).unwrap();
                let subst = custom
                    .lt_slots
                    .iter()
                    .map(|&key| (key, subst[key]))
                    .collect();
                LtData::Custom(*id, subst)
            }
            ModeData::Array(slot, _, ty) => LtData::Array(*slot, Box::new(ty.extract_lts(customs))),
            ModeData::HoleArray(slot, _, ty) => {
                LtData::HoleArray(*slot, Box::new(ty.extract_lts(customs)))
            }
            ModeData::Boxed(slot, _, ty) => LtData::Boxed(*slot, Box::new(ty.extract_lts(customs))),
        }
    }
}

impl<T> ModeData<T> {
    // Must produce the order expected by `collect_mode_data`
    pub fn iter(&self) -> Box<dyn Iterator<Item = &T> + '_> {
        match self {
            ModeData::Bool => Box::new(iter::empty()),
            ModeData::Num(_) => Box::new(iter::empty()),
            ModeData::Tuple(tys) => Box::new(tys.iter().flat_map(ModeData::iter)),
            ModeData::Variants(tys) => Box::new(tys.values().flat_map(ModeData::iter)),
            ModeData::SelfCustom(_) => Box::new(iter::empty()),
            ModeData::Custom(_, ov, tys) => Box::new(ov.values().chain(tys.values())),
            ModeData::Array(m, ov, ty) => Box::new(iter::once(m).chain(ov.iter()).chain(ty.iter())),
            ModeData::HoleArray(m, ov, ty) => {
                Box::new(iter::once(m).chain(ov.iter()).chain(ty.iter()))
            }
            ModeData::Boxed(m, ov, ty) => Box::new(iter::once(m).chain(ov.iter()).chain(ty.iter())),
        }
    }

    pub fn iter_store<'a>(
        &'a self,
        customs: impl MapRef<'a, CustomTypeId, ModeData<SlotId>> + 'a,
    ) -> Box<dyn Iterator<Item = &'a T> + 'a> {
        match self {
            ModeData::Bool => Box::new(iter::empty()),
            ModeData::Num(_) => Box::new(iter::empty()),
            ModeData::Tuple(tys) => Box::new(tys.iter().flat_map(move |ty| ty.iter_store(customs))),
            ModeData::Variants(tys) => {
                Box::new(tys.values().flat_map(move |ty| ty.iter_store(customs)))
            }
            ModeData::SelfCustom(_) => Box::new(iter::empty()),
            ModeData::Custom(id, _, subst) => {
                let custom = customs.get(id).unwrap();
                Box::new(custom.iter_store(customs).map(|slot| &subst[*slot]))
            }
            ModeData::Array(m, _, ty) => Box::new(iter::once(m).chain(ty.iter_store(customs))),
            ModeData::HoleArray(m, _, ty) => Box::new(iter::once(m).chain(ty.iter_store(customs))),
            ModeData::Boxed(m, _, ty) => Box::new(iter::once(m).chain(ty.iter_store(customs))),
        }
    }

    pub fn iter_stack<'a>(&'a self) -> Box<dyn Iterator<Item = &'a T> + 'a> {
        match self {
            ModeData::Bool => Box::new(iter::empty()),
            ModeData::Num(_) => Box::new(iter::empty()),
            ModeData::Tuple(tys) => Box::new(tys.iter().flat_map(|ty| ty.iter_stack())),
            ModeData::Variants(tys) => Box::new(tys.values().flat_map(|ty| ty.iter_stack())),
            ModeData::SelfCustom(_) => Box::new(iter::empty()),
            ModeData::Custom(_, ov, _) => Box::new(ov.values()),
            ModeData::Array(m, _, _) => Box::new(iter::once(m)),
            ModeData::HoleArray(m, _, _) => Box::new(iter::once(m)),
            ModeData::Boxed(m, _, _) => Box::new(iter::once(m)),
        }
    }

    pub fn apply_overlay(&self, ov: &Overlay<T>) -> ModeData<T>
    where
        T: Clone,
    {
        match (self, ov) {
            (ModeData::Bool, Overlay::Bool) => ModeData::Bool,
            (ModeData::Num(n1), Overlay::Num(n2)) if n1 == n2 => ModeData::Num(*n1),
            (ModeData::Tuple(tys), Overlay::Tuple(ovs)) => ModeData::Tuple(
                tys.iter()
                    .zip_eq(ovs)
                    .map(|(ty, ov)| ty.apply_overlay(ov))
                    .collect(),
            ),
            (ModeData::Variants(tys), Overlay::Variants(ovs)) => {
                ModeData::Variants(IdVec::from_vec(
                    tys.values()
                        .zip_eq(ovs.values())
                        .map(|(ty, ov)| ty.apply_overlay(ov))
                        .collect(),
                ))
            }
            (ModeData::SelfCustom(id1), Overlay::SelfCustom(id2)) if id1 == id2 => {
                ModeData::SelfCustom(*id1)
            }
            (ModeData::Custom(id1, ov1, subst), Overlay::Custom(id2, ov2)) if id1 == id2 => {
                debug_assert!(ov1.keys().zip_eq(ov2.keys()).all(|(k1, k2)| k1 == k2));
                ModeData::Custom(*id1, ov2.clone(), subst.clone())
            }
            (ModeData::Array(_, ov, ty), Overlay::Array(m)) => {
                ModeData::Array(m.clone(), ov.clone(), ty.clone())
            }
            (ModeData::HoleArray(_, ov, ty), Overlay::HoleArray(m)) => {
                ModeData::HoleArray(m.clone(), ov.clone(), ty.clone())
            }
            (ModeData::Boxed(_, ov, ty), Overlay::Boxed(m)) => {
                ModeData::Boxed(m.clone(), ov.clone(), ty.clone())
            }
            _ => panic!("type/overlay mismatch"),
        }
    }

    pub fn unapply_overlay(&self) -> Overlay<T>
    where
        T: Clone,
    {
        match self {
            ModeData::Bool => Overlay::Bool,
            ModeData::Num(n) => Overlay::Num(*n),
            ModeData::Tuple(tys) => {
                Overlay::Tuple(tys.iter().map(ModeData::unapply_overlay).collect())
            }
            ModeData::Variants(tys) => {
                Overlay::Variants(tys.map_refs(|_, ty| ty.unapply_overlay()))
            }
            ModeData::SelfCustom(id) => Overlay::SelfCustom(*id),
            ModeData::Custom(id, ov, _) => Overlay::Custom(*id, ov.clone()),
            ModeData::Array(m, _, _) => Overlay::Array(m.clone()),
            ModeData::HoleArray(m, _, _) => Overlay::HoleArray(m.clone()),
            ModeData::Boxed(m, _, _) => Overlay::Boxed(m.clone()),
        }
    }

    pub fn shape(&self) -> Shape {
        match self {
            ModeData::Bool => Shape::Bool,
            ModeData::Num(n) => Shape::Num(*n),
            ModeData::Tuple(tys) => Shape::Tuple(tys.iter().map(ModeData::shape).collect()),
            ModeData::Variants(tys) => Shape::Variants(tys.map_refs(|_, ty| ty.shape())),
            ModeData::SelfCustom(id) => Shape::SelfCustom(*id),
            ModeData::Custom(id, _, _) => Shape::Custom(*id),
            ModeData::Array(_, _, ty) => Shape::Array(Box::new(ty.shape())),
            ModeData::HoleArray(_, _, ty) => Shape::HoleArray(Box::new(ty.shape())),
            ModeData::Boxed(_, _, ty) => Shape::Boxed(Box::new(ty.shape())),
        }
    }

    /// If `self` is `Array`, `HoleArray`, or `Boxed`, return the modes of the inner type.
    pub fn unwrap_item_modes(&self) -> &ModeData<T> {
        match self {
            ModeData::Array(_, _, item)
            | ModeData::HoleArray(_, _, item)
            | ModeData::Boxed(_, _, item) => item,
            _ => panic!("expected an array, hole array, or boxed type"),
        }
    }
}

pub trait CollectModeData<T> {
    fn collect_mode_data<U>(self, orig: &ModeData<U>) -> ModeData<T>;
}

impl<T, J: Iterator<Item = T>> CollectModeData<T> for J {
    fn collect_mode_data<U>(mut self, orig: &ModeData<U>) -> ModeData<T> {
        collect_mode_data(&mut self, orig)
    }
}

// Must expect the order produced by `ModeData::iter`
fn collect_mode_data<T, U>(iter: &mut impl Iterator<Item = T>, orig: &ModeData<U>) -> ModeData<T> {
    match orig {
        ModeData::Bool => ModeData::Bool,
        ModeData::Num(n) => ModeData::Num(*n),
        ModeData::Tuple(items) => ModeData::Tuple(
            items
                .iter()
                .map(|item| collect_mode_data(iter, item))
                .collect(),
        ),
        ModeData::Variants(items) => {
            ModeData::Variants(items.map_refs(|_, item| collect_mode_data(iter, item)))
        }
        ModeData::SelfCustom(id) => ModeData::SelfCustom(*id),
        ModeData::Custom(id, ov, subst) => ModeData::Custom(
            *id,
            btree_map_refs(ov, |_, _| iter.next().unwrap()),
            subst.map_refs(|_, _| iter.next().unwrap()),
        ),
        ModeData::Array(_, ov, item) => ModeData::Array(
            iter.next().unwrap(),
            collect_overlay(iter, ov),
            Box::new(collect_mode_data(iter, item)),
        ),
        ModeData::HoleArray(_, ov, item) => ModeData::HoleArray(
            iter.next().unwrap(),
            collect_overlay(iter, ov),
            Box::new(collect_mode_data(iter, item)),
        ),
        ModeData::Boxed(_, ov, item) => ModeData::Boxed(
            iter.next().unwrap(),
            collect_overlay(iter, ov),
            Box::new(collect_mode_data(iter, item)),
        ),
    }
}

#[derive(Clone, Debug)]
pub struct Type<M, L> {
    lts: LtData<L>,
    modes: ModeData<M>,
}

impl Type<SlotId, SlotId> {
    pub fn hydrate<M: Clone, L: Clone>(
        &self,
        lt_subst: &BTreeMap<SlotId, L>,
        mode_subst: &IdVec<SlotId, M>,
    ) -> Type<M, L> {
        Type {
            lts: self.lts.hydrate(lt_subst),
            modes: self.modes.hydrate(mode_subst),
        }
    }
}

impl<M: Clone> Type<M, Lt> {
    pub fn left_meet(&self, other: &Type<M, Lt>) -> Type<M, Lt> {
        Type {
            lts: self.lts.join(&other.lts),
            modes: self.modes.clone(),
        }
    }
}

impl<M, L> Type<M, L> {
    pub fn new(lts: LtData<L>, modes: ModeData<M>) -> Self {
        debug_assert!(lts.shape() == modes.shape());
        Self { lts, modes }
    }

    pub fn shape(&self) -> Shape {
        self.modes.shape()
    }

    pub fn lts(&self) -> &LtData<L> {
        &self.lts
    }

    pub fn lts_mut(&mut self) -> &mut LtData<L> {
        &mut self.lts
    }

    pub fn modes(&self) -> &ModeData<M> {
        &self.modes
    }

    pub fn modes_mut(&mut self) -> &mut ModeData<M> {
        &mut self.modes
    }

    pub fn into_modes(self) -> ModeData<M> {
        self.modes
    }

    pub fn map<M2, L2>(&self, f: impl Fn(&M) -> M2, g: impl Fn(&L) -> L2) -> Type<M2, L2> {
        let lts = self.lts.iter().map(g).collect_lt_data(&self.lts);
        let modes = self.modes.iter().map(f).collect_mode_data(&self.modes);
        Type { lts, modes }
    }

    pub fn map_modes<M2>(&self, f: impl Fn(&M) -> M2) -> Type<M2, L>
    where
        L: Clone,
    {
        self.map(f, Clone::clone)
    }

    pub fn map_lts<L2>(&self, f: impl Fn(&L) -> L2) -> Type<M, L2>
    where
        M: Clone,
    {
        self.map(Clone::clone, f)
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
        Type<M, L>,  // Return type; needed for retain insertion
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
pub struct TypeDef {
    // `ov` is computable from `ty`, but kept around for convenience
    pub ty: Type<SlotId, SlotId>,
    pub ov: Overlay<SlotId>,
    pub slot_count: Count<SlotId>,
    pub ov_slots: BTreeSet<SlotId>,
    pub lt_slots: BTreeSet<SlotId>,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_path_as_lt() {
        let path = Path::root().seq(0).alt(1, 3).seq(2276);
        let expected = Lt::Local(LocalLt::Seq(
            Box::new(LocalLt::Alt(vec![
                None,
                Some(LocalLt::Seq(Box::new(LocalLt::Final), 2276)),
                None,
            ])),
            0,
        ));
        assert_eq!(path.as_lt(), expected);
    }

    #[test]
    fn test_lt_zoom() {
        let alt = LocalLt::Alt(vec![
            None,
            Some(LocalLt::Seq(Box::new(LocalLt::Final), 2276)),
            None,
        ]);
        let lt = LocalLt::Seq(Box::new(alt.clone()), 0);

        let zoomed = lt.zoom(&Path::root().seq(0).alt(1, 3).seq(2276));
        assert_eq!(zoomed, Some(&LocalLt::Final));

        let zoomed = lt.zoom(&Path::root().seq(0));
        assert_eq!(zoomed, Some(&alt));

        let zoomed = lt.zoom(&Path::root().seq(0).alt(1, 3).seq(2275));
        assert_eq!(zoomed, None);

        let zoomed = lt.zoom(&Path::root().seq(0).alt(2, 3));
        assert_eq!(zoomed, None);
    }

    #[test]
    fn test_lt_order() {
        let lt = Lt::Local(LocalLt::Seq(
            Box::new(LocalLt::Alt(vec![
                None,
                Some(LocalLt::Seq(Box::new(LocalLt::Final), 2276)),
                None,
            ])),
            0,
        ));

        let before = Path::root().seq(0).alt(1, 3).seq(2275);
        let eq = Path::root().seq(0).alt(1, 3).seq(2276);
        let after = Path::root().seq(0).alt(1, 3).seq(2277);

        assert!(!lt.does_not_exceed(&before));
        assert!(lt.does_not_exceed(&eq)); // reflexivity
        assert!(lt.does_not_exceed(&after));

        assert!(lt.contains(&before));
        assert!(lt.contains(&eq));
        assert!(!lt.contains(&after));
    }

    #[test]
    fn test_mode_data_iter() {
        use crate::util::map_ext::FnWrap;

        let modes = ModeData::Array(
            0,
            Overlay::Array(1),
            Box::new(ModeData::Array(2, Overlay::Bool, Box::new(ModeData::Bool))),
        );

        assert_eq!(modes.iter().copied().collect::<Vec<_>>(), vec![0, 1, 2]);
        assert_eq!(modes.iter_stack().copied().collect::<Vec<_>>(), vec![0]);
        assert_eq!(
            modes
                .iter_store(FnWrap::wrap(|_| None))
                .copied()
                .collect::<Vec<_>>(),
            vec![0, 2]
        );
    }
}
