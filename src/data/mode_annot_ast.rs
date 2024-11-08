//! There are a few notable differences from the formalism:
//! - The AST is in A-normal form.
//! - We use nomial types ("custom" types) instead of mu types.
//! - In addition to the `Boxed` type (which is a plain reference counted allocation), we have the
//!   `Array` and `HoleArray` types, which require similar treatment during borrow inference because
//!   they have embedded reference counts.

use crate::data::first_order_ast::{self as first_ord, CustomTypeId};
use crate::data::flat_ast as flat;
use crate::data::guarded_ast::{self as guard, CanGuard, RecipeContent};
use crate::data::guarded_ast::{self as guarded, UnfoldRecipe};
use crate::data::intrinsics::Intrinsic;
use crate::data::metadata::Metadata;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::collection_ext::{FnWrap, MapRef, VecExt};
use crate::util::inequality_graph2 as in_eq;
use crate::util::intern::{self, Interned};
use crate::util::iter::IterExt;
use crate::util::non_empty_set::NonEmptySet;
use id_collections::{id_type, Id, IdVec};
use id_graph_sccs::{SccKind, Sccs};
use std::collections::{BTreeMap, BTreeSet};
use std::hash::Hash;
use std::iter;

pub struct Interner<I> {
    pub shape: intern::Interner<ShapeInner<I>>,
    pub lt: intern::Interner<LocalLt>,
}

impl<I: Id + 'static> Interner<I> {
    pub fn empty() -> Self {
        Interner {
            shape: intern::Interner::empty(),
            lt: intern::Interner::empty(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PathElem {
    Seq(usize),
    Alt { i: usize, n: usize },
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

    pub fn alt(&self, i: usize, n: usize) -> Self {
        let mut elems = self.0.clone();
        elems.push_back(PathElem::Alt { i, n });
        Self(elems)
    }

    pub fn as_local_lt<I: Id + 'static>(&self, interner: &Interner<I>) -> Interned<LocalLt> {
        let mut result = LocalLt::Final;
        for elem in self.0.iter().copied().rev() {
            match elem {
                PathElem::Seq(i) => {
                    result = LocalLt::Seq(interner.lt.new(result), i);
                }
                PathElem::Alt { i, n } => {
                    let mut alt = vec![None; n];
                    alt[i] = Some(interner.lt.new(result));
                    result = LocalLt::Alt(alt);
                }
            }
        }
        interner.lt.new(result)
    }

    pub fn as_lt<I: Id + 'static>(&self, interner: &Interner<I>) -> Lt {
        Lt::Local(self.as_local_lt(interner))
    }
}

#[allow(non_snake_case)]
pub fn ARG_SCOPE() -> Path {
    Path::root().seq(1)
}

/// Invariant: `FUNC_BODY_PATH` < `ARG_SCOPE`
#[allow(non_snake_case)]
pub fn FUNC_BODY_PATH() -> Path {
    Path::root().seq(0)
}

#[id_type]
pub struct LtParam(pub usize);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Lt {
    Empty,
    Local(Interned<LocalLt>),
    Join(NonEmptySet<LtParam>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LocalLt {
    Final,
    // Represents ordered "events", e.g. the binding and body of a let.
    Seq(Interned<LocalLt>, usize),
    // Represents unordered "events", e.g. the arms of a match. Always contains at least one `Some`.
    Alt(Vec<Option<Interned<LocalLt>>>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cmp {
    Boundary,
    Before,
    After,
    Prefix,
    Suffix,
}

impl Cmp {
    pub fn leq(&self) -> bool {
        match self {
            Cmp::Boundary | Cmp::Before => true,
            Cmp::After => false,
            Cmp::Prefix | Cmp::Suffix => {
                panic!("{self:?} cannot be interpreted as an unbiased comparison")
            }
        }
    }

    pub fn leq_left_biased(&self) -> bool {
        match self {
            Cmp::Boundary | Cmp::Before | Cmp::Prefix => true,
            Cmp::After | Cmp::Suffix => false,
        }
    }

    pub fn leq_right_biased(&self) -> bool {
        match self {
            Cmp::Boundary | Cmp::Before | Cmp::Suffix => true,
            Cmp::After | Cmp::Prefix => false,
        }
    }
}

impl Lt {
    pub fn var(x: LtParam) -> Self {
        Lt::Join(NonEmptySet::new(x))
    }

    /// A join over the lifetime lattice: `l1 <= l2` iff, for every leaf of `l1`, there is a leaf of
    /// `l2` that occurs "later in time".
    ///
    /// Panics if `self` and `other` are not structurally compatible.
    pub fn join<I: Id + 'static>(&self, interner: &Interner<I>, other: &Self) -> Self {
        match (self, other) {
            (Lt::Empty, l) | (l, Lt::Empty) => l.clone(),
            (Lt::Local(l1), Lt::Local(l2)) => Lt::Local(interner.lt.new(l1.join(interner, l2))),
            (Lt::Join(s), Lt::Local(_)) | (Lt::Local(_), Lt::Join(s)) => Lt::Join(s.clone()),
            (Lt::Join(s1), Lt::Join(s2)) => Lt::Join(s1 | s2),
        }
    }

    /// Panics if `self` and `other` are not structurally compatible.
    pub fn cmp_path(&self, other: &Path) -> Cmp {
        match (self, other) {
            (Lt::Empty, _) => Cmp::Before,
            (Lt::Local(l), p) => l.cmp_path(p),
            (Lt::Join(_), _) => Cmp::After,
        }
    }
}

impl LocalLt {
    pub fn join<I: Id + 'static>(&self, interner: &Interner<I>, rhs: &Self) -> Self {
        match (self, rhs) {
            (LocalLt::Final, _) | (_, LocalLt::Final) => LocalLt::Final,
            (LocalLt::Seq(l1, i1), LocalLt::Seq(l2, i2)) => {
                if i1 < i2 {
                    LocalLt::Seq(l2.clone(), *i2)
                } else if i2 < i1 {
                    LocalLt::Seq(l1.clone(), *i1)
                } else {
                    LocalLt::Seq(interner.lt.new(l1.join(interner, l2)), *i1)
                }
            }
            (LocalLt::Alt(p1), LocalLt::Alt(p2)) => LocalLt::Alt(
                p1.iter()
                    .zip_eq(p2.iter())
                    .map(|(l1, l2)| match (l1, l2) {
                        (None, None) => None,
                        (None, Some(l)) | (Some(l), None) => Some(l.clone()),
                        (Some(l1), Some(l2)) => Some(interner.lt.new(l1.join(interner, l2))),
                    })
                    .collect(),
            ),
            (LocalLt::Seq(_, _), LocalLt::Alt(_)) | (LocalLt::Alt(_), LocalLt::Seq(_, _)) => {
                panic!("incompatible lifetimes");
            }
        }
    }

    pub fn cmp_path(&self, rhs: &Path) -> Cmp {
        let mut lhs = self;
        for elem in &rhs.0 {
            match (lhs, elem) {
                (LocalLt::Final, _) => {
                    return Cmp::Prefix;
                }
                (LocalLt::Seq(inner, i1), PathElem::Seq(i2)) => {
                    if i1 < i2 {
                        return Cmp::Before;
                    } else if i1 > i2 {
                        return Cmp::After;
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
                            return Cmp::Before;
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
        if *lhs == LocalLt::Final {
            Cmp::Boundary
        } else {
            Cmp::Suffix
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    // Do not reorder these variants. That will change the derived `Ord`
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

/// Solved constraints are written in terms of `ModeParam`s.
#[id_type]
pub struct ModeParam(pub usize);

/// During constraint generation, modes are represented using `ModeVar`s.
#[id_type]
pub struct ModeVar(pub usize);

/// Solution `lb` for variable `solver_var`.
#[derive(Debug, Clone)]
pub struct ModeSolution {
    pub lb: in_eq::LowerBound<ModeParam, Mode>,
    pub solver_var: ModeVar, // For debugging
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct HeapModes<M> {
    pub access: M,
    pub storage: M,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ResModes<M> {
    Stack(M),
    Heap(HeapModes<M>),
}

impl<M> ResModes<M> {
    pub fn map<N>(&self, mut f: impl FnMut(&M) -> N) -> ResModes<N> {
        match self {
            ResModes::Stack(stack) => ResModes::Stack(f(stack)),
            ResModes::Heap(HeapModes { access, storage }) => ResModes::Heap(HeapModes {
                access: f(access),
                storage: f(storage),
            }),
        }
    }

    pub fn stack_or_storage(&self) -> &M {
        match self {
            ResModes::Stack(stack) => stack,
            ResModes::Heap(HeapModes { storage, .. }) => storage,
        }
    }

    pub fn stack_or_access(&self) -> &M {
        match self {
            ResModes::Stack(stack) => stack,
            ResModes::Heap(HeapModes { access, .. }) => access,
        }
    }

    pub fn unwrap_stack(&self) -> &M {
        match self {
            ResModes::Stack(stack) => stack,
            ResModes::Heap(_) => panic!("called `unwrap_stack` on `ResModes::Heap`"),
        }
    }

    pub fn unwrap_heap(&self) -> &HeapModes<M> {
        match self {
            ResModes::Stack(_) => panic!("called `unwrap_heap` on `ResModes::Stack`"),
            ResModes::Heap(heap) => heap,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Res<M, L> {
    pub modes: ResModes<M>,
    pub lt: L,
}

impl<M, L> Res<M, L> {
    pub fn map<N, K>(&self, f: impl FnMut(&M) -> N, mut g: impl FnMut(&L) -> K) -> Res<N, K> {
        Res {
            modes: self.modes.map(f),
            lt: g(&self.lt),
        }
    }
}

#[id_type]
pub struct SlotId(pub usize);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ShapeInner<I> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Shape<I>>),
    Variants(IdVec<first_ord::VariantId, Shape<I>>),
    Custom(I),
    SelfCustom(I),
    Array(Shape<I>),
    HoleArray(Shape<I>),
    Boxed(Shape<I>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Shape<I> {
    pub inner: Interned<ShapeInner<I>>,
    pub num_slots: usize,
}

pub type ShapeFo = Shape<first_ord::CustomTypeId>;

impl ShapeFo {
    pub fn from_guarded<'a>(
        interner: &Interner<first_ord::CustomTypeId>,
        customs: &IdVec<first_ord::CustomTypeId, CustomTypeDefFo>,
        ty: &guard::Type,
    ) -> Self {
        match ty {
            guard::Type::Bool => Shape {
                inner: interner.shape.new(ShapeInner::Bool),
                num_slots: 0,
            },
            guard::Type::Num(num_ty) => Shape {
                inner: interner.shape.new(ShapeInner::Num(*num_ty)),
                num_slots: 0,
            },
            guard::Type::Tuple(tys) => {
                let tys = tys.map_refs(|ty| Shape::from_guarded(interner, customs, ty));
                let num_slots = tys.iter().map(|ty| ty.num_slots).sum();
                Shape {
                    inner: interner.shape.new(ShapeInner::Tuple(tys)),
                    num_slots,
                }
            }
            guard::Type::Variants(tys) => {
                let tys = tys.map_refs(|_, ty| Shape::from_guarded(interner, customs, ty));
                let num_slots = tys.values().map(|ty| ty.num_slots).sum();
                Shape {
                    inner: interner.shape.new(ShapeInner::Variants(tys)),
                    num_slots,
                }
            }
            guard::Type::Custom(id) => Shape {
                inner: interner.shape.new(ShapeInner::Custom(*id)),
                num_slots: customs[id].num_slots,
            },
            guard::Type::Array(ty) => {
                let shape = Shape::from_guarded(interner, customs, ty);
                Shape {
                    num_slots: 1 + shape.num_slots,
                    inner: interner.shape.new(ShapeInner::Array(shape)),
                }
            }
            guard::Type::HoleArray(ty) => {
                let shape = Shape::from_guarded(interner, customs, ty);
                Shape {
                    num_slots: 1 + shape.num_slots,
                    inner: interner.shape.new(ShapeInner::HoleArray(shape)),
                }
            }
            guard::Type::Boxed(ty) => {
                let shape = Shape::from_guarded(interner, customs, ty);
                Shape {
                    num_slots: 1 + shape.num_slots,
                    inner: interner.shape.new(ShapeInner::Boxed(shape)),
                }
            }
        }
    }
}

impl<I: Id + 'static> Shape<I> {
    pub fn unit(interner: &Interner<I>) -> Self {
        Self {
            inner: interner.shape.new(ShapeInner::Tuple(vec![])),
            num_slots: 0,
        }
    }

    pub fn bool_(interner: &Interner<I>) -> Self {
        Self {
            inner: interner.shape.new(ShapeInner::Bool),
            num_slots: 0,
        }
    }

    fn top_level_slots_impl<'a>(
        &self,
        customs: impl MapRef<'a, I, Shape<I>>,
        next_slot: usize,
        slots: &mut BTreeSet<SlotId>,
    ) -> usize {
        match &*self.inner {
            ShapeInner::Bool | ShapeInner::Num(_) => next_slot,
            ShapeInner::Tuple(shapes) => shapes.iter().fold(next_slot, |start, shape| {
                shape.top_level_slots_impl(customs, start, slots)
            }),
            ShapeInner::Variants(shapes) => shapes.values().fold(next_slot, |start, shape| {
                shape.top_level_slots_impl(customs, start, slots)
            }),
            // Since non-trivial cyclic customs are always guarded, this case only occurs if the
            // custom is trivial, i.e. has no slots.
            ShapeInner::SelfCustom(_) => next_slot,
            ShapeInner::Custom(id) => customs
                .get(id)
                .top_level_slots_impl(customs, next_slot, slots),
            ShapeInner::Array(shape) | ShapeInner::HoleArray(shape) | ShapeInner::Boxed(shape) => {
                debug_assert!(!slots.contains(&SlotId(next_slot)));
                slots.insert(SlotId(next_slot));
                next_slot + 1 + shape.num_slots
            }
        }
    }

    pub fn top_level_slots<'a>(&self, customs: impl MapRef<'a, I, Shape<I>>) -> BTreeSet<SlotId> {
        let mut slots = BTreeSet::new();
        self.top_level_slots_impl(customs, 0, &mut slots);
        slots
    }

    fn positions_impl<'a, J: Id + 'static>(
        &self,
        customs: impl MapRef<'a, I, CustomTypeDef<I, J>>,
        sccs: &Sccs<J, I>,
        pos: Position,
        result: &mut Vec<Position>,
    ) {
        match &*self.inner {
            ShapeInner::Bool | ShapeInner::Num(_) => {}
            ShapeInner::Tuple(shapes) => {
                for shape in shapes {
                    shape.positions_impl(customs, sccs, pos, result);
                }
            }
            ShapeInner::Variants(shapes) => {
                for (_, shape) in shapes {
                    shape.positions_impl(customs, sccs, pos, result);
                }
            }
            ShapeInner::SelfCustom(_) => {
                panic!(
                    "`Shape::positions` was called directly on the (folded) content of a \
                      non-trivial cyclic custom, which is almost certainly a bug."
                )
            }
            ShapeInner::Custom(id) => {
                let custom = customs.get(id);
                if sccs.component(custom.scc).kind == SccKind::Cyclic {
                    if custom.can_guard == CanGuard::Yes {
                        assert!(
                            pos == Position::Heap,
                            "`Shape::positions` was called on a type with a non-trival cyclic \
                             custom in stack position",
                        );
                        result.extend(iter::repeat(Position::Heap).take(custom.num_slots));
                    } else {
                        // If a custom is cyclic but can't be guarded it is necessarily trivial and
                        // we needn't do anything.
                    }
                } else {
                    custom.content.positions_impl(customs, sccs, pos, result);
                }
            }
            ShapeInner::Array(shape) | ShapeInner::HoleArray(shape) | ShapeInner::Boxed(shape) => {
                result.push(pos);
                shape.positions_impl(customs, sccs, Position::Heap, result);
            }
        }
    }

    pub fn positions<'a, J: Id + 'static>(
        &self,
        customs: &IdVec<I, CustomTypeDef<I, J>>,
        sccs: &Sccs<J, I>,
    ) -> Vec<Position> {
        let mut result = Vec::new();
        self.positions_impl(customs, sccs, Position::Stack, &mut result);
        debug_assert_eq!(result.len(), self.num_slots);
        result
    }

    pub fn gen_resources<'a, M, L, J: Id + 'static>(
        &self,
        customs: &IdVec<I, CustomTypeDef<I, J>>,
        sccs: &Sccs<J, I>,
        mut next_mode: impl FnMut() -> M,
        mut next_lt: impl FnMut() -> L,
    ) -> IdVec<SlotId, Res<M, L>> {
        IdVec::from_vec(
            self.positions(customs, sccs)
                .into_iter()
                .map(|pos| Res {
                    modes: match pos {
                        Position::Stack => ResModes::Stack(next_mode()),
                        Position::Heap => ResModes::Heap(HeapModes {
                            access: next_mode(),
                            storage: next_mode(),
                        }),
                    },
                    lt: next_lt(),
                })
                .collect(),
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Position {
    Stack,
    Heap,
}

#[derive(Clone, Debug)]
enum FlatIterState<'a, M, L> {
    YieldInner,
    YieldExtra(&'a M, &'a L),
}

#[derive(Debug)]
struct FlatIter<'a, M, L> {
    state: FlatIterState<'a, M, L>,
    inner_iter: std::slice::Iter<'a, Res<M, L>>,
}

impl<'a, M, L> Iterator for FlatIter<'a, M, L> {
    type Item = (&'a M, &'a L);

    fn next(&mut self) -> Option<Self::Item> {
        match self.state {
            FlatIterState::YieldInner => {
                let res = self.inner_iter.next()?;
                match &res.modes {
                    ResModes::Stack(stack) => Some((stack, &res.lt)),
                    ResModes::Heap(HeapModes { access, storage }) => {
                        self.state = FlatIterState::YieldExtra(storage, &res.lt);
                        Some((access, &res.lt))
                    }
                }
            }
            FlatIterState::YieldExtra(next_mode, next_lt) => {
                self.state = FlatIterState::YieldInner;
                Some((next_mode, next_lt))
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Type<M, L, I> {
    shape: Shape<I>,
    res: IdVec<SlotId, Res<M, L>>,
}

pub type TypeFo<M, L> = Type<M, L, first_ord::CustomTypeId>;

impl<M, L, I: Id + 'static> Type<M, L, I> {
    pub fn new(shape: Shape<I>, res: IdVec<SlotId, Res<M, L>>) -> Self {
        debug_assert_eq!(shape.num_slots, res.len());
        Type { shape, res }
    }

    pub fn unit(interner: &Interner<I>) -> Self {
        Type {
            shape: Shape::unit(interner),
            res: IdVec::new(),
        }
    }

    pub fn bool_(interner: &Interner<I>) -> Self {
        Type {
            shape: Shape::bool_(interner),
            res: IdVec::new(),
        }
    }

    pub fn shape(&self) -> &Shape<I> {
        &self.shape
    }

    pub fn res(&self) -> &IdVec<SlotId, Res<M, L>> {
        &self.res
    }

    pub fn res_mut(&mut self) -> &mut IdVec<SlotId, Res<M, L>> {
        &mut self.res
    }

    pub fn iter(&self) -> impl Iterator<Item = &Res<M, L>> {
        self.res.values()
    }

    pub fn iter_modes(&self) -> impl Iterator<Item = &ResModes<M>> {
        self.iter().map(|res| &res.modes)
    }

    pub fn iter_lts(&self) -> impl Iterator<Item = &L> {
        self.iter().map(|res| &res.lt)
    }

    pub fn iter_flat(&self) -> impl Iterator<Item = (&M, &L)> {
        FlatIter {
            state: FlatIterState::YieldInner,
            inner_iter: self.res.values(),
        }
    }

    pub fn stack_lt<'a>(
        &self,
        customs: impl MapRef<'a, I, Shape<I>>,
    ) -> impl Iterator<Item = (SlotId, &L)> {
        self.shape
            .top_level_slots(customs)
            .into_iter()
            .map(|slot| (slot, &self.res[slot].lt))
    }
}

#[derive(Clone, Debug)]
pub struct ShapeIter<'a, T, I> {
    shapes: std::slice::Iter<'a, Shape<I>>,
    res: &'a [T],
    start: usize,
    off: usize,
}

impl<'a, T, I> Iterator for ShapeIter<'a, T, I> {
    type Item = (&'a Shape<I>, (usize, usize), &'a [T]);

    fn next(&mut self) -> Option<Self::Item> {
        let shape = self.shapes.next()?;
        let off = self.off;
        let end = off + shape.num_slots;
        let res = &self.res[off..end];
        self.off = end;
        Some((shape, (off + self.start, end + self.start), res))
    }
}

impl<'a, T, I> ExactSizeIterator for ShapeIter<'a, T, I> {
    fn len(&self) -> usize {
        self.shapes.len()
    }
}

pub fn enumerate_shapes<'a, T, I>(
    shapes: &'a [Shape<I>],
    res: &'a [T],
    start: usize,
) -> impl ExactSizeIterator<Item = (&'a Shape<I>, (usize, usize), &'a [T])> {
    ShapeIter {
        shapes: shapes.iter(),
        res,
        off: 0,
        start,
    }
}

pub fn iter_shapes<'a, T, I>(
    shapes: &'a [Shape<I>],
    res: &'a [T],
) -> impl ExactSizeIterator<Item = (&'a Shape<I>, &'a [T])> {
    enumerate_shapes(shapes, res, 0).map(|(shape, _, res)| (shape, res))
}

#[derive(Debug)]
pub struct ShapeIterMut<'a, T, I> {
    shapes: std::slice::Iter<'a, Shape<I>>,
    rest: &'a mut [T],
    start: usize,
}

impl<'a, T, I> Iterator for ShapeIterMut<'a, T, I> {
    type Item = (&'a Shape<I>, (usize, usize), &'a mut [T]);

    fn next(&mut self) -> Option<Self::Item> {
        let shape = self.shapes.next()?;

        let slice = std::mem::take(&mut self.rest);
        let (result, rest) = slice.split_at_mut(shape.num_slots);
        self.rest = rest;

        let start = self.start;
        let end = start + shape.num_slots;
        self.start = end;

        Some((shape, (start, end), result))
    }
}

impl<'a, T, I> ExactSizeIterator for ShapeIterMut<'a, T, I> {
    fn len(&self) -> usize {
        self.shapes.len()
    }
}

pub fn enumerate_shapes_mut<'a, T, I>(
    shapes: &'a [Shape<I>],
    res: &'a mut [T],
) -> impl ExactSizeIterator<Item = (&'a Shape<I>, (usize, usize), &'a mut [T])> {
    ShapeIterMut {
        shapes: shapes.iter(),
        rest: res,
        start: 0,
    }
}

pub fn iter_shapes_mut<'a, T, I>(
    shapes: &'a [Shape<I>],
    res: &'a mut [T],
) -> impl ExactSizeIterator<Item = (&'a Shape<I>, &'a mut [T])> {
    enumerate_shapes_mut(shapes, res).map(|(shape, _, res)| (shape, res))
}

pub fn join_everywhere<M: Clone, I: Id + 'static>(
    interner: &Interner<I>,
    ty: &Type<M, Lt, I>,
    new_lt: &Lt,
) -> Type<M, Lt, I> {
    let f = |res: &Res<M, Lt>| Res {
        modes: res.modes.clone(),
        lt: res.lt.join(interner, new_lt),
    };
    Type::new(
        ty.shape().clone(),
        IdVec::from_vec(ty.iter().map(f).collect()),
    )
}

pub fn lt_equiv<M, I: Id + 'static>(ty1: &Type<M, Lt, I>, ty2: &Type<M, Lt, I>) -> bool {
    debug_assert!(ty1.shape() == ty2.shape());
    ty1.iter()
        .zip_eq(ty2.iter())
        .all(|(res1, res2)| res1.lt == res2.lt)
}

pub fn nth_res_bounds<I>(shapes: &[Shape<I>], n: usize) -> (usize, usize) {
    let start = shapes.iter().map(|shape| shape.num_slots).take(n).sum();
    let end = start + shapes[n].num_slots;
    (start, end)
}

pub fn split_shapes<M: Clone, L: Clone, I: Id + 'static>(
    shapes: &[Shape<I>],
    res: &[Res<M, L>],
) -> Vec<Type<M, L, I>> {
    iter_shapes(shapes, res)
        .map(|(shape, res)| {
            Type::new(
                shape.clone(),
                IdVec::from_vec(res.iter().cloned().collect()),
            )
        })
        .collect()
}

pub fn elim_tuple<'a, M: Clone, L: Clone, I: Id + 'static>(
    ty: &Type<M, L, I>,
) -> Vec<Type<M, L, I>> {
    let ShapeInner::Tuple(shapes) = &*ty.shape().inner else {
        panic!("expected `Tuple` type");
    };
    split_shapes(shapes, ty.res().as_slice())
}

pub fn elim_variants<'a, M: Clone, L: Clone, I: Id + 'static>(
    ty: &Type<M, L, I>,
) -> IdVec<first_ord::VariantId, Type<M, L, I>> {
    let ShapeInner::Variants(shapes) = &*ty.shape().inner else {
        panic!("expected `Tuple` type");
    };
    let result = split_shapes(shapes.as_slice(), ty.res().as_slice());
    assert_eq!(result.len(), shapes.len());
    IdVec::from_vec(result)
}

pub fn elim_box_like<M: Clone, L: Clone, I: Id + 'static>(
    item: &Shape<I>,
    res: &[Res<M, L>],
) -> (Res<M, L>, Type<M, L, I>) {
    (
        res[0].clone(),
        Type::new(
            item.clone(),
            IdVec::from_vec(res[1..].iter().cloned().collect()),
        ),
    )
}

pub fn elim_array<M: Clone, L: Clone, I: Id + 'static>(
    ty: &Type<M, L, I>,
) -> (Res<M, L>, Type<M, L, I>) {
    let ShapeInner::Array(shape) = &*ty.shape().inner else {
        panic!("expected `Array` type");
    };
    elim_box_like(shape, ty.res().as_slice())
}

pub fn elim_boxed<M: Clone, L: Clone, I: Id + 'static>(
    ty: &Type<M, L, I>,
) -> (Res<M, L>, Type<M, L, I>) {
    let ShapeInner::Boxed(shape) = &*ty.shape().inner else {
        panic!("expected `Boxed` type");
    };
    elim_box_like(shape, ty.res().as_slice())
}

pub fn arg_path(path: &Path, arg_idx: usize, num_args: usize) -> Path {
    if num_args > 1 {
        path.seq(arg_idx)
    } else {
        path.clone()
    }
}

pub fn bind_lts<M, I: Id + 'static>(
    interner: &Interner<I>,
    ty1: &Type<M, LtParam, I>,
    ty2: &Type<M, Lt, I>,
) -> BTreeMap<LtParam, Lt> {
    debug_assert!(ty1.shape() == ty2.shape());
    let mut result = BTreeMap::new();
    for (res1, res2) in ty1.iter().zip_eq(ty2.iter()) {
        result
            .entry(res1.lt)
            .and_modify(|old: &mut Lt| *old = old.join(interner, &res2.lt))
            .or_insert_with(|| res2.lt.clone());
    }
    result
}

pub fn subst_lts<M: Clone, I: Id + 'static>(
    interner: &Interner<I>,
    ty: &Type<M, Lt, I>,
    subst: &BTreeMap<LtParam, Lt>,
) -> Type<M, Lt, I> {
    let f = |res: &Res<M, Lt>| {
        let modes = res.modes.clone();
        let lt = match &res.lt {
            Lt::Empty => Lt::Empty,
            Lt::Local(lt) => Lt::Local(lt.clone()),
            Lt::Join(params) => params
                .iter()
                .map(|p| &subst[p])
                .fold(Lt::Empty, |lt1, lt2| lt1.join(interner, lt2)),
        };
        Res { modes, lt }
    };
    Type::new(
        ty.shape().clone(),
        IdVec::from_vec(ty.iter().map(f).collect()),
    )
}

/// Our analysis makes the following approximation: from the perspective of a function's caller all
/// accesses the callee makes to its arguments happen at the same time. To implement this behavior,
/// we use `prepare_arg_type` to replace all local lifetimes in the argument with the caller's
/// current path. Even if we didn't make this approximation, we would have to somehow relativize the
/// local lifetimes in the argument since they are not meaningful in the caller's scope.
pub fn prepare_arg_type<M: Clone, I: Id + 'static>(
    interner: &Interner<I>,
    path: &Path,
    ty: &Type<M, Lt, I>,
) -> Type<M, Lt, I> {
    let f = |res: &Res<M, Lt>| {
        let modes = res.modes.clone();
        let lt = match &res.lt {
            Lt::Empty => Lt::Empty,
            Lt::Local(_) => path.as_lt(interner),
            Lt::Join(vars) => Lt::Join(vars.clone()),
        };
        Res { modes, lt }
    };
    Type::new(
        ty.shape().clone(),
        IdVec::from_vec(ty.res().values().map(f).collect()),
    )
}

pub fn wrap_lts<M: Clone, I: Id + 'static>(ty: &Type<M, LtParam, I>) -> Type<M, Lt, I> {
    let f = |res: &Res<M, LtParam>| Res {
        modes: res.modes.clone(),
        lt: Lt::Join(NonEmptySet::new(res.lt)),
    };
    Type::new(
        ty.shape().clone(),
        IdVec::from_vec(ty.iter().map(f).collect()),
    )
}

fn extract_custom_content<I: Id + 'static>(interner: &Interner<I>, shape: &Shape<I>) -> Shape<I> {
    match &*shape.inner {
        ShapeInner::Bool => Shape {
            inner: interner.shape.new(ShapeInner::Bool),
            num_slots: 0,
        },
        ShapeInner::Num(num_type) => Shape {
            inner: interner.shape.new(ShapeInner::Num(*num_type)),
            num_slots: 0,
        },
        ShapeInner::Tuple(items) => {
            let items = items
                .iter()
                .map(|shape| extract_custom_content(interner, shape))
                .collect::<Vec<_>>();
            let num_slots = items.iter().map(|shape| shape.num_slots).sum();
            let shape = ShapeInner::Tuple(items);
            let inner = interner.shape.new(shape);
            Shape { inner, num_slots }
        }
        ShapeInner::Variants(variants) => {
            let variants = variants
                .values()
                .map(|shape| extract_custom_content(interner, shape))
                .collect::<Vec<_>>();
            let num_slots = variants.iter().map(|shape| shape.num_slots).sum();
            let shape = ShapeInner::Variants(IdVec::from_vec(variants));
            let inner = interner.shape.new(shape);
            Shape { inner, num_slots }
        }
        ShapeInner::Custom(id) => Shape {
            inner: interner.shape.new(ShapeInner::Custom(*id)),
            num_slots: shape.num_slots,
        },
        ShapeInner::SelfCustom(id) => Shape {
            inner: interner.shape.new(ShapeInner::Custom(*id)),
            num_slots: shape.num_slots,
        },
        ShapeInner::Array(item_shape) => {
            let item_shape = extract_custom_content(interner, item_shape);
            let num_slots = 1 + item_shape.num_slots;
            let shape = ShapeInner::Array(item_shape);
            let inner = interner.shape.new(shape);
            Shape { inner, num_slots }
        }
        ShapeInner::HoleArray(item_shape) => {
            let item_shape = extract_custom_content(interner, item_shape);
            let num_slots = 1 + item_shape.num_slots;
            let shape = ShapeInner::HoleArray(item_shape);
            let inner = interner.shape.new(shape);
            Shape { inner, num_slots }
        }
        ShapeInner::Boxed(item_shape) => {
            let item_shape = extract_custom_content(interner, item_shape);
            let num_slots = 1 + item_shape.num_slots;
            let shape = ShapeInner::Boxed(item_shape);
            let inner = interner.shape.new(shape);
            Shape { inner, num_slots }
        }
    }
}

fn unfold_impl<M: Clone, L: Clone, I: Id + 'static, J: Id>(
    interner: &Interner<I>,
    customs: &IdVec<I, CustomTypeDef<I, J>>,
    sccs: &Sccs<J, I>,
    recipe: &RecipeContent<I>,
    shape: &Shape<I>,
    res: &[Res<M, L>],
    out_res: &mut IdVec<SlotId, Res<M, L>>,
) -> Shape<I> {
    match (&*shape.inner, recipe) {
        (ShapeInner::Bool, RecipeContent::Bool) => {
            debug_assert!(res.is_empty());
            shape.clone()
        }
        (ShapeInner::Num(_), RecipeContent::Num(_)) => {
            debug_assert!(res.is_empty());
            shape.clone()
        }
        (ShapeInner::Tuple(shapes), RecipeContent::Tuple(recipes)) => {
            let shapes = iter_shapes(shapes, res)
                .zip_eq(recipes)
                .map(|((shape, res), recipe)| {
                    unfold_impl(interner, customs, sccs, recipe, shape, res, out_res)
                })
                .collect::<Vec<_>>();

            let num_slots = shapes.iter().map(|shape| shape.num_slots).sum();
            let shape = ShapeInner::Tuple(shapes);
            let inner = interner.shape.new(shape);
            Shape { inner, num_slots }
        }
        (ShapeInner::Variants(shapes), RecipeContent::Variants(recipes)) => {
            let shapes = iter_shapes(shapes.as_slice(), res)
                .zip_eq(recipes.values())
                .map(|((shape, res), recipe)| {
                    unfold_impl(interner, customs, sccs, recipe, shape, res, out_res)
                })
                .collect::<Vec<_>>();

            let num_slots = shapes.iter().map(|shape| shape.num_slots).sum();
            let shape = ShapeInner::Variants(IdVec::from_vec(shapes));
            let inner = interner.shape.new(shape);
            Shape { inner, num_slots }
        }
        (ShapeInner::SelfCustom(_), _) => {
            panic!("`unfold` was called on the *content* of a custom type")
        }
        (ShapeInner::Custom(id1), RecipeContent::DoNothing(id2)) => {
            debug_assert_eq!(id1.to_index(), id2.to_index());
            debug_assert_eq!(res.len(), shape.num_slots);

            let _ = out_res.extend(res.iter().cloned());
            shape.clone()
        }
        (ShapeInner::Custom(id1), RecipeContent::Unfold(id2)) => {
            debug_assert_eq!(id1.to_index(), id2.to_index());
            let custom = &customs[*id1];
            let content_res = custom.subst_helper.do_subst(res);
            debug_assert_eq!(content_res.len(), custom.content.num_slots);

            let _ = out_res.extend(content_res);
            extract_custom_content(interner, &custom.content)
        }
        (ShapeInner::Array(item_shape), RecipeContent::Array(item_recipe)) => {
            let _ = out_res.push(res[0].clone());
            let item_shape = unfold_impl(
                interner,
                customs,
                sccs,
                item_recipe,
                item_shape,
                &res[1..],
                out_res,
            );
            let num_slots = 1 + item_shape.num_slots;
            Shape {
                inner: interner.shape.new(ShapeInner::Array(item_shape)),
                num_slots,
            }
        }
        (ShapeInner::HoleArray(item_shape), RecipeContent::HoleArray(item_recipe)) => {
            let _ = out_res.push(res[0].clone());
            let item_shape = unfold_impl(
                interner,
                customs,
                sccs,
                item_recipe,
                item_shape,
                &res[1..],
                out_res,
            );
            let num_slots = 1 + item_shape.num_slots;
            Shape {
                inner: interner.shape.new(ShapeInner::HoleArray(item_shape)),
                num_slots,
            }
        }
        (ShapeInner::Boxed(item_shape), RecipeContent::Boxed(item_recipe)) => {
            let _ = out_res.push(res[0].clone());
            let item_shape = unfold_impl(
                interner,
                customs,
                sccs,
                item_recipe,
                item_shape,
                &res[1..],
                out_res,
            );
            let num_slots = 1 + item_shape.num_slots;
            Shape {
                inner: interner.shape.new(ShapeInner::Boxed(item_shape)),
                num_slots,
            }
        }
        _ => panic!("shape and recipe do not match"),
    }
}

pub fn unfold<M: Clone, L: Clone, I: Id + 'static, J: Id>(
    interner: &Interner<I>,
    customs: &IdVec<I, CustomTypeDef<I, J>>,
    sccs: &Sccs<J, I>,
    recipe: &UnfoldRecipe<I>,
    ty: &Type<M, L, I>,
) -> Type<M, L, I> {
    let mut res = IdVec::new();
    let shape = match recipe {
        UnfoldRecipe::UnfoldThenRecurse(recipe) => {
            let ShapeInner::Custom(id) = &*ty.shape().inner else {
                unreachable!();
            };
            let custom = &customs[*id];
            unfold_impl(
                interner,
                customs,
                sccs,
                recipe,
                &extract_custom_content(interner, &custom.content),
                &custom.subst_helper.do_subst(ty.res().as_slice()),
                &mut res,
            )
        }
        UnfoldRecipe::Recurse(recipe) => unfold_impl(
            interner,
            customs,
            sccs,
            recipe,
            &ty.shape(),
            ty.res().as_slice(),
            &mut res,
        ),
    };
    Type::new(shape, res)
}

#[derive(Clone, Debug)]
pub struct Occur<M, L> {
    pub id: guard::LocalId,
    pub ty: Type<M, L, first_ord::CustomTypeId>,
}

#[derive(Clone, Debug)]
pub enum ArrayOp<M, L> {
    Get(
        Occur<M, L>,                         // Array
        Occur<M, L>,                         // Index
        Type<M, L, first_ord::CustomTypeId>, // Return type; needed for retain insertion
    ), // Returns item
    Extract(
        Occur<M, L>, // Array
        Occur<M, L>, // Index
    ), // Returns tuple (item, hole array)
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
    // Returns array of bytes
    Input,
    // Takes array of bytes, returns unit
    Output(Occur<M, L>),
}

#[derive(Clone, Debug)]
pub enum Expr<M, L> {
    Local(Occur<M, L>),
    Call(Purity, first_ord::CustomFuncId, Occur<M, L>),
    LetMany(
        Vec<(TypeFo<M, L>, Expr<M, L>, Metadata)>, // Bound values. Each is assigned a new sequential `LocalId`
        Occur<M, L>,                               // Result
    ),

    If(Occur<M, L>, Box<Expr<M, L>>, Box<Expr<M, L>>),
    CheckVariant(first_ord::VariantId, Occur<M, L>), // Returns a bool
    Unreachable(TypeFo<M, L>),

    Tuple(Vec<Occur<M, L>>),
    TupleField(Occur<M, L>, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, TypeFo<M, L>>,
        first_ord::VariantId,
        Occur<M, L>,
    ),
    UnwrapVariant(first_ord::VariantId, Occur<M, L>),
    WrapBoxed(
        Occur<M, L>,
        TypeFo<M, L>, // Output type
    ),
    UnwrapBoxed(
        Occur<M, L>,
        TypeFo<M, L>, // Output type
    ),
    WrapCustom(
        CustomTypeId,
        UnfoldRecipe<first_ord::CustomTypeId>,
        Occur<M, L>,
    ),
    UnwrapCustom(
        CustomTypeId,
        UnfoldRecipe<first_ord::CustomTypeId>,
        Occur<M, L>,
    ),

    Intrinsic(Intrinsic, Occur<M, L>),
    ArrayOp(ArrayOp<M, L>),
    IoOp(IoOp<M, L>),
    Panic(
        TypeFo<M, L>, // Return type
        Occur<M, L>,
    ),

    ArrayLit(TypeFo<M, L>, Vec<Occur<M, L>>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
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
    pub arg_ty: TypeFo<ModeParam, Lt>,
    pub ret_ty: TypeFo<ModeParam, LtParam>,
    pub constrs: Constrs,

    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument
    pub body: Expr<ModeSolution, Lt>,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct SubstHelper {
    // Maps from unfolded index to folded index
    mapping: Vec<SlotId>,
    res_len: usize,
}

fn is_identity(mapping: &[SlotId]) -> bool {
    mapping.iter().enumerate().all(|(i, slot)| slot.0 == i)
}

impl SubstHelper {
    pub fn new(kind: SccKind, mapping: Vec<SlotId>) -> Self {
        // Later passes assume that there is a one-to-one correspondence between the parameters of
        // custom types which appear on the stack (all such customs are acyclic after guarding) and
        // the slots that appear in the bodies of those custom types. In particular, this is
        // relevant when generating stack lifetimes (obligations for top-level slots). We make the
        // stronger assumption that the mapping is the identity because that simplifies those
        // passes. You would have to carefully revise every procedure in this part of the compiler
        // that unfolds a custom if you were to ever change this assumption.
        debug_assert!(kind == SccKind::Cyclic || is_identity(&mapping));
        let res_len = mapping.iter().map(|slot| slot.0).max().map_or(0, |x| x + 1);
        SubstHelper { mapping, res_len }
    }

    pub fn folded_to_unfolded_mapping(&self) -> BTreeMap<SlotId, Vec<SlotId>> {
        let mut result = BTreeMap::new();
        for (unfolded_idx, folded_idx) in self.mapping.iter().enumerate() {
            result
                .entry(*folded_idx)
                .or_insert_with(Vec::new)
                .push(SlotId(unfolded_idx));
        }
        result
    }

    /// Takes the resource list for a custom and transforms it into the resource list for that
    /// custom's body.
    pub fn do_subst<T: Clone>(&self, res: &[T]) -> Vec<T> {
        debug_assert_eq!(res.len(), self.res_len);
        self.mapping
            .iter()
            .map(|slot| res[slot.0].clone())
            .collect()
    }
}

#[derive(Clone, Debug)]
pub struct CustomTypeDef<I, J> {
    pub content: Shape<I>,
    pub subst_helper: SubstHelper,
    pub num_slots: usize,
    pub scc: J,
    pub can_guard: guarded::CanGuard,
}

pub type CustomTypeDefFo = CustomTypeDef<first_ord::CustomTypeId, flat::CustomTypeSccId>;

#[derive(Clone, Debug)]
pub struct CustomTypes<I: Id, J: Id> {
    // Guarded customs.
    pub types: IdVec<I, CustomTypeDef<I, J>>,
    // The SCCs of the *pre-guarded* customs.
    pub sccs: Sccs<J, I>,
}

impl<I: Id, J: Id> CustomTypes<I, J> {
    pub fn view_shapes(&self) -> impl MapRef<'_, I, Shape<I>> {
        FnWrap::wrap(|id| &self.types[id].content)
    }
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: CustomTypes<first_ord::CustomTypeId, flat::CustomTypeSccId>,
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
        let interner: Interner<first_ord::CustomTypeId> = Interner::empty();
        let new = |lt| interner.lt.new(lt);
        let path = Path::root().seq(0).alt(1, 3).seq(2276);
        let expected = Lt::Local(new(LocalLt::Seq(
            new(LocalLt::Alt(vec![
                None,
                Some(new(LocalLt::Seq(new(LocalLt::Final), 2276))),
                None,
            ])),
            0,
        )));
        assert_eq!(path.as_lt(&interner), expected);
    }

    #[test]
    fn test_join() {
        let interner: Interner<first_ord::CustomTypeId> = Interner::empty();
        let new = |lt| interner.lt.new(lt);
        let lhs = Lt::Local(new(LocalLt::Seq(
            new(LocalLt::Seq(
                new(LocalLt::Seq(
                    new(LocalLt::Alt(vec![
                        Some(new(LocalLt::Seq(new(LocalLt::Final), 0))),
                        Some(new(LocalLt::Seq(new(LocalLt::Final), 0))),
                        Some(new(LocalLt::Seq(new(LocalLt::Final), 0))),
                    ])),
                    1,
                )),
                0,
            )),
            0,
        )));
        let rhs = Path::root().seq(0).seq(0).seq(0).as_lt(&interner);
        let actual = lhs.join(&interner, &rhs);
        assert_eq!(actual, lhs);
    }

    #[test]
    fn test_lt_order() {
        let interner: Interner<first_ord::CustomTypeId> = Interner::empty();
        let new = |lt| interner.lt.new(lt);
        let lt = Lt::Local(new(LocalLt::Seq(
            new(LocalLt::Alt(vec![
                None,
                Some(new(LocalLt::Seq(new(LocalLt::Final), 2276))),
                None,
            ])),
            0,
        )));

        let before = Path::root().seq(0).alt(1, 3).seq(2275);
        let eq = Path::root().seq(0).alt(1, 3).seq(2276);
        let after = Path::root().seq(0).alt(1, 3).seq(2277);

        assert_eq!(lt.cmp_path(&before), Cmp::After);
        assert_eq!(lt.cmp_path(&eq), Cmp::Boundary);
        assert_eq!(lt.cmp_path(&after), Cmp::Before);
    }
}
