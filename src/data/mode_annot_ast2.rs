//! There are a few notable differences from the formalism:
//! - The AST is in A-normal form.
//! - We use nomial types ("custom" types) instead of mu types.
//! - In addition to the `Boxed` type (which is a plain reference counted allocation), we have the
//!   `Array` and `HoleArray` types, which require similar treatment during borrow inference because
//!   they have embedded reference counts.

use crate::data::first_order_ast::{self as first_ord, CustomTypeId};
use crate::data::flat_ast as flat;
use crate::data::guarded_ast as guard;
use crate::data::guarded_ast as guarded;
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
use id_collections::{id_type, IdVec};
use id_graph_sccs::Sccs;
use std::collections::BTreeSet;
use std::hash::Hash;

pub struct Interner {
    pub shape: intern::Interner<ShapeInner>,
    pub lt: intern::Interner<LocalLt>,
}

impl Interner {
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

    pub fn as_local_lt(&self, interner: &Interner) -> Interned<LocalLt> {
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

    pub fn as_lt(&self, interner: &Interner) -> Lt {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lt {
    Empty,
    Local(Interned<LocalLt>),
    Join(NonEmptySet<LtParam>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LocalLt {
    Final,
    // Represents ordered "events", e.g. the binding and body of a let.
    Seq(Interned<LocalLt>, usize),
    // Represents unordered "events", e.g. the arms of a match. Always contains at least one `Some`.
    Alt(Vec<Option<Interned<LocalLt>>>),
}

impl Lt {
    pub fn var(x: LtParam) -> Self {
        Lt::Join(NonEmptySet::new(x))
    }

    /// A join over the lifetime lattice: `l1 <= l2` iff, for every leaf of `l1`, there is a leaf of
    /// `l2` that occurs "later in time".
    ///
    /// Panics if `self` and `other` are not structurally compatible.
    pub fn join(&self, interner: &Interner, other: &Self) -> Self {
        match (self, other) {
            (Lt::Empty, l) | (l, Lt::Empty) => l.clone(),
            (Lt::Local(l1), Lt::Local(l2)) => Lt::Local(interner.lt.new(l1.join(interner, l2))),
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
    pub fn join(&self, interner: &Interner, rhs: &Self) -> Self {
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

#[derive(Debug, Clone)]
pub struct HeapModes<M> {
    pub access: M,
    pub storage: M,
}

#[derive(Debug, Clone)]
pub enum ResModes<M> {
    Stack(M),
    Heap(HeapModes<M>),
}

impl<M> ResModes<M> {
    pub fn map<N>(&self, f: impl Fn(&M) -> N) -> ResModes<N> {
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

    pub fn unwrap_stack(&self) -> &M {
        match self {
            ResModes::Stack(stack) => stack,
            ResModes::Heap(_) => panic!("called `unwrap_stack` on `ResModes::Heap`"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Res<M, L> {
    pub modes: ResModes<M>,
    pub lt: L,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelfInfo {
    Structural,
    Custom(flat::CustomTypeSccId),
}

impl SelfInfo {
    pub fn is_my_scc(&self, scc_id: flat::CustomTypeSccId) -> bool {
        match self {
            SelfInfo::Structural => false,
            SelfInfo::Custom(my_scc_id) => *my_scc_id == scc_id,
        }
    }
}

#[id_type]
pub struct SlotId(pub usize);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ShapeInner {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Shape>),
    Variants(IdVec<first_ord::VariantId, Shape>),
    Custom(first_ord::CustomTypeId),
    SelfCustom(first_ord::CustomTypeId),
    Array(Shape),
    HoleArray(Shape),
    Boxed(Shape),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Shape {
    pub inner: Interned<ShapeInner>,
    pub num_slots: usize,
}

impl Shape {
    pub fn unit(interner: &Interner) -> Shape {
        Shape {
            inner: interner.shape.new(ShapeInner::Tuple(vec![])),
            num_slots: 0,
        }
    }

    pub fn bool_(interner: &Interner) -> Shape {
        Shape {
            inner: interner.shape.new(ShapeInner::Bool),
            num_slots: 0,
        }
    }

    // We don't read SCCs directly from `customs` because this function is called before we have
    // fully computed all `CustomTypeDef`s in the same SCC as `ty`.
    pub fn from_guarded<'a>(
        interner: &Interner,
        customs: impl MapRef<'a, CustomTypeId, CustomTypeDef>,
        sccs: impl MapRef<'a, CustomTypeId, flat::CustomTypeSccId>,
        self_info: SelfInfo,
        ty: &guard::Type,
    ) -> Shape {
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
                let mut num_slots = 0;
                let inner = interner.shape.new(ShapeInner::Tuple(tys.map_refs(|ty| {
                    let shape = Shape::from_guarded(interner, customs, sccs, self_info, ty);
                    num_slots += shape.num_slots;
                    shape
                })));
                Shape { inner, num_slots }
            }
            guard::Type::Variants(tys) => {
                let mut num_slots = 0;
                let inner = interner
                    .shape
                    .new(ShapeInner::Variants(tys.map_refs(|_, ty| {
                        let shape = Shape::from_guarded(interner, customs, sccs, self_info, ty);
                        num_slots += shape.num_slots;
                        shape
                    })));
                Shape { inner, num_slots }
            }
            guard::Type::Custom(id) => {
                if self_info.is_my_scc(*sccs.get(id)) {
                    Shape {
                        inner: interner.shape.new(ShapeInner::SelfCustom(*id)),
                        num_slots: 0,
                    }
                } else {
                    Shape {
                        inner: interner.shape.new(ShapeInner::Custom(*id)),
                        num_slots: customs.get(id).content.num_slots,
                    }
                }
            }
            guard::Type::Array(ty) => {
                let shape = Shape::from_guarded(interner, customs, sccs, self_info, ty);
                Shape {
                    num_slots: shape.num_slots + 1,
                    inner: interner.shape.new(ShapeInner::Array(shape)),
                }
            }
            guard::Type::HoleArray(ty) => {
                let shape = Shape::from_guarded(interner, customs, sccs, self_info, ty);
                Shape {
                    num_slots: shape.num_slots + 1,
                    inner: interner.shape.new(ShapeInner::HoleArray(shape)),
                }
            }
            guard::Type::Boxed(ty) => {
                let shape = Shape::from_guarded(interner, customs, sccs, self_info, ty);
                Shape {
                    num_slots: shape.num_slots + 1,
                    inner: interner.shape.new(ShapeInner::Boxed(shape)),
                }
            }
        }
    }

    fn top_level_slots_impl<'a>(
        &self,
        customs: impl MapRef<'a, CustomTypeId, Shape>,
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

    pub fn top_level_slots<'a>(
        &self,
        customs: impl MapRef<'a, CustomTypeId, Shape>,
    ) -> BTreeSet<SlotId> {
        let mut slots = BTreeSet::new();
        self.top_level_slots_impl(customs, 0, &mut slots);
        slots
    }

    fn positions_impl<'a>(
        &self,
        customs: impl MapRef<'a, CustomTypeId, CustomTypeDef>,
        pos: Position,
        result: &mut Vec<Position>,
    ) {
        match &*self.inner {
            ShapeInner::Bool | ShapeInner::Num(_) => {}
            ShapeInner::Tuple(shapes) => {
                for shape in shapes {
                    shape.positions_impl(customs, pos, result);
                }
            }
            ShapeInner::Variants(shapes) => {
                for (_, shape) in shapes {
                    shape.positions_impl(customs, pos, result);
                }
            }
            ShapeInner::Custom(id) => match pos {
                Position::Stack => {
                    result.extend(&customs.get(id).pos);
                }
                Position::Heap => {
                    result.extend(customs.get(id).pos.iter().map(|_| Position::Heap));
                }
            },
            ShapeInner::SelfCustom(_) => {}
            ShapeInner::Array(shape) | ShapeInner::HoleArray(shape) | ShapeInner::Boxed(shape) => {
                result.push(pos);
                shape.positions_impl(customs, Position::Heap, result);
            }
        }
    }

    pub fn positions<'a>(
        &self,
        customs: impl MapRef<'a, CustomTypeId, CustomTypeDef>,
    ) -> Vec<Position> {
        let mut result = Vec::new();
        self.positions_impl(customs, Position::Stack, &mut result);
        assert!(result.len() == self.num_slots);
        result
    }

    pub fn gen_resources<'a, M, L>(
        &self,
        customs: impl MapRef<'a, CustomTypeId, CustomTypeDef>,
        mut next_mode: impl FnMut() -> M,
        mut next_lt: impl FnMut() -> L,
    ) -> IdVec<SlotId, Res<M, L>> {
        IdVec::from_vec(
            self.positions(customs)
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

#[derive(Clone, Debug)]
pub struct Type<M, L> {
    pub shape: Shape,
    pub res: IdVec<SlotId, Res<M, L>>,
}

impl<M, L> Type<M, L> {
    pub fn unit(interner: &Interner) -> Self {
        Type {
            shape: Shape::unit(interner),
            res: IdVec::new(),
        }
    }

    pub fn bool_(interner: &Interner) -> Self {
        Type {
            shape: Shape::bool_(interner),
            res: IdVec::new(),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Res<M, L>> {
        self.res.values()
    }

    pub fn iter_modes(&self) -> impl Iterator<Item = &ResModes<M>> {
        self.iter().map(|res| &res.modes)
    }

    pub fn iter_flat(&self) -> impl Iterator<Item = (&M, &L)> {
        FlatIter {
            state: FlatIterState::YieldInner,
            inner_iter: self.res.values(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ShapeIter<'a, T> {
    shapes: std::slice::Iter<'a, Shape>,
    res: &'a [T],
    start: usize,
}

impl<'a, T> Iterator for ShapeIter<'a, T> {
    type Item = (&'a Shape, (usize, usize), &'a [T]);

    fn next(&mut self) -> Option<Self::Item> {
        let shape = self.shapes.next()?;
        let start = self.start;
        let end = start + shape.num_slots;
        let res = &self.res[start..end];
        self.start = end;
        Some((shape, (start, end), res))
    }
}

impl<'a, T> ExactSizeIterator for ShapeIter<'a, T> {
    fn len(&self) -> usize {
        self.shapes.len()
    }
}

pub fn enumerate_shapes<'a, T>(
    shapes: &'a [Shape],
    res: &'a [T],
) -> impl ExactSizeIterator<Item = (&'a Shape, (usize, usize), &'a [T])> {
    ShapeIter {
        shapes: shapes.iter(),
        res,
        start: 0,
    }
}

pub fn iter_shapes<'a, T>(
    shapes: &'a [Shape],
    res: &'a [T],
) -> impl ExactSizeIterator<Item = (&'a Shape, &'a [T])> {
    enumerate_shapes(shapes, res).map(|(shape, _, res)| (shape, res))
}

#[derive(Debug)]
pub struct ShapeIterMut<'a, T> {
    shapes: std::slice::Iter<'a, Shape>,
    rest: &'a mut [T],
    start: usize,
}

impl<'a, T> Iterator for ShapeIterMut<'a, T> {
    type Item = (&'a Shape, (usize, usize), &'a mut [T]);

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

impl<'a, T> ExactSizeIterator for ShapeIterMut<'a, T> {
    fn len(&self) -> usize {
        self.shapes.len()
    }
}

pub fn enumerate_shapes_mut<'a, T>(
    shapes: &'a [Shape],
    res: &'a mut [T],
) -> impl ExactSizeIterator<Item = (&'a Shape, (usize, usize), &'a mut [T])> {
    ShapeIterMut {
        shapes: shapes.iter(),
        rest: res,
        start: 0,
    }
}

pub fn iter_shapes_mut<'a, T>(
    shapes: &'a [Shape],
    res: &'a mut [T],
) -> impl ExactSizeIterator<Item = (&'a Shape, &'a mut [T])> {
    enumerate_shapes_mut(shapes, res).map(|(shape, _, res)| (shape, res))
}

#[derive(Clone, Debug)]
pub struct Occur<M, L> {
    pub id: guard::LocalId,
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
    Input,               // Returns array of bytes
    Output(Occur<M, L>), // Takes array of bytes, returns unit
}

#[derive(Clone, Debug)]
pub enum Expr<M, L> {
    Local(Occur<M, L>),
    Call(Purity, first_ord::CustomFuncId, Occur<M, L>),
    LetMany(
        Vec<(Type<M, L>, Expr<M, L>, Metadata)>, // Bound values. Each is assigned a new sequential `LocalId`
        Occur<M, L>,                             // Result
    ),

    If(Occur<M, L>, Box<Expr<M, L>>, Box<Expr<M, L>>),
    CheckVariant(first_ord::VariantId, Occur<M, L>), // Returns a bool
    Unreachable(Type<M, L>),

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
pub struct CustomTypeDef {
    pub content: Shape,
    pub pos: Vec<Position>,
    pub scc: flat::CustomTypeSccId,
    pub can_guard: guarded::CanGuard,
}

#[derive(Clone, Debug)]
pub struct CustomTypes {
    pub types: IdVec<CustomTypeId, CustomTypeDef>,
    pub sccs: Sccs<flat::CustomTypeSccId, CustomTypeId>,
}

impl CustomTypes {
    pub fn view_shapes(&self) -> impl MapRef<'_, first_ord::CustomTypeId, Shape> {
        FnWrap::wrap(|id| &self.types[id].content)
    }
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
        let interner = Interner::empty();
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
        let interner = Interner::empty();
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
        let interner = Interner::empty();
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

        assert!(!lt.does_not_exceed(&before));
        assert!(lt.does_not_exceed(&eq)); // reflexivity
        assert!(lt.does_not_exceed(&after));

        assert!(lt.contains(&before));
        assert!(lt.contains(&eq));
        assert!(!lt.contains(&after));
    }
}
