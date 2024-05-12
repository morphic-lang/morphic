//! The output AST for the specializing variant of the inference pass from the borrow inference
//! paper.
//!
//! There are a few notable differences from the paper:
//! - The AST is in A-normal form.
//! - We use nomial types (called "custom" types) instead of mu types.
//! - In addition to the `Boxed` type (which is a plain reference counted allocation), we have the
//!   `Array` and `HoleArray`, which require similar treatment during borrow inference because they
//!   have an embedded reference count.

use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast::{self as first_ord, CustomTypeId};
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::inequality_graph2 as in_eq;
use crate::util::intern::InternTable;
use crate::util::iter::IterExt;
use crate::util::map_ext::Map;
use id_collections::{id_type, Count, Id, IdMap, IdVec};
use std::collections::{btree_set, BTreeSet};
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

#[id_type]
pub struct ModeVar(pub usize);

/// During constraint generation, modes are represented using `ModeVar`s. These get replaced by
/// `ModeParam`s when the constraints are solved.
#[id_type]
pub struct ModeParam(pub usize);

/// `lb` is the solution for variable `solver_var`, which we keep around for debugging purposes.
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

    fn elems(&self) -> impl Iterator<Item = PathElem> + '_ {
        self.0.iter().copied().rev()
    }

    pub fn as_local_lt(&self) -> LocalLt {
        let mut local_lt = LocalLt::Final;
        for elem in self.elems() {
            match elem {
                PathElem::Seq(i) => {
                    local_lt = LocalLt::Seq(Box::new(local_lt), i);
                }
                PathElem::Par { i, n } => {
                    let mut par = vec![None; n];
                    par[i] = Some(local_lt);
                    local_lt = LocalLt::Par(par);
                }
            }
        }
        local_lt
    }

    pub fn as_lt(&self) -> Lt {
        Lt::Local(self.as_local_lt())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NonEmptySet<T>(BTreeSet<T>);

impl<T> NonEmptySet<T> {
    pub fn singleton(value: T) -> Self
    where
        T: Ord,
    {
        Self(std::iter::once(value).collect())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter<'a>(&'a self) -> btree_set::Iter<'a, T> {
        self.0.iter()
    }
}

impl<'a, T> IntoIterator for &'a NonEmptySet<T> {
    type Item = &'a T;
    type IntoIter = btree_set::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> TryFrom<BTreeSet<T>> for NonEmptySet<T> {
    type Error = ();

    fn try_from(set: BTreeSet<T>) -> Result<Self, Self::Error> {
        if !set.is_empty() {
            Ok(Self(set))
        } else {
            Err(())
        }
    }
}

impl<T: Ord + Clone> std::ops::BitOr for &NonEmptySet<T> {
    type Output = NonEmptySet<T>;

    fn bitor(self, rhs: &NonEmptySet<T>) -> Self::Output {
        NonEmptySet(&self.0 | &rhs.0)
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
        Lt::Join(NonEmptySet::singleton(x))
    }

    /// A join over the lattice: `l1 <= l2` iff, for every leaf of `l1`, there is a leaf of `l2`
    /// that occurs "later in time".
    ///
    /// Panics if `self` and `other` are not structurally compatible.
    pub fn join(&mut self, other: &Self) {
        match (self, other) {
            (_, Lt::Empty) => {}
            (l1 @ Lt::Empty, l2) => *l1 = l2.clone(),
            (Lt::Local(l1), Lt::Local(l2)) => l1.join(l2),
            (Lt::Join(_), Lt::Local(_)) => {}
            (l1 @ Lt::Local(_), Lt::Join(s)) => *l1 = Lt::Join(s.clone()),
            (Lt::Join(s1), Lt::Join(s2)) => s1.0.extend(s2.0.iter().copied()),
        }
    }

    /// True iff no leaf of `self` occurs "later in time" than any leaf of `other`. This condition
    /// is non-transitive.
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
        // If we reach the end of `rhs`, then `rhs` is a prefix of `self` along the relevant branch.
        // Hence, `self` points to a subscope of the scope pointed to by `rhs`.
        true
    }
}

#[id_type]
pub struct SlotId(pub usize);

#[id_type]
pub struct OverlayId(pub usize);

#[derive(Clone, Debug)]
pub enum Overlay<A> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Overlay<A>>),
    Variants(IdVec<first_ord::VariantId, Overlay<A>>),
    SelfCustom(CustomTypeId),
    Custom(CustomTypeId, IdVec<SlotId, A>),
    Array(A),
    HoleArray(A),
    Boxed(A),
}

#[derive(Clone, Debug)]
pub struct AnnotOverlay<M> {
    ov: OverlayId,
    ms: IdVec<SlotId, M>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct OverlaySkeleton {
    ov: OverlayId,
    num_modes: Count<SlotId>,
}

impl<M: Copy> AnnotOverlay<M> {
    pub fn ms<'a>(&'a self) -> SlotIter<OverlayId, impl Iterator<Item = M> + 'a> {
        SlotIter::new(self.ov, self.ms.values().copied())
    }
}

impl<M> AnnotOverlay<M> {
    pub fn ms_mut<'a>(&'a mut self) -> SlotIter<OverlayId, impl Iterator<Item = &'a mut M> + 'a> {
        SlotIter::new(self.ov, self.ms.values_mut())
    }
}

#[id_type]
pub struct TypeId(pub usize);

#[derive(Clone, Debug)]
pub enum Type<A, B> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Type<A, B>>),
    Variants(IdVec<first_ord::VariantId, Type<A, B>>),
    SelfCustom(CustomTypeId),
    Custom(CustomTypeId, IdVec<SlotId, B>, IdVec<SlotId, A>),
    Array(A, Overlay<B>, Box<Type<A, B>>),
    HoleArray(A, Overlay<B>, Box<Type<A, B>>),
    Boxed(A, Overlay<B>, Box<Type<A, B>>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SlotKind {
    Stack,
    StackOverlay,
    Heap,
    HeapOverlay,
}

#[derive(Clone, Debug)]
pub struct AnnotType<M, L> {
    ty: TypeId,
    ks: Vec<SlotKind>,
    ms: IdVec<SlotId, M>,
    ls: IdVec<SlotId, L>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeSkeleton {
    ty: TypeId,
    num_slots: Count<SlotId>,
    num_overlay_slots: Count<SlotId>,
}

impl TypeSkeleton {
    fn num_nonoverlay_slots(&self) -> Count<SlotId> {
        Count::from_value(self.num_slots.to_value() - self.num_overlay_slots.to_value())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IterKind {
    All,
    OverlayOnly,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IterId(TypeId, IterKind);

impl<M, L> AnnotType<M, L> {
    pub fn ks<'a>(&'a self) -> SlotIter<IterId, impl Iterator<Item = SlotKind> + 'a> {
        SlotIter::new(IterId(self.ty, IterKind::All), self.ks.iter().copied())
    }

    pub fn ls<'a>(&'a self) -> SlotIter<IterId, impl Iterator<Item = &'a L> + 'a> {
        SlotIter::new(IterId(self.ty, IterKind::OverlayOnly), self.ls.values())
    }

    pub fn ms_mut<'a>(&'a mut self) -> SlotIter<IterId, impl Iterator<Item = &'a mut M> + 'a> {
        SlotIter::new(IterId(self.ty, IterKind::All), self.ms.values_mut())
    }

    pub fn ls_mut<'a>(&'a mut self) -> SlotIter<IterId, impl Iterator<Item = &'a mut L> + 'a> {
        SlotIter::new(IterId(self.ty, IterKind::OverlayOnly), self.ls.values_mut())
    }
}

impl<M: Copy, L> AnnotType<M, L> {
    pub fn ms<'a>(&'a self) -> SlotIter<IterId, impl Iterator<Item = M> + 'a> {
        SlotIter::new(IterId(self.ty, IterKind::All), self.ms.values().copied())
    }

    pub fn overlay_ms<'a>(&'a self) -> SlotIter<IterId, impl Iterator<Item = M> + 'a> {
        SlotIter::new(
            IterId(self.ty, IterKind::OverlayOnly),
            self.ms.values().zip(&self.ks).filter_map(|(m, k)| match k {
                SlotKind::Stack | SlotKind::Heap => Some(*m),
                _ => None,
            }),
        )
    }
}

fn parameterize_overlay(
    ty_table: &InternTable<TypeId, TypeSkeleton>,
    parameterized: &IdMap<CustomTypeId, TypeId>,
    customs: &IdVec<CustomTypeId, flat::CustomTypeDef>,
    sccs: &IdVec<CustomTypeId, flat::CustomTypeSccId>,
    self_id: Option<flat::CustomTypeSccId>,
    ty: &anon::Type,
    num_slots: &mut Count<SlotId>,
) -> Overlay<SlotId> {
    match ty {
        anon::Type::Bool => Overlay::Bool,
        anon::Type::Num(num_ty) => Overlay::Num(*num_ty),
        anon::Type::Tuple(tys) => Overlay::Tuple(
            tys.iter()
                .map(|ty| {
                    parameterize_overlay(
                        ty_table,
                        parameterized,
                        customs,
                        sccs,
                        self_id,
                        ty,
                        num_slots,
                    )
                })
                .collect(),
        ),
        anon::Type::Variants(tys) => Overlay::Variants(tys.map_refs(|_, ty| {
            parameterize_overlay(
                ty_table,
                parameterized,
                customs,
                sccs,
                self_id,
                ty,
                num_slots,
            )
        })),
        anon::Type::Custom(id) => {
            if self_id.map(|x| x == sccs[id]).unwrap_or(false) {
                Overlay::SelfCustom(*id)
            } else {
                let ty = ty_table.get(parameterized[id]);
                let subst = IdVec::from_count_with(ty.num_overlay_slots, |_| num_slots.inc());
                Overlay::Custom(*id, subst)
            }
        }
        anon::Type::Array(_) => Overlay::Array(num_slots.inc()),
        anon::Type::HoleArray(_) => Overlay::HoleArray(num_slots.inc()),
        anon::Type::Boxed(_) => Overlay::Boxed(num_slots.inc()),
    }
}

pub fn parameterize(
    ty_table: &InternTable<TypeId, TypeSkeleton>,
    parameterized: &IdMap<CustomTypeId, TypeId>,
    customs: &IdVec<CustomTypeId, flat::CustomTypeDef>,
    sccs: &IdVec<CustomTypeId, flat::CustomTypeSccId>,
    self_id: Option<flat::CustomTypeSccId>,
    ty: &anon::Type,
    num_slots: &mut Count<SlotId>,
) -> Type<SlotId, SlotId> {
    match ty {
        anon::Type::Bool => Type::Bool,
        anon::Type::Num(num_ty) => Type::Num(*num_ty),
        anon::Type::Tuple(tys) => Type::Tuple(
            tys.iter()
                .map(|ty| {
                    parameterize(
                        ty_table,
                        parameterized,
                        customs,
                        sccs,
                        self_id,
                        ty,
                        num_slots,
                    )
                })
                .collect(),
        ),
        anon::Type::Variants(tys) => Type::Variants(tys.map_refs(|_, ty| {
            parameterize(
                ty_table,
                parameterized,
                customs,
                sccs,
                self_id,
                ty,
                num_slots,
            )
        })),
        anon::Type::Custom(id) => {
            if self_id.map(|x| x == sccs[id]).unwrap_or(false) {
                Type::SelfCustom(*id)
            } else {
                let ty = ty_table.get(parameterized[id]);
                let ty_subst = IdVec::from_count_with(ty.num_slots, |_| num_slots.inc());
                let ov_subst = IdVec::from_count_with(ty.num_overlay_slots, |_| num_slots.inc());
                Type::Custom(*id, ov_subst, ty_subst)
            }
        }
        anon::Type::Array(ty) => Type::Array(
            num_slots.inc(),
            parameterize_overlay(
                ty_table,
                parameterized,
                customs,
                sccs,
                self_id,
                ty,
                num_slots,
            ),
            Box::new(parameterize(
                ty_table,
                parameterized,
                customs,
                sccs,
                self_id,
                ty,
                num_slots,
            )),
        ),
        anon::Type::HoleArray(ty) => Type::HoleArray(
            num_slots.inc(),
            parameterize_overlay(
                ty_table,
                parameterized,
                customs,
                sccs,
                self_id,
                ty,
                num_slots,
            ),
            Box::new(parameterize(
                ty_table,
                parameterized,
                customs,
                sccs,
                self_id,
                ty,
                num_slots,
            )),
        ),
        anon::Type::Boxed(ty) => Type::Boxed(
            num_slots.inc(),
            parameterize_overlay(
                ty_table,
                parameterized,
                customs,
                sccs,
                self_id,
                ty,
                num_slots,
            ),
            Box::new(parameterize(
                ty_table,
                parameterized,
                customs,
                sccs,
                self_id,
                ty,
                num_slots,
            )),
        ),
    }
}

/// An iterator over data corresponding to the "slots" of an annotated mode inference type or
/// overlay. This type helps ensure we don't perform non-sense operations on such data, e.g. zipping
/// together data from difference types.
pub struct SlotIter<I, J> {
    pub id: I,
    pub inner: J,
}

impl<'a, I: Eq, J, A> SlotIter<I, J>
where
    J: Iterator<Item = A>,
{
    pub fn new(id: I, inner: J) -> Self {
        SlotIter { id, inner }
    }

    pub fn zip<B>(
        self,
        other: SlotIter<I, impl Iterator<Item = B>>,
    ) -> SlotIter<I, impl Iterator<Item = (A, B)>> {
        assert!(self.id == other.id);
        SlotIter::new(self.id, self.inner.zip_eq(other.inner))
    }

    pub fn map<B>(self, f: impl FnMut(A) -> B) -> SlotIter<I, impl Iterator<Item = B>> {
        SlotIter::new(self.id, self.inner.map(f))
    }

    pub fn for_each(self, f: impl FnMut(A)) {
        self.inner.for_each(f)
    }

    pub fn fold<B>(self, init: B, f: impl FnMut(B, A) -> B) -> B {
        self.inner.fold(init, f)
    }
}

/// Returns the meet of two types over the lifetime lattice. This meet is "left" in the sense that
/// the modes of the first argument are retained.
pub fn left_meet<M>(this: &mut AnnotType<M, Lt>, other: &AnnotType<M, Lt>) {
    this.ls_mut().zip(other.ls()).for_each(|(l1, l2)| {
        l1.join(l2);
    })
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
        Vec<(AnnotType<M, L>, Expr<M, L>)>, // bound values.  Each is assigned a new sequential LocalId
        Occur<M, L>,                        // body
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

/// `sig` holds the constraints on the mode parameters of the relevant function's signature. We keep
/// around a copy of all of the constraints generated during inference in `all` for debugging.
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
pub struct CustomTypes {
    pub types: IdVec<CustomTypeId, TypeId>,
    pub type_table: InternTable<TypeId, TypeSkeleton>,
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
