//! The output AST for the specializing variant of the inference pass from the borrow inference
//! paper.
//!
//! There are a few notable differences from the paper:
//! - We use nomial types (called "custom" types in this compiler) instead of mu types.
//! - The AST is in A-normal form.
//! - In addition to the type `Boxed` (which is a plain reference counted allocation), we have the
//!   types `Array` and `HoleArray`, which need similar treatment during borrow inference because
//!   they have an embedded reference count.

use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast::{self as first_ord, CustomTypeId};
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::inequality_graph2 as in_eq;
use crate::util::iter::IterExt;
use id_collections::{id_type, Count, IdVec};
use id_graph_sccs::Sccs;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::Hash;

// TODO: instead of representing types structurally, we might be able to get away with just
// representing them as a `Vec` of modes in many places

#[id_type]
pub struct ModeVar(pub usize);

#[id_type]
pub struct ModeParam(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    Borrowed,
    Owned,
}

pub type ModeLowerBound = in_eq::LowerBound<ModeParam, Mode>;

/// During constraint generation, modes are represented using `ModeVar`s. These get replaced by
/// `ModeParam`s when the constraints are solved. `lb` is the solution. We keep around the
/// generation-phase representation, `solver_var`, purely for debugging purposes.
#[derive(Debug, Clone)]
pub struct ModeSolution {
    pub lb: ModeLowerBound,
    pub solver_var: ModeVar,
}

impl in_eq::BoundedSemilattice for Mode {
    fn join_mut(&mut self, other: &Self) {
        *self = (*self).max(*other);
    }

    fn least() -> Self {
        Mode::Borrowed
    }
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
        let mut lt = LocalLt::Final;
        for elem in self.elems() {
            match elem {
                PathElem::Seq(i) => {
                    lt = LocalLt::Seq(Box::new(lt), i);
                }
                PathElem::Par { i, n } => {
                    let mut par = vec![None; n];
                    par[i] = Some(lt);
                    lt = LocalLt::Par(par);
                }
            }
        }
        lt
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

    pub fn iter<'a>(&'a self) -> std::collections::btree_set::Iter<'a, T> {
        self.0.iter()
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

impl<'a, T> IntoIterator for &'a NonEmptySet<T> {
    type Item = &'a T;
    type IntoIter = std::collections::btree_set::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
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
    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Lt::Empty, l) | (l, Lt::Empty) => l.clone(),
            (Lt::Local(l1), Lt::Local(l2)) => Lt::Local(l1.join(l2)),
            (Lt::Join(s), Lt::Local(_)) | (Lt::Local(_), Lt::Join(s)) => Lt::Join(s.clone()),
            (Lt::Join(s1), Lt::Join(s2)) => Lt::Join(s1 | s2),
        }
    }

    /// True iff no leaf of `self` occurs "later in time" than any leaf of `other`. This condition
    /// is non-transitive.
    ///
    /// Panics if `self` and `other` are not structurally compatible.
    pub fn does_not_exceed(&self, other: &Path) -> bool {
        match (self, other) {
            (Lt::Empty, _) => true,
            (Lt::Local(lt), p) => lt.does_not_exceed(p),
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
        // If we reach the end of `rhs`, then `rhs` is a prefix of `self` along the relevant branch.
        // Hence, `self` points to a subscope of the scope pointed to by `rhs`.
        true
    }
}

#[derive(Clone, Debug)]
pub struct Occur<M, L> {
    pub id: flat::LocalId,
    pub ty: Type<M, L>,
    pub is_final: Selector,
}

#[derive(Clone, Debug)]
pub enum ArrayOp<M, L> {
    Get(
        Type<M, L>,  // Item type (of input)
        Occur<M, L>, // Array
        Occur<M, L>, // Index
        Type<M, L>,  // Return type; needed for retain/release insertion
    ), // Returns item
    Extract(
        Type<M, L>,  // Item type (of input)
        Occur<M, L>, // Array
        Occur<M, L>, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        Type<M, L>,  // Item type (of input)
        Occur<M, L>, // Array
    ), // Returns int
    Push(
        Type<M, L>,  // Item type (of input)
        Occur<M, L>, // Array
        Occur<M, L>, // Item
    ), // Returns new array
    Pop(
        Type<M, L>,  // Item type (of input)
        Occur<M, L>, // Array
    ), // Returns tuple (array, item)
    Replace(
        Type<M, L>,  // Item type (of input)
        Occur<M, L>, // Hole array
        Occur<M, L>, // Item
    ), // Returns new array
    Reserve(
        Type<M, L>,  // Item type (of input)
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
        Vec<(Type<M, L>, Expr<M, L>)>, // bound values.  Each is assigned a new sequential LocalId
        Occur<M, L>,                   // body
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
    Panic(Type<M, L>, Occur<M, L>),

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OverlaySubst<M>(pub BTreeMap<ModeParam, M>);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Overlay<A, B> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Overlay<A, B>>),
    Variants(IdVec<first_ord::VariantId, Overlay<A, B>>),
    SelfCustom(CustomTypeId),
    Custom(CustomTypeId, A),
    Array(B),
    HoleArray(B),
    Boxed(B),
}

impl<A, B> Overlay<A, B> {
    pub fn update_with(
        &mut self,
        other: &Overlay<A, B>,
        mut f: impl FnMut(&mut A, &A),
        mut g: impl FnMut(&mut B, &B),
    ) {
        match (self, other) {
            (Overlay::Bool, Overlay::Bool) => {}
            (Overlay::Num(n1), Overlay::Num(n2)) if n1 == n2 => {}
            (Overlay::Tuple(lhs), Overlay::Tuple(rhs)) => {
                for (lhs, rhs) in lhs.iter_mut().zip_eq(rhs) {
                    lhs.update_with(rhs, &mut f, &mut g);
                }
            }
            (Overlay::Variants(lhs), Overlay::Variants(rhs)) => {
                for (lhs, rhs) in lhs.values_mut().zip_eq(rhs.values()) {
                    lhs.update_with(rhs, &mut f, &mut g);
                }
            }
            (Overlay::SelfCustom(id1), Overlay::SelfCustom(id2)) if id1 == id2 => {}
            (Overlay::Custom(id1, lhs), Overlay::Custom(id2, rhs)) if id1 == id2 => {
                f(lhs, rhs);
            }
            (Overlay::Array(lhs), Overlay::Array(rhs))
            | (Overlay::HoleArray(lhs), Overlay::HoleArray(rhs))
            | (Overlay::Boxed(lhs), Overlay::Boxed(rhs)) => {
                g(lhs, rhs);
            }
            _ => unreachable!(),
        }
    }
}

pub type ModeOverlay<M> = Overlay<OverlaySubst<M>, M>;

impl<M: Clone> OverlaySubst<M> {
    pub fn apply_to(&self, overlay: &ModeOverlay<ModeParam>) -> ModeOverlay<M> {
        overlay
            .items()
            .map(&|_, subst| subst.map_vals(|m| self.0[m].clone()), &|m| {
                self.0
                    .get(m)
                    .expect(format!("missing mode param: {:?}", m).as_str())
                    .clone()
            })
            .collect_ov()
    }

    pub fn map_vals<M2>(&self, mut f: impl FnMut(&M) -> M2) -> OverlaySubst<M2> {
        OverlaySubst(self.0.iter().map(|(p, m)| (*p, f(m))).collect())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MoveStatus {
    Present,
    Absent,
}

pub type Selector = Overlay<IdVec<LtParam, MoveStatus>, MoveStatus>;

impl Selector {
    pub fn from_ty<M: Clone, L>(ty: &Type<M, L>, leaf: MoveStatus) -> Self {
        match ty {
            Type::Bool => Overlay::Bool,
            Type::Num(num_ty) => Overlay::Num(*num_ty),
            Type::Tuple(field_tys) => Overlay::Tuple(
                field_tys
                    .iter()
                    .map(|ty| Selector::from_ty(ty, leaf))
                    .collect(),
            ),
            Type::Variants(variant_tys) => {
                Overlay::Variants(variant_tys.map_refs(|_, ty| Selector::from_ty(ty, leaf)))
            }
            Type::SelfCustom(id) => Overlay::SelfCustom(*id),
            Type::Custom(id, tsub, _) => Overlay::Custom(*id, tsub.lts.map_refs(|_, _| leaf)),
            Type::Array(_, _, _, _) => Overlay::Array(leaf),
            Type::HoleArray(_, _, _, _) => Overlay::HoleArray(leaf),
            Type::Boxed(_, _, _, _) => Overlay::Boxed(leaf),
        }
    }

    pub fn and_eq(&mut self, other: &Selector) {
        let compute_status = |lhs, rhs| match (lhs, rhs) {
            (MoveStatus::Present, MoveStatus::Present) => MoveStatus::Present,
            _ => MoveStatus::Absent,
        };
        self.update_with(
            other,
            |lhs, rhs| {
                for (lhs, rhs) in lhs.values_mut().zip_eq(rhs.values()) {
                    *lhs = compute_status(*lhs, *rhs);
                }
            },
            |lhs, rhs| {
                *lhs = compute_status(*lhs, *rhs);
            },
        );
    }

    pub fn or_eq(&mut self, other: &Selector) {
        let compute_status = |lhs, rhs| match (lhs, rhs) {
            (MoveStatus::Absent, MoveStatus::Absent) => MoveStatus::Absent,
            _ => MoveStatus::Present,
        };
        self.update_with(
            other,
            |lhs, rhs| {
                for (lhs, rhs) in lhs.values_mut().zip_eq(rhs.values()) {
                    *lhs = compute_status(*lhs, *rhs);
                }
            },
            |lhs, rhs| {
                *lhs = compute_status(*lhs, *rhs);
            },
        );
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeSubst<M, L> {
    pub ms: IdVec<ModeParam, M>,
    pub lts: IdVec<LtParam, L>,
}

impl<M: Clone, L: Clone> TypeSubst<M, L> {
    pub fn apply_to(&self, ty: &Type<ModeParam, LtParam>) -> Type<M, L> {
        ty.items()
            .map(
                &|_, (tsub, osub)| {
                    (
                        tsub.map_vals(|m| self.ms[m].clone(), |lt| self.lts[lt].clone()),
                        osub.map_vals(|m| self.ms[m].clone()),
                    )
                },
                &|(m, lt)| (self.ms[m].clone(), self.lts[lt].clone()),
                &|_, osub| osub.map_vals(|m| self.ms[m].clone()),
                &|m| self.ms[m].clone(),
            )
            .collect_ty()
    }

    pub fn map_vals<M2, L2>(
        &self,
        mut f: impl FnMut(&M) -> M2,
        mut g: impl FnMut(&L) -> L2,
    ) -> TypeSubst<M2, L2> {
        TypeSubst {
            ms: self.ms.map_refs(|_, m| f(m)),
            lts: self.lts.map_refs(|_, lt| g(lt)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<M, L> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Type<M, L>>),
    Variants(IdVec<first_ord::VariantId, Type<M, L>>),
    SelfCustom(CustomTypeId),
    Custom(CustomTypeId, TypeSubst<M, L>, OverlaySubst<M>),
    Array(M, L, Box<Type<M, L>>, ModeOverlay<M>),
    HoleArray(M, L, Box<Type<M, L>>, ModeOverlay<M>),
    Boxed(M, L, Box<Type<M, L>>, ModeOverlay<M>),
}

impl<M: Clone> Type<M, Lt> {
    /// Returns the meet of two types over the lifetime lattice. This meet is "left" in the sense
    /// that the modes of the output are taken from the first argument.
    pub fn left_meet(&self, other: &Self) -> Self {
        self.items()
            .zip(other.items())
            .map(
                &|_, ((tsub1, osub1), (tsub2, _))| {
                    (
                        TypeSubst {
                            ms: tsub1.ms.clone(),
                            lts: IdVec::from_vec(
                                tsub1
                                    .lts
                                    .values()
                                    .zip_eq(tsub2.lts.values())
                                    .map(|(lt1, lt2)| lt1.join(&lt2))
                                    .collect(),
                            ),
                        },
                        osub1.clone(),
                    )
                },
                &|((m1, lt1), (_, lt2))| (m1.clone(), lt1.join(&lt2)),
                &|_, (osub1, _)| osub1.clone(),
                &|(m1, _)| m1.clone(),
            )
            .collect_ty()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    // Total number of params in `arg_type` and `ret_type`
    pub num_mode_params: Count<ModeParam>,
    pub num_lt_params: Count<LtParam>,

    // Return types are always "fully-flexible" in their lifetimes, i.e. contain only lifetime
    // parameters.
    pub arg_type: Type<ModeParam, Lt>,
    pub ret_type: Type<ModeParam, LtParam>,
}

/// `sig` describes the constraints relevant to the mode parameters of the function's signature. We
/// keep around a copy of all of the constraints generated for the function body during constraint
/// generation in `internal` for debugging purposes.
#[derive(Clone, Debug)]
pub struct FuncConstrs {
    pub sig: IdVec<ModeParam, ModeLowerBound>,
    pub internal: in_eq::ConstrGraph<ModeVar, Mode>,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub sig: Signature,
    pub constrs: FuncConstrs,

    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument
    pub body: Expr<ModeSolution, Lt>,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub num_mode_params: Count<ModeParam>,
    pub num_lt_params: Count<LtParam>,

    // The mode params in `overlay` are a subset of the mode params in `content`
    pub overlay_params: BTreeSet<ModeParam>,
    pub content: Type<ModeParam, LtParam>,
    pub overlay: ModeOverlay<ModeParam>, // TODO: remove; always compute from `content`
}

#[derive(Clone, Debug)]
pub struct CustomTypes {
    pub types: IdVec<CustomTypeId, TypeDef>,
    pub sccs: Sccs<flat::CustomTypeSccId, CustomTypeId>,
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

pub type Lazy<'a, T> = Box<dyn Fn() -> T + 'a>;
pub type DynIter<'a, T> = Box<dyn Iterator<Item = T> + 'a>;

/// An iterator like interface for overlays.
pub enum OverlayLike<'a, A, B> {
    Bool,
    Num(first_ord::NumType),
    Tuple(DynIter<'a, OverlayLike<'a, A, B>>),
    Variants(DynIter<'a, OverlayLike<'a, A, B>>),
    SelfCustom(CustomTypeId),
    Custom(CustomTypeId, A),
    Array(B),
    HoleArray(B),
    Boxed(B),
}

/// An iterator like interface for types.
pub enum TypeLike<'a, A, B, C, D> {
    Bool,
    Num(first_ord::NumType),
    Tuple(DynIter<'a, TypeLike<'a, A, B, C, D>>),
    Variants(DynIter<'a, TypeLike<'a, A, B, C, D>>),
    SelfCustom(CustomTypeId),
    Custom(CustomTypeId, A),
    Array(
        B,
        Lazy<'a, TypeLike<'a, A, B, C, D>>,
        Lazy<'a, OverlayLike<'a, C, D>>,
    ),
    HoleArray(
        B,
        Lazy<'a, TypeLike<'a, A, B, C, D>>,
        Lazy<'a, OverlayLike<'a, C, D>>,
    ),
    Boxed(
        B,
        Lazy<'a, TypeLike<'a, A, B, C, D>>,
        Lazy<'a, OverlayLike<'a, C, D>>,
    ),
}

impl<A, B> Overlay<A, B> {
    pub fn items<'a>(&'a self) -> OverlayLike<'a, &'a A, &'a B> {
        match self {
            Overlay::Bool => OverlayLike::Bool,
            Overlay::Num(n) => OverlayLike::Num(*n),
            Overlay::Tuple(items) => {
                OverlayLike::Tuple(Box::new(items.iter().map(|next| next.items())))
            }
            Overlay::Variants(variants) => {
                OverlayLike::Variants(Box::new(variants.values().map(|next| next.items())))
            }
            Overlay::SelfCustom(id) => OverlayLike::SelfCustom(*id),
            Overlay::Custom(id, subst) => OverlayLike::Custom(*id, subst),
            Overlay::Array(m) => OverlayLike::Array(m),
            Overlay::HoleArray(m) => OverlayLike::HoleArray(m),
            Overlay::Boxed(m) => OverlayLike::Boxed(m),
        }
    }
}

impl<'a, A, B> OverlayLike<'a, A, B> {
    pub fn collect_ov(self) -> Overlay<A, B> {
        match self {
            OverlayLike::Bool => Overlay::Bool,
            OverlayLike::Num(n) => Overlay::Num(n),
            OverlayLike::Tuple(items) => {
                Overlay::Tuple(items.map(|next| next.collect_ov()).collect())
            }
            OverlayLike::Variants(variants) => Overlay::Variants(IdVec::from_vec(
                variants.map(|next| next.collect_ov()).collect(),
            )),
            OverlayLike::SelfCustom(id) => Overlay::SelfCustom(id),
            OverlayLike::Custom(id, subst) => Overlay::Custom(id, subst),
            OverlayLike::Array(m) => Overlay::Array(m),
            OverlayLike::HoleArray(m) => Overlay::HoleArray(m),
            OverlayLike::Boxed(m) => Overlay::Boxed(m),
        }
    }
}

pub type TypeItem<'a, M, L> = TypeLike<
    'a,
    (&'a TypeSubst<M, L>, &'a OverlaySubst<M>),
    (&'a M, &'a L),
    &'a OverlaySubst<M>,
    &'a M,
>;

pub type ModeOverlayItem<'a, M> = OverlayLike<'a, &'a OverlaySubst<M>, &'a M>;

impl<M, L> Type<M, L> {
    pub fn items<'a>(&'a self) -> TypeItem<'a, M, L> {
        match self {
            Type::Bool => TypeLike::Bool,
            Type::Num(n) => TypeLike::Num(*n),
            Type::Tuple(items) => TypeLike::Tuple(Box::new(items.iter().map(|next| next.items()))),
            Type::Variants(variants) => {
                TypeLike::Variants(Box::new(variants.iter().map(|(_, next)| next.items())))
            }
            Type::SelfCustom(id) => TypeLike::SelfCustom(*id),
            Type::Custom(id, tsub, osub) => TypeLike::Custom(*id, (tsub, osub)),
            Type::Array(m, lt, ty, ov) => {
                TypeLike::Array((m, lt), Box::new(|| ty.items()), Box::new(|| ov.items()))
            }
            Type::HoleArray(m, lt, ty, ov) => {
                TypeLike::HoleArray((m, lt), Box::new(|| ty.items()), Box::new(|| ov.items()))
            }
            Type::Boxed(m, lt, ty, ov) => {
                TypeLike::Boxed((m, lt), Box::new(|| ty.items()), Box::new(|| ov.items()))
            }
        }
    }

    pub fn overlay_items<'a>(&'a self) -> ModeOverlayItem<'a, M> {
        match self {
            Type::Bool => OverlayLike::Bool,
            Type::Num(n) => OverlayLike::Num(*n),
            Type::Tuple(items) => {
                OverlayLike::Tuple(Box::new(items.iter().map(|next| next.overlay_items())))
            }
            Type::Variants(variants) => OverlayLike::Variants(Box::new(
                variants.iter().map(|(_, next)| next.overlay_items()),
            )),
            Type::SelfCustom(id) => OverlayLike::SelfCustom(*id),
            Type::Custom(id, _, osub) => OverlayLike::Custom(*id, osub),
            Type::Array(mode, _, _, _) => OverlayLike::Array(mode),
            Type::HoleArray(mode, _, _, _) => OverlayLike::HoleArray(mode),
            Type::Boxed(mode, _, _, _) => OverlayLike::Boxed(mode),
        }
    }
}

pub type OwnedTypeItem<'a, M, L> =
    TypeLike<'a, (TypeSubst<M, L>, OverlaySubst<M>), (M, L), OverlaySubst<M>, M>;

impl<'a, M, L> OwnedTypeItem<'a, M, L> {
    pub fn collect_ty(self) -> Type<M, L> {
        match self {
            TypeLike::Bool => Type::Bool,
            TypeLike::Num(n) => Type::Num(n),
            TypeLike::Tuple(items) => Type::Tuple(items.map(|next| next.collect_ty()).collect()),
            TypeLike::Variants(variants) => Type::Variants(IdVec::from_vec(
                variants.map(|next| next.collect_ty()).collect(),
            )),
            TypeLike::SelfCustom(id) => Type::SelfCustom(id),
            TypeLike::Custom(id, (tsub, osub)) => Type::Custom(id, tsub, osub),
            TypeLike::Array((m, lt), ty, ov) => {
                Type::Array(m, lt, Box::new(ty().collect_ty()), ov().collect_ov())
            }
            TypeLike::HoleArray((m, lt), ty, ov) => {
                Type::HoleArray(m, lt, Box::new(ty().collect_ty()), ov().collect_ov())
            }
            TypeLike::Boxed((m, lt), ty, ov) => {
                Type::Boxed(m, lt, Box::new(ty().collect_ty()), ov().collect_ov())
            }
        }
    }
}

impl anon::Type {
    /// If this is the content of a custom type, `custom_data` must be provided so that the
    /// appropriate `Custom`s can be lifted to `SelfCustom`s. If it is `None`, all `Custom`s will be
    /// lifted to plain `Custom`s.
    pub fn items<'a>(
        &'a self,
        custom_data: Option<(
            &'a IdVec<CustomTypeId, flat::CustomTypeSccId>, // sccs
            flat::CustomTypeSccId,                          // self_id
        )>,
    ) -> TypeLike<'a, (), (), (), ()> {
        match self {
            anon::Type::Bool => TypeLike::Bool,
            anon::Type::Num(n) => TypeLike::Num(*n),
            anon::Type::Tuple(items) => TypeLike::Tuple(Box::new(
                items.into_iter().map(move |next| next.items(custom_data)),
            )),
            anon::Type::Variants(variants) => TypeLike::Variants(Box::new(
                variants
                    .into_iter()
                    .map(move |(_, next)| next.items(custom_data)),
            )),
            anon::Type::Custom(id) => {
                if custom_data
                    .map(|(sccs, self_id)| self_id == sccs[*id])
                    .unwrap_or(false)
                {
                    TypeLike::SelfCustom(*id)
                } else {
                    TypeLike::Custom(*id, ())
                }
            }

            anon::Type::Array(ty) => TypeLike::Array(
                (),
                Box::new(move || ty.items(custom_data)),
                Box::new(move || ty.overlay_items(custom_data)),
            ),
            anon::Type::HoleArray(ty) => TypeLike::HoleArray(
                (),
                Box::new(move || ty.items(custom_data)),
                Box::new(move || ty.overlay_items(custom_data)),
            ),
            anon::Type::Boxed(ty) => TypeLike::Boxed(
                (),
                Box::new(move || ty.items(custom_data)),
                Box::new(move || ty.overlay_items(custom_data)),
            ),
        }
    }

    /// If this is the overlay of a custom type, `custom_data` must be provided so that the
    /// appropriate `Custom`s can be lifted to `SelfCustom`s. If it is `None`, all `Custom`s will be
    /// lifted to plain `Custom`s.
    pub fn overlay_items<'a>(
        &'a self,
        custom_data: Option<(
            &'a IdVec<CustomTypeId, flat::CustomTypeSccId>, // sccs
            flat::CustomTypeSccId,                          // self_id
        )>,
    ) -> OverlayLike<'a, (), ()> {
        match self {
            anon::Type::Bool => OverlayLike::Bool,
            anon::Type::Num(n) => OverlayLike::Num(*n),
            anon::Type::Tuple(items) => OverlayLike::Tuple(Box::new(
                items
                    .into_iter()
                    .map(move |next| next.overlay_items(custom_data)),
            )),
            anon::Type::Variants(variants) => OverlayLike::Variants(Box::new(
                variants
                    .into_iter()
                    .map(move |(_, next)| next.overlay_items(custom_data)),
            )),
            anon::Type::Custom(id) => {
                if custom_data
                    .map(|(sccs, self_id)| self_id == sccs[*id])
                    .unwrap_or(false)
                {
                    OverlayLike::SelfCustom(*id)
                } else {
                    OverlayLike::Custom(*id, ())
                }
            }
            anon::Type::Array(_) => OverlayLike::Array(()),
            anon::Type::HoleArray(_) => OverlayLike::HoleArray(()),
            anon::Type::Boxed(_) => OverlayLike::Boxed(()),
        }
    }
}

impl<'a, A: 'a, B: 'a> OverlayLike<'a, A, B> {
    #[must_use]
    pub fn map<'b, C, D>(
        self,
        f1: &'b impl Fn(CustomTypeId, A) -> C,
        f2: &'b impl Fn(B) -> D,
    ) -> OverlayLike<'b, C, D>
    where
        'a: 'b,
    {
        match self {
            OverlayLike::Bool => OverlayLike::Bool,
            OverlayLike::Num(n) => OverlayLike::Num(n),
            OverlayLike::Tuple(items) => {
                OverlayLike::Tuple(Box::new(items.map(move |next| next.map(f1, f2))))
            }
            OverlayLike::Variants(variants) => {
                OverlayLike::Variants(Box::new(variants.map(move |next| next.map(f1, f2))))
            }
            OverlayLike::SelfCustom(id) => OverlayLike::SelfCustom(id),
            OverlayLike::Custom(id, v) => OverlayLike::Custom(id, f1(id, v)),
            OverlayLike::Array(v) => OverlayLike::Array(f2(v)),
            OverlayLike::HoleArray(v) => OverlayLike::HoleArray(f2(v)),
            OverlayLike::Boxed(v) => OverlayLike::Boxed(f2(v)),
        }
    }

    pub fn zip<C: 'a, D: 'a>(
        self,
        other: OverlayLike<'a, C, D>,
    ) -> OverlayLike<'a, (A, C), (B, D)> {
        match (self, other) {
            (OverlayLike::Bool, OverlayLike::Bool) => OverlayLike::Bool,
            (OverlayLike::Num(n1), OverlayLike::Num(n2)) if n1 == n2 => OverlayLike::Num(n1),
            (OverlayLike::Tuple(items1), OverlayLike::Tuple(items2)) => {
                OverlayLike::Tuple(Box::new(
                    items1
                        .into_iter()
                        .zip_eq(items2)
                        .map(|(next1, next2)| next1.zip(next2)),
                ))
            }
            (OverlayLike::Variants(variants1), OverlayLike::Variants(variants2)) => {
                OverlayLike::Variants(Box::new(
                    variants1
                        .into_iter()
                        .zip_eq(variants2)
                        .map(|(next1, next2)| next1.zip(next2)),
                ))
            }
            (OverlayLike::SelfCustom(id1), OverlayLike::SelfCustom(id2)) if id1 == id2 => {
                OverlayLike::SelfCustom(id1)
            }
            (OverlayLike::Custom(id1, v1), OverlayLike::Custom(id2, v2)) if id1 == id2 => {
                OverlayLike::Custom(id1, (v1, v2))
            }
            (OverlayLike::Array(v1), OverlayLike::Array(v2)) => OverlayLike::Array((v1, v2)),
            (OverlayLike::HoleArray(v1), OverlayLike::HoleArray(v2)) => {
                OverlayLike::HoleArray((v1, v2))
            }
            (OverlayLike::Boxed(v1), OverlayLike::Boxed(v2)) => OverlayLike::Boxed((v1, v2)),
            _ => panic!("incompatible types"),
        }
    }

    pub fn for_each(self, f1: &impl Fn(CustomTypeId, A), f2: &impl Fn(B)) {
        match self {
            OverlayLike::Bool => {}
            OverlayLike::Num(_) => {}
            OverlayLike::Tuple(items) => {
                for next in items {
                    next.for_each(f1, f2);
                }
            }
            OverlayLike::Variants(variants) => {
                for next in variants {
                    next.for_each(f1, f2);
                }
            }
            OverlayLike::SelfCustom(_) => {}
            OverlayLike::Custom(id, v) => f1(id, v),
            OverlayLike::Array(v) => f2(v),
            OverlayLike::HoleArray(v) => f2(v),
            OverlayLike::Boxed(v) => f2(v),
        }
    }
}

impl<'a, R: Clone> OverlayLike<'a, R, R> {
    pub fn fold(self, empty: R, append: impl Fn(R, R) -> R + Clone) -> R {
        match self {
            OverlayLike::Bool => empty,
            OverlayLike::Num(_) => empty,
            OverlayLike::Tuple(items) => items.into_iter().fold(empty.clone(), |acc, next| {
                append(acc, next.fold(empty.clone(), append.clone()))
            }),
            OverlayLike::Variants(variants) => {
                variants.into_iter().fold(empty.clone(), |acc, next| {
                    append(acc, next.fold(empty.clone(), append.clone()))
                })
            }
            OverlayLike::SelfCustom(_) => empty,
            OverlayLike::Custom(_, v) => v,
            OverlayLike::Array(v) => v,
            OverlayLike::HoleArray(v) => v,
            OverlayLike::Boxed(v) => v,
        }
    }
}

impl<'a, A: 'a, B: 'a, C: 'a, D: 'a> TypeLike<'a, A, B, C, D> {
    #[must_use]
    pub fn map<'b, E, F, G, H>(
        self,
        f1: &'b impl Fn(CustomTypeId, A) -> E,
        f2: &'b impl Fn(B) -> F,
        f3: &'b impl Fn(CustomTypeId, C) -> G,
        f4: &'b impl Fn(D) -> H,
    ) -> TypeLike<'b, E, F, G, H>
    where
        'a: 'b,
    {
        match self {
            TypeLike::Bool => TypeLike::Bool,
            TypeLike::Num(n) => TypeLike::Num(n),
            TypeLike::Tuple(items) => {
                TypeLike::Tuple(Box::new(items.map(move |next| next.map(f1, f2, f3, f4))))
            }
            TypeLike::Variants(variants) => {
                TypeLike::Variants(Box::new(variants.map(move |next| next.map(f1, f2, f3, f4))))
            }
            TypeLike::SelfCustom(id) => TypeLike::SelfCustom(id),
            TypeLike::Custom(id, v) => TypeLike::Custom(id, f1(id, v)),
            TypeLike::Array(v, ty, overlay) => TypeLike::Array(
                f2(v),
                Box::new(move || ty().map(f1, f2, f3, f4)),
                Box::new(move || overlay().map(f3, f4)),
            ),
            TypeLike::HoleArray(v, ty, overlay) => TypeLike::HoleArray(
                f2(v),
                Box::new(move || ty().map(f1, f2, f3, f4)),
                Box::new(move || overlay().map(f3, f4)),
            ),
            TypeLike::Boxed(v, ty, overlay) => TypeLike::Boxed(
                f2(v),
                Box::new(move || ty().map(f1, f2, f3, f4)),
                Box::new(move || overlay().map(f3, f4)),
            ),
        }
    }

    pub fn zip<E: 'a, F: 'a, G: 'a, H: 'a>(
        self,
        other: TypeLike<'a, E, F, G, H>,
    ) -> TypeLike<'a, (A, E), (B, F), (C, G), (D, H)> {
        match (self, other) {
            (TypeLike::Bool, TypeLike::Bool) => TypeLike::Bool,
            (TypeLike::Num(n1), TypeLike::Num(n2)) if n1 == n2 => TypeLike::Num(n1),
            (TypeLike::Tuple(items1), TypeLike::Tuple(items2)) => TypeLike::Tuple(Box::new(
                items1
                    .into_iter()
                    .zip_eq(items2)
                    .map(|(next1, next2)| next1.zip(next2)),
            )),
            (TypeLike::Variants(variants1), TypeLike::Variants(variants2)) => {
                TypeLike::Variants(Box::new(
                    variants1
                        .into_iter()
                        .zip_eq(variants2)
                        .map(|(next1, next2)| next1.zip(next2)),
                ))
            }
            (TypeLike::Custom(id1, v1), TypeLike::Custom(id2, v2)) if id1 == id2 => {
                TypeLike::Custom(id1, (v1, v2))
            }
            (TypeLike::Array(v1, ty1, overlay1), TypeLike::Array(v2, ty2, overlay2)) => {
                TypeLike::Array(
                    (v1, v2),
                    Box::new(move || ty1().zip(ty2())),
                    Box::new(move || overlay1().zip(overlay2())),
                )
            }
            (TypeLike::HoleArray(v1, ty1, overlay1), TypeLike::HoleArray(v2, ty2, overlay2)) => {
                TypeLike::HoleArray(
                    (v1, v2),
                    Box::new(move || ty1().zip(ty2())),
                    Box::new(move || overlay1().zip(overlay2())),
                )
            }
            (TypeLike::Boxed(v1, ty1, overlay1), TypeLike::Boxed(v2, ty2, overlay2)) => {
                TypeLike::Boxed(
                    (v1, v2),
                    Box::new(move || ty1().zip(ty2())),
                    Box::new(move || overlay1().zip(overlay2())),
                )
            }
            _ => panic!("incompatible types"),
        }
    }

    pub fn for_each(
        self,
        f1: &impl Fn(CustomTypeId, A),
        f2: &impl Fn(B),
        f3: &impl Fn(CustomTypeId, C),
        f4: &impl Fn(D),
    ) {
        match self {
            TypeLike::Bool => {}
            TypeLike::Num(_) => {}
            TypeLike::Tuple(items) => {
                for next in items {
                    next.for_each(f1, f2, f3, f4);
                }
            }
            TypeLike::Variants(variants) => {
                for next in variants {
                    next.for_each(f1, f2, f3, f4);
                }
            }
            TypeLike::SelfCustom(_) => {}
            TypeLike::Custom(id, v) => f1(id, v),
            TypeLike::Array(v, ty, overlay) => {
                f2(v);
                ty().for_each(f1, f2, f3, f4);
                overlay().for_each(f3, f4);
            }
            TypeLike::HoleArray(v, ty, overlay) => {
                f2(v);
                ty().for_each(f1, f2, f3, f4);
                overlay().for_each(f3, f4);
            }
            TypeLike::Boxed(v, ty, overlay) => {
                f2(v);
                ty().for_each(f1, f2, f3, f4);
                overlay().for_each(f3, f4);
            }
        }
    }
}

impl<'a, R: Clone> TypeLike<'a, R, R, R, R> {
    pub fn fold(self, empty: R, append: &impl Fn(R, R) -> R) -> R {
        match self {
            TypeLike::Bool => empty,
            TypeLike::Num(_) => empty,
            TypeLike::Tuple(items) => items.into_iter().fold(empty.clone(), |acc, next| {
                append(acc, next.fold(empty.clone(), append))
            }),
            TypeLike::Variants(variants) => {
                variants.into_iter().fold(empty.clone(), |acc, next| {
                    append(acc, next.fold(empty.clone(), append))
                })
            }
            TypeLike::SelfCustom(_) => empty,
            TypeLike::Custom(_, v) => v,
            TypeLike::Array(v, ty, overlay) => {
                let a = ty().fold(empty.clone(), append);
                let b = overlay().fold(empty, append);
                append(append(v, a), b)
            }
            TypeLike::HoleArray(v, ty, overlay) => {
                let a = ty().fold(empty.clone(), append);
                let b = overlay().fold(empty, append);
                append(append(v, a), b)
            }
            TypeLike::Boxed(v, ty, overlay) => {
                let a = ty().fold(empty.clone(), append);
                let b = overlay().fold(empty, append);
                append(append(v, a), b)
            }
        }
    }
}
