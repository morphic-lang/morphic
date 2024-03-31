use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast::{self as first_ord, CustomTypeId};
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::iter::{try_zip_eq, IterExt};
use id_collections::{id_type, Count, IdVec};
use std::collections::{BTreeMap, BTreeSet};
use std::hash::Hash;

// Notes:
// - have instantiate return a dictionary of updates?
// - for let-many, make sure to clone Gamma(x) at the right time

#[id_type]
pub struct ModeParam(pub usize);

#[id_type]
pub struct LtParam(pub usize);

/// We compute the least solution to our mode constraints where `Borrowed` < `Owned`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModeTerm<M> {
    Owned,
    Borrowed,
    Join(BTreeSet<M>), // Always non-empty
}

impl<M: Ord> ModeTerm<M> {
    pub fn var(x: M) -> Self {
        ModeTerm::Join(std::iter::once(x).collect())
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
    pub fn final_() -> Self {
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

    // Yields the elements of this path in the same order they would be traversed if it were
    // converted to a lifetime and then recursively destructured.
    fn elems(&self) -> impl Iterator<Item = PathElem> + '_ {
        self.0.iter().cloned()
    }

    pub fn as_lt(&self) -> Lt {
        let mut res = LocalLt::Final;
        for elem in self.elems() {
            match elem {
                PathElem::Seq(i) => {
                    res = LocalLt::Seq(Box::new(res), i);
                }
                PathElem::Par { i, n } => {
                    let mut par = vec![None; n];
                    par[i] = Some(res);
                    res = LocalLt::Par(par);
                }
            }
        }
        Lt::Local(res)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModeConstr<M> {
    Lte(M, M),
    Owned(M),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lt {
    Empty,
    Local(LocalLt),
    Join(BTreeSet<LtParam>), // Always non-empty
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
        Lt::Join(std::iter::once(x).collect())
    }

    /// A join over the lattice: `l1 <= l2` iff, for every leaf of `l1`, there is a leaf of `l2`
    /// that occurs "later in time".
    ///
    /// Panics if `self` and `other` are not structurally compatible.
    pub fn join(&self, other: &Self) -> Self {
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
            (LocalLt::Par(p1), LocalLt::Par(p2)) => LocalLt::Par(
                p1.iter()
                    .try_zip_eq(p2.iter())
                    .expect("incompatible lifetimes")
                    .map(|(l1, l2)| match (l1, l2) {
                        (None, None) => None,
                        (None, Some(l2)) => Some(l2.clone()),
                        (Some(l1), None) => Some(l1.clone()),
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
                        lhs = &**inner;
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
                        }
                    }
                }
                _ => {
                    panic!("incompatible lifetimes");
                }
            }
        }
        true
    }
}

#[derive(Clone, Debug)]
pub struct Occur<M, L> {
    pub local: flat::LocalId,
    pub ty: Type<M, L>,
}

#[derive(Clone, Debug)]
pub enum ArrayOp<M, L> {
    Get(
        Type<M, L>,  // Item type (of input)
        Occur<M, L>, // Array
        Occur<M, L>, // Index
        Type<M, L>,  // Return type; needed for RC op insertion
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
        Vec<(Type<M, L>, Expr<M, L>)>, // bound values.  Each is assigned a new sequential Occur<M,L>
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
pub enum Overlay<M> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Overlay<M>>),
    Variants(IdVec<first_ord::VariantId, Overlay<M>>),
    Custom(CustomTypeId, BTreeMap<ModeParam, M>),
    Array(M),
    HoleArray(M),
    Boxed(M),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<M, L> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Type<M, L>>),
    Variants(IdVec<first_ord::VariantId, Type<M, L>>),
    Custom(CustomTypeId, IdVec<ModeParam, M>, IdVec<LtParam, L>),
    Array(M, L, Box<Type<M, L>>, Overlay<M>),
    HoleArray(M, L, Box<Type<M, L>>, Overlay<M>),
    Boxed(M, L, Box<Type<M, L>>, Overlay<M>),
}

impl<M: Clone> Type<M, Lt> {
    // Returns the meet of two types over the lifetime lattice. This meet is "left" in the sense
    // that the modes of the output are taken from the first argument.
    pub fn left_meet(&self, other: &Self) -> Self {
        match (self, other) {
            (Type::Bool, Type::Bool) => Type::Bool,
            (Type::Num(n1), Type::Num(n2)) if n1 == n2 => Type::Num(*n1),
            (Type::Tuple(tys1), Type::Tuple(tys2)) => Type::Tuple(
                tys1.iter()
                    .try_zip_eq(tys2)
                    .expect("incompatible types")
                    .map(|(t1, t2)| t1.left_meet(t2))
                    .collect(),
            ),
            (Type::Variants(vs1), Type::Variants(vs2)) => Type::Variants(IdVec::from_vec(
                try_zip_eq(vs1, vs2)
                    .expect("incompatible types")
                    .map(|(_, v1, v2)| v1.left_meet(v2))
                    .collect(),
            )),
            (Type::Custom(id1, ms1, lts1), Type::Custom(id2, _ms2, _lts2)) if id1 == id2 => {
                Type::Custom(*id1, ms1.clone(), lts1.clone())
            }
            (Type::Array(m1, lt1, ty1, o1), Type::Array(_m2, lt2, ty2, _o2)) => Type::Array(
                m1.clone(),
                lt1.join(lt2),
                Box::new(ty1.left_meet(ty2)),
                o1.clone(),
            ),
            (Type::HoleArray(m1, lt1, ty1, o1), Type::HoleArray(_m2, lt2, ty2, _o2)) => {
                Type::HoleArray(
                    m1.clone(),
                    lt1.join(lt2),
                    Box::new(ty1.left_meet(ty2)),
                    o1.clone(),
                )
            }
            (Type::Boxed(m1, lt1, ty1, o1), Type::Boxed(_m2, lt2, ty2, _o2)) => Type::Boxed(
                m1.clone(),
                lt1.join(lt2),
                Box::new(ty1.left_meet(ty2)),
                o1.clone(),
            ),
            _ => panic!("incompatible types"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sig {
    // Total number of params in `arg_type` and `ret_type`
    pub num_mode_params: Count<ModeParam>,
    pub num_lt_params: Count<LtParam>,

    pub arg_type: Type<ModeParam, LtParam>,
    pub ret_type: Type<ModeParam, LtParam>,
    pub constrs: Vec<ModeConstr<ModeParam>>,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub sig: Sig,

    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument
    pub body: Expr<ModeParam, LtParam>,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub num_mode_params: Count<ModeParam>,
    pub num_lt_params: Count<LtParam>,
    pub overlay_params: BTreeSet<ModeParam>,

    pub content: Type<ModeParam, LtParam>,
    pub overlay: Overlay<ModeParam>,
}

#[derive(Clone, Debug)]
pub struct CustomTypes {
    pub types: IdVec<CustomTypeId, TypeDef>,
    pub sccs: IdVec<flat::CustomTypeSccId, Vec<CustomTypeId>>,
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

pub type Next<'a, T> = Box<dyn Fn() -> T + 'a>;
pub type DynIter<'a, T> = Box<dyn Iterator<Item = T> + 'a>;

#[derive(Clone, Copy, Debug)]
pub enum DataKind {
    Stack,
    Heap,
}

pub enum OverlayLike<'a, A, B> {
    Bool,
    Num(first_ord::NumType),
    Tuple(DynIter<'a, OverlayLike<'a, A, B>>),
    Variants(DynIter<'a, OverlayLike<'a, A, B>>),
    Custom(CustomTypeId, A),
    Array(B),
    HoleArray(B),
    Boxed(B),
}

pub enum TypeLike<'a, A, B, C, D> {
    Bool,
    Num(first_ord::NumType),
    Tuple(DynIter<'a, TypeLike<'a, A, B, C, D>>),
    Variants(DynIter<'a, TypeLike<'a, A, B, C, D>>),
    Custom(CustomTypeId, A),
    Array(
        B,
        Next<'a, TypeLike<'a, A, B, C, D>>,
        Next<'a, OverlayLike<'a, C, D>>,
    ),
    HoleArray(
        B,
        Next<'a, TypeLike<'a, A, B, C, D>>,
        Next<'a, OverlayLike<'a, C, D>>,
    ),
    Boxed(
        B,
        Next<'a, TypeLike<'a, A, B, C, D>>,
        Next<'a, OverlayLike<'a, C, D>>,
    ),
}

pub type OverlayItem<'a, M> = OverlayLike<'a, &'a BTreeMap<ModeParam, M>, &'a M>;
pub type OwnedOverlayItem<'a, M> = OverlayLike<'a, BTreeMap<ModeParam, M>, M>;

pub type TypeItem<'a, M, L> = TypeLike<
    'a,
    (&'a IdVec<ModeParam, M>, &'a IdVec<LtParam, L>),
    (&'a M, &'a L),
    &'a BTreeMap<ModeParam, M>,
    &'a M,
>;
pub type OwnedTypeItem<'a, M, L> =
    TypeLike<'a, (IdVec<ModeParam, M>, IdVec<LtParam, L>), (M, L), BTreeMap<ModeParam, M>, M>;

impl<M> Overlay<M> {
    pub fn items<'a>(&'a self) -> OverlayItem<M> {
        match self {
            Overlay::Bool => OverlayLike::Bool,
            Overlay::Num(n) => OverlayLike::Num(*n),
            Overlay::Tuple(items) => {
                OverlayLike::Tuple(Box::new(items.iter().map(|next| next.items())))
            }
            Overlay::Variants(variants) => {
                OverlayLike::Variants(Box::new(variants.iter().map(|(_, next)| next.items())))
            }
            Overlay::Custom(id, modes) => OverlayLike::Custom(*id, modes),
            Overlay::Array(mode) => OverlayLike::Array(mode),
            Overlay::HoleArray(mode) => OverlayLike::HoleArray(mode),
            Overlay::Boxed(mode) => OverlayLike::Boxed(mode),
        }
    }
}

impl<'a, M: Clone> OwnedOverlayItem<'a, M> {
    pub fn collect(self) -> Overlay<M> {
        match self {
            OverlayLike::Bool => Overlay::Bool,
            OverlayLike::Num(n) => Overlay::Num(n),
            OverlayLike::Tuple(items) => Overlay::Tuple(items.map(|next| next.collect()).collect()),
            OverlayLike::Variants(variants) => Overlay::Variants(IdVec::from_vec(
                variants.map(|next| next.collect()).collect(),
            )),
            OverlayLike::Custom(id, modes) => Overlay::Custom(id, modes),
            OverlayLike::Array(mode) => Overlay::Array(mode),
            OverlayLike::HoleArray(mode) => Overlay::HoleArray(mode),
            OverlayLike::Boxed(mode) => Overlay::Boxed(mode),
        }
    }
}

impl<M, L> Type<M, L> {
    pub fn items<'a>(&'a self) -> TypeItem<'a, M, L> {
        match self {
            Type::Bool => TypeLike::Bool,
            Type::Num(n) => TypeLike::Num(*n),
            Type::Tuple(items) => TypeLike::Tuple(Box::new(items.iter().map(|next| next.items()))),
            Type::Variants(variants) => {
                TypeLike::Variants(Box::new(variants.iter().map(|(_, next)| next.items())))
            }
            Type::Custom(id, ms, lts) => TypeLike::Custom(*id, (ms, lts)),
            Type::Array(mode, lt, ty, overlay) => TypeLike::Array(
                (mode, lt),
                Box::new(|| ty.items()),
                Box::new(|| overlay.items()),
            ),
            Type::HoleArray(mode, lt, ty, overlay) => TypeLike::HoleArray(
                (mode, lt),
                Box::new(|| ty.items()),
                Box::new(|| overlay.items()),
            ),
            Type::Boxed(mode, lt, ty, overlay) => TypeLike::Boxed(
                (mode, lt),
                Box::new(|| ty.items()),
                Box::new(|| overlay.items()),
            ),
        }
    }

    fn overlay_items<'a>(&'a self) -> OverlayLike<&'a IdVec<ModeParam, M>, &'a M> {
        match self {
            Type::Bool => OverlayLike::Bool,
            Type::Num(n) => OverlayLike::Num(*n),
            Type::Tuple(items) => {
                OverlayLike::Tuple(Box::new(items.iter().map(|next| next.overlay_items())))
            }
            Type::Variants(variants) => OverlayLike::Variants(Box::new(
                variants.iter().map(|(_, next)| next.overlay_items()),
            )),
            Type::Custom(id, modes, _) => OverlayLike::Custom(*id, modes),
            Type::Array(mode, _, _, _) => OverlayLike::Array(mode),
            Type::HoleArray(mode, _, _, _) => OverlayLike::HoleArray(mode),
            Type::Boxed(mode, _, _, _) => OverlayLike::Boxed(mode),
        }
    }
}

impl<'a, M: Clone, L: Clone> OwnedTypeItem<'a, M, L> {
    pub fn collect(self) -> Type<M, L> {
        match self {
            TypeLike::Bool => Type::Bool,
            TypeLike::Num(n) => Type::Num(n),
            TypeLike::Tuple(items) => Type::Tuple(items.map(|next| next.collect()).collect()),
            TypeLike::Variants(variants) => Type::Variants(IdVec::from_vec(
                variants.map(|next| next.collect()).collect(),
            )),
            TypeLike::Custom(id, (modes, lts)) => Type::Custom(id, modes, lts),
            TypeLike::Array((mode, lt), ty, overlay) => {
                Type::Array(mode, lt, Box::new(ty().collect()), overlay().collect())
            }
            TypeLike::HoleArray((mode, lt), ty, overlay) => {
                Type::HoleArray(mode, lt, Box::new(ty().collect()), overlay().collect())
            }
            TypeLike::Boxed((mode, lt), ty, overlay) => {
                Type::Boxed(mode, lt, Box::new(ty().collect()), overlay().collect())
            }
        }
    }
}

impl anon::Type {
    pub fn items<'a>(&'a self) -> TypeLike<(), (), (), ()> {
        match self {
            anon::Type::Bool => TypeLike::Bool,
            anon::Type::Num(n) => TypeLike::Num(*n),
            anon::Type::Tuple(items) => {
                TypeLike::Tuple(Box::new(items.into_iter().map(|next| next.items())))
            }
            anon::Type::Variants(variants) => {
                TypeLike::Variants(Box::new(variants.into_iter().map(|(_, next)| next.items())))
            }
            anon::Type::Custom(id) => TypeLike::Custom(*id, ()),
            anon::Type::Array(ty) => {
                TypeLike::Array((), Box::new(|| ty.items()), Box::new(|| ty.overlay_items()))
            }
            anon::Type::HoleArray(ty) => {
                TypeLike::HoleArray((), Box::new(|| ty.items()), Box::new(|| ty.overlay_items()))
            }
            anon::Type::Boxed(ty) => {
                TypeLike::Boxed((), Box::new(|| ty.items()), Box::new(|| ty.overlay_items()))
            }
        }
    }

    pub fn overlay_items<'a>(&'a self) -> OverlayLike<(), ()> {
        match self {
            anon::Type::Bool => OverlayLike::Bool,
            anon::Type::Num(n) => OverlayLike::Num(*n),
            anon::Type::Tuple(items) => {
                OverlayLike::Tuple(Box::new(items.into_iter().map(|next| next.overlay_items())))
            }
            anon::Type::Variants(variants) => OverlayLike::Variants(Box::new(
                variants.into_iter().map(|(_, next)| next.overlay_items()),
            )),
            anon::Type::Custom(id) => OverlayLike::Custom(*id, ()),
            anon::Type::Array(_) => OverlayLike::Array(()),
            anon::Type::HoleArray(_) => OverlayLike::HoleArray(()),
            anon::Type::Boxed(_) => OverlayLike::Boxed(()),
        }
    }
}

impl<'a, A: 'a, B: 'a> OverlayLike<'a, A, B> {
    pub fn map<C, D>(
        self,
        f1: impl Fn(CustomTypeId, A) -> C + Clone + 'a,
        f2: impl Fn(B) -> D + Clone + 'a,
    ) -> OverlayLike<'a, C, D> {
        // `DataKind::Stack` is a dummy value. We only care about the kind when the overlay is part
        // of a type, in which case `map_impl` will be called directly.
        self.map_impl(
            DataKind::Stack,
            move |_, id, v| f1(id, v),
            move |_, v| f2(v),
        )
    }

    fn map_impl<C, D>(
        self,
        kind: DataKind,
        f1: impl Fn(DataKind, CustomTypeId, A) -> C + Clone + 'a,
        f2: impl Fn(DataKind, B) -> D + Clone + 'a,
    ) -> OverlayLike<'a, C, D> {
        match self {
            OverlayLike::Bool => OverlayLike::Bool,
            OverlayLike::Num(n) => OverlayLike::Num(n),
            OverlayLike::Tuple(items) => OverlayLike::Tuple(Box::new(
                items.map(move |next| next.map_impl(kind, f1.clone(), f2.clone())),
            )),
            OverlayLike::Variants(variants) => OverlayLike::Variants(Box::new(
                variants.map(move |next| next.map_impl(kind, f1.clone(), f2.clone())),
            )),
            OverlayLike::Custom(id, v) => OverlayLike::Custom(id, f1(kind, id, v)),
            OverlayLike::Array(v) => OverlayLike::Array(f2(kind, v)),
            OverlayLike::HoleArray(v) => OverlayLike::HoleArray(f2(kind, v)),
            OverlayLike::Boxed(v) => OverlayLike::Boxed(f2(kind, v)),
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

    pub fn for_each(self, f1: impl Fn(CustomTypeId, A) + Clone, f2: impl Fn(B) + Clone) {
        // `DataKind::Stack` is a dummy value. We only care about the kind when the overlay is part
        // of a type, in which case `for_each_impl` will be called directly.
        self.for_each_impl(
            DataKind::Stack,
            move |_, id, v| f1(id, v),
            move |_, v| f2(v),
        )
    }

    fn for_each_impl(
        self,
        kind: DataKind,
        f1: impl Fn(DataKind, CustomTypeId, A) + Clone,
        f2: impl Fn(DataKind, B) + Clone,
    ) {
        match self {
            OverlayLike::Bool => {}
            OverlayLike::Num(_) => {}
            OverlayLike::Tuple(items) => {
                for next in items {
                    next.for_each_impl(DataKind::Heap, f1.clone(), f2.clone());
                }
            }
            OverlayLike::Variants(variants) => {
                for next in variants {
                    next.for_each_impl(DataKind::Heap, f1.clone(), f2.clone());
                }
            }
            OverlayLike::Custom(id, v) => f1(kind, id, v),
            OverlayLike::Array(v) => f2(kind, v),
            OverlayLike::HoleArray(v) => f2(kind, v),
            OverlayLike::Boxed(v) => f2(kind, v),
        }
    }
}

impl<'a, R: Clone> OverlayLike<'a, R, R> {
    pub fn fold(self, init: R, f: impl Fn(R, R) -> R + Clone) -> R {
        match self {
            OverlayLike::Bool => init,
            OverlayLike::Num(_) => init,
            OverlayLike::Tuple(items) => items.into_iter().fold(init.clone(), |acc, next| {
                f(acc, next.fold(init.clone(), f.clone()))
            }),
            OverlayLike::Variants(variants) => {
                variants.into_iter().fold(init.clone(), |acc, next| {
                    f(acc, next.fold(init.clone(), f.clone()))
                })
            }
            OverlayLike::Custom(_, v) => v,
            OverlayLike::Array(v) => v,
            OverlayLike::HoleArray(v) => v,
            OverlayLike::Boxed(v) => v,
        }
    }
}

impl<'a, A: 'a, B: 'a, C: 'a, D: 'a> TypeLike<'a, A, B, C, D> {
    pub fn map<E, F, G, H>(
        self,
        ty_f1: impl Fn(DataKind, CustomTypeId, A) -> E + Clone + 'a,
        ty_f2: impl Fn(DataKind, B) -> F + Clone + 'a,
        ov_f1: impl Fn(DataKind, CustomTypeId, C) -> G + Clone + 'a,
        ov_f2: impl Fn(DataKind, D) -> H + Clone + 'a,
    ) -> TypeLike<'a, E, F, G, H> {
        self.map_impl(DataKind::Stack, ty_f1, ty_f2, ov_f1, ov_f2)
    }

    fn map_impl<E, F, G, H>(
        self,
        kind: DataKind,
        ty_f1: impl Fn(DataKind, CustomTypeId, A) -> E + Clone + 'a,
        ty_f2: impl Fn(DataKind, B) -> F + Clone + 'a,
        ov_f1: impl Fn(DataKind, CustomTypeId, C) -> G + Clone + 'a,
        ov_f2: impl Fn(DataKind, D) -> H + Clone + 'a,
    ) -> TypeLike<'a, E, F, G, H> {
        match self {
            TypeLike::Bool => TypeLike::Bool,
            TypeLike::Num(n) => TypeLike::Num(n),
            TypeLike::Tuple(items) => TypeLike::Tuple(Box::new(items.map(move |next| {
                next.map_impl(
                    kind,
                    ty_f1.clone(),
                    ty_f2.clone(),
                    ov_f1.clone(),
                    ov_f2.clone(),
                )
            }))),
            TypeLike::Variants(variants) => {
                TypeLike::Variants(Box::new(variants.map(move |next| {
                    next.map_impl(
                        kind,
                        ty_f1.clone(),
                        ty_f2.clone(),
                        ov_f1.clone(),
                        ov_f2.clone(),
                    )
                })))
            }
            TypeLike::Custom(id, v) => TypeLike::Custom(id, ty_f1(kind, id, v)),
            TypeLike::Array(v, ty, overlay) => TypeLike::Array(
                ty_f2(kind, v),
                {
                    let ov_f1 = ov_f1.clone();
                    let ov_f2 = ov_f2.clone();
                    Box::new(move || {
                        ty().map_impl(
                            DataKind::Heap,
                            ty_f1.clone(),
                            ty_f2.clone(),
                            ov_f1.clone(),
                            ov_f2.clone(),
                        )
                    })
                },
                Box::new(move || overlay().map_impl(kind, ov_f1.clone(), ov_f2.clone())),
            ),
            TypeLike::HoleArray(v, ty, overlay) => TypeLike::HoleArray(
                ty_f2(kind, v),
                {
                    let ov_f1 = ov_f1.clone();
                    let ov_f2 = ov_f2.clone();
                    Box::new(move || {
                        ty().map_impl(
                            DataKind::Heap,
                            ty_f1.clone(),
                            ty_f2.clone(),
                            ov_f1.clone(),
                            ov_f2.clone(),
                        )
                    })
                },
                Box::new(move || overlay().map_impl(kind, ov_f1.clone(), ov_f2.clone())),
            ),
            TypeLike::Boxed(v, ty, overlay) => TypeLike::Boxed(
                ty_f2(kind, v),
                {
                    let ov_f1 = ov_f1.clone();
                    let ov_f2 = ov_f2.clone();
                    Box::new(move || {
                        ty().map_impl(
                            DataKind::Heap,
                            ty_f1.clone(),
                            ty_f2.clone(),
                            ov_f1.clone(),
                            ov_f2.clone(),
                        )
                    })
                },
                Box::new(move || overlay().map_impl(kind, ov_f1.clone(), ov_f2.clone())),
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
        f1: impl Fn(DataKind, CustomTypeId, A) + Clone,
        f2: impl Fn(DataKind, B) + Clone,
        f3: impl Fn(DataKind, CustomTypeId, C) + Clone,
        f4: impl Fn(DataKind, D) + Clone,
    ) {
        self.for_each_impl(DataKind::Stack, f1, f2, f3, f4)
    }

    fn for_each_impl(
        self,
        kind: DataKind,
        f1: impl Fn(DataKind, CustomTypeId, A) + Clone,
        f2: impl Fn(DataKind, B) + Clone,
        f3: impl Fn(DataKind, CustomTypeId, C) + Clone,
        f4: impl Fn(DataKind, D) + Clone,
    ) {
        match self {
            TypeLike::Bool => {}
            TypeLike::Num(_) => {}
            TypeLike::Tuple(items) => {
                for next in items {
                    next.for_each_impl(
                        DataKind::Heap,
                        f1.clone(),
                        f2.clone(),
                        f3.clone(),
                        f4.clone(),
                    );
                }
            }
            TypeLike::Variants(variants) => {
                for next in variants {
                    next.for_each_impl(
                        DataKind::Heap,
                        f1.clone(),
                        f2.clone(),
                        f3.clone(),
                        f4.clone(),
                    );
                }
            }
            TypeLike::Custom(id, v) => f1(kind, id, v),
            TypeLike::Array(v, ty, overlay) => {
                f2(kind, v);
                ty().for_each_impl(
                    DataKind::Heap,
                    f1.clone(),
                    f2.clone(),
                    f3.clone(),
                    f4.clone(),
                );
                overlay().for_each_impl(kind, f3.clone(), f4.clone());
            }
            TypeLike::HoleArray(v, ty, overlay) => {
                f2(kind, v);
                ty().for_each_impl(
                    DataKind::Heap,
                    f1.clone(),
                    f2.clone(),
                    f3.clone(),
                    f4.clone(),
                );
                overlay().for_each_impl(kind, f3.clone(), f4.clone());
            }
            TypeLike::Boxed(v, ty, overlay) => {
                f2(kind, v);
                ty().for_each_impl(
                    DataKind::Heap,
                    f1.clone(),
                    f2.clone(),
                    f3.clone(),
                    f4.clone(),
                );
                overlay().for_each_impl(kind, f3.clone(), f4.clone());
            }
        }
    }
}

impl<'a, R: Clone> TypeLike<'a, R, R, R, R> {
    pub fn fold(self, init: R, f: impl Fn(R, R) -> R + Clone) -> R {
        match self {
            TypeLike::Bool => init,
            TypeLike::Num(_) => init,
            TypeLike::Tuple(items) => items.into_iter().fold(init.clone(), |acc, next| {
                f(acc, next.fold(init.clone(), f.clone()))
            }),
            TypeLike::Variants(variants) => variants.into_iter().fold(init.clone(), |acc, next| {
                f(acc, next.fold(init.clone(), f.clone()))
            }),
            TypeLike::Custom(_, v) => v,
            TypeLike::Array(v, ty, overlay) => {
                f(v, ty().fold(init.clone(), f.clone()));
                overlay().fold(init, f)
            }
            TypeLike::HoleArray(v, ty, overlay) => {
                f(v, ty().fold(init.clone(), f.clone()));
                overlay().fold(init, f)
            }
            TypeLike::Boxed(v, ty, overlay) => {
                f(v, ty().fold(init.clone(), f.clone()));
                overlay().fold(init, f)
            }
        }
    }
}
