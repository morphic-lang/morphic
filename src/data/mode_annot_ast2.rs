use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::lazy::{lazy, DynLazy};
use id_collections::{id_type, Count, IdVec};
use std::collections::BTreeSet;
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
            (LocalLt::Par(p1), LocalLt::Par(p2)) => {
                if p1.len() != p2.len() {
                    panic!("incompatible lifetimes")
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
    pub ty: OldType<M, L>,
}

#[derive(Clone, Debug)]
pub enum ArrayOp<M, L> {
    Get(
        OldType<M, L>, // Item type (of input)
        Occur<M, L>,   // Array
        Occur<M, L>,   // Index
        OldType<M, L>, // Return type; needed for RC op insertion
    ), // Returns item
    Extract(
        OldType<M, L>, // Item type (of input)
        Occur<M, L>,   // Array
        Occur<M, L>,   // Index
    ), // Returns tuple of (item, hole array)
    Len(
        OldType<M, L>, // Item type (of input)
        Occur<M, L>,   // Array
    ), // Returns int
    Push(
        OldType<M, L>, // Item type (of input)
        Occur<M, L>,   // Array
        Occur<M, L>,   // Item
    ), // Returns new array
    Pop(
        OldType<M, L>, // Item type (of input)
        Occur<M, L>,   // Array
    ), // Returns tuple (array, item)
    Replace(
        OldType<M, L>, // Item type (of input)
        Occur<M, L>,   // Hole array
        Occur<M, L>,   // Item
    ), // Returns new array
    Reserve(
        OldType<M, L>, // Item type (of input)
        Occur<M, L>,   // Array
        Occur<M, L>,   // Capacity
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
        OldType<M, L>,
    ),
    LetMany(
        Vec<(OldType<M, L>, Expr<M, L>)>, // bound values.  Each is assigned a new sequential Occur<M,L>
        Occur<M, L>,                      // body
    ),

    Tuple(Vec<Occur<M, L>>),
    TupleField(Occur<M, L>, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, OldType<M, L>>,
        first_ord::VariantId,
        Occur<M, L>,
    ),
    UnwrapVariant(first_ord::VariantId, Occur<M, L>),
    WrapBoxed(
        Occur<M, L>,
        OldType<M, L>, // Inner type
    ),
    UnwrapBoxed(
        Occur<M, L>,
        OldType<M, L>, // Inner type
    ),
    WrapCustom(first_ord::CustomTypeId, Occur<M, L>),
    UnwrapCustom(first_ord::CustomTypeId, Occur<M, L>),

    Intrinsic(Intrinsic, Occur<M, L>),
    ArrayOp(ArrayOp<M, L>),
    IoOp(IoOp<M, L>),
    Panic(OldType<M, L>, Occur<M, L>),

    ArrayLit(OldType<M, L>, Vec<Occur<M, L>>),
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
        OldType<M, L>, // Inner type
    ),
    Custom(first_ord::CustomTypeId, Box<Condition<M, L>>),
    BoolConst(bool),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OldOverlay<M> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<OldOverlay<M>>),
    Variants(IdVec<first_ord::VariantId, OldOverlay<M>>),
    // The mode and lifetime substitutions for this custom type's parameters are stored in the type
    // which corresponds to this overlay.
    Custom(first_ord::CustomTypeId),
    Array(M),
    HoleArray(M),
    Boxed(M),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OldType<M, L> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<OldType<M, L>>),
    Variants(IdVec<first_ord::VariantId, OldType<M, L>>),
    Custom(
        first_ord::CustomTypeId,
        IdVec<ModeParam, M>,
        IdVec<LtParam, L>,
    ),
    Array(M, L, Box<OldType<M, L>>, OldOverlay<M>),
    HoleArray(M, L, Box<OldType<M, L>>, OldOverlay<M>),
    Boxed(M, L, Box<OldType<M, L>>, OldOverlay<M>),
}

impl<M: Clone> OldType<M, Lt> {
    // Returns the meet of two types over the lifetime lattice. This meet is "left" in the sense
    // that the modes of the output are taken from the first argument.
    pub fn left_meet(&self, other: &Self) -> Self {
        match (self, other) {
            (OldType::Bool, OldType::Bool) => OldType::Bool,
            (OldType::Num(n1), OldType::Num(n2)) if n1 == n2 => OldType::Num(*n1),
            (OldType::Tuple(tys1), OldType::Tuple(tys2)) => OldType::Tuple(
                tys1.iter()
                    .zip(tys2)
                    .map(|(t1, t2)| t1.left_meet(t2))
                    .collect(),
            ),
            (OldType::Custom(id1, ms1, lts1), OldType::Custom(id2, _ms2, _lts2)) if id1 == id2 => {
                OldType::Custom(*id1, ms1.clone(), lts1.clone())
            }
            (OldType::Array(m1, lt1, ty1, o1), OldType::Array(_m2, lt2, ty2, _o2)) => {
                OldType::Array(
                    m1.clone(),
                    lt1.join(lt2),
                    Box::new(ty1.left_meet(ty2)),
                    o1.clone(),
                )
            }
            (OldType::HoleArray(m1, lt1, ty1, o1), OldType::HoleArray(_m2, lt2, ty2, _o2)) => {
                OldType::HoleArray(
                    m1.clone(),
                    lt1.join(lt2),
                    Box::new(ty1.left_meet(ty2)),
                    o1.clone(),
                )
            }
            (OldType::Boxed(m1, lt1, ty1, o1), OldType::Boxed(_m2, lt2, ty2, _o2)) => {
                OldType::Boxed(
                    m1.clone(),
                    lt1.join(lt2),
                    Box::new(ty1.left_meet(ty2)),
                    o1.clone(),
                )
            }
            _ => panic!("incompatible types"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sig {
    // Total number of params in `arg_type` and `ret_type`
    pub num_mode_params: Count<ModeParam>, // Does not include overlay mode params
    pub num_overlay_mode_params: Count<ModeParam>,
    pub num_lt_params: Count<LtParam>,

    pub arg_type: OldType<ModeParam, LtParam>,
    pub ret_type: OldType<ModeParam, LtParam>,
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
pub struct CustomTypeDef {
    pub num_mode_params: Count<ModeParam>,
    pub num_overlay_mode_params: Count<ModeParam>,
    pub num_lt_params: Count<LtParam>,
    pub content: OldType<ModeParam, LtParam>,
    pub overlay: OldOverlay<ModeParam>,
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

// The F-algebra for types
pub enum TF<A, B, X, Y> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Y>),
    Variants(IdVec<first_ord::VariantId, Y>),
    Custom(first_ord::CustomTypeId, A),
    Array(B, X, Y),
    HoleArray(B, X, Y),
    Boxed(B, X, Y),
}

// The F-algebra for "simple" types; used when all we care about is the shape of the type
pub enum STF<X> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<X>),
    Variants(IdVec<first_ord::VariantId, X>),
    Custom(first_ord::CustomTypeId),
    Array,
    HoleArray,
    Boxed,
}

// The F-algebra for overlays
#[derive(Clone, Debug)]
pub enum OF<A, B, X> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<X>),
    Variants(IdVec<first_ord::VariantId, X>),
    Custom(first_ord::CustomTypeId, A),
    Array(B),
    HoleArray(B),
    Boxed(B),
}

pub trait VecCompat {
    type Item;

    fn map_refs<U, F>(&self, f: F) -> Vec<U>
    where
        F: FnMut(usize, &Self::Item) -> U;
}

impl<T> VecCompat for Vec<T> {
    type Item = T;

    fn map_refs<U, F>(&self, mut f: F) -> Vec<U>
    where
        F: FnMut(usize, &Self::Item) -> U,
    {
        self.iter().enumerate().map(|(i, v)| f(i, v)).collect()
    }
}

pub struct TL<'a, A, B, C, D>(TF<A, B, OL<'a, C, D>, DynLazy<'a, TL<'a, A, B, C, D>>>);
pub struct STL<'a>(STF<DynLazy<'a, STL<'a>>>);
pub struct OL<'a, A, B>(OF<A, B, DynLazy<'a, OL<'a, A, B>>>);

pub type Type<M, L> =
    TL<'static, (IdVec<ModeParam, M>, IdVec<LtParam, L>), (M, L), IdVec<ModeParam, M>, M>;
pub type Overlay<M> = OL<'static, IdVec<ModeParam, M>, M>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DataKind {
    Stack,
    Heap,
}

// impl<'a, A: 'static, B: 'static> OL<'a, A, B> {
//     pub fn map<A2, B2, F1, F2>(&self, f1: F1, f2: F2) -> OL<'a, A2, B2>
//     where
//         F1: Fn(&A) -> A2 + Clone + 'a,
//         F2: Fn(&B) -> B2 + Clone + 'a,
//     {
//         // `DataKind::Stack` is just a dummy value here. `DataKind` is only relevant when the
//         // overlay resides inside a type, in which case `map_rec` will be called directly.
//         self.map_rec(DataKind::Stack, move |_, v| f1(v), move |_, v| f2(v))
//     }
//
//     fn map_rec<A2, B2, F1, F2>(&self, kind: DataKind, f1: F1, f2: F2) -> OL<'a, A2, B2>
//     where
//         F1: Fn(DataKind, &A) -> A2 + Clone + 'a,
//         F2: Fn(DataKind, &B) -> B2 + Clone + 'a,
//     {
//         let recurse = |ty: &DynLazy<OL<A, B>>, kind: DataKind| {
//             let ty: DynLazy<_> = ty.clone();
//             let f1 = f1.clone();
//             let f2 = f2.clone();
//             lazy(move || ty.map_rec(kind, f1, f2))
//         };
//
//         match &self.0 {
//             OF::Bool => OL(OF::Bool),
//             OF::Num(n) => OL(OF::Num(*n)),
//             OF::Tuple(tys) => OL(OF::Tuple(tys.map_refs(|_, ty| recurse(ty, kind)))),
//             OF::Variants(tys) => OL(OF::Variants(tys.map_refs(|_, ty| recurse(ty, kind)))),
//             OF::Custom(id, tys) => OL(OF::Custom(*id, f1(DataKind::Stack, tys))),
//             OF::Array(v) => OL(OF::Array(f2(kind, v))),
//             OF::HoleArray(v) => OL(OF::HoleArray(f2(kind, v))),
//             OF::Boxed(v) => OL(OF::Boxed(f2(kind, v))),
//         }
//     }
// }

// impl<'a, A: 'a, B: 'a, C: 'a, D: 'a> TL<'a, A, B, C, D> {
//     pub fn map<A2, B2, C2, D2, F1, F2, F3, F4>(
//         &self,
//         f1: F1,
//         f2: F2,
//         f3: F3,
//         f4: F4,
//     ) -> TL<'a, A2, B2, C2, D2>
//     where
//         F1: Fn(DataKind, &A) -> A2 + Clone + 'a,
//         F2: Fn(DataKind, &B) -> B2 + Clone + 'a,
//         F3: Fn(DataKind, &C) -> C2 + Clone + 'a,
//         F4: Fn(DataKind, &D) -> D2 + Clone + 'a,
//     {
//         self.map_rec(DataKind::Stack, f1, f2, f3, f4)
//     }
//
//     fn map_rec<A2, B2, C2, D2, F1, F2, F3, F4>(
//         &self,
//         kind: DataKind,
//         f1: F1,
//         f2: F2,
//         f3: F3,
//         f4: F4,
//     ) -> TL<'a, A2, B2, C2, D2>
//     where
//         F1: Fn(DataKind, &A) -> A2 + Clone + 'static,
//         F2: Fn(DataKind, &B) -> B2 + Clone + 'static,
//         F3: Fn(DataKind, &C) -> C2 + Clone + 'static,
//         F4: Fn(DataKind, &D) -> D2 + Clone + 'static,
//     {
//         let recurse = |ty: &DynLazy<TL<A, B, C, D>>, kind: DataKind| {
//             let ty = ty.clone();
//             let f1 = f1.clone();
//             let f2 = f2.clone();
//             let f3 = f3.clone();
//             let f4 = f4.clone();
//             lazy(move || ty.map_rec(kind, f1, f2, f3, f4))
//         };
//
//         match &self.0 {
//             TF::Bool => TL(TF::Bool),
//             TF::Num(n) => TL(TF::Num(*n)),
//             TF::Tuple(tys) => TL(TF::Tuple(tys.map_refs(|_, ty| recurse(ty, kind)))),
//             TF::Variants(tys) => TL(TF::Variants(tys.map_refs(|_, ty| recurse(ty, kind)))),
//             TF::Custom(id, tys) => TL(TF::Custom(*id, f1(kind, tys))),
//             TF::Array(v, ov, ty) => TL(TF::Array(
//                 f2(kind, v),
//                 ov.map_rec(kind, f3.clone(), f4.clone()),
//                 recurse(ty, DataKind::Heap),
//             )),
//             TF::HoleArray(v, ov, ty) => TL(TF::HoleArray(
//                 f2(kind, v),
//                 ov.map_rec(kind, f3.clone(), f4.clone()),
//                 recurse(ty, DataKind::Heap),
//             )),
//             TF::Boxed(v, ov, ty) => TL(TF::Boxed(
//                 f2(kind, v),
//                 ov.map_rec(kind, f3.clone(), f4.clone()),
//                 recurse(ty, DataKind::Heap),
//             )),
//         }
//     }
// }
