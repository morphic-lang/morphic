use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use id_collections::{id_type, Count, IdVec};
use once_cell::unsync::Lazy;
use std::collections::BTreeSet;
use std::hash::Hash;
use std::marker::PhantomData;
use std::rc::Rc;

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
    WrapCustom(first_ord::CustomTypeId, Occur<M, L>),
    UnwrapCustom(first_ord::CustomTypeId, Occur<M, L>),

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
    Custom(first_ord::CustomTypeId, Box<Condition<M, L>>),
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
    // The mode and lifetime substitutions for this custom type's parameters are stored in the type
    // which corresponds to this overlay.
    Custom(first_ord::CustomTypeId),
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
    Custom(
        first_ord::CustomTypeId,
        IdVec<ModeParam, M>,
        IdVec<LtParam, L>,
    ),
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
                    .zip(tys2)
                    .map(|(t1, t2)| t1.left_meet(t2))
                    .collect(),
            ),
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
    pub num_mode_params: Count<ModeParam>, // Does not include overlay mode params
    pub num_overlay_mode_params: Count<ModeParam>,
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
pub struct CustomTypeDef {
    pub num_mode_params: Count<ModeParam>,
    pub num_overlay_mode_params: Count<ModeParam>,
    pub num_lt_params: Count<LtParam>,
    pub content: Type<ModeParam, LtParam>,
    pub overlay: Overlay<ModeParam>,
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

pub type DynLazy<T> = Rc<Lazy<T, Box<dyn FnOnce() -> T>>>;

pub fn lazy<T>(f: impl FnOnce() -> T + 'static) -> DynLazy<T> {
    Rc::new(Lazy::new(Box::new(f)))
}

// The F-algebra for types
pub enum TF<A, B, X, Y> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<X>),
    Variants(IdVec<first_ord::VariantId, X>),
    Custom(first_ord::CustomTypeId, A),
    Array(B, Y, X),
    HoleArray(B, Y, X),
    Boxed(B, Y, X),
}

// The F-algebra for "simple" types, i.e. types without overlays
pub enum STF<A, B, X> {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<X>),
    Variants(IdVec<first_ord::VariantId, X>),
    Custom(first_ord::CustomTypeId, A),
    Array(B, X),
    HoleArray(B, X),
    Boxed(B, X),
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

pub struct TL<A, B, C, D>(TF<A, B, OL<C, D>, DynLazy<TL<A, B, C, D>>>);
pub struct STL<A, B>(STF<A, B, DynLazy<STL<A, B>>>);
pub struct OL<A, B>(OF<A, B, DynLazy<OL<A, B>>>);

pub type Overlay2<M> = OL<IdVec<ModeParam, M>, M>;

// pub enum OverlayLike<'a, A, B> {
//     Bool,
//     Num(first_ord::NumType),
//     Tuple(Vec<Lazy<'a, OverlayLike<'a, A, B>>>),
//     Variants(IdVec<first_ord::VariantId, Lazy<'a, OverlayLike<'a, A, B>>>),
//     Custom(first_ord::CustomTypeId, A),
//     Array(B),
//     HoleArray(B),
//     Boxed(B),
// }
//
// struct TypeLike2<'a, A, B>(OverlayLike<'a, (), Box<TypeLike2<'a, A, B>>>);
//
// pub enum TypeLike<'a, A, B> {
//     Bool,
//     Num(first_ord::NumType),
//     Tuple(Vec<Lazy<'a, TypeLike<'a, A, B>>>),
//     Variants(IdVec<first_ord::VariantId, Lazy<'a, TypeLike<'a, A, B>>>),
//     Custom(first_ord::CustomTypeId, A),
//     Array(B, Lazy<'a, TypeLike<'a, A, B>>),
//     HoleArray(B, Lazy<'a, TypeLike<'a, A, B>>),
//     Boxed(B, Lazy<'a, TypeLike<'a, A, B>>),
// }
//
// pub enum AnnotLike<'a, A, B, C, D> {
//     Bool,
//     Num(first_ord::NumType),
//     Tuple(Vec<Lazy<'a, AnnotLike<'a, A, B, C, D>>>),
//     Variants(IdVec<first_ord::VariantId, Lazy<'a, AnnotLike<'a, A, B, C, D>>>),
//     Custom(first_ord::CustomTypeId, A),
//     Array(
//         B,
//         Lazy<'a, AnnotLike<'a, A, B, C, D>>,
//         Lazy<'a, OverlayLike<'a, C, D>>,
//     ),
//     HoleArray(
//         B,
//         Lazy<'a, AnnotLike<'a, A, B, C, D>>,
//         Lazy<'a, OverlayLike<'a, C, D>>,
//     ),
//     Boxed(
//         B,
//         Lazy<'a, AnnotLike<'a, A, B, C, D>>,
//         Lazy<'a, OverlayLike<'a, C, D>>,
//     ),
// }
//
// pub type OverlayIter<'a, M> = OverlayLike<'a, (), &'a M>;
// pub type AnnotTypeIter<'a, M, L> =
//     AnnotLike<'a, (&'a IdVec<ModeParam, M>, &'a IdVec<LtParam, L>), (&'a M, &'a L), (), &'a M>;
//
// impl<M> Overlay<M> {
//     pub fn iter<'a>(&'a self) -> OverlayIter<'a, M> {
//         match self {
//             Overlay::Bool => OverlayLike::Bool,
//             Overlay::Num(num_ty) => OverlayLike::Num(*num_ty),
//             Overlay::Tuple(overlays) => OverlayLike::Tuple(
//                 overlays
//                     .iter()
//                     .map(|overlay| Lazy::new(|| overlay.iter()))
//                     .collect(),
//             ),
//             Overlay::Variants(variants) => OverlayLike::Variants(IdVec::from_vec(
//                 variants
//                     .values()
//                     .map(|overlay| Lazy::new(|| overlay.iter()))
//                     .collect(),
//             )),
//             Overlay::Custom(id) => OverlayLike::Custom(*id, ()),
//             Overlay::Array(mode) => OverlayLike::Array(mode),
//             Overlay::HoleArray(mode) => OverlayLike::HoleArray(mode),
//             Overlay::Boxed(mode) => OverlayLike::Boxed(mode),
//         }
//     }
// }
//
// impl<M, L> Type<M, L> {
//     pub fn iter<'a>(&'a self) -> AnnotTypeIter<'a, M, L> {
//         match self {
//             Type::Bool => AnnotLike::Bool,
//             Type::Num(num_ty) => AnnotLike::Num(*num_ty),
//             Type::Tuple(tys) => {
//                 AnnotLike::Tuple(tys.iter().map(|ty| Lazy::new(|| ty.iter())).collect())
//             }
//             Type::Variants(variants) => AnnotLike::Variants(IdVec::from_vec(
//                 variants
//                     .values()
//                     .map(|ty| Lazy::new(|| ty.iter()))
//                     .collect(),
//             )),
//             Type::Custom(id, modes, lts) => AnnotLike::Custom(*id, (modes, lts)),
//             Type::Array(mode, lt, ty, overlay) => AnnotLike::Array(
//                 (mode, lt),
//                 Lazy::new(move || ty.iter()),
//                 Lazy::new(move || overlay.iter()),
//             ),
//             Type::HoleArray(mode, lt, ty, overlay) => AnnotLike::Array(
//                 (mode, lt),
//                 Lazy::new(move || ty.iter()),
//                 Lazy::new(move || overlay.iter()),
//             ),
//             Type::Boxed(mode, lt, ty, overlay) => AnnotLike::Array(
//                 (mode, lt),
//                 Lazy::new(move || ty.iter()),
//                 Lazy::new(move || overlay.iter()),
//             ),
//         }
//     }
// }
//
// impl<'a, A, B, C, D> AnnotLike<'a, A, B, C, D> {
//     pub fn zip<E, F, G, H>(
//         self,
//         other: AnnotLike<E, F, G, H>,
//     ) -> AnnotLike<(A, E), (B, F), (C, G), (D, H)> {
//         todo!()
//         match (self, other) {
//             (TypeLike::Bool, TypeLike::Bool) => TypeLike::Bool,
//             (TypeLike::Num(n1), TypeLike::Num(n2)) if n1 == n2 => TypeLike::Num(n1),
//             (TypeLike::Tuple(tys1), TypeLike::Tuple(tys2)) => TypeLike::Tuple(
//                 tys1.into_iter()
//                     .zip(tys2)
//                     .map(|(t1, t2)| DynLazy::new(move || t1.force().zip(t2.force())))
//                     .collect(),
//             ),
//             (TypeLike::Custom(id1, a1), TypeLike::Custom(id2, a2)) if id1 == id2 => {
//                 TypeLike::Custom(id1, (a1, a2))
//             }
//             (TypeLike::Array(m1, ty1, o1), TypeLike::Array(m2, ty2, o2)) => {
//                 TypeLike::Array((m1, m2), ty1.zip(ty2), o1.map(|o1| o1.zip(o2)))
//             }
//             (TypeLike::HoleArray(m1, ty1, o1), TypeLike::HoleArray(m2, ty2, o2)) => {
//                 TypeLike::HoleArray((m1, m2), ty1.zip(ty2), o1.map(|o1| o1.zip(o2)))
//             }
//             (TypeLike::Boxed(m1, ty1, o1), TypeLike::Boxed(m2, ty2, o2)) => {
//                 TypeLike::Boxed((m1, m2), ty1.zip(ty2), o1.map(|o1| o1.zip(o2)))
//             }
//             _ => panic!("incompatible types"),
//         }
//     }
// }

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub enum Overlay<M> {
//     Bool,
//     Num(first_ord::NumType),
//     Tuple(Vec<Overlay<M>>),
//     Variants(IdVec<first_ord::VariantId, Overlay<M>>),
//     // The mode and lifetime substitutions for this custom type's parameters are stored in the type
//     // which corresponds to this overlay.
//     Custom(first_ord::CustomTypeId),
//     Array(M),
//     HoleArray(M),
//     Boxed(M),
// }

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub enum Type<M, L> {
//     Bool,
//     Num(first_ord::NumType),
//     Tuple(Vec<Type<M, L>>),
//     Variants(IdVec<first_ord::VariantId, Type<M, L>>),
//     Custom(
//         first_ord::CustomTypeId,
//         IdVec<ModeParam, M>,
//         IdVec<LtParam, L>,
//     ),
//     Array(M, L, Box<Type<M, L>>, Overlay<M>),
//     HoleArray(M, L, Box<Type<M, L>>, Overlay<M>),
//     Boxed(M, L, Box<Type<M, L>>, Overlay<M>),
// }
