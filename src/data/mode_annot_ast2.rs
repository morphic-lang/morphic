use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
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

#[derive(Debug, Clone, Copy)]
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
pub enum ArrayOp<M, L> {
    Get(
        Type<M, L>,    // Item type
        flat::LocalId, // Array
        flat::LocalId, // Index
    ), // Returns item
    Extract(
        Type<M, L>,    // Item type
        flat::LocalId, // Array
        flat::LocalId, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        Type<M, L>,    // Item type
        flat::LocalId, // Array
    ), // Returns int
    Push(
        Type<M, L>,    // Item type
        flat::LocalId, // Array
        flat::LocalId, // Item
    ), // Returns new array
    Pop(
        Type<M, L>,    // Item type
        flat::LocalId, // Array
    ), // Returns tuple (array, item)
    Replace(
        Type<M, L>,    // Item type
        flat::LocalId, // Hole array
        flat::LocalId, // Item
    ), // Returns new array
    Reserve(
        Type<M, L>,    // Item type
        flat::LocalId, // Array
        flat::LocalId, // Capacity
    ), // Returns new array
}

#[derive(Clone, Debug)]
pub enum Expr<M, L> {
    Local(flat::LocalId),
    Call(Purity, first_ord::CustomFuncId, flat::LocalId),
    Branch(
        flat::LocalId,
        Vec<(Condition<M, L>, Expr<M, L>)>,
        Type<M, L>,
    ),
    LetMany(
        Vec<(Type<M, L>, Expr<M, L>)>, // bound values.  Each is assigned a new sequential flat::LocalId
        flat::LocalId,                 // body
    ),

    Tuple(Vec<flat::LocalId>),
    TupleField(flat::LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type<M, L>>,
        first_ord::VariantId,
        flat::LocalId,
    ),
    UnwrapVariant(first_ord::VariantId, flat::LocalId),
    WrapBoxed(
        flat::LocalId,
        Type<M, L>, // Inner type
    ),
    UnwrapBoxed(
        flat::LocalId,
        Type<M, L>, // Inner type
    ),
    WrapCustom(first_ord::CustomTypeId, flat::LocalId),
    UnwrapCustom(first_ord::CustomTypeId, flat::LocalId),

    Intrinsic(Intrinsic, flat::LocalId),
    ArrayOp(ArrayOp<M, L>),
    IoOp(flat::IoOp),
    Panic(Type<M, L>, flat::LocalId),

    ArrayLit(Type<M, L>, Vec<flat::LocalId>),
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

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,

    // Total number of params in `arg_type` and `ret_type`.
    pub num_mode_params: Count<ModeParam>,
    pub num_overlay_mode_params: Count<ModeParam>,
    pub num_lt_params: Count<LtParam>,

    pub arg_type: Type<ModeParam, LtParam>,
    pub ret_type: Type<ModeParam, LtParam>,
    pub constrs: Vec<ModeConstr<ModeParam>>,

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

pub mod iter {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Item<A, B> {
        Bool,
        Num(first_ord::NumType),
        Tuple(usize),
        Variants(Count<first_ord::VariantId>),
        Custom(first_ord::CustomTypeId, A),
        Array(B),
        HoleArray(B),
        Boxed(B),
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Item2<A, B, C, D> {
        Outer(Item<A, B>), // Holds type data
        Inner(Item<C, D>), // Holds overlay data
    }

    // An iterator over these items can be used to construct a `Type`.
    pub type TypeItem<'a, M, L> =
        Item2<(&'a IdVec<ModeParam, M>, &'a IdVec<LtParam, L>), (&'a M, &'a L), (), &'a M>;

    // The item type for types when co-iterating over types and overlays.
    pub type StackTypeItem<'a, M, L> =
        Item<(&'a IdVec<ModeParam, M>, &'a IdVec<LtParam, L>), (&'a M, &'a L)>;

    // An iterator over these items can be used to construct a `Overlay`.
    pub type OverlayItem<'a, M> = Item<(), &'a M>;

    pub trait IterExt<A, B>
    where
        Self: Iterator<Item = Item<A, B>> + Sized,
    {
        fn zip_annot<C, D, I>(self, other: I) -> Zip<Self, I>
        where
            I: Iterator<Item = Item<C, D>>,
        {
            Zip {
                iter1: self,
                iter2: other,
            }
        }

        fn map_annot<C, D, F1, F2>(self, f1: F1, f2: F2) -> Map<Self, F1, F2>
        where
            F1: FnMut(A) -> C,
            F2: FnMut(B) -> D,
        {
            Map { iter: self, f1, f2 }
        }
    }

    impl<A, B, I> IterExt<A, B> for I where I: Iterator<Item = Item<A, B>> {}

    pub trait IterExt2<A, B, C, D>
    where
        Self: Iterator<Item = Item2<A, B, C, D>> + Sized,
    {
        fn zip_annot2<E, F, G, H, I>(self, other: I) -> Zip2<Self, I>
        where
            I: Iterator<Item = Item2<E, F, G, H>>,
        {
            Zip2 {
                iter1: self,
                iter2: other,
            }
        }

        fn map_annot2<E, F, G, H, F1, F2, F3, F4>(
            self,
            f1: F1,
            f2: F2,
            f3: F3,
            f4: F4,
        ) -> Map2<Self, F1, F2, F3, F4>
        where
            F1: FnMut(A) -> E,
            F2: FnMut(B) -> F,
            F3: FnMut(C) -> G,
            F4: FnMut(D) -> H,
        {
            Map2 {
                iter: self,
                f1,
                f2,
                f3,
                f4,
            }
        }
    }

    impl<A, B, C, D, I> IterExt2<A, B, C, D> for I where I: Iterator<Item = Item2<A, B, C, D>> {}

    pub struct Zip<I, J> {
        iter1: I,
        iter2: J,
    }

    impl<A, B, C, D, E, F> Iterator for Zip<A, B>
    where
        A: Iterator<Item = Item<C, D>>,
        B: Iterator<Item = Item<E, F>>,
    {
        type Item = Item<(C, E), (D, F)>;

        fn next(&mut self) -> Option<Self::Item> {
            match (self.iter1.next(), self.iter2.next()) {
                (Some(item1), Some(item2)) => Some(zip_items(item1, item2)),
                (None, None) => None,
                _ => panic!("incompatible types"),
            }
        }
    }

    pub struct Zip2<I, J> {
        iter1: I,
        iter2: J,
    }

    impl<A, B, C, D, E, F, G, H, I, J> Iterator for Zip2<I, J>
    where
        I: Iterator<Item = Item2<A, B, C, D>>,
        J: Iterator<Item = Item2<E, F, G, H>>,
    {
        type Item = Item2<(A, E), (B, F), (C, G), (D, H)>;

        fn next(&mut self) -> Option<Self::Item> {
            match (self.iter1.next(), self.iter2.next()) {
                (Some(Item2::Outer(n1)), Some(Item2::Outer(n2))) => {
                    Some(Item2::Outer(zip_items(n1, n2)))
                }
                (Some(Item2::Inner(n1)), Some(Item2::Inner(n2))) => {
                    Some(Item2::Inner(zip_items(n1, n2)))
                }
                (None, None) => None,
                _ => panic!("incompatible types"),
            }
        }
    }

    fn zip_items<A, B, C, D>(n1: Item<A, B>, n2: Item<C, D>) -> Item<(A, C), (B, D)> {
        match (n1, n2) {
            (Item::Bool, Item::Bool) => Item::Bool,
            (Item::Num(t1), Item::Num(t2)) if t1 == t2 => Item::Num(t1),
            (Item::Tuple(n1), Item::Tuple(n2)) if n1 == n2 => Item::Tuple(n1),
            (Item::Variants(n1), Item::Variants(n2)) if n1 == n2 => Item::Variants(n1),
            (Item::Custom(id1, v1), Item::Custom(id2, v2)) if id1 == id2 => {
                Item::Custom(id1, (v1, v2))
            }
            (Item::Array(v1), Item::Array(v2)) => Item::Array((v1, v2)),
            (Item::HoleArray(v1), Item::HoleArray(v2)) => Item::HoleArray((v1, v2)),
            (Item::Boxed(v1), Item::Boxed(v2)) => Item::Boxed((v1, v2)),
            _ => panic!("incompatible types"),
        }
    }

    pub struct Map<I, F1, F2> {
        iter: I,
        f1: F1,
        f2: F2,
    }

    impl<A, B, C, D, I, F1, F2> Iterator for Map<I, F1, F2>
    where
        I: Iterator<Item = Item<A, B>>,
        F1: FnMut(A) -> C,
        F2: FnMut(B) -> D,
    {
        type Item = Item<C, D>;

        fn next(&mut self) -> Option<Self::Item> {
            self.iter.next().map(|item| match item {
                Item::Bool => Item::Bool,
                Item::Num(t) => Item::Num(t),
                Item::Tuple(n) => Item::Tuple(n),
                Item::Variants(n) => Item::Variants(n),
                Item::Custom(id, v) => Item::Custom(id, (self.f1)(v)),
                Item::Array(v) => Item::Array((self.f2)(v)),
                Item::HoleArray(v) => Item::HoleArray((self.f2)(v)),
                Item::Boxed(v) => Item::Boxed((self.f2)(v)),
            })
        }
    }

    pub struct Map2<I, F1, F2, F3, F4> {
        iter: I,
        f1: F1,
        f2: F2,
        f3: F3,
        f4: F4,
    }

    impl<A, B, C, D, E, F, G, H, I, F1, F2, F3, F4> Iterator for Map2<I, F1, F2, F3, F4>
    where
        I: Iterator<Item = Item2<A, B, C, D>>,
        F1: FnMut(A) -> E,
        F2: FnMut(B) -> F,
        F3: FnMut(C) -> G,
        F4: FnMut(D) -> H,
    {
        type Item = Item2<E, F, G, H>;

        fn next(&mut self) -> Option<Self::Item> {
            self.iter.next().map(|item| match item {
                Item2::Outer(Item::Bool) => Item2::Outer(Item::Bool),
                Item2::Outer(Item::Num(t)) => Item2::Outer(Item::Num(t)),
                Item2::Outer(Item::Tuple(n)) => Item2::Outer(Item::Tuple(n)),
                Item2::Outer(Item::Variants(n)) => Item2::Outer(Item::Variants(n)),
                Item2::Outer(Item::Custom(id, v)) => Item2::Outer(Item::Custom(id, (self.f1)(v))),
                Item2::Outer(Item::Array(v)) => Item2::Outer(Item::Array((self.f2)(v))),
                Item2::Outer(Item::HoleArray(v)) => Item2::Outer(Item::HoleArray((self.f2)(v))),
                Item2::Outer(Item::Boxed(v)) => Item2::Outer(Item::Boxed((self.f2)(v))),
                Item2::Inner(Item::Bool) => Item2::Inner(Item::Bool),
                Item2::Inner(Item::Num(t)) => Item2::Inner(Item::Num(t)),
                Item2::Inner(Item::Tuple(n)) => Item2::Inner(Item::Tuple(n)),
                Item2::Inner(Item::Variants(n)) => Item2::Inner(Item::Variants(n)),
                Item2::Inner(Item::Custom(id, v)) => Item2::Inner(Item::Custom(id, (self.f3)(v))),
                Item2::Inner(Item::Array(v)) => Item2::Inner(Item::Array((self.f4)(v))),
                Item2::Inner(Item::HoleArray(v)) => Item2::Inner(Item::HoleArray((self.f4)(v))),
                Item2::Inner(Item::Boxed(v)) => Item2::Inner(Item::Boxed((self.f4)(v))),
            })
        }
    }

    pub trait CollectTypeExt<M, L> {
        fn collect_type(self) -> Type<M, L>;
    }

    impl<'a, I, M, L> CollectTypeExt<M, L> for I
    where
        I: Iterator<Item = TypeItem<'a, M, L>>,
        M: 'a + Clone,
        L: 'a + Clone,
    {
        fn collect_type(self) -> Type<M, L> {
            let items: Vec<_> = self.collect();
            collect_outer(&items, 0).0
        }
    }

    pub trait CollectOverlayExt<M> {
        fn collect_overlay(self) -> Overlay<M>;
    }

    impl<'a, I, M> CollectOverlayExt<M> for I
    where
        I: Iterator<Item = OverlayItem<'a, M>>,
        M: 'a + Clone,
    {
        fn collect_overlay(self) -> Overlay<M> {
            let items: Vec<_> = self.collect();
            collect_items(&items, 0).0
        }
    }

    fn collect_many<T, F>(n: usize, mut i: usize, mut collect_one: F) -> (Vec<T>, usize)
    where
        F: FnMut(usize) -> (T, usize),
    {
        let mut res = Vec::with_capacity(n);
        for _ in 0..n {
            let (item, j) = collect_one(i);
            res.push(item);
            i = j;
        }
        (res, i)
    }

    // Expects types to be layed out in DFS preorder with overlays appearing before types in the
    // relevant cases.
    fn collect_outer<M, L>(items: &[TypeItem<'_, M, L>], i: usize) -> (Type<M, L>, usize)
    where
        M: Clone,
        L: Clone,
    {
        match items[i].clone() {
            Item2::Outer(Item::Bool) => (Type::Bool, i + 1),
            Item2::Outer(Item::Num(t)) => (Type::Num(t), i + 1),
            Item2::Outer(Item::Tuple(n)) => {
                let (tys, j) = collect_many(n, i + 1, |i| collect_outer(items, i));
                (Type::Tuple(tys), j)
            }
            Item2::Outer(Item::Variants(n)) => {
                let (tys, j) = collect_many(n.to_value(), i + 1, |i| collect_outer(items, i));
                (Type::Variants(IdVec::from_vec(tys)), j)
            }
            Item2::Outer(Item::Custom(id, (modes, lts))) => {
                (Type::Custom(id, modes.clone(), lts.clone()), i + 1)
            }
            Item2::Outer(Item::Array((mode, lt))) => {
                let (overlay, j) = collect_inner(items, i + 1);
                let (ty, k) = collect_outer(items, j);
                let res = Type::Array(mode.clone(), lt.clone(), Box::new(ty), overlay);
                (res, k)
            }
            Item2::Outer(Item::HoleArray((mode, lt))) => {
                let (overlay, j) = collect_inner(items, i + 1);
                let (ty, k) = collect_outer(items, j);
                let res = Type::Array(mode.clone(), lt.clone(), Box::new(ty), overlay);
                (res, k)
            }
            Item2::Outer(Item::Boxed((mode, lt))) => {
                let (overlay, j) = collect_inner(items, i + 1);
                let (ty, k) = collect_outer(items, j);
                let res = Type::Array(mode.clone(), lt.clone(), Box::new(ty), overlay);
                (res, k)
            }
            Item2::Inner(_) => panic!("expected outer node"),
        }
    }

    fn collect_inner<M, L>(items: &[TypeItem<'_, M, L>], i: usize) -> (Overlay<M>, usize)
    where
        M: Clone,
    {
        match items[i].clone() {
            Item2::Inner(Item::Bool) => (Overlay::Bool, i + 1),
            Item2::Inner(Item::Num(t)) => (Overlay::Num(t), i + 1),
            Item2::Inner(Item::Tuple(n)) => {
                let (tys, j) = collect_many(n, i + 1, |j| collect_inner(items, j));
                (Overlay::Tuple(tys), j)
            }
            Item2::Inner(Item::Variants(n)) => {
                let (tys, j) = collect_many(n.to_value(), i + 1, |j| collect_inner(items, j));
                (Overlay::Variants(IdVec::from_vec(tys)), j)
            }
            Item2::Inner(Item::Custom(id, ())) => (Overlay::Custom(id), i + 1),
            Item2::Inner(Item::Array(mode)) => (Overlay::Array(mode.clone()), i + 1),
            Item2::Inner(Item::HoleArray(mode)) => (Overlay::HoleArray(mode.clone()), i + 1),
            Item2::Inner(Item::Boxed(mode)) => (Overlay::Boxed(mode.clone()), i + 1),
            Item2::Outer(_) => panic!("expected inner node"),
        }
    }

    fn collect_items<M>(items: &[OverlayItem<'_, M>], i: usize) -> (Overlay<M>, usize)
    where
        M: Clone,
    {
        match items[i].clone() {
            Item::Bool => (Overlay::Bool, i + 1),
            Item::Num(t) => (Overlay::Num(t), i + 1),
            Item::Tuple(n) => {
                let (tys, j) = collect_many(n, i + 1, |j| collect_items(items, j));
                (Overlay::Tuple(tys), j)
            }
            Item::Variants(n) => {
                let (tys, j) = collect_many(n.to_value(), i + 1, |j| collect_items(items, j));
                (Overlay::Variants(IdVec::from_vec(tys)), j)
            }
            Item::Custom(id, ()) => (Overlay::Custom(id), i + 1),
            Item::Array(mode) => (Overlay::Array(mode.clone()), i + 1),
            Item::HoleArray(mode) => (Overlay::HoleArray(mode.clone()), i + 1),
            Item::Boxed(mode) => (Overlay::Boxed(mode.clone()), i + 1),
        }
    }

    // Must produce nodes in the order that `collect_outer` etc. expect.
    #[derive(Clone, Debug)]
    pub struct TypeIter<'a, M, L> {
        stack: Vec<TypeFrame<'a, M, L>>,
    }

    #[derive(Clone, Debug)]
    pub struct StackTypeIter<'a, M, L> {
        stack: Vec<StackTypeFrame<'a, M, L>>,
    }

    #[derive(Clone, Debug)]
    pub struct OverlayIter<'a, M> {
        stack: Vec<OverlayFrame<'a, M>>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum TypeFrame<'a, M, L> {
        // Outer nodes
        Bool,
        Num(first_ord::NumType),
        Tuple(&'a Vec<Type<M, L>>),
        TupleItem(usize, &'a Vec<Type<M, L>>),
        Variants(&'a IdVec<first_ord::VariantId, Type<M, L>>),
        Variant(usize, &'a IdVec<first_ord::VariantId, Type<M, L>>),
        Custom(
            first_ord::CustomTypeId,
            &'a IdVec<ModeParam, M>,
            &'a IdVec<LtParam, L>,
        ),
        Array(&'a M, &'a L, &'a Box<Type<M, L>>, &'a Overlay<M>),
        HoleArray(&'a M, &'a L, &'a Box<Type<M, L>>, &'a Overlay<M>),
        Boxed(&'a M, &'a L, &'a Box<Type<M, L>>, &'a Overlay<M>),

        // Inner nodes
        OverlayBool,
        OverlayNum(first_ord::NumType),
        OverlayTuple(&'a Vec<Overlay<M>>),
        OverlayTupleItem(usize, &'a Vec<Overlay<M>>),
        OverlayVariants(&'a IdVec<first_ord::VariantId, Overlay<M>>),
        OverlayVariant(usize, &'a IdVec<first_ord::VariantId, Overlay<M>>),
        OverlayCustom(first_ord::CustomTypeId),
        OverlayArray(&'a M),
        OverlayHoleArray(&'a M),
        OverlayBoxed(&'a M),
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum StackTypeFrame<'a, M, L> {
        Bool,
        Num(first_ord::NumType),
        Tuple(&'a Vec<Type<M, L>>),
        TupleItem(usize, &'a Vec<Type<M, L>>),
        Variants(&'a IdVec<first_ord::VariantId, Type<M, L>>),
        Variant(usize, &'a IdVec<first_ord::VariantId, Type<M, L>>),
        Custom(
            first_ord::CustomTypeId,
            &'a IdVec<ModeParam, M>,
            &'a IdVec<LtParam, L>,
        ),
        Array(&'a M, &'a L),
        HoleArray(&'a M, &'a L),
        Boxed(&'a M, &'a L),
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum OverlayFrame<'a, M> {
        Bool,
        Num(first_ord::NumType),
        Tuple(&'a Vec<Overlay<M>>),
        TupleItem(usize, &'a Vec<Overlay<M>>),
        Variants(&'a IdVec<first_ord::VariantId, Overlay<M>>),
        Variant(usize, &'a IdVec<first_ord::VariantId, Overlay<M>>),
        Custom(first_ord::CustomTypeId),
        Array(&'a M),
        HoleArray(&'a M),
        Boxed(&'a M),
    }

    #[derive(Clone, Debug)]
    enum StepResult<T> {
        Done,
        Step,
        Yield(T),
    }

    impl<M, L> Type<M, L> {
        pub fn iter(&self) -> TypeIter<M, L> {
            TypeIter::new(self)
        }

        pub fn iter_stack(&self) -> StackTypeIter<M, L> {
            StackTypeIter::new(self)
        }
    }

    impl<'a, M, L> Iterator for TypeIter<'a, M, L> {
        type Item = TypeItem<'a, M, L>;

        fn next(&mut self) -> Option<Self::Item> {
            loop {
                match self.step() {
                    StepResult::Done => return None,
                    StepResult::Step => {}
                    StepResult::Yield(item) => return Some(item),
                }
            }
        }
    }

    impl<'a, M, L> Iterator for StackTypeIter<'a, M, L> {
        type Item = StackTypeItem<'a, M, L>;

        fn next(&mut self) -> Option<Self::Item> {
            loop {
                match self.step() {
                    StepResult::Done => return None,
                    StepResult::Step => {}
                    StepResult::Yield(item) => return Some(item),
                }
            }
        }
    }

    impl<M> Overlay<M> {
        pub fn iter(&self) -> OverlayIter<M> {
            OverlayIter::new(self)
        }
    }

    impl<'a, M> Iterator for OverlayIter<'a, M> {
        type Item = OverlayItem<'a, M>;

        fn next(&mut self) -> Option<Self::Item> {
            loop {
                match self.step() {
                    StepResult::Done => return None,
                    StepResult::Step => {}
                    StepResult::Yield(item) => return Some(item),
                }
            }
        }
    }

    impl<'a, M, L> TypeFrame<'a, M, L> {
        fn from_type(ty: &'a Type<M, L>) -> Self {
            match ty {
                Type::Bool => TypeFrame::Bool,
                Type::Num(t) => TypeFrame::Num(*t),
                Type::Tuple(tys) => TypeFrame::Tuple(tys),
                Type::Variants(tys) => TypeFrame::Variants(tys),
                Type::Custom(id, modes, lts) => TypeFrame::Custom(*id, modes, lts),
                Type::Array(m, lt, ty, overlay) => TypeFrame::Array(m, lt, ty, overlay),
                Type::HoleArray(m, lt, ty, overlay) => TypeFrame::HoleArray(m, lt, ty, overlay),
                Type::Boxed(m, lt, ty, overlay) => TypeFrame::Boxed(m, lt, ty, overlay),
            }
        }

        fn from_overlay(overlay: &'a Overlay<M>) -> Self {
            match overlay {
                Overlay::Bool => TypeFrame::OverlayBool,
                Overlay::Num(t) => TypeFrame::OverlayNum(*t),
                Overlay::Tuple(tys) => TypeFrame::OverlayTuple(tys),
                Overlay::Variants(tys) => TypeFrame::OverlayVariants(tys),
                Overlay::Custom(id) => TypeFrame::OverlayCustom(*id),
                Overlay::Array(m) => TypeFrame::OverlayArray(m),
                Overlay::HoleArray(m) => TypeFrame::OverlayHoleArray(m),
                Overlay::Boxed(m) => TypeFrame::OverlayBoxed(m),
            }
        }
    }

    impl<'a, M, L> StackTypeFrame<'a, M, L> {
        fn new(ty: &'a Type<M, L>) -> Self {
            match ty {
                Type::Bool => StackTypeFrame::Bool,
                Type::Num(t) => StackTypeFrame::Num(*t),
                Type::Tuple(tys) => StackTypeFrame::Tuple(tys),
                Type::Variants(tys) => StackTypeFrame::Variants(tys),
                Type::Custom(id, modes, lts) => StackTypeFrame::Custom(*id, modes, lts),
                Type::Array(m, lt, _ty, _overlay) => StackTypeFrame::Array(m, lt),
                Type::HoleArray(m, lt, _ty, _overlay) => StackTypeFrame::HoleArray(m, lt),
                Type::Boxed(m, lt, _ty, _overlay) => StackTypeFrame::Boxed(m, lt),
            }
        }
    }

    impl<'a, M> OverlayFrame<'a, M> {
        fn new(overlay: &'a Overlay<M>) -> Self {
            match overlay {
                Overlay::Bool => OverlayFrame::Bool,
                Overlay::Num(t) => OverlayFrame::Num(*t),
                Overlay::Tuple(tys) => OverlayFrame::Tuple(tys),
                Overlay::Variants(tys) => OverlayFrame::Variants(tys),
                Overlay::Custom(id) => OverlayFrame::Custom(*id),
                Overlay::Array(m) => OverlayFrame::Array(m),
                Overlay::HoleArray(m) => OverlayFrame::HoleArray(m),
                Overlay::Boxed(m) => OverlayFrame::Boxed(m),
            }
        }
    }

    impl<'a, M, L> TypeIter<'a, M, L> {
        pub fn new(ty: &'a Type<M, L>) -> Self {
            Self {
                stack: vec![TypeFrame::from_type(ty)],
            }
        }

        fn step(&mut self) -> StepResult<TypeItem<'a, M, L>> {
            let Some(frame) = self.stack.pop() else {
                return StepResult::Done;
            };
            match frame {
                TypeFrame::Bool => StepResult::Yield(Item2::Outer(Item::Bool)),
                TypeFrame::Num(t) => StepResult::Yield(Item2::Outer(Item::Num(t))),
                TypeFrame::Tuple(tys) => {
                    if !tys.is_empty() {
                        self.stack.push(TypeFrame::TupleItem(0, tys));
                    }
                    StepResult::Yield(Item2::Outer(Item::Tuple(tys.len())))
                }
                TypeFrame::TupleItem(i, tys) => {
                    if i + 1 < tys.len() {
                        self.stack.push(TypeFrame::TupleItem(i + 1, tys));
                    }
                    self.stack.push(TypeFrame::from_type(&tys[i]));
                    StepResult::Step
                }
                TypeFrame::Variants(tys) => {
                    if !tys.is_empty() {
                        self.stack.push(TypeFrame::Variant(0, tys));
                    }
                    StepResult::Yield(Item2::Outer(Item::Variants(tys.count())))
                }
                TypeFrame::Variant(i, tys) => {
                    if i + 1 < tys.len() {
                        self.stack.push(TypeFrame::Variant(i + 1, tys));
                    }
                    self.stack
                        .push(TypeFrame::from_type(&tys[first_ord::VariantId(i)]));
                    StepResult::Step
                }
                TypeFrame::Custom(id, modes, lts) => {
                    StepResult::Yield(Item2::Outer(Item::Custom(id, (modes, lts))))
                }
                TypeFrame::Array(m, lt, ty, overlay) => {
                    self.stack.push(TypeFrame::from_type(ty));
                    self.stack.push(TypeFrame::from_overlay(overlay));
                    StepResult::Yield(Item2::Outer(Item::Array((m, lt))))
                }
                TypeFrame::HoleArray(m, lt, ty, overlay) => {
                    self.stack.push(TypeFrame::from_type(ty));
                    self.stack.push(TypeFrame::from_overlay(overlay));
                    StepResult::Yield(Item2::Outer(Item::HoleArray((m, lt))))
                }
                TypeFrame::Boxed(m, lt, ty, overlay) => {
                    self.stack.push(TypeFrame::from_type(ty));
                    self.stack.push(TypeFrame::from_overlay(overlay));
                    StepResult::Yield(Item2::Outer(Item::Boxed((m, lt))))
                }

                TypeFrame::OverlayBool => StepResult::Yield(Item2::Inner(Item::Bool)),
                TypeFrame::OverlayNum(t) => StepResult::Yield(Item2::Inner(Item::Num(t))),
                TypeFrame::OverlayTuple(tys) => {
                    if !tys.is_empty() {
                        self.stack.push(TypeFrame::OverlayTupleItem(0, tys));
                    }
                    StepResult::Yield(Item2::Inner(Item::Tuple(tys.len())))
                }
                TypeFrame::OverlayTupleItem(i, tys) => {
                    if i + 1 < tys.len() {
                        self.stack.push(TypeFrame::OverlayTupleItem(i + 1, tys));
                    }
                    self.stack.push(TypeFrame::from_overlay(&tys[i]));
                    StepResult::Step
                }
                TypeFrame::OverlayVariants(tys) => {
                    if !tys.is_empty() {
                        self.stack.push(TypeFrame::OverlayVariant(0, tys));
                    }
                    StepResult::Yield(Item2::Inner(Item::Variants(tys.count())))
                }
                TypeFrame::OverlayVariant(i, tys) => {
                    if i + 1 < tys.len() {
                        self.stack.push(TypeFrame::OverlayVariant(i + 1, tys));
                    }
                    self.stack
                        .push(TypeFrame::from_overlay(&tys[first_ord::VariantId(i)]));
                    StepResult::Step
                }
                TypeFrame::OverlayCustom(id) => {
                    StepResult::Yield(Item2::Inner(Item::Custom(id, ())))
                }
                TypeFrame::OverlayArray(m) => StepResult::Yield(Item2::Inner(Item::Array(m))),
                TypeFrame::OverlayHoleArray(m) => {
                    StepResult::Yield(Item2::Inner(Item::HoleArray(m)))
                }
                TypeFrame::OverlayBoxed(m) => StepResult::Yield(Item2::Inner(Item::Boxed(m))),
            }
        }
    }

    impl<'a, M, L> StackTypeIter<'a, M, L> {
        pub fn new(ty: &'a Type<M, L>) -> Self {
            Self {
                stack: vec![StackTypeFrame::new(ty)],
            }
        }

        fn step(&mut self) -> StepResult<StackTypeItem<'a, M, L>> {
            let Some(frame) = self.stack.pop() else {
                return StepResult::Done;
            };
            match frame {
                StackTypeFrame::Bool => StepResult::Yield(Item::Bool),
                StackTypeFrame::Num(t) => StepResult::Yield(Item::Num(t)),
                StackTypeFrame::Tuple(tys) => {
                    if !tys.is_empty() {
                        self.stack.push(StackTypeFrame::TupleItem(0, tys));
                    }
                    StepResult::Yield(Item::Tuple(tys.len()))
                }
                StackTypeFrame::TupleItem(i, tys) => {
                    if i + 1 < tys.len() {
                        self.stack.push(StackTypeFrame::TupleItem(i + 1, tys));
                    }
                    self.stack.push(StackTypeFrame::new(&tys[i]));
                    StepResult::Step
                }
                StackTypeFrame::Variants(tys) => {
                    if !tys.is_empty() {
                        self.stack.push(StackTypeFrame::Variant(0, tys));
                    }
                    StepResult::Yield(Item::Variants(tys.count()))
                }
                StackTypeFrame::Variant(i, tys) => {
                    if i + 1 < tys.len() {
                        self.stack.push(StackTypeFrame::Variant(i + 1, tys));
                    }
                    self.stack
                        .push(StackTypeFrame::new(&tys[first_ord::VariantId(i)]));
                    StepResult::Step
                }
                StackTypeFrame::Custom(id, modes, lts) => {
                    StepResult::Yield(Item::Custom(id, (modes, lts)))
                }
                StackTypeFrame::Array(m, lt) => StepResult::Yield(Item::Array((m, lt))),
                StackTypeFrame::HoleArray(m, lt) => StepResult::Yield(Item::HoleArray((m, lt))),
                StackTypeFrame::Boxed(m, lt) => StepResult::Yield(Item::Boxed((m, lt))),
            }
        }
    }

    impl<'a, M> OverlayIter<'a, M> {
        pub fn new(overlay: &'a Overlay<M>) -> Self {
            Self {
                stack: vec![OverlayFrame::new(overlay)],
            }
        }

        fn step(&mut self) -> StepResult<OverlayItem<'a, M>> {
            let Some(frame) = self.stack.pop() else {
                return StepResult::Done;
            };
            match frame {
                OverlayFrame::Bool => StepResult::Yield(Item::Bool),
                OverlayFrame::Num(t) => StepResult::Yield(Item::Num(t)),
                OverlayFrame::Tuple(tys) => {
                    if !tys.is_empty() {
                        self.stack.push(OverlayFrame::TupleItem(0, tys));
                    }
                    StepResult::Yield(Item::Tuple(tys.len()))
                }
                OverlayFrame::TupleItem(i, tys) => {
                    if i + 1 < tys.len() {
                        self.stack.push(OverlayFrame::TupleItem(i + 1, tys));
                    }
                    self.stack.push(OverlayFrame::new(&tys[i]));
                    StepResult::Step
                }
                OverlayFrame::Variants(tys) => {
                    if !tys.is_empty() {
                        self.stack.push(OverlayFrame::Variant(0, tys));
                    }
                    StepResult::Yield(Item::Variants(tys.count()))
                }
                OverlayFrame::Variant(i, tys) => {
                    if i + 1 < tys.len() {
                        self.stack.push(OverlayFrame::Variant(i + 1, tys));
                    }
                    self.stack
                        .push(OverlayFrame::new(&tys[first_ord::VariantId(i)]));
                    StepResult::Step
                }
                OverlayFrame::Custom(id) => StepResult::Yield(Item::Custom(id, ())),
                OverlayFrame::Array(m) => StepResult::Yield(Item::Array(m)),
                OverlayFrame::HoleArray(m) => StepResult::Yield(Item::HoleArray(m)),
                OverlayFrame::Boxed(m) => StepResult::Yield(Item::Boxed(m)),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::iter::*;
    use super::*;

    #[test]
    fn test_iter_collect() {
        let ty1: Type<ModeParam, LtParam> = Type::Tuple(vec![
            Type::Tuple(vec![Type::Bool, Type::Num(first_ord::NumType::Int)]),
            Type::Tuple(vec![
                Type::Num(first_ord::NumType::Byte),
                Type::Num(first_ord::NumType::Float),
            ]),
        ]);
        let ty2 = ty1.iter().collect_type();
        assert_eq!(ty1, ty2);
    }

    #[test]
    fn test_zip2() {
        let ty1 = Type::Tuple(vec![
            Type::Bool,
            Type::Array(
                ModeParam(0),
                LtParam(0),
                Box::new(Type::Num(first_ord::NumType::Int)),
                Overlay::Num(first_ord::NumType::Int),
            ),
        ]);
        let ty2 = Type::Tuple(vec![
            Type::Bool,
            Type::Array(
                ModeParam(1),
                LtParam(1),
                Box::new(Type::Num(first_ord::NumType::Int)),
                Overlay::Num(first_ord::NumType::Int),
            ),
        ]);
        let items: Vec<_> = ty1.iter().zip_annot2(ty2.iter()).collect();
        assert_eq!(
            items,
            vec![
                Item2::Outer(Item::Tuple(2)),
                Item2::Outer(Item::Bool),
                Item2::Outer(Item::Array((
                    (&ModeParam(0), &LtParam(0)),
                    (&ModeParam(1), &LtParam(1))
                ))),
                Item2::Inner(Item::Num(first_ord::NumType::Int)),
                Item2::Outer(Item::Num(first_ord::NumType::Int)),
            ]
        );
    }

    #[test]
    #[should_panic]
    fn test_zip2_incompatible() {
        let ty1 = Type::Tuple(vec![
            Type::Bool,
            Type::Array(
                ModeParam(0),
                LtParam(0),
                Box::new(Type::Num(first_ord::NumType::Int)),
                Overlay::Bool,
            ),
        ]);
        let ty2 = Type::Tuple(vec![
            Type::Bool,
            Type::Array(
                ModeParam(1),
                LtParam(1),
                Box::new(Type::Num(first_ord::NumType::Int)),
                Overlay::Num(first_ord::NumType::Int),
            ),
        ]);
        let _: Vec<_> = ty1.iter().zip_annot2(ty2.iter()).collect();
    }

    #[test]
    fn test_zip() {
        let ty = Type::Tuple(vec![
            Type::Bool,
            Type::Array(
                ModeParam(0),
                LtParam(0),
                Box::new(Type::Num(first_ord::NumType::Int)),
                Overlay::Num(first_ord::NumType::Int),
            ),
        ]);
        let overlay = Overlay::Tuple(vec![Overlay::Bool, Overlay::Array(ModeParam(1))]);
        let items: Vec<_> = ty.iter_stack().zip_annot(overlay.iter()).collect();
        assert_eq!(
            items,
            vec![
                Item::Tuple(2),
                Item::Bool,
                Item::Array(((&ModeParam(0), &LtParam(0)), &ModeParam(1))),
            ]
        );
    }
}
