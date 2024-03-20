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
    // Represents unordered "events", e.g. the arms of a match.
    // Always contains at least one `Some`.
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node2<A, B, C, D> {
    Outer(Node<A, B>),
    Inner(Node<C, D>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node<A, B> {
    Bool,
    Num(first_ord::NumType),
    Tuple(usize),
    Variants(Count<first_ord::VariantId>),
    Custom(first_ord::CustomTypeId, A),
    Array(B),
    HoleArray(B),
    Boxed(B),
}

pub type TypeLike<'a, M, L> =
    Node2<(&'a IdVec<ModeParam, M>, &'a IdVec<LtParam, L>), (&'a M, &'a L), (), &'a M>;

pub trait CollectType<M, L> {
    fn collect_type(self) -> Type<M, L>;
}

impl<'a, I, M, L> CollectType<M, L> for I
where
    I: Iterator<Item = TypeLike<'a, M, L>>,
    M: 'a + Clone,
    L: 'a + Clone,
{
    fn collect_type(self) -> Type<M, L> {
        let items: Vec<_> = self.collect();
        collect_outer(&items, 0).0
    }
}

pub type OverlayLike<'a, M> = Node<(), &'a M>;

pub trait CollectOverlay<M> {
    fn collect_overlay(self) -> Overlay<M>;
}

impl<'a, I, M> CollectOverlay<M> for I
where
    I: Iterator<Item = OverlayLike<'a, M>>,
    M: 'a + Clone,
{
    fn collect_overlay(self) -> Overlay<M> {
        let items: Vec<_> = self.collect();
        collect_nodes(&items, 0).0
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
fn collect_outer<M, L>(items: &[TypeLike<'_, M, L>], i: usize) -> (Type<M, L>, usize)
where
    M: Clone,
    L: Clone,
{
    match items[i].clone() {
        Node2::Outer(Node::Bool) => (Type::Bool, i + 1),
        Node2::Outer(Node::Num(t)) => (Type::Num(t), i + 1),
        Node2::Outer(Node::Tuple(n)) => {
            let (tys, j) = collect_many(n, i + 1, |i| collect_outer(items, i));
            (Type::Tuple(tys), j)
        }
        Node2::Outer(Node::Variants(n)) => {
            let (tys, j) = collect_many(n.to_value(), i + 1, |i| collect_outer(items, i));
            (Type::Variants(IdVec::from_vec(tys)), j)
        }
        Node2::Outer(Node::Custom(id, (modes, lts))) => {
            (Type::Custom(id, modes.clone(), lts.clone()), i + 1)
        }
        Node2::Outer(Node::Array((mode, lt))) => {
            let (overlay, j) = collect_inner(items, i + 1);
            let (ty, k) = collect_outer(items, j);
            let res = Type::Array(mode.clone(), lt.clone(), Box::new(ty), overlay);
            (res, k)
        }
        Node2::Outer(Node::HoleArray((mode, lt))) => {
            let (overlay, j) = collect_inner(items, i + 1);
            let (ty, k) = collect_outer(items, j);
            let res = Type::Array(mode.clone(), lt.clone(), Box::new(ty), overlay);
            (res, k)
        }
        Node2::Outer(Node::Boxed((mode, lt))) => {
            let (overlay, j) = collect_inner(items, i + 1);
            let (ty, k) = collect_outer(items, j);
            let res = Type::Array(mode.clone(), lt.clone(), Box::new(ty), overlay);
            (res, k)
        }
        Node2::Inner(_) => panic!("expected outer node"),
    }
}

fn collect_inner<M, L>(items: &[TypeLike<'_, M, L>], i: usize) -> (Overlay<M>, usize)
where
    M: Clone,
{
    match items[i].clone() {
        Node2::Inner(Node::Bool) => (Overlay::Bool, i + 1),
        Node2::Inner(Node::Num(t)) => (Overlay::Num(t), i + 1),
        Node2::Inner(Node::Tuple(n)) => {
            let (tys, j) = collect_many(n, i + 1, |j| collect_inner(items, j));
            (Overlay::Tuple(tys), j)
        }
        Node2::Inner(Node::Variants(n)) => {
            let (tys, j) = collect_many(n.to_value(), i + 1, |j| collect_inner(items, j));
            (Overlay::Variants(IdVec::from_vec(tys)), j)
        }
        Node2::Inner(Node::Custom(id, ())) => (Overlay::Custom(id), i + 1),
        Node2::Inner(Node::Array(mode)) => (Overlay::Array(mode.clone()), i + 1),
        Node2::Inner(Node::HoleArray(mode)) => (Overlay::HoleArray(mode.clone()), i + 1),
        Node2::Inner(Node::Boxed(mode)) => (Overlay::Boxed(mode.clone()), i + 1),
        Node2::Outer(_) => panic!("expected inner node"),
    }
}

fn collect_nodes<M>(items: &[OverlayLike<'_, M>], i: usize) -> (Overlay<M>, usize)
where
    M: Clone,
{
    match items[i].clone() {
        Node::Bool => (Overlay::Bool, i + 1),
        Node::Num(t) => (Overlay::Num(t), i + 1),
        Node::Tuple(n) => {
            let (tys, j) = collect_many(n, i + 1, |j| collect_nodes(items, j));
            (Overlay::Tuple(tys), j)
        }
        Node::Variants(n) => {
            let (tys, j) = collect_many(n.to_value(), i + 1, |j| collect_nodes(items, j));
            (Overlay::Variants(IdVec::from_vec(tys)), j)
        }
        Node::Custom(id, ()) => (Overlay::Custom(id), i + 1),
        Node::Array(mode) => (Overlay::Array(mode.clone()), i + 1),
        Node::HoleArray(mode) => (Overlay::HoleArray(mode.clone()), i + 1),
        Node::Boxed(mode) => (Overlay::Boxed(mode.clone()), i + 1),
    }
}

pub struct Zip2<I, J> {
    iter1: I,
    iter2: J,
}

pub fn zip2<A, B, C, D, E, F, G, H, I, J>(iter1: I, iter2: J) -> Zip2<I, J>
where
    // Enforcing this constraint here improves error messages. Otherwise, the compiler will not give
    // us an error until we try to iterate over our `Zip2`.
    I: Iterator<Item = Node2<A, B, C, D>>,
    J: Iterator<Item = Node2<E, F, G, H>>,
{
    Zip2 { iter1, iter2 }
}

impl<A, B, C, D, E, F, G, H, I, J> Iterator for Zip2<I, J>
where
    I: Iterator<Item = Node2<A, B, C, D>>,
    J: Iterator<Item = Node2<E, F, G, H>>,
{
    type Item = Node2<(A, E), (B, F), (C, G), (D, H)>;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.iter1.next(), self.iter2.next()) {
            (Some(Node2::Outer(n1)), Some(Node2::Outer(n2))) => {
                Some(Node2::Outer(zip_nodes(n1, n2)))
            }
            (Some(Node2::Inner(n1)), Some(Node2::Inner(n2))) => {
                Some(Node2::Inner(zip_nodes(n1, n2)))
            }
            (None, None) => None,
            (Some(Node2::Outer(_)), Some(Node2::Inner(_)))
            | (Some(Node2::Inner(_)), Some(Node2::Outer(_)))
            | (None, Some(_))
            | (Some(_), None) => panic!("incompatible types"),
        }
    }
}

pub struct Zip<I, J> {
    iter1: I,
    iter2: J,
}

pub fn zip<A, B, C, D, I, J>(iter1: I, iter2: J) -> Zip<I, J>
where
    // Enforcing this constraint here improves error messages. Otherwise, the compiler will not give
    // us an error until we try to iterate over our `Zip`.
    I: Iterator<Item = Node<A, B>>,
    J: Iterator<Item = Node<C, D>>,
{
    Zip { iter1, iter2 }
}

impl<A, B, C, D, E, F> Iterator for Zip<A, B>
where
    A: Iterator<Item = Node<C, D>>,
    B: Iterator<Item = Node<E, F>>,
{
    type Item = Node<(C, E), (D, F)>;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.iter1.next(), self.iter2.next()) {
            (Some(item1), Some(item2)) => Some(zip_nodes(item1, item2)),
            (None, None) => None,
            (None, Some(_)) | (Some(_), None) => panic!("incompatible types"),
        }
    }
}

fn zip_nodes<A, B, C, D>(n1: Node<A, B>, n2: Node<C, D>) -> Node<(A, C), (B, D)> {
    match (n1, n2) {
        (Node::Bool, Node::Bool) => Node::Bool,
        (Node::Num(t1), Node::Num(t2)) if t1 == t2 => Node::Num(t1),
        (Node::Tuple(n1), Node::Tuple(n2)) if n1 == n2 => Node::Tuple(n1),
        (Node::Variants(n1), Node::Variants(n2)) if n1 == n2 => Node::Variants(n1),
        (Node::Custom(id1, v1), Node::Custom(id2, v2)) if id1 == id2 => Node::Custom(id1, (v1, v2)),
        (Node::Array(v1), Node::Array(v2)) => Node::Array((v1, v2)),
        (Node::HoleArray(v1), Node::HoleArray(v2)) => Node::HoleArray((v1, v2)),
        (Node::Boxed(v1), Node::Boxed(v2)) => Node::Boxed((v1, v2)),
        _ => panic!("incompatible types"),
    }
}

pub fn map2<I, A1, A2, B1, B2, C1, C2, D1, D2, F1, F2, F3, F4>(
    iter: I,
    mut f1: F1,
    mut f2: F2,
    mut f3: F3,
    mut f4: F4,
) -> impl Iterator<Item = Node2<A2, B2, C2, D2>>
where
    I: Iterator<Item = Node2<A1, B1, C1, D1>>,
    F1: FnMut(A1) -> A2,
    F2: FnMut(B1) -> B2,
    F3: FnMut(C1) -> C2,
    F4: FnMut(D1) -> D2,
{
    iter.map(move |item| match item {
        Node2::Outer(Node::Bool) => Node2::Outer(Node::Bool),
        Node2::Outer(Node::Num(t)) => Node2::Outer(Node::Num(t)),
        Node2::Outer(Node::Tuple(n)) => Node2::Outer(Node::Tuple(n)),
        Node2::Outer(Node::Variants(n)) => Node2::Outer(Node::Variants(n)),
        Node2::Outer(Node::Custom(id, v)) => Node2::Outer(Node::Custom(id, f1(v))),
        Node2::Outer(Node::Array(v)) => Node2::Outer(Node::Array(f2(v))),
        Node2::Outer(Node::HoleArray(v)) => Node2::Outer(Node::HoleArray(f2(v))),
        Node2::Outer(Node::Boxed(v)) => Node2::Outer(Node::Boxed(f2(v))),
        Node2::Inner(Node::Bool) => Node2::Inner(Node::Bool),
        Node2::Inner(Node::Num(t)) => Node2::Inner(Node::Num(t)),
        Node2::Inner(Node::Tuple(n)) => Node2::Inner(Node::Tuple(n)),
        Node2::Inner(Node::Variants(n)) => Node2::Inner(Node::Variants(n)),
        Node2::Inner(Node::Custom(id, v)) => Node2::Inner(Node::Custom(id, f3(v))),
        Node2::Inner(Node::Array(v)) => Node2::Inner(Node::Array(f4(v))),
        Node2::Inner(Node::HoleArray(v)) => Node2::Inner(Node::HoleArray(f4(v))),
        Node2::Inner(Node::Boxed(v)) => Node2::Inner(Node::Boxed(f4(v))),
    })
}

pub fn map<I, A1, A2, B1, B2, F1, F2>(
    iter: I,
    mut f1: F1,
    mut f2: F2,
) -> impl Iterator<Item = Node<A2, B2>>
where
    I: Iterator<Item = Node<A1, B1>>,
    F1: FnMut(A1) -> A2,
    F2: FnMut(B1) -> B2,
{
    iter.map(move |item| match item {
        Node::Bool => Node::Bool,
        Node::Num(t) => Node::Num(t),
        Node::Tuple(n) => Node::Tuple(n),
        Node::Variants(n) => Node::Variants(n),
        Node::Custom(id, v) => Node::Custom(id, f1(v)),
        Node::Array(v) => Node::Array(f2(v)),
        Node::HoleArray(v) => Node::HoleArray(f2(v)),
        Node::Boxed(v) => Node::Boxed(f2(v)),
    })
}

// Must produce nodes in the order that `collect_outer` etc. expect.
#[derive(Clone, Debug)]
pub struct TypeIter<'a, M, L> {
    stack: Vec<TypeFrame<'a, M, L>>,
}

#[derive(Clone, Debug)]
pub struct TypeStackIter<'a, M, L> {
    stack: Vec<TypeStackFrame<'a, M, L>>,
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

    // Inner nodesj
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
pub enum TypeStackFrame<'a, M, L> {
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

    pub fn iter_stack(&self) -> TypeStackIter<M, L> {
        TypeStackIter::new(self)
    }
}

impl<'a, M, L> Iterator for TypeIter<'a, M, L> {
    type Item = TypeLike<'a, M, L>;

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

pub type TypeStackLike<'a, M, L> =
    Node<(&'a IdVec<ModeParam, M>, &'a IdVec<LtParam, L>), (&'a M, &'a L)>;

impl<'a, M, L> Iterator for TypeStackIter<'a, M, L> {
    type Item = TypeStackLike<'a, M, L>;

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
    type Item = OverlayLike<'a, M>;

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

impl<'a, M, L> TypeStackFrame<'a, M, L> {
    fn from_type(ty: &'a Type<M, L>) -> Self {
        match ty {
            Type::Bool => TypeStackFrame::Bool,
            Type::Num(t) => TypeStackFrame::Num(*t),
            Type::Tuple(tys) => TypeStackFrame::Tuple(tys),
            Type::Variants(tys) => TypeStackFrame::Variants(tys),
            Type::Custom(id, modes, lts) => TypeStackFrame::Custom(*id, modes, lts),
            Type::Array(m, lt, _ty, _overlay) => TypeStackFrame::Array(m, lt),
            Type::HoleArray(m, lt, _ty, _overlay) => TypeStackFrame::HoleArray(m, lt),
            Type::Boxed(m, lt, _ty, _overlay) => TypeStackFrame::Boxed(m, lt),
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

    fn step(&mut self) -> StepResult<TypeLike<'a, M, L>> {
        let Some(frame) = self.stack.pop() else {
            return StepResult::Done;
        };
        match frame {
            TypeFrame::Bool => StepResult::Yield(Node2::Outer(Node::Bool)),
            TypeFrame::Num(t) => StepResult::Yield(Node2::Outer(Node::Num(t))),
            TypeFrame::Tuple(tys) => {
                if !tys.is_empty() {
                    self.stack.push(TypeFrame::TupleItem(0, tys));
                }
                StepResult::Yield(Node2::Outer(Node::Tuple(tys.len())))
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
                StepResult::Yield(Node2::Outer(Node::Variants(tys.count())))
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
                StepResult::Yield(Node2::Outer(Node::Custom(id, (modes, lts))))
            }
            TypeFrame::Array(m, lt, ty, overlay) => {
                self.stack.push(TypeFrame::from_type(ty));
                self.stack.push(TypeFrame::from_overlay(overlay));
                StepResult::Yield(Node2::Outer(Node::Array((m, lt))))
            }
            TypeFrame::HoleArray(m, lt, ty, overlay) => {
                self.stack.push(TypeFrame::from_type(ty));
                self.stack.push(TypeFrame::from_overlay(overlay));
                StepResult::Yield(Node2::Outer(Node::HoleArray((m, lt))))
            }
            TypeFrame::Boxed(m, lt, ty, overlay) => {
                self.stack.push(TypeFrame::from_type(ty));
                self.stack.push(TypeFrame::from_overlay(overlay));
                StepResult::Yield(Node2::Outer(Node::Boxed((m, lt))))
            }

            TypeFrame::OverlayBool => StepResult::Yield(Node2::Inner(Node::Bool)),
            TypeFrame::OverlayNum(t) => StepResult::Yield(Node2::Inner(Node::Num(t))),
            TypeFrame::OverlayTuple(tys) => {
                if !tys.is_empty() {
                    self.stack.push(TypeFrame::OverlayTupleItem(0, tys));
                }
                StepResult::Yield(Node2::Inner(Node::Tuple(tys.len())))
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
                StepResult::Yield(Node2::Inner(Node::Variants(tys.count())))
            }
            TypeFrame::OverlayVariant(i, tys) => {
                if i + 1 < tys.len() {
                    self.stack.push(TypeFrame::OverlayVariant(i + 1, tys));
                }
                self.stack
                    .push(TypeFrame::from_overlay(&tys[first_ord::VariantId(i)]));
                StepResult::Step
            }
            TypeFrame::OverlayCustom(id) => StepResult::Yield(Node2::Inner(Node::Custom(id, ()))),
            TypeFrame::OverlayArray(m) => StepResult::Yield(Node2::Inner(Node::Array(m))),
            TypeFrame::OverlayHoleArray(m) => StepResult::Yield(Node2::Inner(Node::HoleArray(m))),
            TypeFrame::OverlayBoxed(m) => StepResult::Yield(Node2::Inner(Node::Boxed(m))),
        }
    }
}

impl<'a, M, L> TypeStackIter<'a, M, L> {
    pub fn new(ty: &'a Type<M, L>) -> Self {
        Self {
            stack: vec![TypeStackFrame::from_type(ty)],
        }
    }

    fn step(&mut self) -> StepResult<TypeStackLike<'a, M, L>> {
        let Some(frame) = self.stack.pop() else {
            return StepResult::Done;
        };
        match frame {
            TypeStackFrame::Bool => StepResult::Yield(Node::Bool),
            TypeStackFrame::Num(t) => StepResult::Yield(Node::Num(t)),
            TypeStackFrame::Tuple(tys) => {
                if !tys.is_empty() {
                    self.stack.push(TypeStackFrame::TupleItem(0, tys));
                }
                StepResult::Yield(Node::Tuple(tys.len()))
            }
            TypeStackFrame::TupleItem(i, tys) => {
                if i + 1 < tys.len() {
                    self.stack.push(TypeStackFrame::TupleItem(i + 1, tys));
                }
                self.stack.push(TypeStackFrame::from_type(&tys[i]));
                StepResult::Step
            }
            TypeStackFrame::Variants(tys) => {
                if !tys.is_empty() {
                    self.stack.push(TypeStackFrame::Variant(0, tys));
                }
                StepResult::Yield(Node::Variants(tys.count()))
            }
            TypeStackFrame::Variant(i, tys) => {
                if i + 1 < tys.len() {
                    self.stack.push(TypeStackFrame::Variant(i + 1, tys));
                }
                self.stack
                    .push(TypeStackFrame::from_type(&tys[first_ord::VariantId(i)]));
                StepResult::Step
            }
            TypeStackFrame::Custom(id, modes, lts) => {
                StepResult::Yield(Node::Custom(id, (modes, lts)))
            }
            TypeStackFrame::Array(m, lt) => StepResult::Yield(Node::Array((m, lt))),
            TypeStackFrame::HoleArray(m, lt) => StepResult::Yield(Node::HoleArray((m, lt))),
            TypeStackFrame::Boxed(m, lt) => StepResult::Yield(Node::Boxed((m, lt))),
        }
    }
}

impl<'a, M> OverlayIter<'a, M> {
    pub fn new(overlay: &'a Overlay<M>) -> Self {
        Self {
            stack: vec![OverlayFrame::new(overlay)],
        }
    }

    fn step(&mut self) -> StepResult<OverlayLike<'a, M>> {
        let Some(frame) = self.stack.pop() else {
            return StepResult::Done;
        };
        match frame {
            OverlayFrame::Bool => StepResult::Yield(Node::Bool),
            OverlayFrame::Num(t) => StepResult::Yield(Node::Num(t)),
            OverlayFrame::Tuple(tys) => {
                if !tys.is_empty() {
                    self.stack.push(OverlayFrame::TupleItem(0, tys));
                }
                StepResult::Yield(Node::Tuple(tys.len()))
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
                StepResult::Yield(Node::Variants(tys.count()))
            }
            OverlayFrame::Variant(i, tys) => {
                if i + 1 < tys.len() {
                    self.stack.push(OverlayFrame::Variant(i + 1, tys));
                }
                self.stack
                    .push(OverlayFrame::new(&tys[first_ord::VariantId(i)]));
                StepResult::Step
            }
            OverlayFrame::Custom(id) => StepResult::Yield(Node::Custom(id, ())),
            OverlayFrame::Array(m) => StepResult::Yield(Node::Array(m)),
            OverlayFrame::HoleArray(m) => StepResult::Yield(Node::HoleArray(m)),
            OverlayFrame::Boxed(m) => StepResult::Yield(Node::Boxed(m)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_round_trip() {
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
        let items: Vec<_> = zip2(ty1.iter(), ty2.iter()).collect();
        assert_eq!(
            items,
            vec![
                Node2::Outer(Node::Tuple(2)),
                Node2::Outer(Node::Bool),
                Node2::Outer(Node::Array((
                    (&ModeParam(0), &LtParam(0)),
                    (&ModeParam(1), &LtParam(1))
                ))),
                Node2::Inner(Node::Num(first_ord::NumType::Int)),
                Node2::Outer(Node::Num(first_ord::NumType::Int)),
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
        let _: Vec<_> = zip2(ty1.iter(), ty2.iter()).collect();
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
        let items: Vec<_> = zip(ty.iter_stack(), overlay.iter()).collect();
        assert_eq!(
            items,
            vec![
                Node::Tuple(2),
                Node::Bool,
                Node::Array(((&ModeParam(0), &LtParam(0)), &ModeParam(1))),
            ]
        );
    }
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
