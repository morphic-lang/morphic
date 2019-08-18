use crate::annot_aliases::{FieldPath, UniqueInfo};
pub use crate::data::first_order_ast::{self, BinOp, Comparison, NumType, VariantId};
use crate::data::purity::Purity;
pub use crate::data::repr_annot_ast::{self, ArithOp, ExprId, LocalId, Term};
use im_rc::Vector;
use std::collections::BTreeSet;
use std::rc::Rc;

id_type!(pub CustomFuncId);

id_type!(pub CustomTypeId);

#[derive(Clone, Copy, Debug)]
pub enum Primitive {
    Bool,
    Num(NumType),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PrimVal {
    Bool(bool),
    Int(i64),
    Byte(u8),
    Float(f64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Repr {
    Shared,
    Unique,
}

#[derive(Clone, Debug)]
pub enum Type {
    Prim(Primitive),
    Array(Box<Type>, Repr),
    HoleArray(Box<Type>, Repr),
    Tuple(Vec<Type>),
    Custom(CustomTypeId),
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub variants: Vec<Option<Type>>,
}

#[derive(Clone, Debug)]
pub enum IOOp {
    Input(Repr),
    Output(Term),
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Construct(Box<Type>, Repr, Vec<Term>),
    Item(
        Term, // Array
        Term, // Index
    ), // Returns tuple of (item, (potentially wrapped) hole array)
    Len(Term),
    Push(
        Term, // Array
        Term, // Item
    ), // Returns new array
    Pop(Term), // Returns tuple of (array, item)
    Replace(
        Term, // Hole array
        Term, // Item
    ), // Returns new array
}

#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    Any,
    Tuple(Vec<Pattern>),
    Ctor(CustomTypeId, VariantId, Option<Box<Pattern>>),
    Const(PrimVal),
}

#[derive(Clone, Debug)]
pub enum Expr {
    Term(Term),
    ArithOp(ArithOp),
    ArrayOp(ArrayOp),
    IOOp(IOOp),
    Ctor(CustomTypeId, VariantId, Option<Term>),
    Tuple(Vec<Term>),
    Local(LocalId),
    Call(Purity, CustomFuncId, Term),
    Match(LocalId, Vec<(Pattern, Block)>, Box<Type>),
}

#[derive(Clone, Debug)]
pub struct Block {
    pub initial_idx: usize, // offset of `LocalId`s (nothing to do with `ExprId`)
    // `exprs` and `types` are indexed by LocalId *offset by `initial_idx`*
    pub exprs: Vec<Expr>,
    pub types: Vec<Type>,
    pub expr_ids: Vector<ExprId>, // indexed by LocalId
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub arg_type: Type,
    pub body: Block,
    pub unique_info: Rc<UniqueInfo>,
    pub ret_aliasing: Rc<BTreeSet<(FieldPath, FieldPath)>>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: Vec<TypeDef>,
    pub funcs: Vec<FuncDef>,
    pub main: CustomFuncId,
}
