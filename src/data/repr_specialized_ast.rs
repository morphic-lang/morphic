use crate::annot_aliases::{FieldPath, UniqueInfo};
pub use crate::data::first_order_ast::{self, BinOp, Comparison, VariantId};
use crate::data::purity::Purity;
pub use crate::data::repr_annot_ast::{self, ExprId, LocalId, Term};
use im_rc::Vector;
use std::collections::BTreeSet;
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CustomFuncId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CustomTypeId(pub usize);

#[derive(Clone, Copy, Debug)]
pub enum NumType {
    Int,
    Byte,
    Float,
}

#[derive(Clone, Copy, Debug)]
pub enum Primitive {
    Bool,
    Num(NumType),
}

#[derive(Clone, Copy, Debug)]
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
pub enum ArithOp {
    Op(NumType, BinOp, Term, Term),
    Cmp(NumType, Comparison, Term, Term),
    Negate(NumType, Term),
}
impl From<crate::data::repr_annot_ast::ArithOp> for ArithOp {
    fn from(arith_op: crate::data::repr_annot_ast::ArithOp) -> Self {
        use crate::data::repr_annot_ast::ArithOp as A;
        match arith_op {
            A::IntOp(bin_op, left, right) => ArithOp::Op(NumType::Int, bin_op, left, right),
            A::ByteOp(bin_op, left, right) => ArithOp::Op(NumType::Byte, bin_op, left, right),
            A::FloatOp(bin_op, left, right) => ArithOp::Op(NumType::Float, bin_op, left, right),
            A::IntCmp(cmp, left, right) => ArithOp::Cmp(NumType::Int, cmp, left, right),
            A::ByteCmp(cmp, left, right) => ArithOp::Cmp(NumType::Byte, cmp, left, right),
            A::FloatCmp(cmp, left, right) => ArithOp::Cmp(NumType::Float, cmp, left, right),
            A::NegateInt(t) => ArithOp::Negate(NumType::Int, t),
            A::NegateByte(t) => ArithOp::Negate(NumType::Byte, t),
            A::NegateFloat(t) => ArithOp::Negate(NumType::Float, t),
        }
    }
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

#[derive(Clone, Debug)]
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
