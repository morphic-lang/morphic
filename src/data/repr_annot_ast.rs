use crate::annot_aliases;
pub use crate::data::first_order_ast::{
    self, BinOp, Comparison, CustomFuncId, CustomTypeId, NumType, VariantId,
};
use crate::data::purity::Purity;
use im_rc::Vector;
use std::collections::BTreeSet;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<ReprVar = Solution> {
    Bool,
    Num(NumType),
    Array(Box<Type<ReprVar>>, ReprVar),
    HoleArray(Box<Type<ReprVar>>, ReprVar),
    Tuple(Vec<Type<ReprVar>>),
    Custom(
        CustomTypeId,
        Vec<ReprVar>, // length must be `num_params` from the identified custom type
    ),
}

impl<T> From<&Type<T>> for first_order_ast::Type {
    fn from(t: &Type<T>) -> Self {
        use first_order_ast::Type as FOType;
        match t {
            Type::Bool => FOType::Bool,
            Type::Num(num_type) => FOType::Num(*num_type),
            Type::Array(t, _) => FOType::Array(Box::new(From::from(&**t))),
            Type::HoleArray(t, _) => FOType::HoleArray(Box::new(From::from(&**t))),
            Type::Tuple(ts) => FOType::Tuple(ts.iter().map(From::from).collect()),
            Type::Custom(id, _) => FOType::Custom(*id),
        }
    }
}

impl<T> From<Type<T>> for first_order_ast::Type {
    fn from(t: Type<T>) -> Self {
        (&t).into()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeDef<ReprVar = Solution> {
    pub num_params: usize,
    pub variants: Vec<Option<Type<ReprVar>>>,
}

// 0 is the function's argument. Every Expr in a Block has a LocalId.
id_type!(pub LocalId);

// Terms do not have to be assigned to temps before being used.
// Thus they can have no operational side-effects.
#[derive(Clone, Debug)]
pub enum Term {
    Access(
        LocalId,
        annot_aliases::FieldPath, // actual accessed path
        annot_aliases::FieldPath, // type-folded (pruned) path for alias analysis
    ),
    BoolLit(bool),
    IntLit(i64),
    ByteLit(u8),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub enum IOOp {
    // Input evaluates to an array of bytes
    Input(Solution),
    // Output takes an array of bytes
    Output(Term),
}

#[derive(Clone, Debug)]
pub enum ArithOp {
    Op(NumType, BinOp, Term, Term),
    Cmp(NumType, Comparison, Term, Term),
    Negate(NumType, Term),
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    // Construct(..) effectively contains an array type (i.e. Type::Array variant)
    Construct(Box<Type<Solution>>, Solution, Vec<Term>),
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

// `Pattern`s describe a pattern for the sake of branching, without binding variables
#[derive(Clone, Debug)]
pub enum Pattern {
    Any,
    Tuple(Vec<Pattern>),
    Ctor(CustomTypeId, VariantId, Option<Box<Pattern>>),
    BoolConst(bool),
    IntConst(i64),
    ByteConst(u8),
    FloatConst(f64),
}

id_type!(pub RepParamId);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Solution {
    Shared,
    Unique,
    Var(RepParamId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SharingPlace {
    Arg,
    Ret,
}

#[derive(Clone, Debug, Eq, PartialOrd, Ord)]
pub enum Constraint {
    // FieldPaths are relative to the argument
    SharedIfOutlivesCall(SharingPlace, annot_aliases::FieldPath),
    SharedIfAliased(annot_aliases::FieldPath, annot_aliases::FieldPath),
    Shared,
}

impl PartialEq for Constraint {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Constraint::SharedIfOutlivesCall(place, path),
                Constraint::SharedIfOutlivesCall(other_place, other_path),
            ) => place == other_place && path == other_path,
            (
                Constraint::SharedIfAliased(path_a, path_b),
                Constraint::SharedIfAliased(other_path_a, other_path_b),
            ) => {
                use std::cmp::{max, min};
                min(path_a, path_b) == min(other_path_a, other_path_b)
                    && max(path_a, path_b) == max(other_path_a, other_path_b)
            }
            (Constraint::Shared, Constraint::Shared) => true,
            _ => false,
        }
    }
}

// ExprId does not index into any field of `Block`. ExprId indexes into
// maps created in annot_reprs::aliasing
id_type!(pub ExprId);

impl ExprId {
    pub const ARG: ExprId = ExprId(0);
    pub fn next(&self) -> ExprId {
        ExprId(self.0 + 1)
    }
}

#[derive(Clone, Debug)]
pub enum Expr {
    Term(Term),
    ArithOp(ArithOp),
    ArrayOp(ArrayOp),
    IOOp(IOOp),
    Ctor(
        CustomTypeId,
        Vec<Solution>, // repr params for the custom type
        VariantId,
        Option<Term>, // constructor arg
    ),
    Tuple(Vec<Term>),
    Local(LocalId),
    Call(
        Purity,
        CustomFuncId,
        Term,
        Vec<Solution>, // repr var arguments to callee
    ),
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
    pub params: Vec<BTreeSet<Constraint>>,
    pub arg_type: Type,
    pub body: Block,
    pub unique_info: Rc<annot_aliases::UniqueInfo>,
    pub ret_aliasing: Rc<BTreeSet<(annot_aliases::FieldPath, annot_aliases::FieldPath)>>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: Vec<TypeDef<RepParamId>>,
    pub funcs: Vec<FuncDef>,
    pub main: CustomFuncId,
}
