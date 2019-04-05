use crate::annot_aliases;
pub use crate::data::first_order_ast::{self, BinOp, CustomFuncId, CustomTypeId, VariantId};
use crate::data::purity::Purity;
use im_rc::{vector, Vector};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RepParamId(pub usize);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<ReprVar = RepParamId> {
    Bool,
    Int,
    Float,
    Text,
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
            Type::Int => FOType::Int,
            Type::Float => FOType::Float,
            Type::Text => FOType::Text,
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Constraint {
    // FieldPaths are relative to the argument
    SharedIfOutlivesCall(annot_aliases::FieldPath),
    SharedIfAliased(annot_aliases::FieldPath, annot_aliases::FieldPath), // FIXME: NameVar
    Shared,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeDef<ReprVar = RepParamId> {
    pub num_params: usize,
    pub variants: Vec<Option<Type<ReprVar>>>,
}

// 0 is the function's argument. Every Expr in a Block has a LocalId.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalId(pub usize);

// Terms do not have to be assigned to temps before being used.
// Thus they can have no operational side-effects.
#[derive(Clone, Debug)]
pub enum Term {
    Access(
        LocalId,
        annot_aliases::FieldPath,         // actual accessed path
        Option<annot_aliases::FieldPath>, // type-folded (pruned) path for alias analysis
    ),
    BoolLit(bool),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub enum ArithOp {
    IntOp(BinOp, Term, Term),
    FloatOp(BinOp, Term, Term),
    IntCmp(std::cmp::Ordering, Term, Term),
    FloatCmp(std::cmp::Ordering, Term, Term),
    NegateInt(Term),
    NegateFloat(Term),
}

#[derive(Clone, Debug)]
pub enum ArrayOp<ReprVar> {
    // Construct(..) effectively contains an array type (i.e. Type::Array variant)
    Construct(Box<Type<ReprVar>>, ReprVar, Vec<Term>),
    Item(
        Term,                              // Array
        Term,                              // Index
        Option<(CustomTypeId, VariantId)>, // Constructor to wrap returned HoleArray in
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

// Patterns which describe for the sake of branching, without binding variables
#[derive(Clone, Debug)]
pub enum Pattern {
    Any,
    Tuple(Vec<Pattern>),
    Ctor(CustomTypeId, VariantId, Option<Box<Pattern>>),
    BoolConst(bool),
    IntConst(i64),
    FloatConst(f64),
    TextConst(String),
}

#[derive(Clone, Debug)]
pub enum ReprParams<ReprVar> {
    Determined(Vec<ReprVar>),
    Pending, // for calls to the same SCC
}

#[derive(Clone, Debug)]
pub enum Expr<ReprVar, ExprType> {
    Term(Term),
    ArithOp(ArithOp),
    ArrayOp(ArrayOp<ReprVar>),
    Ctor(CustomTypeId, VariantId, Option<Term>),
    Tuple(Vec<Term>),
    Local(LocalId),
    Call(Purity, CustomFuncId, Term, Option<ReprParams<ReprVar>>),
    Match(
        LocalId,
        Vec<(Pattern, Block<ReprVar, ExprType>)>,
        Box<Type<ReprVar>>,
    ),
}

// ExprId does not index into any field of `Block`. ExprId indexes into
// maps created in annot_reprs::aliasing
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExprId(pub usize);
impl ExprId {
    pub const ARG: ExprId = ExprId(0);
    pub fn next(&self) -> ExprId {
        ExprId(self.0 + 1)
    }
}

#[derive(Clone, Debug)]
pub struct Block<ReprVar, ExprType> {
    pub initial_idx: usize, // for LocalId, not ExprId
    // `terms` and `types` are indexed by LocalId *offset by `initial_idx`
    pub terms: Vec<Expr<ReprVar, ExprType>>,
    pub types: Vec<ExprType>,
    pub expr_ids: Vector<ExprId>, // indexed by LocalId
}

pub type TypedExpr<ReprVar> = Expr<ReprVar, Type<ReprVar>>;
pub type TypedBlock<ReprVar> = Block<ReprVar, Type<ReprVar>>;

// TODO: move out of data module?
impl<T, E> Block<T, E> {
    pub fn function_body() -> Block<T, E> {
        Block {
            // LocalId(0) is arg, so first term index is 1
            initial_idx: 1,
            terms: vec![],
            types: vec![],
            expr_ids: vector![ExprId::ARG],
        }
    }

    pub fn branch_from(block: &Block<T, E>) -> Block<T, E> {
        Block {
            initial_idx: block.initial_idx + block.terms.len(),
            terms: vec![],
            types: vec![],
            expr_ids: block.expr_ids.clone(),
        }
    }

    // Adds an expression to the block and returns a Term referring to that expression
    pub fn add(&mut self, e: Expr<T, E>) -> Term {
        Term::Access(self.add_local(e), vector![], None)
    }

    pub fn add_local(&mut self, e: Expr<T, E>) -> LocalId {
        let idx = self.initial_idx + self.terms.len();
        self.terms.push(e);
        LocalId(idx)
    }

    pub fn expr_id_of(&self, l: LocalId) -> ExprId {
        self.expr_ids[l.0]
    }
}

#[derive(Clone, Debug)]
pub struct FuncDef<ReprVar, ExprType> {
    pub purity: Purity,
    pub arg_type: Type<ReprVar>,
    pub ret_type: Type<ReprVar>,
    pub constraints: Vec<Vec<Constraint>>,
    pub body: Block<ReprVar, ExprType>,
}

type TypedFuncDef<ReprVar> = FuncDef<ReprVar, Type<ReprVar>>;

#[derive(Clone, Debug)]
pub struct Program<ReprVar> {
    pub custom_types: Vec<TypeDef<ReprVar>>,
    pub funcs: Vec<FuncDef<ReprVar, ()>>,
    pub main: CustomFuncId,
}
