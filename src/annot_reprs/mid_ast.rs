pub use super::out_ast::{
    Comparison, Constraint, ExprId, LocalId, Pattern, RepParamId, Type, TypeDef,
};
use crate::annot_aliases;
pub use crate::data::first_order_ast::{self, BinOp, CustomFuncId, CustomTypeId, VariantId};
use crate::data::purity::Purity;
use crate::util::constraint_graph::SolverVarId;
use im_rc::{vector, Vector};

#[derive(Clone, Debug)]
pub enum IOOp {
    // Input evaluates to an array of bytes
    Input(SolverVarId),
    // Output takes an array of bytes
    Output(Term),
}

#[derive(Clone, Debug)]
pub enum ArithOp {
    IntOp(BinOp, Term, Term),
    FloatOp(BinOp, Term, Term),
    ByteOp(BinOp, Term, Term),
    IntCmp(Comparison, Term, Term),
    FloatCmp(Comparison, Term, Term),
    ByteCmp(Comparison, Term, Term),
    NegateInt(Term),
    NegateFloat(Term),
    NegateByte(Term),
}

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
    ByteLit(u8),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    // Construct(..) effectively contains an array type (i.e. Type::Array variant)
    Construct(Box<Type<SolverVarId>>, SolverVarId, Vec<Term>),
    Item(
        Term, // Array
        Term, // Index
    ), // Returns tuple of (item, hole array)
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
pub enum ReprParams<ReprVar> {
    Determined(Vec<ReprVar>),
    Pending, // for calls to the same SCC
}

#[derive(Clone, Debug)]
pub enum Expr<ExprType> {
    Term(Term),
    ArithOp(ArithOp),
    ArrayOp(ArrayOp),
    IOOp(IOOp),
    Ctor(CustomTypeId, VariantId, Option<Term>),
    Tuple(Vec<Term>),
    Local(LocalId),
    Call(Purity, CustomFuncId, Term, Option<ReprParams<SolverVarId>>),
    Match(
        LocalId,
        Vec<(Pattern, Block<ExprType>)>,
        Box<Type<SolverVarId>>,
    ),
}

#[derive(Clone, Debug)]
pub struct Block<ExprType> {
    pub initial_idx: usize, // for LocalId, not ExprId
    // `terms` and `types` are indexed by LocalId *offset by `initial_idx`
    pub terms: Vec<Expr<ExprType>>,
    pub types: Vec<ExprType>,
    pub expr_ids: Vector<ExprId>, // indexed by LocalId
}

pub type TypedExpr = Expr<Type<SolverVarId>>;
pub type TypedBlock = Block<Type<SolverVarId>>;

// TODO: move out of data module?
impl<T> Block<T> {
    pub fn function_body() -> Block<T> {
        Block {
            // LocalId(0) is arg, so first term index is 1
            initial_idx: 1,
            terms: vec![],
            types: vec![],
            expr_ids: vector![ExprId::ARG],
        }
    }

    pub fn branch_from(block: &Block<T>) -> Block<T> {
        Block {
            initial_idx: block.initial_idx + block.terms.len(),
            terms: vec![],
            types: vec![],
            expr_ids: block.expr_ids.clone(),
        }
    }

    // Adds an expression to the block and returns a Term referring to that expression
    pub fn add(&mut self, e: Expr<T>) -> Term {
        Term::Access(self.add_local(e), vector![], None)
    }

    pub fn add_local(&mut self, e: Expr<T>) -> LocalId {
        let idx = self.initial_idx + self.terms.len();
        self.terms.push(e);
        LocalId(idx)
    }

    pub fn expr_id_of(&self, l: LocalId) -> ExprId {
        self.expr_ids[l.0]
    }
}

#[derive(Clone, Debug)]
pub struct FuncDef<ExprType> {
    pub purity: Purity,
    pub arg_type: Type<SolverVarId>,
    pub ret_type: Type<SolverVarId>,
    pub constraints: Vec<Vec<Constraint>>,
    pub body: Block<ExprType>,
}

type TypedFuncDef = FuncDef<Type<SolverVarId>>;
