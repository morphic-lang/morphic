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
pub type TypedExpr = Expr<Type<SolverVarId>>;
impl<T> Expr<T> {
    pub fn assert_typefolded(&self) {
        match self {
            Expr::Term(t) => atf(t),
            Expr::IOOp(IOOp::Output(t)) => atf(t),
            Expr::Ctor(_, _, Some(t)) => atf(t),
            Expr::Tuple(ts) => {
                for t in ts {
                    atf(t);
                }
            }
            Expr::Call(_, _, t, _) => atf(t),
            Expr::Match(_, branches, _) => {
                for (_, body) in branches {
                    for expr in &body.terms {
                        expr.assert_typefolded();
                    }
                }
            }
            Expr::Local(_)
            | Expr::IOOp(IOOp::Input(_))
            | Expr::ArithOp(_)
            | Expr::ArrayOp(_)
            | Expr::Ctor(_, _, None) => {}
        }
        fn atf(t: &Term) {
            if let Term::Access(_, _, typefolded) = t {
                assert!(typefolded.is_some());
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Block<ExprType> {
    pub initial_idx: usize, // for LocalId, not ExprId
    // `terms` and `types` are indexed by LocalId *offset by `initial_idx`
    pub terms: Vec<Expr<ExprType>>,
    pub types: Vec<ExprType>,
    pub expr_ids: Option<Vector<ExprId>>, // indexed by `LocalId` (includes all lexically available locals)
}
pub type TypedBlock = Block<Type<SolverVarId>>;

impl<T: std::fmt::Debug> Block<T> {
    pub fn assert_valid(&self) {
        assert_eq!(self.terms.len(), self.types.len());
        assert!(self.terms.len() > 0); // empty blocks are invalid
        if let Some(expr_ids) = self.expr_ids.as_ref() {
            assert_eq!(expr_ids.len(), self.initial_idx + self.terms.len());
        }
    }

    #[must_use]
    pub fn expr_id_of(&self, l: LocalId) -> ExprId {
        self.expr_ids.as_ref().unwrap()[l.0]
    }
}

impl Block<()> {
    /// Adds an expression to the block and returns a Term referring to that expression
    #[must_use]
    pub fn add(&mut self, e: Expr<()>) -> Term {
        Term::Access(self.add_local(e), vector![], None)
    }

    #[must_use]
    pub fn add_local(&mut self, e: Expr<()>) -> LocalId {
        let idx = self.initial_idx + self.terms.len();
        self.terms.push(e);
        self.types.push(());
        LocalId(idx)
    }
}

#[derive(Clone, Debug)]
pub struct FuncDef<ExprType> {
    pub purity: Purity,
    pub arg_type: Type<SolverVarId>,
    pub ret_type: Type<SolverVarId>,
    pub body: Block<ExprType>,
}

type TypedFuncDef = FuncDef<Type<SolverVarId>>;
