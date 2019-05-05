use super::unify;
use super::{mid_ast, out_ast};
use crate::util::constraint_graph::{EquivClass, EquivClasses, SolverVarId};
use std::collections::{BTreeMap, BTreeSet};
pub struct SignatureGen<'a> {
    equiv_classes: &'a EquivClasses,
    params: Vec<EquivClass>, // indexed by out_ast::RepParamId
    params_reverse: BTreeMap<EquivClass, out_ast::RepParamId>,
}
impl<'a> SignatureGen<'a> {
    fn new(equiv_classes: &'a EquivClasses) -> Self {
        SignatureGen {
            equiv_classes,
            params: Vec::new(),
            params_reverse: BTreeMap::new(),
        }
    }

    fn soln_for(&mut self, var: SolverVarId) -> out_ast::RepParamId {
        let class = self.equiv_classes.class(var);
        if let Some(rep_param) = self.params_reverse.get(&class) {
            *rep_param
        } else {
            let rep_param = out_ast::RepParamId(self.params.len());
            self.params.push(class);
            self.params_reverse.insert(class, rep_param);
            rep_param
        }
    }
}

pub struct SolutionExtractor<'a> {
    equiv_classes: &'a EquivClasses,
    class_constraints: Vec<BTreeSet<out_ast::Constraint>>, // indexed by EquivClass
    solutions: Vec<Option<out_ast::Solution>>,             // indexed by EquivClass
    params: Vec<EquivClass>,                               // indexed by out_ast::RepParamId
}
impl<'a> SolutionExtractor<'a> {
    pub fn from_sig_gen(
        siggen: &SignatureGen<'a>,
        class_constraints: Vec<BTreeSet<out_ast::Constraint>>,
    ) -> Self {
        let mut solutions = vec![None; siggen.equiv_classes.count()];
        for (equiv_class, rep_param) in &siggen.params_reverse {
            solutions[equiv_class.0] = Some(out_ast::Solution::Var(*rep_param));
        }
        SolutionExtractor {
            equiv_classes: siggen.equiv_classes,
            class_constraints,
            solutions,
            params: siggen.params.clone(),
        }
    }
    fn fresh_for(&mut self, class: EquivClass) -> out_ast::RepParamId {
        let param = out_ast::RepParamId(self.params.len());
        self.params.push(class);
        param
    }

    fn soln_in_body_for(&mut self, var: SolverVarId) -> out_ast::Solution {
        let class = self.equiv_classes.class(var);
        if let Some(soln) = self.solutions[class.0] {
            soln
        } else {
            let var_constraints = &self.class_constraints[class.0];
            let soln = if var_constraints.is_empty() {
                out_ast::Solution::Unique
            } else if var_constraints.contains(&out_ast::Constraint::Shared) {
                out_ast::Solution::Shared
            } else {
                unreachable!() // Other constraints are only applied to equiv classes that appear in the arg or return
            };
            self.solutions[class.0] = Some(soln);
            soln
        }
    }

    pub fn drain_constraints(self) -> Vec<BTreeSet<out_ast::Constraint>> {
        self.params
            .iter()
            .map(|class| self.class_constraints[class.0].clone()) // TODO: heinous clone of constraints
            .collect()
    }
}

pub fn gen_sigs<'a, 'b>(
    equiv_classes: &'a EquivClasses,
    funcs: &'b BTreeMap<out_ast::CustomFuncId, (mid_ast::Type<SolverVarId>, mid_ast::TypedBlock)>,
    signatures: &'b mut [Option<unify::Signature>],
) -> SignatureGen<'a> {
    let mut param_gen = SignatureGen::new(equiv_classes);
    let mut type_sigs = Vec::new();
    for (&id, (arg_type, body)) in funcs {
        // Generate types in signature first so they have the first `RepParamId`s
        body.assert_valid();
        type_sigs.push((
            id,
            gen_sig_type(&mut param_gen, arg_type),
            gen_sig_type(&mut param_gen, &body.types.last().unwrap()),
        ));
    }
    for (id, arg_type, ret_type) in type_sigs {
        assert!(signatures[id.0].is_none());
        signatures[id.0] = Some(unify::Signature {
            num_params: param_gen.params.len(),
            arg_type,
            ret_type,
        });
    }
    param_gen
}

pub fn gen_func(
    param_gen: &mut SolutionExtractor,
    (arg_type, body): &(mid_ast::Type<SolverVarId>, mid_ast::TypedBlock),
) -> (out_ast::Type, out_ast::Block) {
    (gen_type(param_gen, arg_type), gen_block(param_gen, body))
}

fn gen_block(param_gen: &mut SolutionExtractor, block: &mid_ast::TypedBlock) -> out_ast::Block {
    let mut out_block = out_ast::Block {
        initial_idx: block.initial_idx,
        exprs: Vec::new(),
        types: Vec::new(),
        expr_ids: block.expr_ids.clone().unwrap(),
    };
    for (expr, type_) in block.terms.iter().zip(block.types.iter()) {
        let out_type = gen_type(param_gen, type_);
        out_block.exprs.push(gen_expr(param_gen, expr, &out_type));
        out_block.types.push(out_type);
    }
    out_block
}

fn gen_expr(
    param_gen: &mut SolutionExtractor,
    expr: &mid_ast::TypedExpr,
    type_: &out_ast::Type,
) -> out_ast::Expr {
    return match expr {
        mid_ast::Expr::Term(term) => out_ast::Expr::Term(gen_term(term)),
        mid_ast::Expr::ArithOp(arith_op) => {
            let a = match arith_op {
                mid_ast::ArithOp::IntOp(binop, left, right) => {
                    out_ast::ArithOp::IntOp(*binop, gen_term(left), gen_term(right))
                }
                mid_ast::ArithOp::ByteOp(binop, left, right) => {
                    out_ast::ArithOp::ByteOp(*binop, gen_term(left), gen_term(right))
                }
                mid_ast::ArithOp::FloatOp(binop, left, right) => {
                    out_ast::ArithOp::FloatOp(*binop, gen_term(left), gen_term(right))
                }
                mid_ast::ArithOp::IntCmp(cmp, left, right) => {
                    out_ast::ArithOp::IntCmp(*cmp, gen_term(left), gen_term(right))
                }
                mid_ast::ArithOp::ByteCmp(cmp, left, right) => {
                    out_ast::ArithOp::ByteCmp(*cmp, gen_term(left), gen_term(right))
                }
                mid_ast::ArithOp::FloatCmp(cmp, left, right) => {
                    out_ast::ArithOp::FloatCmp(*cmp, gen_term(left), gen_term(right))
                }
                mid_ast::ArithOp::NegateInt(term) => out_ast::ArithOp::NegateInt(gen_term(term)),
                mid_ast::ArithOp::NegateByte(term) => out_ast::ArithOp::NegateByte(gen_term(term)),
                mid_ast::ArithOp::NegateFloat(term) => {
                    out_ast::ArithOp::NegateFloat(gen_term(term))
                }
            };
            out_ast::Expr::ArithOp(a)
        }
        mid_ast::Expr::IOOp(mid_ast::IOOp::Input(repr_var)) => {
            out_ast::Expr::IOOp(out_ast::IOOp::Input(param_gen.soln_in_body_for(*repr_var)))
        }
        mid_ast::Expr::IOOp(mid_ast::IOOp::Output(term)) => {
            out_ast::Expr::IOOp(out_ast::IOOp::Output(gen_term(term)))
        }
        mid_ast::Expr::ArrayOp(array_op) => {
            let a = match array_op {
                mid_ast::ArrayOp::Construct(item_type, repr_var, items) => {
                    out_ast::ArrayOp::Construct(
                        Box::new(gen_type(param_gen, item_type)),
                        param_gen.soln_in_body_for(*repr_var),
                        items.iter().map(gen_term).collect(),
                    )
                }
                mid_ast::ArrayOp::Item(array, idx) => {
                    out_ast::ArrayOp::Item(gen_term(array), gen_term(idx))
                }
                mid_ast::ArrayOp::Len(array) => out_ast::ArrayOp::Len(gen_term(array)),
                mid_ast::ArrayOp::Push(array, item) => {
                    out_ast::ArrayOp::Push(gen_term(array), gen_term(item))
                }
                mid_ast::ArrayOp::Pop(array) => out_ast::ArrayOp::Pop(gen_term(array)),
                mid_ast::ArrayOp::Replace(hole_array, item) => {
                    out_ast::ArrayOp::Replace(gen_term(hole_array), gen_term(item))
                }
            };
            out_ast::Expr::ArrayOp(a)
        }
        mid_ast::Expr::Ctor(type_id, variant_id, arg) => {
            let solns = if let mid_ast::Type::Custom(t_type_id, solns) = type_ {
                assert_eq!(type_id, t_type_id);
                solns.clone()
            } else {
                panic!("internal type error")
            };
            out_ast::Expr::Ctor(*type_id, solns, *variant_id, arg.as_ref().map(gen_term))
        }
        mid_ast::Expr::Tuple(items) => out_ast::Expr::Tuple(items.iter().map(gen_term).collect()),
        mid_ast::Expr::Local(local_id) => out_ast::Expr::Local(*local_id),
        mid_ast::Expr::Call(
            purity,
            func_id,
            arg,
            Some(mid_ast::ReprParams::Determined(repr_params)),
        ) => out_ast::Expr::Call(
            *purity,
            *func_id,
            gen_term(arg),
            repr_params
                .iter()
                .map(|p| param_gen.soln_in_body_for(*p))
                .collect(),
        ),
        mid_ast::Expr::Call(purity, func_id, arg, Some(mid_ast::ReprParams::Pending)) => {
            out_ast::Expr::Call(
                *purity,
                *func_id,
                gen_term(arg),
                (0..param_gen.params.len())
                    .into_iter()
                    .map(|rep_id| out_ast::Solution::Var(out_ast::RepParamId(rep_id)))
                    .collect(),
            )
        }
        mid_ast::Expr::Call(_, _, _, None) => unreachable!(),
        mid_ast::Expr::Match(matched_local, branches, result_t) => out_ast::Expr::Match(
            *matched_local,
            branches
                .iter()
                .map(|(pat, branch)| (pat.clone(), gen_block(param_gen, branch)))
                .collect(),
            Box::new(gen_type(param_gen, result_t)),
        ),
    };

    fn gen_term(term: &mid_ast::Term) -> out_ast::Term {
        match term {
            mid_ast::Term::Access(expr, field, typefolded_field) => {
                out_ast::Term::Access(*expr, field.clone(), typefolded_field.clone().unwrap())
            }
            &mid_ast::Term::BoolLit(v) => out_ast::Term::BoolLit(v),
            &mid_ast::Term::IntLit(v) => out_ast::Term::IntLit(v),
            &mid_ast::Term::ByteLit(v) => out_ast::Term::ByteLit(v),
            &mid_ast::Term::FloatLit(v) => out_ast::Term::FloatLit(v),
        }
    }
}

fn gen_type(
    param_gen: &mut SolutionExtractor,
    type_: &mid_ast::Type<SolverVarId>,
) -> out_ast::Type {
    use out_ast::Type as T;
    match type_ {
        T::Bool => T::Bool,
        T::Int => T::Int,
        T::Float => T::Float,
        T::Byte => T::Byte,
        T::Array(item_t, var) => T::Array(
            Box::new(gen_type(param_gen, item_t)),
            param_gen.soln_in_body_for(*var),
        ),
        T::HoleArray(item_t, var) => T::HoleArray(
            Box::new(gen_type(param_gen, item_t)),
            param_gen.soln_in_body_for(*var),
        ),
        T::Tuple(item_types) => {
            T::Tuple(item_types.iter().map(|t| gen_type(param_gen, t)).collect())
        }
        T::Custom(type_id, vars) => T::Custom(
            *type_id,
            vars.iter()
                .map(|v| param_gen.soln_in_body_for(*v))
                .collect(),
        ),
    }
}

fn gen_sig_type(
    sig_gen: &mut SignatureGen,
    type_: &mid_ast::Type<SolverVarId>,
) -> out_ast::Type<out_ast::RepParamId> {
    use out_ast::Type as T;
    match type_ {
        T::Bool => T::Bool,
        T::Int => T::Int,
        T::Byte => T::Byte,
        T::Float => T::Float,
        T::Array(item_t, var) => T::Array(
            Box::new(gen_sig_type(sig_gen, item_t)),
            sig_gen.soln_for(*var),
        ),
        T::HoleArray(item_t, var) => T::HoleArray(
            Box::new(gen_sig_type(sig_gen, item_t)),
            sig_gen.soln_for(*var),
        ),
        T::Tuple(item_types) => T::Tuple(
            item_types
                .iter()
                .map(|t| gen_sig_type(sig_gen, t))
                .collect(),
        ),
        T::Custom(type_id, vars) => T::Custom(
            *type_id,
            vars.iter().map(|v| sig_gen.soln_for(*v)).collect(),
        ),
    }
}
