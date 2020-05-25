use crate::data::first_order_ast as first_ord;
use crate::data::mutation_annot_ast as mutation;
use crate::data::repr_constrained_ast as constrain;
use crate::data::repr_unified_ast as unif;
use crate::fixed_point::{annot_all, Signature, SignatureAssumptions};
use crate::mutation_status::translate_callee_status_cond_disj;
use crate::util::disjunction::Disj;
use crate::util::id_vec::IdVec;

impl Signature for constrain::FuncRepConstraints {
    type Sig = IdVec<unif::RepParamId, constrain::ParamConstraints>;

    fn signature(&self) -> &Self::Sig {
        &self.param_constraints
    }
}

fn constrain_var(
    params: &mut IdVec<unif::RepParamId, constrain::ParamConstraints>,
    internal: &mut IdVec<unif::InternalRepVarId, constrain::RepChoice>,
    rep_var: unif::RepSolution,
    fallback_cond: Disj<mutation::MutationCondition>,
) {
    match rep_var {
        unif::RepSolution::Internal(var) => match fallback_cond {
            Disj::True => internal[var] = constrain::RepChoice::FallbackImmut,

            Disj::Any(clauses) => {
                assert!(
                    clauses.is_empty(),
                    "Internal representation variables should not be constrained by symbolic \
                     aliasing/mutation conditions from the caller.  Any variable constrained by a \
                     symbolic condition should have unified with an external representation \
                     parameter at some point."
                );
            }
        },

        unif::RepSolution::Param(param) => params[param].fallback_immut_if.or_mut(fallback_cond),
    }
}

fn constrain_expr(
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, constrain::FuncRepConstraints>,
    params: &mut IdVec<unif::RepParamId, constrain::ParamConstraints>,
    internal: &mut IdVec<unif::InternalRepVarId, constrain::RepChoice>,
    expr: &unif::Expr<unif::SolvedCall<unif::RepSolution>, unif::RepSolution>,
) {
    match expr {
        unif::Expr::Call(unif::SolvedCall(
            _purity,
            func,
            rep_vars,
            arg_aliases,
            arg_folded_aliases,
            arg_statuses,
            arg,
        )) => {
            if let Some(callee_sig) = sigs.sig_of(func) {
                for (callee_param, callee_constraint) in callee_sig {
                    let caller_rep_var = rep_vars[callee_param];
                    let caller_cond = translate_callee_status_cond_disj(
                        *arg,
                        arg_aliases,
                        arg_folded_aliases,
                        arg_statuses,
                        &callee_constraint.fallback_immut_if,
                    );

                    constrain_var(params, internal, caller_rep_var, caller_cond);
                }
            }
            // If `sigs.sig_of(func)` is `None` then we are on the first iteration of fixed-point
            // analysis, and we can optimistically assume that the callee imposes no constraints.
        }

        unif::Expr::Branch(_discrim, cases, _result_type) => {
            for (_cond, body) in cases {
                constrain_expr(sigs, params, internal, body);
            }
        }

        unif::Expr::LetMany(bindings, _final_local) => {
            for (_type, binding) in bindings {
                constrain_expr(sigs, params, internal, binding);
            }
        }

        unif::Expr::ArrayOp(rep_var, _, status, _)
        | unif::Expr::IoOp(rep_var, mutation::IoOp::Output(status, _)) => {
            constrain_var(params, internal, *rep_var, status.mutated_cond.clone())
        }

        // Explicitly discard additional cases to trigger exhaustivity check if more cases are added
        // in the future.
        unif::Expr::Local(_)
        | unif::Expr::Tuple(_)
        | unif::Expr::TupleField(_, _)
        | unif::Expr::WrapVariant(_, _, _)
        | unif::Expr::UnwrapVariant(_, _)
        | unif::Expr::WrapCustom(_, _, _)
        | unif::Expr::UnwrapCustom(_, _, _)
        | unif::Expr::ArithOp(_)
        | unif::Expr::IoOp(_, mutation::IoOp::Input)
        | unif::Expr::ArrayLit(_, _, _)
        | unif::Expr::BoolLit(_)
        | unif::Expr::ByteLit(_)
        | unif::Expr::IntLit(_)
        | unif::Expr::FloatLit(_) => {}
    }
}

fn constrain_func(
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, constrain::FuncRepConstraints>,
    func_def: &unif::FuncDef,
) -> constrain::FuncRepConstraints {
    let mut param_constraints = IdVec::from_items(vec![
        constrain::ParamConstraints {
            fallback_immut_if: Disj::new()
        };
        func_def.num_params
    ]);

    let mut internal_vars = IdVec::from_items(vec![
        constrain::RepChoice::OptimizedMut;
        func_def.num_internal_vars
    ]);

    constrain_expr(
        sigs,
        &mut param_constraints,
        &mut internal_vars,
        &func_def.body,
    );

    constrain::FuncRepConstraints {
        param_constraints,
        internal_vars,
    }
}

pub fn constrain_reprs(program: unif::Program) -> constrain::Program {
    let rep_constraints = annot_all(
        program.funcs.len(),
        |sigs, func| constrain_func(sigs, &program.funcs[func]),
        &program.sccs,
    );

    constrain::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs: program.funcs,
        func_symbols: program.func_symbols,
        rep_constraints,
        profile_points: program.profile_points,
        main: program.main,
    }
}
