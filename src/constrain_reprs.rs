use im_rc::OrdMap;

use crate::data::alias_annot_ast as alias;
use crate::data::first_order_ast as first_ord;
use crate::data::mutation_annot_ast as mutation;
use crate::data::rc_specialized_ast as rc;
use crate::data::repr_constrained_ast as constrain;
use crate::data::repr_unified_ast as unif;
use crate::fixed_point::{annot_all, Signature, SignatureAssumptions};
use crate::mutation_status::translate_callee_status_cond_disj_post_rc;
use crate::util::disjunction::Disj;
use crate::util::id_vec::IdVec;
use crate::util::progress_logger::ProgressLogger;

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

fn constrain_path(
    typedefs: &IdVec<first_ord::CustomTypeId, unif::TypeDef>,
    params: &mut IdVec<unif::RepParamId, constrain::ParamConstraints>,
    internal: &mut IdVec<unif::InternalRepVarId, constrain::RepChoice>,
    type_: &unif::Type<unif::RepSolution>,
    path: &alias::FieldPath,
    fallback_cond: Disj<mutation::MutationCondition>,
) {
    #[derive(Clone, Debug)]
    enum State<'a> {
        Outer {
            curr_type: &'a unif::Type<unif::RepSolution>,
        },
        Inner {
            curr_type: &'a unif::Type<unif::RepParamId>,
            param_mapping: IdVec<unif::RepParamId, unif::RepSolution>,
        },
    }

    let mut state = State::Outer { curr_type: type_ };
    for field in path {
        state = match state {
            State::Outer { curr_type } => match (field, curr_type) {
                (alias::Field::Field(idx), unif::Type::Tuple(item_types)) => State::Outer {
                    curr_type: &item_types[*idx],
                },
                (alias::Field::Variant(variant_id), unif::Type::Variants(variant_types)) => {
                    State::Outer {
                        curr_type: &variant_types[variant_id],
                    }
                }
                (alias::Field::Boxed, unif::Type::Boxed(content_type)) => State::Outer {
                    curr_type: content_type,
                },
                (
                    alias::Field::Custom(custom_id),
                    unif::Type::Custom(custom_id_2, custom_params),
                ) => {
                    // Note: the custom type ids are *not* guaranteed to match -- they are only
                    // guaranteed to belong to the same SCC! This is safe because all custom types
                    // in an SCC share a common parameterization.
                    debug_assert_eq!(custom_params.len(), typedefs[custom_id].num_params);
                    debug_assert_eq!(custom_params.len(), typedefs[custom_id_2].num_params);
                    State::Inner {
                        curr_type: &typedefs[custom_id].content,
                        param_mapping: custom_params.clone(),
                    }
                }
                (alias::Field::ArrayMembers, unif::Type::Array(_, item_type))
                | (alias::Field::ArrayMembers, unif::Type::HoleArray(_, item_type)) => {
                    State::Outer {
                        curr_type: item_type,
                    }
                }
                (alias::Field::CustomScc(_, _), custom @ unif::Type::Custom(_, _)) => {
                    // Note: here was have the constraint that the custom type must belong to the
                    // SCC listed in the field. It would be nice to have an assertion for that
                    // constraint, but we don't because it's cumbersome to check.
                    State::Outer { curr_type: custom }
                }
                // We explicitly enumerate these cases to trigger an exhaustivity error if we ever
                // add a new field variant.
                (alias::Field::Field(_), _)
                | (alias::Field::Variant(_), _)
                | (alias::Field::Boxed, _)
                | (alias::Field::Custom(_), _)
                | (alias::Field::ArrayMembers, _)
                | (alias::Field::CustomScc(_, _), _) => unreachable!(),
            },
            State::Inner {
                curr_type,
                param_mapping,
            } => match (field, curr_type) {
                (alias::Field::Field(idx), unif::Type::Tuple(item_types)) => State::Inner {
                    curr_type: &item_types[*idx],
                    param_mapping,
                },
                (alias::Field::Variant(variant_id), unif::Type::Variants(variant_types)) => {
                    State::Inner {
                        curr_type: &variant_types[variant_id],
                        param_mapping,
                    }
                }
                (alias::Field::Boxed, unif::Type::Boxed(content_type)) => State::Inner {
                    curr_type: content_type,
                    param_mapping,
                },
                (
                    alias::Field::Custom(custom_id),
                    unif::Type::Custom(custom_id_2, custom_params),
                ) => {
                    // Note: the custom type ids are *not* guaranteed to match! See the comment on
                    // the State::Outer arm above.
                    debug_assert_eq!(custom_params.len(), typedefs[custom_id].num_params);
                    debug_assert_eq!(custom_params.len(), typedefs[custom_id_2].num_params);
                    State::Inner {
                        curr_type: &typedefs[custom_id].content,
                        param_mapping: custom_params.map(|_, param| param_mapping[param]),
                    }
                }
                (alias::Field::ArrayMembers, unif::Type::Array(_, item_type))
                | (alias::Field::ArrayMembers, unif::Type::HoleArray(_, item_type)) => {
                    State::Inner {
                        curr_type: item_type,
                        param_mapping,
                    }
                }
                (alias::Field::CustomScc(_, _), custom @ unif::Type::Custom(_, _)) => {
                    State::Inner {
                        // See the comment on the State::Outer arm above.
                        curr_type: custom,
                        param_mapping,
                    }
                }
                // We explicitly enumerate these cases to trigger an exhaustivity error if we ever
                // add a new field variant.
                (alias::Field::Field(_), _)
                | (alias::Field::Variant(_), _)
                | (alias::Field::Boxed, _)
                | (alias::Field::Custom(_), _)
                | (alias::Field::ArrayMembers, _)
                | (alias::Field::CustomScc(_, _), _) => unreachable!(),
            },
        };
    }

    let rep_var = match state {
        State::Outer { curr_type } => match curr_type {
            unif::Type::Array(rep_var, _) | unif::Type::HoleArray(rep_var, _) => *rep_var,
            _ => unreachable!(),
        },
        State::Inner {
            curr_type,
            param_mapping,
        } => match curr_type {
            unif::Type::Array(rep_param, _) | unif::Type::HoleArray(rep_param, _) => {
                param_mapping[rep_param]
            }
            _ => unreachable!(),
        },
    };

    constrain_var(params, internal, rep_var, fallback_cond);
}

fn constrain_deep_access(
    typedefs: &IdVec<first_ord::CustomTypeId, unif::TypeDef>,
    params: &mut IdVec<unif::RepParamId, constrain::ParamConstraints>,
    internal: &mut IdVec<unif::InternalRepVarId, constrain::RepChoice>,
    type_: &unif::Type<unif::RepSolution>,
    statuses: &OrdMap<alias::FieldPath, mutation::LocalStatus>,
) {
    for (path, status) in statuses {
        constrain_path(
            typedefs,
            params,
            internal,
            type_,
            path,
            status.mutated_cond.clone(),
        );
    }
}

fn constrain_expr(
    typedefs: &IdVec<first_ord::CustomTypeId, unif::TypeDef>,
    sigs: &SignatureAssumptions<rc::CustomFuncId, constrain::FuncRepConstraints>,
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
            arg_statuses,
            _arg,
        )) => {
            if let Some(callee_sig) = sigs.sig_of(func) {
                for (callee_param, callee_constraint) in callee_sig {
                    let caller_rep_var = rep_vars[callee_param];
                    let caller_cond = translate_callee_status_cond_disj_post_rc(
                        arg_aliases,
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
                constrain_expr(typedefs, sigs, params, internal, body);
            }
        }

        unif::Expr::LetMany(bindings, _final_local) => {
            for (_type, binding) in bindings {
                constrain_expr(typedefs, sigs, params, internal, binding);
            }
        }

        unif::Expr::ArrayOp(rep_var, item_type, statuses, array_op) => {
            // Note: We don't strictly speaking *need* to pass a `HoleArray` type for the `Replace`
            // case, because the resulting constraint generation logic will be identical either way,
            // but there is a sense in which that would only work "by coincidence."  Using the
            // correct type is more robust to refactorings.
            let array_type = match array_op {
                unif::ArrayOp::Get(_, _)
                | unif::ArrayOp::Extract(_, _)
                | unif::ArrayOp::Len(_)
                | unif::ArrayOp::Push(_, _)
                | unif::ArrayOp::Pop(_)
                | unif::ArrayOp::Reserve(_, _) => {
                    unif::Type::Array(*rep_var, Box::new(item_type.clone()))
                }

                unif::ArrayOp::Replace(_, _) => {
                    unif::Type::HoleArray(*rep_var, Box::new(item_type.clone()))
                }
            };

            constrain_deep_access(typedefs, params, internal, &array_type, statuses);
        }

        unif::Expr::IoOp(rep_var, rc::IoOp::Output(status, _))
        | unif::Expr::Panic(_, rep_var, status, _) => {
            constrain_var(params, internal, *rep_var, status.mutated_cond.clone())
        }

        // Explicitly discard additional cases to trigger exhaustivity check if more cases are added
        // in the future.
        unif::Expr::Local(_)
        | unif::Expr::Tuple(_)
        | unif::Expr::TupleField(_, _)
        | unif::Expr::WrapVariant(_, _, _)
        | unif::Expr::UnwrapVariant(_, _)
        | unif::Expr::WrapBoxed(_, _)
        | unif::Expr::UnwrapBoxed(_, _)
        | unif::Expr::WrapCustom(_, _, _)
        | unif::Expr::UnwrapCustom(_, _, _)
        | unif::Expr::IoOp(_, rc::IoOp::Input)
        | unif::Expr::ArrayLit(_, _, _)
        | unif::Expr::BoolLit(_)
        | unif::Expr::ByteLit(_)
        | unif::Expr::IntLit(_)
        | unif::Expr::FloatLit(_) => {}

        unif::Expr::RcOp(_rc_op, container, item_type, local_statuses, _local) => {
            let container_type = match container {
                unif::ContainerType::Boxed => unif::Type::Boxed(Box::new(item_type.clone())),
                unif::ContainerType::Array(rep_var) => {
                    unif::Type::Array(*rep_var, Box::new(item_type.clone()))
                }
                unif::ContainerType::HoleArray(rep_var) => {
                    unif::Type::HoleArray(*rep_var, Box::new(item_type.clone()))
                }
            };

            constrain_deep_access(typedefs, params, internal, &container_type, local_statuses);
        }

        // NOTE [intrinsics]: If we ever add array intrinsics in the future, this will need to be
        // modified.
        unif::Expr::Intrinsic(_, _) => {}
    }
}

fn constrain_func(
    typedefs: &IdVec<first_ord::CustomTypeId, unif::TypeDef>,
    sigs: &SignatureAssumptions<rc::CustomFuncId, constrain::FuncRepConstraints>,
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
        typedefs,
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

pub fn constrain_reprs(
    program: unif::Program,
    progress: impl ProgressLogger,
) -> constrain::Program {
    let rep_constraints = annot_all(
        program.funcs.len(),
        |sigs, func| constrain_func(&program.custom_types, sigs, &program.funcs[func]),
        &program.sccs,
        progress,
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
