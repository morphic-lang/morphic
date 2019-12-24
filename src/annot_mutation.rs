use im_rc::{OrdMap, OrdSet};

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as annot;
use crate::field_path::{get_names_in, translate_callee_cond, translate_callee_cond_disj};
use crate::fixed_point::{annot_all, Signature, SignatureAssumptions};
use crate::util::disjunction::Disj;
use crate::util::id_vec::IdVec;

impl Signature for annot::FuncDef {
    type Sig = annot::MutationSig;

    fn signature(&self) -> &Self::Sig {
        &self.mutation_sig
    }
}

pub fn annot_mutation(program: alias::Program) -> annot::Program {
    let funcs = annot_all(
        program.funcs.len(),
        |sig_assumptions, func| annot_func(&program, sig_assumptions, &program.funcs[func]),
        &program.sccs,
    );

    annot::Program {
        custom_types: program.custom_types,
        funcs,
        main: program.main,
        sccs: program.sccs,
    }
}

#[derive(Clone, Debug)]
struct LocalInfo {
    type_: anon::Type,
    statuses: OrdMap<alias::FieldPath, annot::LocalStatus>,
}

#[derive(Clone, Debug)]
struct ExprInfo {
    mutations: Vec<(flat::LocalId, alias::FieldPath, Disj<alias::AliasCondition>)>,
    val_statuses: OrdMap<alias::FieldPath, annot::LocalStatus>,
}

fn empty_statuses(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &anon::Type,
) -> OrdMap<alias::FieldPath, annot::LocalStatus> {
    get_names_in(typedefs, type_)
        .into_iter()
        .map(|(name, _)| {
            (
                name,
                annot::LocalStatus {
                    mutated_cond: Disj::new(),
                },
            )
        })
        .collect()
}

fn translate_callee_status_cond(
    arg_id: flat::LocalId,
    arg_aliases: &OrdMap<alias::FieldPath, alias::LocalAliases>,
    arg_folded_aliases: &OrdMap<alias::FieldPath, alias::FoldedAliases>,
    arg_statuses: &OrdMap<alias::FieldPath, annot::LocalStatus>,
    callee_cond: &annot::MutationCondition,
) -> Disj<annot::MutationCondition> {
    match callee_cond {
        annot::MutationCondition::AliasCondition(alias_cond) => {
            translate_callee_cond(arg_id, arg_aliases, arg_folded_aliases, alias_cond)
                .into_mapped(annot::MutationCondition::AliasCondition)
        }

        annot::MutationCondition::ArgMutated(alias::ArgName(arg_path)) => {
            arg_statuses[arg_path].mutated_cond.clone()
        }
    }
}

fn annot_expr(
    orig: &alias::Program,
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, annot::FuncDef>,
    ctx: &OrdMap<flat::LocalId, LocalInfo>,
    expr: &alias::Expr,
) -> (annot::Expr, ExprInfo) {
    match expr {
        alias::Expr::Local(local) => (
            annot::Expr::Local(*local),
            ExprInfo {
                mutations: Vec::new(),
                val_statuses: ctx[local].statuses.clone(),
            },
        ),

        alias::Expr::Call(purity, func, arg_aliases, arg_folded_aliases, arg) => {
            let arg_info = &ctx[arg];

            let annot_expr = annot::Expr::Call(
                *purity,
                *func,
                arg_aliases.clone(),
                arg_folded_aliases.clone(),
                arg_info.statuses.clone(),
                *arg,
            );

            let ret_type = &orig.funcs[func].ret_type;

            let expr_info = match sigs.sig_of(func) {
                None => {
                    // On the first iteration of fixed point analysis, we assume all recursive calls
                    // return fresh (un-mutated) values, and do not mutate their arguments.
                    ExprInfo {
                        mutations: Vec::new(),
                        val_statuses: empty_statuses(&orig.custom_types, ret_type),
                    }
                }

                Some(sig) => {
                    let mut mutations = Vec::new();
                    for (alias::ArgName(arg_path), mut_cond) in &sig.arg_mutation_conds {
                        mutations.push((
                            *arg,
                            arg_path.clone(),
                            translate_callee_cond_disj(
                                *arg,
                                arg_aliases,
                                arg_folded_aliases,
                                mut_cond,
                            ),
                        ));

                        // Propagate mutations along aliasing edges
                        if mut_cond == &Disj::True {
                            for ((other, other_path), alias_cond) in &arg_aliases[arg_path].aliases
                            {
                                if other == arg {
                                    // The consequences of this aliasing relationship have already
                                    // been accounted for in the callee's signature.
                                    continue;
                                }

                                mutations.push((*other, other_path.clone(), alias_cond.clone()));
                            }
                        }
                    }

                    let val_statuses = sig
                        .ret_statuses
                        .iter()
                        .map(|(alias::RetName(ret_path), callee_status)| {
                            (
                                ret_path.clone(),
                                annot::LocalStatus {
                                    mutated_cond: callee_status.mutated_cond.flat_map(
                                        |callee_cond| {
                                            translate_callee_status_cond(
                                                *arg,
                                                arg_aliases,
                                                arg_folded_aliases,
                                                &arg_info.statuses,
                                                callee_cond,
                                            )
                                        },
                                    ),
                                },
                            )
                        })
                        .collect();

                    ExprInfo {
                        mutations,
                        val_statuses,
                    }
                }
            };

            (annot_expr, expr_info)
        }

        alias::Expr::Branch(discrim, cases, result_type) => {
            let mut annot_cases = Vec::with_capacity(cases.len());
            let mut mutations = Vec::new();
            let mut val_statuses = empty_statuses(&orig.custom_types, result_type);

            for (cond, body) in cases {
                let (annot_body, body_info) = annot_expr(orig, sigs, ctx, body);
                annot_cases.push((cond.clone(), annot_body));

                for mutation in body_info.mutations {
                    mutations.push(mutation);
                }

                for (path, status) in body_info.val_statuses {
                    val_statuses[&path].mutated_cond.or_mut(status.mutated_cond);
                }
            }

            let annot_expr = annot::Expr::Branch(*discrim, annot_cases, result_type.clone());
            let expr_info = ExprInfo {
                mutations,
                val_statuses,
            };

            (annot_expr, expr_info)
        }

        alias::Expr::LetMany(bindings, final_local) => {
            let mut new_bindings = Vec::with_capacity(bindings.len());
            let mut mutations = Vec::new();

            let mut new_ctx = ctx.clone();
            for (type_, rhs) in bindings {
                let (annot_rhs, rhs_info) = annot_expr(orig, sigs, &new_ctx, rhs);

                new_bindings.push((type_.clone(), annot_rhs));

                for (other, other_path, mut_cond) in rhs_info.mutations {
                    if other.0 < ctx.len() {
                        // This is a mutation of a variable outside the scope of this `let`.
                        mutations.push((other, other_path.clone(), mut_cond.clone()));
                    }

                    new_ctx[&other].statuses[&other_path]
                        .mutated_cond
                        .or_mut(mut_cond.into_mapped(annot::MutationCondition::AliasCondition));
                }

                let lhs = flat::LocalId(new_ctx.len());
                debug_assert!(!new_ctx.contains_key(&lhs));

                let lhs_info = LocalInfo {
                    type_: type_.clone(),
                    statuses: rhs_info.val_statuses,
                };

                new_ctx.insert(lhs, lhs_info);
            }

            debug_assert_eq!(new_bindings.len(), bindings.len());

            (
                annot::Expr::LetMany(new_bindings, *final_local),
                ExprInfo {
                    mutations,
                    val_statuses: new_ctx[final_local].statuses.clone(),
                },
            )
        }

        _ => unimplemented!(),
    }
}

fn annot_func(
    orig: &alias::Program,
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, annot::FuncDef>,
    func_def: &alias::FuncDef,
) -> annot::FuncDef {
    let arg_names = get_names_in(&orig.custom_types, &func_def.arg_type)
        .into_iter()
        .map(|(name, _)| alias::ArgName(name))
        .collect::<Vec<_>>();

    let mut arg_init_statuses = OrdMap::new();
    for name in &arg_names {
        arg_init_statuses.insert(
            name.0.clone(),
            annot::LocalStatus {
                mutated_cond: Disj::Any(OrdSet::unit(annot::MutationCondition::ArgMutated(
                    name.clone(),
                ))),
            },
        );
    }

    let arg_info = LocalInfo {
        type_: func_def.arg_type.clone(),
        statuses: arg_init_statuses,
    };

    let init_ctx = OrdMap::unit(flat::ARG_LOCAL, arg_info);

    let (annot_body, body_info) = annot_expr(orig, sigs, &init_ctx, &func_def.body);

    let mut arg_mutation_conds = OrdMap::new();
    for name in arg_names {
        arg_mutation_conds.insert(name, Disj::new());
    }

    for (local, name, cond) in body_info.mutations {
        debug_assert_eq!(local, flat::ARG_LOCAL);
        arg_mutation_conds[&alias::ArgName(name.clone())].or_mut(cond);
    }

    let mutation_sig = annot::MutationSig {
        arg_mutation_conds,
        ret_statuses: body_info
            .val_statuses
            .into_iter()
            .map(|(name, status)| (alias::RetName(name), status))
            .collect(),
    };

    annot::FuncDef {
        purity: func_def.purity,
        arg_type: func_def.arg_type.clone(),
        ret_type: func_def.ret_type.clone(),
        mutation_sig,
        body: annot_body,
    }
}
