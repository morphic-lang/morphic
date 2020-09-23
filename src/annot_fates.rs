use im_rc::OrdSet;
use std::collections::btree_map::{self, BTreeMap};

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as mutation;
use crate::field_path::get_refs_in;
use crate::fixed_point::{annot_all, Signature, SignatureAssumptions};
use crate::util::id_gen::IdGen;
use crate::util::id_vec::IdVec;
use crate::util::local_context::LocalContext;

impl Signature for fate::FuncDef {
    type Sig = BTreeMap<alias::ArgName, fate::ArgFieldFate>;

    fn signature(&self) -> &Self::Sig {
        &self.arg_fate
    }
}

#[derive(Clone, Debug)]
struct LocalUses {
    uses: BTreeMap<flat::LocalId, fate::Fate>,
}

fn merge_field_fates(fate1: &mut fate::FieldFate, fate2: &fate::FieldFate) {
    fate1.internal = fate1.internal.max(fate2.internal);

    fate1
        .blocks_escaped
        .extend(fate2.blocks_escaped.iter().cloned());

    fate1
        .ret_destinations
        .extend(fate2.ret_destinations.iter().cloned());
}

fn merge_fates(fate1: &mut fate::Fate, fate2: &fate::Fate) {
    debug_assert_eq!(fate1.fates.len(), fate2.fates.len());
    for (path, path_fate1) in &mut fate1.fates {
        merge_field_fates(path_fate1, &fate2.fates[path]);
    }
}

fn add_use(uses: &mut LocalUses, local: flat::LocalId, fate: fate::Fate) {
    match uses.uses.entry(local) {
        btree_map::Entry::Occupied(mut curr_fate) => {
            merge_fates(curr_fate.get_mut(), &fate);
        }
        btree_map::Entry::Vacant(vacant) => {
            vacant.insert(fate);
        }
    }
}

fn add_occurence(
    occurs: &mut IdVec<fate::OccurId, fate::Fate>,
    uses: &mut LocalUses,
    local: flat::LocalId,
    fate: fate::Fate,
) -> fate::Local {
    let occur_id = occurs.push(fate.clone());
    add_use(uses, local, fate);
    fate::Local(occur_id, local)
}

fn empty_fate(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &anon::Type,
) -> fate::Fate {
    fate::Fate {
        fates: get_refs_in(typedefs, type_)
            .into_iter()
            .map(|(path, _)| {
                (
                    path,
                    fate::FieldFate {
                        internal: fate::InternalFate::Unused,
                        blocks_escaped: OrdSet::new(),
                        ret_destinations: OrdSet::new(),
                    },
                )
            })
            .collect(),
    }
}

// TODO: We could achieve slightly better asymptotics (in the case of deeply-nested expressions) if
// this function mutated a provided `LocalUses` instead of returning its own.  However, if we did
// this then it might be slightly less clear what the intended data flow and invariants are.  Would
// this change be worth it?
fn annot_expr(
    orig: &mutation::Program,
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, fate::FuncDef>,
    locals: &mut LocalContext<flat::LocalId, anon::Type>,
    expr: &mutation::Expr,
    val_fate: fate::Fate,
    occurs: &mut IdVec<fate::OccurId, fate::Fate>,
    expr_fates: &mut IdVec<fate::ExprId, fate::Fate>,
    calls: &mut IdGen<fate::CallId>,
    let_blocks: &mut IdGen<fate::LetBlockId>,
    branch_blocks: &mut IdGen<fate::BranchBlockId>,
) -> (fate::Expr, LocalUses) {
    let mut uses = LocalUses {
        uses: BTreeMap::new(),
    };

    let fate_expr_kind = match expr {
        mutation::Expr::Local(local) => {
            fate::ExprKind::Local(add_occurence(occurs, &mut uses, *local, val_fate.clone()))
        }

        mutation::Expr::Call(
            purity,
            func,
            arg_alises,
            arg_folded_alises,
            arg_statuses,
            arg_local,
        ) => {
            let arg_fate = match sigs.sig_of(func) {
                None => empty_fate(&orig.custom_types, &orig.funcs[func].arg_type),
                Some(sig_arg_fate) => fate::Fate {
                    fates: sig_arg_fate
                        .iter()
                        .map(|(alias::ArgName(arg_path), sig_path_fate)| {
                            let mut path_fate = fate::FieldFate {
                                internal: sig_path_fate.internal,
                                blocks_escaped: OrdSet::new(),
                                ret_destinations: OrdSet::new(),
                            };

                            for alias::RetName(dest) in &sig_path_fate.ret_destinations {
                                merge_field_fates(&mut path_fate, &val_fate.fates[dest]);
                            }

                            (arg_path.clone(), path_fate)
                        })
                        .collect(),
                },
            };

            let local_annot = add_occurence(occurs, &mut uses, *arg_local, arg_fate);

            fate::ExprKind::Call(
                calls.fresh(),
                *purity,
                *func,
                arg_alises.clone(),
                arg_folded_alises.clone(),
                arg_statuses.clone(),
                local_annot,
            )
        }

        mutation::Expr::Branch(discrim, cases, ret_type) => {
            // TODO: We currently consider all paths in the discrim to be accessed, even if they're
            // not used in any condition.  We could make this more precise in the future.
            let mut discrim_access_fate =
                empty_fate(&orig.custom_types, locals.local_binding(*discrim));
            for (_, path_fate) in &mut discrim_access_fate.fates {
                path_fate.internal = fate::InternalFate::Accessed;
            }

            let discrim_annot = add_occurence(occurs, &mut uses, *discrim, discrim_access_fate);

            let cases_annot = cases
                .iter()
                .map(|(cond, body)| {
                    let (body_annot, body_uses) = annot_expr(
                        orig,
                        sigs,
                        locals,
                        body,
                        val_fate.clone(),
                        occurs,
                        expr_fates,
                        calls,
                        let_blocks,
                        branch_blocks,
                    );

                    for (local, body_fate) in body_uses.uses {
                        add_use(&mut uses, local, body_fate);
                    }

                    (branch_blocks.fresh(), cond.clone(), body_annot)
                })
                .collect();

            fate::ExprKind::Branch(discrim_annot, cases_annot, ret_type.clone())
        }

        // We're only using `with_scope` here for its debug assertion, and to signal intent; by the
        // time the passed closure returns, we've manually truncated away all the variables which it
        // would usually be `with_scope`'s responsibility to remove.
        mutation::Expr::LetMany(bindings, final_local) => locals.with_scope(|sub_locals| {
            let block_id = let_blocks.fresh();
            let mut block_val_fate = val_fate.clone();
            for (_, path_fate) in &mut block_val_fate.fates {
                path_fate.blocks_escaped.insert(block_id);
            }

            let locals_offset = sub_locals.len();

            for (type_, _) in bindings.iter() {
                sub_locals.add_local(type_.clone());
            }

            let mut let_uses = LocalUses {
                uses: BTreeMap::new(),
            };
            let final_local_annot =
                add_occurence(occurs, &mut let_uses, *final_local, block_val_fate.clone());

            let mut bindings_annot_rev = Vec::new();

            for (i, (type_, rhs)) in bindings.iter().enumerate().rev() {
                let binding_local = flat::LocalId(locals_offset + i);

                // Note: After truncation, `sub_locals` contains all locals *strictly* before
                // `binding_local`.
                sub_locals.truncate(binding_local.0);

                let rhs_fate = let_uses
                    .uses
                    .get(&binding_local)
                    .cloned()
                    .unwrap_or_else(|| empty_fate(&orig.custom_types, type_));

                let (rhs_annot, rhs_uses) = annot_expr(
                    orig,
                    sigs,
                    sub_locals,
                    rhs,
                    rhs_fate,
                    occurs,
                    expr_fates,
                    calls,
                    let_blocks,
                    branch_blocks,
                );

                for (used_var, var_fate) in rhs_uses.uses {
                    debug_assert!(used_var.0 < binding_local.0);
                    add_use(&mut let_uses, used_var, var_fate);
                }

                bindings_annot_rev.push((type_.clone(), rhs_annot));
            }

            for (var, let_use) in let_uses.uses {
                if var.0 < locals_offset {
                    debug_assert!(!uses.uses.contains_key(&var));
                    uses.uses.insert(var, let_use);
                }
            }

            let bindings_annot = {
                bindings_annot_rev.reverse();
                bindings_annot_rev
            };

            fate::ExprKind::LetMany(block_id, bindings_annot, final_local_annot)
        }),

        _ => todo!(),
    };

    let id = expr_fates.push(val_fate);

    (
        fate::Expr {
            id,
            kind: fate_expr_kind,
        },
        uses,
    )
}

fn annot_func(
    orig: &mutation::Program,
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, fate::FuncDef>,
    func_def: &mutation::FuncDef,
) -> fate::FuncDef {
    let ret_fate = fate::Fate {
        fates: get_refs_in(&orig.custom_types, &func_def.ret_type)
            .into_iter()
            .map(|(path, _)| {
                (
                    path.clone(),
                    fate::FieldFate {
                        internal: fate::InternalFate::Unused,
                        blocks_escaped: OrdSet::new(),
                        ret_destinations: OrdSet::unit(alias::RetName(path)),
                    },
                )
            })
            .collect(),
    };

    let mut locals = LocalContext::new();
    locals.add_local(func_def.arg_type.clone());

    let mut occurs = IdVec::new();
    let mut expr_fates = IdVec::new();
    let mut calls = IdGen::new();
    let mut let_blocks = IdGen::new();
    let mut branch_blocks = IdGen::new();

    let (body_annot, body_uses) = annot_expr(
        orig,
        sigs,
        &mut locals,
        &func_def.body,
        ret_fate,
        &mut occurs,
        &mut expr_fates,
        &mut calls,
        &mut let_blocks,
        &mut branch_blocks,
    );

    let arg_internal_fate = match body_uses.uses.get(&flat::ARG_LOCAL) {
        Some(fate) => {
            debug_assert_eq!(body_uses.uses.len(), 1);
            fate.clone()
        }
        None => {
            debug_assert_eq!(body_uses.uses.len(), 0);
            empty_fate(&orig.custom_types, &func_def.arg_type)
        }
    };

    let arg_fate = arg_internal_fate
        .fates
        .into_iter()
        .map(|(path, path_fate)| {
            (
                alias::ArgName(path),
                fate::ArgFieldFate {
                    internal: path_fate.internal,
                    ret_destinations: path_fate.ret_destinations,
                },
            )
        })
        .collect();

    fate::FuncDef {
        purity: func_def.purity,
        arg_type: func_def.arg_type.clone(),
        ret_type: func_def.ret_type.clone(),
        alias_sig: func_def.alias_sig.clone(),
        mutation_sig: func_def.mutation_sig.clone(),
        arg_fate,
        body: body_annot,
        occur_fates: occurs,
        expr_fates: expr_fates,
        num_calls: calls.count(),
        num_let_blocks: let_blocks.count(),
        num_branch_blocks: branch_blocks.count(),
        profile_point: func_def.profile_point,
    }
}

fn annot_fates(program: mutation::Program) -> fate::Program {
    let funcs = annot_all(
        program.funcs.len(),
        |sig_assumptions, func| annot_func(&program, sig_assumptions, &program.funcs[func]),
        &program.sccs,
    );

    fate::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        func_symbols: program.func_symbols,
        profile_points: program.profile_points,
        main: program.main,

        sccs: program.sccs,
    }
}
