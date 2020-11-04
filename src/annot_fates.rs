use im_rc::{OrdSet, Vector};
use std::collections::btree_map::{self, BTreeMap};

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as mutation;
use crate::field_path::{get_refs_in, split_at_fold};
use crate::fixed_point::{annot_all, Signature, SignatureAssumptions};
use crate::util::event_set as event;
use crate::util::id_gen::IdGen;
use crate::util::id_vec::IdVec;
use crate::util::im_rc_ext::VectorExtensions;
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
        .last_internal_use
        .merge_latest(&fate2.last_internal_use);

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
            .map(|(path, _)| (path, fate::FieldFate::new()))
            .collect(),
    }
}

fn consumed_fate(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &anon::Type,
    expr_event: &event::Horizon,
) -> fate::Fate {
    fate::Fate {
        fates: get_refs_in(typedefs, type_)
            .into_iter()
            .map(|(path, _)| {
                (
                    path,
                    fate::FieldFate {
                        internal: fate::InternalFate::Owned,
                        last_internal_use: expr_event.clone(),
                        blocks_escaped: OrdSet::new(),
                        ret_destinations: OrdSet::new(),
                    },
                )
            })
            .collect(),
    }
}

fn access_field_fate(expr_event: event::Horizon) -> fate::FieldFate {
    fate::FieldFate {
        internal: fate::InternalFate::Accessed,
        last_internal_use: expr_event,
        blocks_escaped: OrdSet::new(),
        ret_destinations: OrdSet::new(),
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
    expr_annots: &mut IdVec<fate::ExprId, fate::ExprAnnot>,
    calls: &mut IdGen<fate::CallId>,
    let_block_end_events: &mut IdVec<fate::LetBlockId, event::Horizon>,
    branch_block_end_events: &mut IdVec<fate::BranchBlockId, event::Horizon>,
    event_set: &mut event::EventSet,
    event_block: event::BlockId,
) -> (fate::Expr, LocalUses) {
    let mut uses = LocalUses {
        uses: BTreeMap::new(),
    };

    let expr_event = event_set.prepend_event(event_block);

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
                                last_internal_use: match sig_path_fate.internal {
                                    fate::InternalFate::Accessed | fate::InternalFate::Owned => {
                                        expr_event.clone()
                                    }
                                    fate::InternalFate::Unused => event::Horizon::new(),
                                },
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
            let case_event_blocks = event_set.prepend_branch(event_block, cases.len());

            let cases_annot = cases
                .iter()
                .zip(case_event_blocks)
                .map(|((cond, body), case_event_block)| {
                    let case_end_event = event_set.prepend_event(case_event_block);

                    let (body_annot, body_uses) = annot_expr(
                        orig,
                        sigs,
                        locals,
                        body,
                        val_fate.clone(),
                        occurs,
                        expr_annots,
                        calls,
                        let_block_end_events,
                        branch_block_end_events,
                        event_set,
                        case_event_block,
                    );

                    for (local, body_fate) in body_uses.uses {
                        add_use(&mut uses, local, body_fate);
                    }

                    (
                        branch_block_end_events.push(case_end_event),
                        cond.clone(),
                        body_annot,
                    )
                })
                .collect();

            // We need to mark the discrim as accessed *before* the body of the branch, so we create
            // a separate event for it instead of using `expr_event`.
            let discrim_check_event = event_set.prepend_event(event_block);

            // TODO: We currently consider all paths in the discrim to be accessed, even if they're
            // not used in any condition.  We could make this more precise in the future.
            let mut discrim_access_fate =
                empty_fate(&orig.custom_types, locals.local_binding(*discrim));
            for (_, path_fate) in &mut discrim_access_fate.fates {
                path_fate.internal = fate::InternalFate::Accessed;
                path_fate.last_internal_use = discrim_check_event.clone();
            }
            let discrim_annot = add_occurence(occurs, &mut uses, *discrim, discrim_access_fate);

            fate::ExprKind::Branch(discrim_annot, cases_annot, ret_type.clone())
        }

        // We're only using `with_scope` here for its debug assertion, and to signal intent; by the
        // time the passed closure returns, we've manually truncated away all the variables which it
        // would usually be `with_scope`'s responsibility to remove.
        mutation::Expr::LetMany(bindings, final_local) => locals.with_scope(|sub_locals| {
            let block_end_event = event_set.prepend_event(event_block);
            let block_id = let_block_end_events.push(block_end_event);
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
                    expr_annots,
                    calls,
                    let_block_end_events,
                    branch_block_end_events,
                    event_set,
                    event_block,
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

        mutation::Expr::Tuple(items) => {
            let mut new_items = Vec::new();

            for (i, item) in items.iter().enumerate() {
                let mut item_fate = fate::Fate::new();

                for (path, _) in get_refs_in(&orig.custom_types, locals.local_binding(*item)) {
                    let val_path = path.clone().add_front(alias::Field::Field(i));
                    item_fate
                        .fates
                        .insert(path, val_fate.fates[&val_path].clone());
                }

                new_items.push(add_occurence(occurs, &mut uses, *item, item_fate));
            }

            fate::ExprKind::Tuple(new_items)
        }

        mutation::Expr::TupleField(tuple, idx) => {
            let mut tuple_fate = fate::Fate::new();

            for (path, _) in get_refs_in(&orig.custom_types, locals.local_binding(*tuple)) {
                // Heap paths in tuples are necessarily non-empty, because the tuple is not itself a
                // heap structure
                debug_assert!(matches!(&path[0], alias::Field::Field(_)));
                let path_fate = if &path[0] == &alias::Field::Field(*idx) {
                    val_fate.fates[&path.clone().slice(1..)].clone()
                } else {
                    fate::FieldFate::new()
                };
                tuple_fate.fates.insert(path, path_fate);
            }

            fate::ExprKind::TupleField(add_occurence(occurs, &mut uses, *tuple, tuple_fate), *idx)
        }

        mutation::Expr::WrapVariant(variant_types, variant_id, content) => {
            let mut content_fate = fate::Fate::new();

            debug_assert_eq!(&variant_types[variant_id], locals.local_binding(*content));

            for (path, _) in get_refs_in(&orig.custom_types, locals.local_binding(*content)) {
                let path_fate = val_fate.fates
                    [&path.clone().add_front(alias::Field::Variant(*variant_id))]
                    .clone();

                content_fate.fates.insert(path, path_fate);
            }

            fate::ExprKind::WrapVariant(
                variant_types.clone(),
                *variant_id,
                add_occurence(occurs, &mut uses, *content, content_fate),
            )
        }

        mutation::Expr::UnwrapVariant(variant_id, wrapped) => {
            let mut wrapped_fate = fate::Fate::new();

            for (path, _) in get_refs_in(&orig.custom_types, locals.local_binding(*wrapped)) {
                // Heap paths in variants are necessarily non-empty, because the variant is not
                // itself a heap structure
                debug_assert!(matches!(&path[0], alias::Field::Variant(_)));
                let path_fate = if &path[0] == &alias::Field::Variant(*variant_id) {
                    val_fate.fates[&path.clone().slice(1..)].clone()
                } else {
                    fate::FieldFate::new()
                };
                wrapped_fate.fates.insert(path, path_fate);
            }

            fate::ExprKind::UnwrapVariant(
                *variant_id,
                add_occurence(occurs, &mut uses, *wrapped, wrapped_fate),
            )
        }

        mutation::Expr::WrapBoxed(content, item_type) => {
            let content_fate = consumed_fate(&orig.custom_types, item_type, &expr_event);

            fate::ExprKind::WrapBoxed(
                add_occurence(occurs, &mut uses, *content, content_fate),
                item_type.clone(),
            )
        }

        mutation::Expr::UnwrapBoxed(wrapped, item_type) => {
            let mut wrapped_fate = fate::Fate::new();

            for (path, _) in get_refs_in(&orig.custom_types, item_type) {
                wrapped_fate.fates.insert(
                    path.clone().add_front(alias::Field::Boxed),
                    val_fate.fates[&path].clone(),
                );
            }

            wrapped_fate
                .fates
                .insert(Vector::new(), access_field_fate(expr_event.clone()));

            fate::ExprKind::UnwrapBoxed(
                add_occurence(occurs, &mut uses, *wrapped, wrapped_fate),
                item_type.clone(),
            )
        }

        mutation::Expr::WrapCustom(custom_id, content) => {
            let mut content_fate = fate::Fate::new();

            let content_type = &orig.custom_types[custom_id];
            for (content_path, _) in get_refs_in(&orig.custom_types, content_type) {
                let (_, alias::SubPath(sub_path)) = split_at_fold(*custom_id, content_path.clone());

                content_fate.fates.insert(
                    content_path,
                    val_fate.fates[&sub_path.add_front(alias::Field::Custom(*custom_id))].clone(),
                );
            }

            fate::ExprKind::WrapCustom(
                *custom_id,
                add_occurence(occurs, &mut uses, *content, content_fate),
            )
        }

        mutation::Expr::UnwrapCustom(custom_id, wrapped) => {
            let wrapped_type = anon::Type::Custom(*custom_id);
            let mut wrapped_fate = empty_fate(&orig.custom_types, &wrapped_type);

            let content_type = &orig.custom_types[custom_id];
            for (content_path, _) in get_refs_in(&orig.custom_types, content_type) {
                let (_, alias::SubPath(sub_path)) = split_at_fold(*custom_id, content_path.clone());

                merge_field_fates(
                    wrapped_fate
                        .fates
                        .get_mut(&sub_path.add_front(alias::Field::Custom(*custom_id)))
                        .unwrap(),
                    &val_fate.fates[&content_path],
                );
            }

            fate::ExprKind::UnwrapCustom(
                *custom_id,
                add_occurence(occurs, &mut uses, *wrapped, wrapped_fate),
            )
        }

        // NOTE [intrinsics]: If we add array intrinsics in the future, this will need to be
        // modified.
        mutation::Expr::Intrinsic(intr, arg) => fate::ExprKind::Intrinsic(
            *intr,
            add_occurence(occurs, &mut uses, *arg, fate::Fate::new()),
        ),

        mutation::Expr::ArrayOp(mutation::ArrayOp::Item(
            item_type,
            array_aliases,
            array_status,
            array,
            index,
        )) => {
            let mut array_fate = fate::Fate::new();

            for (item_path, _) in get_refs_in(&orig.custom_types, item_type) {
                // The first return value is the item
                let item_fate =
                    val_fate.fates[&item_path.clone().add_front(alias::Field::Field(0))].clone();

                // We don't need to consider any contribution of the returned hole array to the
                // array's fate, because the returned array is unconditionally retained and is
                // therefore essentially an unrelated object for the purposes of RC elision.

                array_fate
                    .fates
                    .insert(item_path.add_front(alias::Field::ArrayMembers), item_fate);
            }

            // Note: We assume the input array is always unconditionally retained to obtain the hole
            // array, so that this occurrence of the input array effectively does not escape this
            // expression for the purposes of RC elision.
            array_fate
                .fates
                .insert(Vector::new(), access_field_fate(expr_event.clone()));

            fate::ExprKind::ArrayOp(fate::ArrayOp::Item(
                item_type.clone(),
                array_aliases.clone(),
                array_status.clone(),
                add_occurence(occurs, &mut uses, *array, array_fate),
                add_occurence(occurs, &mut uses, *index, fate::Fate::new()),
            ))
        }

        mutation::Expr::ArrayOp(mutation::ArrayOp::Len(
            item_type,
            array_aliases,
            array_status,
            array,
        )) => {
            let mut array_fate = fate::Fate::new();

            for (item_path, _) in get_refs_in(&orig.custom_types, item_type) {
                array_fate.fates.insert(
                    item_path.add_front(alias::Field::ArrayMembers),
                    fate::FieldFate::new(),
                );
            }

            array_fate
                .fates
                .insert(Vector::new(), access_field_fate(expr_event.clone()));

            fate::ExprKind::ArrayOp(fate::ArrayOp::Len(
                item_type.clone(),
                array_aliases.clone(),
                array_status.clone(),
                add_occurence(occurs, &mut uses, *array, array_fate),
            ))
        }

        mutation::Expr::ArrayOp(mutation::ArrayOp::Push(
            item_type,
            array_aliases,
            array_status,
            array,
            item,
        )) => {
            let array_fate = consumed_fate(
                &orig.custom_types,
                &anon::Type::Array(Box::new(item_type.clone())),
                &expr_event,
            );

            let item_fate = consumed_fate(&orig.custom_types, item_type, &expr_event);

            fate::ExprKind::ArrayOp(fate::ArrayOp::Push(
                item_type.clone(),
                array_aliases.clone(),
                array_status.clone(),
                add_occurence(occurs, &mut uses, *array, array_fate),
                add_occurence(occurs, &mut uses, *item, item_fate),
            ))
        }

        mutation::Expr::ArrayOp(mutation::ArrayOp::Pop(
            item_type,
            array_aliases,
            array_status,
            array,
        )) => {
            let array_fate = consumed_fate(
                &orig.custom_types,
                &anon::Type::Array(Box::new(item_type.clone())),
                &expr_event,
            );

            fate::ExprKind::ArrayOp(fate::ArrayOp::Pop(
                item_type.clone(),
                array_aliases.clone(),
                array_status.clone(),
                add_occurence(occurs, &mut uses, *array, array_fate),
            ))
        }

        mutation::Expr::ArrayOp(mutation::ArrayOp::Replace(
            item_type,
            hole_array_aliases,
            hole_array_status,
            hole_array,
            item,
        )) => {
            let hole_array_fate = consumed_fate(
                &orig.custom_types,
                &anon::Type::HoleArray(Box::new(item_type.clone())),
                &expr_event,
            );

            let item_fate = consumed_fate(&orig.custom_types, item_type, &expr_event);

            fate::ExprKind::ArrayOp(fate::ArrayOp::Replace(
                item_type.clone(),
                hole_array_aliases.clone(),
                hole_array_status.clone(),
                add_occurence(occurs, &mut uses, *hole_array, hole_array_fate),
                add_occurence(occurs, &mut uses, *item, item_fate),
            ))
        }

        mutation::Expr::IoOp(mutation::IoOp::Input) => fate::ExprKind::IoOp(fate::IoOp::Input),

        mutation::Expr::IoOp(mutation::IoOp::Output(
            byte_array_aliases,
            byte_array_status,
            byte_array,
        )) => {
            let mut byte_array_fate = fate::Fate::new();
            byte_array_fate
                .fates
                .insert(Vector::new(), access_field_fate(expr_event.clone()));

            fate::ExprKind::IoOp(fate::IoOp::Output(
                byte_array_aliases.clone(),
                byte_array_status.clone(),
                add_occurence(occurs, &mut uses, *byte_array, byte_array_fate),
            ))
        }

        mutation::Expr::Panic(ret_type, byte_array_status, byte_array) => {
            let mut byte_array_fate = fate::Fate::new();
            byte_array_fate
                .fates
                .insert(Vector::new(), access_field_fate(expr_event.clone()));

            fate::ExprKind::Panic(
                ret_type.clone(),
                byte_array_status.clone(),
                add_occurence(occurs, &mut uses, *byte_array, byte_array_fate),
            )
        }

        mutation::Expr::ArrayLit(item_type, item_ids) => {
            let item_fate = consumed_fate(&orig.custom_types, item_type, &expr_event);

            let new_items = item_ids
                .iter()
                .map(|item| add_occurence(occurs, &mut uses, *item, item_fate.clone()))
                .collect();

            fate::ExprKind::ArrayLit(item_type.clone(), new_items)
        }

        mutation::Expr::BoolLit(val) => fate::ExprKind::BoolLit(*val),
        mutation::Expr::ByteLit(val) => fate::ExprKind::ByteLit(*val),
        mutation::Expr::IntLit(val) => fate::ExprKind::IntLit(*val),
        mutation::Expr::FloatLit(val) => fate::ExprKind::FloatLit(*val),
    };

    let id = expr_annots.push(fate::ExprAnnot {
        fate: val_fate,
        event: expr_event,
    });

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
                        last_internal_use: event::Horizon::new(),
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
    let mut expr_annots = IdVec::new();
    let mut calls = IdGen::new();
    let mut let_block_end_events = IdVec::new();
    let mut branch_block_end_events = IdVec::new();
    let (mut event_set, root_event_block) = event::EventSet::new();

    let (body_annot, body_uses) = annot_expr(
        orig,
        sigs,
        &mut locals,
        &func_def.body,
        ret_fate,
        &mut occurs,
        &mut expr_annots,
        &mut calls,
        &mut let_block_end_events,
        &mut branch_block_end_events,
        &mut event_set,
        root_event_block,
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
        expr_annots,
        num_calls: calls.count(),
        let_block_end_events,
        branch_block_end_events,
        profile_point: func_def.profile_point,
    }
}

pub fn annot_fates(program: mutation::Program) -> fate::Program {
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
