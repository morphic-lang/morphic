use std::collections::{BTreeMap, BTreeSet};

use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::purity::Purity;
use crate::data::repr_specialized_ast as special;
use crate::data::tail_rec_ast as tail;
use crate::util::graph::{self, Graph};
use crate::util::id_vec::IdVec;

fn last_index<T>(slice: &[T]) -> Option<usize> {
    if slice.is_empty() {
        None
    } else {
        Some(slice.len() - 1)
    }
}

// This function should only be called on 'expr' when the expression occurs in tail position.
fn add_tail_call_deps(
    deps: &mut BTreeSet<special::CustomFuncId>,
    vars_in_scope: usize,
    expr: &special::Expr,
) {
    match expr {
        special::Expr::Call(_purity, id, _arg) => {
            deps.insert(*id);
        }

        special::Expr::Branch(_discrim, cases, _result_type) => {
            for (_cond, body) in cases {
                add_tail_call_deps(deps, vars_in_scope, body);
            }
        }

        special::Expr::LetMany(bindings, final_local) => {
            if let Some(last_i) = last_index(bindings) {
                if final_local == &flat::LocalId(vars_in_scope + last_i) {
                    add_tail_call_deps(deps, vars_in_scope + last_i, &bindings[last_i].1);
                }
            }
        }

        _ => {}
    }
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum CallMode {
    AlwaysTail,
    // A function's call mode must be 'NotAlwaysTail' if it is called in non-tail position, *or* if
    // it is called in tail position from a function outside its tail call SCC.
    NotAlwaysTail,
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum Position {
    Tail,
    NotTail,
}

fn mark_call_modes(
    modes: &mut IdVec<special::CustomFuncId, CallMode>,
    curr_scc: &BTreeSet<special::CustomFuncId>,
    pos: Position,
    vars_in_scope: usize,
    expr: &special::Expr,
) {
    match expr {
        special::Expr::Call(_purity, id, _arg) => {
            if pos != Position::Tail || !curr_scc.contains(id) {
                modes[id] = CallMode::NotAlwaysTail;
            }
        }

        special::Expr::Branch(_discrim, cases, _result_type) => {
            for (_cond, body) in cases {
                mark_call_modes(modes, curr_scc, pos, vars_in_scope, body);
            }
        }

        special::Expr::LetMany(bindings, final_local) => {
            for (i, (_type, binding)) in bindings.iter().enumerate() {
                let sub_pos =
                    if i == bindings.len() && final_local == &flat::LocalId(vars_in_scope + i) {
                        pos
                    } else {
                        Position::NotTail
                    };

                mark_call_modes(modes, curr_scc, sub_pos, vars_in_scope + i, binding);
            }
        }

        _ => {}
    }
}

#[derive(Clone, Debug)]
enum FuncMapping {
    Direct(tail::CustomFuncId),
    Variant(
        tail::CustomFuncId,
        IdVec<first_ord::VariantId, special::Type>,
        first_ord::VariantId,
    ),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum EntryPoint {
    Direct,
    Single(tail::TailFuncId),
    Variants(IdVec<first_ord::VariantId, tail::TailFuncId>),
}

fn trans_expr(
    funcs: &IdVec<special::CustomFuncId, special::FuncDef>,
    mappings: &IdVec<special::CustomFuncId, Option<FuncMapping>>,
    local_tail_mappings: &BTreeMap<special::CustomFuncId, tail::TailFuncId>,
    pos: Position,
    vars_in_scope: usize,
    expr: &special::Expr,
) -> tail::Expr {
    match expr {
        special::Expr::Local(id) => tail::Expr::Local(*id),

        special::Expr::Call(purity, func, arg) => {
            if pos == Position::Tail && local_tail_mappings.contains_key(func) {
                tail::Expr::TailCall(local_tail_mappings[func], *arg)
            } else {
                match mappings[func]
                    .as_ref()
                    .expect("We should have marked this function as an entry point to its SCC")
                {
                    FuncMapping::Direct(new_func) => tail::Expr::Call(*purity, *new_func, *arg),

                    FuncMapping::Variant(new_func, variant_types, variant) => {
                        let local_wrapped_id = flat::LocalId(vars_in_scope);
                        let local_return_id = flat::LocalId(vars_in_scope + 1);

                        tail::Expr::LetMany(
                            vec![
                                (
                                    special::Type::Variants(variant_types.clone()),
                                    tail::Expr::WrapVariant(variant_types.clone(), *variant, *arg),
                                ),
                                (
                                    funcs[func].ret_type.clone(),
                                    tail::Expr::Call(*purity, *new_func, local_wrapped_id),
                                ),
                            ],
                            local_return_id,
                        )
                    }
                }
            }
        }

        special::Expr::Branch(discrim, cases, result_type) => tail::Expr::Branch(
            *discrim,
            cases
                .iter()
                .map(|(cond, body)| {
                    (
                        cond.clone(),
                        trans_expr(
                            funcs,
                            mappings,
                            local_tail_mappings,
                            pos,
                            vars_in_scope,
                            body,
                        ),
                    )
                })
                .collect(),
            result_type.clone(),
        ),

        special::Expr::LetMany(bindings, final_local) => tail::Expr::LetMany(
            bindings
                .iter()
                .enumerate()
                .map(|(i, (type_, binding))| {
                    let is_final_binding =
                        i == bindings.len() && final_local == &flat::LocalId(vars_in_scope + i);

                    let sub_pos = if is_final_binding {
                        pos
                    } else {
                        Position::NotTail
                    };

                    (
                        type_.clone(),
                        trans_expr(
                            funcs,
                            mappings,
                            local_tail_mappings,
                            sub_pos,
                            vars_in_scope + i,
                            binding,
                        ),
                    )
                })
                .collect(),
            *final_local,
        ),

        special::Expr::Tuple(items) => tail::Expr::Tuple(items.clone()),

        special::Expr::TupleField(tuple, idx) => tail::Expr::TupleField(*tuple, *idx),

        special::Expr::WrapVariant(variant_types, variant, content) => {
            tail::Expr::WrapVariant(variant_types.clone(), *variant, *content)
        }

        special::Expr::UnwrapVariant(variant, wrapped) => {
            tail::Expr::UnwrapVariant(*variant, *wrapped)
        }

        special::Expr::WrapCustom(custom, content) => tail::Expr::WrapCustom(*custom, *content),

        special::Expr::UnwrapCustom(custom, wrapped) => tail::Expr::UnwrapCustom(*custom, *wrapped),

        special::Expr::ArithOp(op) => tail::Expr::ArithOp(*op),

        special::Expr::ArrayOp(rep, item_type, op) => {
            tail::Expr::ArrayOp(*rep, item_type.clone(), *op)
        }

        special::Expr::IoOp(rep, op) => tail::Expr::IoOp(*rep, *op),

        special::Expr::ArrayLit(rep, item_type, items) => {
            tail::Expr::ArrayLit(*rep, item_type.clone(), items.clone())
        }

        &special::Expr::BoolLit(val) => tail::Expr::BoolLit(val),
        &special::Expr::ByteLit(val) => tail::Expr::ByteLit(val),
        &special::Expr::IntLit(val) => tail::Expr::IntLit(val),
        &special::Expr::FloatLit(val) => tail::Expr::FloatLit(val),
    }
}

pub fn tail_call_elim(program: special::Program) -> tail::Program {
    let tail_call_deps = Graph {
        edges_out: program.funcs.map(|_, func| {
            let mut deps = BTreeSet::new();
            // The argument always provides exactly one free variable in scope for the body of the
            // function.
            add_tail_call_deps(&mut deps, 1, &func.body);
            deps.into_iter().collect()
        }),
    };

    let sccs: IdVec<tail::CustomFuncId, _> =
        IdVec::from_items(graph::acyclic_and_cyclic_sccs(&tail_call_deps));

    let modes = {
        let mut modes = IdVec::from_items(vec![CallMode::AlwaysTail; program.funcs.len()]);

        // In principle, 'main' could be tail-recursive, so we need to make sure it still has an
        // entry point even in that case.  In other words, we need this because our logic that marks
        // call modes can't otherwise "see" that 'main' is called by something *outside the
        // program*!
        modes[program.main] = CallMode::NotAlwaysTail;

        for (_, scc) in &sccs {
            match scc {
                graph::Scc::Acyclic(id) => {
                    mark_call_modes(
                        &mut modes,
                        // 'curr_scc' doesn't matter, because there are no recursive tail calls
                        &BTreeSet::new(),
                        Position::Tail,
                        1,
                        &program.funcs[id].body,
                    );
                }

                graph::Scc::Cyclic(ids) => {
                    let curr_scc = ids.iter().cloned().collect::<BTreeSet<_>>();

                    for id in ids {
                        mark_call_modes(
                            &mut modes,
                            &curr_scc,
                            Position::Tail,
                            1,
                            &program.funcs[id].body,
                        );
                    }
                }
            }
        }

        modes
    };

    // 'mappings' specifies how to translate a non-tail-call to a given function in the source AST
    // to a call to the appropriate function in the target AST.  'mappings' provides information
    // about a function "from the outside", i.e. for use by its callers.
    //
    // 'entry_points' specifies how the 'body' of each target AST function should dispatch on its
    // argument.  Specifically, it records whether a target AST function's "calling convention" is
    // such that it has only a single entry point, or whether its entry point can be dynamically
    // controlled via a sum type argument.  'entry_points' provides information about a function
    // "from the inside", i.e. for use in generating its internal implementation.
    let (mappings, entry_points) = {
        let mut mappings: IdVec<special::CustomFuncId, Option<FuncMapping>> =
            IdVec::from_items(vec![None; program.funcs.len()]);

        let entry_points = sccs.map(|new_func_id, scc| match scc {
            graph::Scc::Acyclic(orig_id) => {
                debug_assert!(mappings[orig_id].is_none());
                mappings[orig_id] = Some(FuncMapping::Direct(new_func_id));

                EntryPoint::Direct
            }

            graph::Scc::Cyclic(orig_ids) => {
                let not_always_tail_funcs = orig_ids
                    .iter()
                    .enumerate()
                    .map(|(i, &orig_id)| (tail::TailFuncId(i), orig_id))
                    .filter(|(_, orig_id)| modes[orig_id] == CallMode::NotAlwaysTail)
                    .collect::<Vec<_>>();

                match not_always_tail_funcs.len() {
                    1 => {
                        let (entry_tail_id, entry_orig_id) = not_always_tail_funcs.first().unwrap();

                        mappings[*entry_orig_id] = Some(FuncMapping::Direct(new_func_id));

                        EntryPoint::Single(*entry_tail_id)
                    }

                    _ => {
                        let entry_variants: IdVec<
                            first_ord::VariantId,
                            (tail::TailFuncId, special::CustomFuncId),
                        > = IdVec::from_items(not_always_tail_funcs);

                        let variant_types = entry_variants
                            .map(|_, (_, orig_id)| program.funcs[orig_id].arg_type.clone());

                        for (variant_id, (_, orig_id)) in &entry_variants {
                            mappings[orig_id] = Some(FuncMapping::Variant(
                                new_func_id,
                                variant_types.clone(),
                                variant_id,
                            ));
                        }

                        EntryPoint::Variants(
                            entry_variants.map(|_, (tail_func_id, _)| *tail_func_id),
                        )
                    }
                }
            }
        });

        (mappings, entry_points)
    };

    let mut new_funcs = sccs.map(|new_func_id, scc| match scc {
        graph::Scc::Acyclic(orig_id) => {
            debug_assert_eq!(&entry_points[new_func_id], &EntryPoint::Direct);

            let orig_def = &program.funcs[orig_id];

            tail::FuncDef {
                tail_funcs: IdVec::new(),

                purity: orig_def.purity,
                arg_type: orig_def.arg_type.clone(),
                ret_type: orig_def.ret_type.clone(),
                body: trans_expr(
                    &program.funcs,
                    &mappings,
                    &BTreeMap::new(),
                    Position::Tail,
                    1,
                    &orig_def.body,
                ),
            }
        }

        graph::Scc::Cyclic(orig_ids) => {
            let local_tail_mappings = orig_ids
                .iter()
                .enumerate()
                .map(|(i, &orig_id)| (orig_id, tail::TailFuncId(i)))
                .collect::<BTreeMap<_, _>>();

            let ret_type = program.funcs[*orig_ids.first().unwrap()].ret_type.clone();
            debug_assert!(orig_ids
                .iter()
                .all(|orig_id| &program.funcs[orig_id].ret_type == &ret_type));

            let purity = program.funcs[*orig_ids.first().unwrap()].purity;
            debug_assert!(orig_ids
                .iter()
                .all(|orig_id| &program.funcs[orig_id].purity == &purity));

            let tail_funcs: IdVec<tail::TailFuncId, tail::TailFunc> = IdVec::from_items(
                orig_ids
                    .iter()
                    .map(|orig_id| {
                        let orig_def = &program.funcs[orig_id];

                        tail::TailFunc {
                            arg_type: orig_def.arg_type.clone(),
                            body: trans_expr(
                                &program.funcs,
                                &mappings,
                                &local_tail_mappings,
                                Position::Tail,
                                1,
                                &orig_def.body,
                            ),
                        }
                    })
                    .collect(),
            );

            let (entry_arg_type, entry_body) = match &entry_points[new_func_id] {
                EntryPoint::Direct => unreachable!(),

                EntryPoint::Single(entry_func_id) => {
                    let arg_type = program.funcs[orig_ids[entry_func_id.0]].arg_type.clone();

                    (
                        arg_type.clone(),
                        tail::Expr::TailCall(*entry_func_id, flat::ARG_LOCAL),
                    )
                }

                EntryPoint::Variants(entry_func_ids) => {
                    let arg_variant_types = entry_func_ids.map(|_, entry_func_id| {
                        program.funcs[orig_ids[entry_func_id.0]].arg_type.clone()
                    });

                    let body = tail::Expr::Branch(
                        flat::ARG_LOCAL,
                        entry_func_ids
                            .iter()
                            .map(|(variant_id, tail_func_id)| {
                                let unwrapped_var = flat::LocalId(1);
                                let call_result_var = flat::LocalId(2);

                                (
                                    special::Condition::Variant(
                                        variant_id,
                                        Box::new(special::Condition::Any),
                                    ),
                                    tail::Expr::LetMany(
                                        vec![
                                            (
                                                arg_variant_types[variant_id].clone(),
                                                tail::Expr::UnwrapVariant(
                                                    variant_id,
                                                    flat::ARG_LOCAL,
                                                ),
                                            ),
                                            (
                                                ret_type.clone(),
                                                tail::Expr::TailCall(*tail_func_id, unwrapped_var),
                                            ),
                                        ],
                                        call_result_var,
                                    ),
                                )
                            })
                            .collect(),
                        ret_type.clone(),
                    );

                    (special::Type::Variants(arg_variant_types), body)
                }
            };

            tail::FuncDef {
                tail_funcs,
                purity,
                arg_type: entry_arg_type,
                ret_type,
                body: entry_body,
            }
        }
    });

    let main = match &mappings[program.main] {
        None => unreachable!("main must be marked as an entry point for its tail call SCC"),

        Some(FuncMapping::Direct(tail_func_id)) => *tail_func_id,

        Some(FuncMapping::Variant(_, _, _)) => {
            let main_wrapper = tail::FuncDef {
                tail_funcs: IdVec::new(),

                purity: Purity::Impure,
                arg_type: special::Type::Tuple(Vec::new()),
                ret_type: special::Type::Tuple(Vec::new()),
                body: trans_expr(
                    &program.funcs,
                    &mappings,
                    &BTreeMap::new(),
                    Position::Tail,
                    1,
                    &special::Expr::Call(Purity::Impure, program.main, flat::ARG_LOCAL),
                ),
            };

            new_funcs.push(main_wrapper)
        }
    };

    tail::Program {
        mod_symbols: program.mod_symbols.clone(),
        custom_types: program.custom_types,
        funcs: new_funcs,
        main,
    }
}
