use crate::data::first_order_ast as first_ord;
use crate::data::metadata::Metadata;
use crate::data::obligation_annot_ast as ob;
use crate::data::purity::Purity;
use crate::data::rc_specialized_ast2 as rc;
use crate::data::tail_rec_ast::{self as tail, TailFuncSymbols};
use crate::util::graph::{self, Graph};
use crate::util::let_builder::{BuildMatch, FromBindings, LetManyBuilder};
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{Count, IdVec};
use std::collections::{BTreeMap, BTreeSet};

impl FromBindings for tail::Expr {
    type LocalId = rc::LocalId;
    type Type = rc::Type;

    fn from_bindings(bindings: Vec<(Self::Type, Self, Metadata)>, ret: Self::LocalId) -> Self {
        tail::Expr::LetMany(bindings, ret)
    }
}

impl BuildMatch for tail::Expr {
    type VariantId = first_ord::VariantId;

    fn bool_type() -> Self::Type {
        rc::Type::Bool
    }

    fn build_binding(
        builder: &mut crate::util::let_builder::LetManyBuilder<Self>,
        ty: Self::Type,
        expr: Self,
    ) -> Self::LocalId {
        builder.add_binding(ty, expr)
    }

    fn build_if(cond: Self::LocalId, then_expr: Self, else_expr: Self) -> Self {
        tail::Expr::If(cond, Box::new(then_expr), Box::new(else_expr))
    }

    fn build_check_variant(variant: Self::VariantId, local: Self::LocalId) -> Self {
        tail::Expr::CheckVariant(variant, local)
    }

    fn build_unwrap_variant(variant: Self::VariantId, local: Self::LocalId) -> Self {
        tail::Expr::UnwrapVariant(variant, local)
    }
}

fn last_index<T>(slice: &[T]) -> Option<usize> {
    if slice.is_empty() {
        None
    } else {
        Some(slice.len() - 1)
    }
}

// This function should only be called on 'expr' when the expression occurs in tail position.
fn add_tail_call_deps(
    deps: &mut BTreeSet<ob::CustomFuncId>,
    vars_in_scope: usize,
    expr: &rc::Expr,
) {
    match expr {
        rc::Expr::Call(_purity, id, _arg) => {
            deps.insert(*id);
        }

        rc::Expr::LetMany(bindings, final_local) => {
            if let Some(last_i) = last_index(bindings) {
                if final_local == &rc::LocalId(vars_in_scope + last_i) {
                    add_tail_call_deps(deps, vars_in_scope + last_i, &bindings[last_i].1);
                }
            }
        }

        rc::Expr::If(_discrim, then_case, else_case) => {
            add_tail_call_deps(deps, vars_in_scope, then_case);
            add_tail_call_deps(deps, vars_in_scope, else_case);
        }

        _ => {}
    }
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord)]
enum CallMode {
    AlwaysTail,
    // A function's call mode must be 'NotAlwaysTail' if it is called in non-tail position, *or* if
    // it is called in tail position from a function outside its tail call SCC.
    NotAlwaysTail,
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord)]
enum Position {
    Tail,
    NotTail,
}

fn mark_call_modes(
    modes: &mut IdVec<ob::CustomFuncId, CallMode>,
    curr_scc: &BTreeSet<ob::CustomFuncId>,
    pos: Position,
    vars_in_scope: usize,
    expr: &rc::Expr,
) {
    match expr {
        rc::Expr::Call(_purity, id, _arg) => {
            if pos != Position::Tail || !curr_scc.contains(id) {
                modes[id] = CallMode::NotAlwaysTail;
            }
        }

        rc::Expr::LetMany(bindings, final_local) => {
            for (i, (_type, binding, _)) in bindings.iter().enumerate() {
                let sub_pos =
                    if i + 1 == bindings.len() && final_local == &rc::LocalId(vars_in_scope + i) {
                        pos
                    } else {
                        Position::NotTail
                    };

                mark_call_modes(modes, curr_scc, sub_pos, vars_in_scope + i, binding);
            }
        }

        rc::Expr::If(_discrim, then_case, else_case) => {
            mark_call_modes(modes, curr_scc, pos, vars_in_scope, then_case);
            mark_call_modes(modes, curr_scc, pos, vars_in_scope, else_case);
        }

        _ => {}
    }
}

#[derive(Clone, Debug)]
enum FuncMapping {
    Direct(tail::CustomFuncId),
    Variant(
        tail::CustomFuncId,
        IdVec<first_ord::VariantId, rc::Type>,
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
    funcs: &IdVec<ob::CustomFuncId, rc::FuncDef>,
    mappings: &IdVec<ob::CustomFuncId, Option<FuncMapping>>,
    local_tail_mappings: &BTreeMap<ob::CustomFuncId, tail::TailFuncId>,
    pos: Position,
    vars_in_scope: usize,
    expr: &rc::Expr,
) -> tail::Expr {
    match expr {
        rc::Expr::Local(id) => tail::Expr::Local(*id),

        rc::Expr::Call(purity, func, arg) => {
            if pos == Position::Tail && local_tail_mappings.contains_key(func) {
                tail::Expr::TailCall(local_tail_mappings[func], *arg)
            } else {
                match mappings[func]
                    .as_ref()
                    .expect("We should have marked this function as an entry point to its SCC")
                {
                    FuncMapping::Direct(new_func) => tail::Expr::Call(*purity, *new_func, *arg),

                    FuncMapping::Variant(new_func, variant_types, variant) => {
                        let local_wrapped_id = rc::LocalId(vars_in_scope);
                        let local_return_id = rc::LocalId(vars_in_scope + 1);

                        tail::Expr::LetMany(
                            vec![
                                (
                                    rc::Type::Variants(variant_types.clone()),
                                    tail::Expr::WrapVariant(variant_types.clone(), *variant, *arg),
                                    Metadata::default(),
                                ),
                                (
                                    funcs[func].ret_type.clone(),
                                    tail::Expr::Call(*purity, *new_func, local_wrapped_id),
                                    Metadata::default(),
                                ),
                            ],
                            local_return_id,
                        )
                    }
                }
            }
        }

        rc::Expr::LetMany(bindings, final_local) => tail::Expr::LetMany(
            bindings
                .iter()
                .enumerate()
                .map(|(i, (type_, binding, metadata))| {
                    let is_final_binding =
                        i + 1 == bindings.len() && final_local == &rc::LocalId(vars_in_scope + i);

                    let sub_pos = if is_final_binding {
                        pos
                    } else {
                        Position::NotTail
                    };

                    let new_binding = trans_expr(
                        funcs,
                        mappings,
                        local_tail_mappings,
                        sub_pos,
                        vars_in_scope + i,
                        binding,
                    );

                    (type_.clone(), new_binding, metadata.clone())
                })
                .collect(),
            *final_local,
        ),

        rc::Expr::If(discrim, then_case, else_case) => tail::Expr::If(
            *discrim,
            Box::new(trans_expr(
                funcs,
                mappings,
                local_tail_mappings,
                pos,
                vars_in_scope,
                then_case,
            )),
            Box::new(trans_expr(
                funcs,
                mappings,
                local_tail_mappings,
                pos,
                vars_in_scope,
                else_case,
            )),
        ),

        rc::Expr::CheckVariant(variant_id, variant) => {
            tail::Expr::CheckVariant(*variant_id, *variant)
        }

        rc::Expr::Unreachable(ret_type) => tail::Expr::Unreachable(ret_type.clone()),

        rc::Expr::Tuple(items) => tail::Expr::Tuple(items.clone()),

        rc::Expr::TupleField(tuple, idx) => tail::Expr::TupleField(*tuple, *idx),

        rc::Expr::WrapVariant(variant_types, variant, content) => {
            tail::Expr::WrapVariant(variant_types.clone(), *variant, *content)
        }

        rc::Expr::UnwrapVariant(variant, wrapped) => tail::Expr::UnwrapVariant(*variant, *wrapped),

        rc::Expr::WrapBoxed(content, type_) => tail::Expr::WrapBoxed(*content, type_.clone()),

        rc::Expr::UnwrapBoxed(content, type_) => tail::Expr::UnwrapBoxed(*content, type_.clone()),

        rc::Expr::WrapCustom(custom, content) => tail::Expr::WrapCustom(*custom, *content),

        rc::Expr::UnwrapCustom(custom, wrapped) => tail::Expr::UnwrapCustom(*custom, *wrapped),

        rc::Expr::RcOp(op, local) => tail::Expr::RcOp(op.clone(), *local),

        rc::Expr::Intrinsic(intr, arg) => tail::Expr::Intrinsic(*intr, *arg),

        rc::Expr::ArrayOp(op) => tail::Expr::ArrayOp(op.clone()),

        rc::Expr::IoOp(op) => tail::Expr::IoOp(op.clone()),

        rc::Expr::Panic(ret_type, message) => tail::Expr::Panic(ret_type.clone(), *message),

        rc::Expr::ArrayLit(scheme, items) => tail::Expr::ArrayLit(scheme.clone(), items.clone()),

        &rc::Expr::BoolLit(val) => tail::Expr::BoolLit(val),
        &rc::Expr::ByteLit(val) => tail::Expr::ByteLit(val),
        &rc::Expr::IntLit(val) => tail::Expr::IntLit(val),
        &rc::Expr::FloatLit(val) => tail::Expr::FloatLit(val),
    }
}

pub fn tail_call_elim(program: rc::Program, progress: impl ProgressLogger) -> tail::Program {
    let progress = progress.start_session(None);

    let tail_call_deps = Graph {
        edges_out: program.funcs.map_refs(|_, func| {
            let mut deps = BTreeSet::new();
            // The argument always provides exactly one free variable in scope for the body of the
            // function.
            add_tail_call_deps(&mut deps, 1, &func.body);
            deps.into_iter().collect()
        }),
    };

    let sccs: IdVec<tail::CustomFuncId, _> =
        IdVec::from_vec(graph::acyclic_and_cyclic_sccs(&tail_call_deps));

    let modes = {
        let mut modes = IdVec::from_vec(vec![CallMode::AlwaysTail; program.funcs.len()]);

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
        let mut mappings: IdVec<ob::CustomFuncId, Option<FuncMapping>> =
            IdVec::from_vec(vec![None; program.funcs.len()]);

        let entry_points = sccs.map_refs(|new_func_id, scc| match scc {
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
                            (tail::TailFuncId, ob::CustomFuncId),
                        > = IdVec::from_vec(not_always_tail_funcs);

                        let variant_types = entry_variants
                            .map_refs(|_, (_, orig_id)| program.funcs[orig_id].arg_type.clone());

                        for (variant_id, (_, orig_id)) in &entry_variants {
                            mappings[orig_id] = Some(FuncMapping::Variant(
                                new_func_id,
                                variant_types.clone(),
                                variant_id,
                            ));
                        }

                        EntryPoint::Variants(
                            entry_variants.map(|_, (tail_func_id, _)| tail_func_id),
                        )
                    }
                }
            }
        });

        (mappings, entry_points)
    };

    let mut new_funcs = sccs.map_refs(|new_func_id, scc| match scc {
        graph::Scc::Acyclic(orig_id) => {
            debug_assert_eq!(&entry_points[new_func_id], &EntryPoint::Direct);

            let orig_def = &program.funcs[orig_id];

            tail::FuncDef {
                tail_funcs: IdVec::new(),
                tail_func_symbols: IdVec::new(),

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
                profile_point: orig_def.profile_point,
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

            let tail_funcs = IdVec::from_vec(
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
                            profile_point: orig_def.profile_point,
                        }
                    })
                    .collect(),
            );

            let tail_func_symbols = IdVec::from_vec(
                orig_ids
                    .iter()
                    .map(|orig_id| program.func_symbols[orig_id].clone())
                    .collect(),
            );

            let (entry_arg_type, entry_body) = match &entry_points[new_func_id] {
                EntryPoint::Direct => unreachable!(),

                EntryPoint::Single(entry_func_id) => {
                    let arg_type = program.funcs[orig_ids[entry_func_id.0]].arg_type.clone();

                    (
                        arg_type.clone(),
                        tail::Expr::TailCall(*entry_func_id, rc::ARG_LOCAL),
                    )
                }

                EntryPoint::Variants(entry_func_ids) => {
                    let arg_variant_types = entry_func_ids.map_refs(|_, entry_func_id| {
                        program.funcs[orig_ids[entry_func_id.0]].arg_type.clone()
                    });

                    let mut builder = LetManyBuilder::new(Count::from_value(1));

                    let match_ = tail::Expr::build_match(
                        &mut builder,
                        rc::ARG_LOCAL,
                        arg_variant_types.iter().map(|(id, ty)| (id, ty.clone())),
                        &ret_type,
                        || tail::Expr::Unreachable(ret_type.clone()),
                        |builder, variant_id, unwrapped| {
                            builder.add_binding(
                                ret_type.clone(),
                                tail::Expr::TailCall(entry_func_ids[variant_id], unwrapped),
                            )
                        },
                    );

                    let body = builder.to_expr(match_);
                    (rc::Type::Variants(arg_variant_types), body)
                }
            };

            tail::FuncDef {
                tail_funcs,
                tail_func_symbols,
                purity,
                arg_type: entry_arg_type,
                ret_type,
                body: entry_body,
                profile_point: None,
            }
        }
    });

    let new_func_symbols = sccs.map_refs(|_, scc| match scc {
        graph::Scc::Acyclic(orig_id) => {
            TailFuncSymbols::Acyclic(program.func_symbols[orig_id].clone())
        }
        graph::Scc::Cyclic(_) => TailFuncSymbols::Cyclic,
    });

    let main = match &mappings[program.main] {
        None => unreachable!("main must be marked as an entry point for its tail call SCC"),

        Some(FuncMapping::Direct(tail_func_id)) => *tail_func_id,

        Some(FuncMapping::Variant(_, _, _)) => {
            let main_wrapper = tail::FuncDef {
                tail_funcs: IdVec::new(),
                tail_func_symbols: IdVec::new(),

                purity: Purity::Impure,
                arg_type: rc::Type::Tuple(Vec::new()),
                ret_type: rc::Type::Tuple(Vec::new()),
                body: trans_expr(
                    &program.funcs,
                    &mappings,
                    &BTreeMap::new(),
                    Position::Tail,
                    1,
                    &rc::Expr::Call(Purity::Impure, program.main, rc::ARG_LOCAL),
                ),
                profile_point: None,
            };

            new_funcs.push(main_wrapper)
        }
    };

    progress.finish();

    tail::Program {
        mod_symbols: program.mod_symbols.clone(),
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs: new_funcs,
        func_symbols: new_func_symbols,
        schemes: program.schemes,
        profile_points: program.profile_points,
        main,
    }
}
