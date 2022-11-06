use im_rc::{OrdMap, OrdSet, Vector};
use std::collections::{BTreeMap, BTreeSet};

use crate::alias_spec_flag::lookup_concrete_cond;
use crate::cli;
use crate::data::alias_annot_ast as alias;
use crate::data::alias_specialized_ast as spec;
use crate::data::anon_sum_ast as anon;
use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast as mode;
use crate::field_path;
use crate::stack_path;
use crate::util::disjunction::Disj;
use crate::util::event_set as event;
use crate::util::graph::{strongly_connected, Graph};
use crate::util::id_vec::IdVec;
use crate::util::im_rc_ext::VectorExtensions;
use crate::util::inequality_graph as ineq;
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum OccurKind {
    Intermediate,
    Final,
    Unused,
}

// TODO: Should we unify this with `OccurKind`?
//
// TODO: Should this exist at all?  We may not actually care about the distinct between `Used` vs
// `Moved` in any code that consumes this type.
//
/// The ordering on this type is meaningful, with Used < Moved.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum UseKind {
    Used,
    Moved,
}

#[derive(Clone, Debug)]
struct FutureUses {
    uses: OrdMap<flat::LocalId, OrdMap<mode::StackPath, UseKind>>,
}

/// An `ExprUses` is conceptually a diff on a `FutureUses`.
///
/// Representing an expression's uses in terms of a diff, rather than in terms of a snapshot of all
/// future uses, is useful because it allows us to more efficiently merge the effects of different
/// arms of a `Branch` expression.  If we represented each branch arm's uses as a snapshot of all
/// future uses, we would be forced to merge the use flags of *every* variable used during or after
/// the branch, including uses which did not occur during the branch (and which therefore cannot
/// actually vary across arms of the branch).
///
/// This is somewhat analogous to how it is more efficient to perform a git diff than to diff raw
/// directories, because the git history provides extra information about which files changed since
/// the most recent common ancestor.
#[derive(Clone, Debug)]
struct ExprUses {
    uses: OrdMap<flat::LocalId, OrdMap<mode::StackPath, UseKind>>,
}

fn merge_uses(
    curr_uses: &mut OrdMap<flat::LocalId, OrdMap<mode::StackPath, UseKind>>,
    new_uses: &OrdMap<flat::LocalId, OrdMap<mode::StackPath, UseKind>>,
) {
    for (local, new_local_uses) in new_uses {
        for (path, new_use_kind) in new_local_uses {
            let curr_use_kind = curr_uses
                .entry(*local)
                .or_insert_with(OrdMap::new)
                .entry(path.clone())
                .or_insert(UseKind::Used);

            *curr_use_kind = (*curr_use_kind).max(*new_use_kind);
        }
    }
}

impl FutureUses {
    fn add_expr_uses(&mut self, expr_uses: &ExprUses) {
        merge_uses(&mut self.uses, &expr_uses.uses);
    }
}

#[derive(Clone, Debug)]
enum DeclarationSite {
    Arg,
    Block(fate::LetBlockId),
}

// TODO: Borrowing the type here is a good idea.  We should modify other passes to do this too.
#[derive(Clone, Debug)]
struct MarkOccurLocalInfo<'a> {
    type_: &'a anon::Type,
    decl_site: DeclarationSite,
}

type MarkOccurContext<'a> = LocalContext<flat::LocalId, MarkOccurLocalInfo<'a>>;

fn mark_occur(
    typedefs: &flat::CustomTypes,
    local_info: &MarkOccurLocalInfo,
    fate: &fate::Fate,
    ret_fates: &BTreeMap<alias::RetName, spec::RetFate>,
    future_uses_after_expr: Option<&OrdMap<mode::StackPath, UseKind>>,
    future_uses_in_expr: Option<&OrdMap<mode::StackPath, UseKind>>,
    extra_owned: Option<&BTreeSet<mode::StackPath>>,
) -> BTreeMap<mode::StackPath, OccurKind> {
    let mut result = BTreeMap::new();

    for path in stack_path::stack_paths_in(typedefs, &local_info.type_) {
        let used_after_expr = future_uses_after_expr
            .map(|uses| uses.contains_key(&path))
            .unwrap_or(false);

        let used_later_in_expr = future_uses_in_expr
            .map(|uses| uses.contains_key(&path))
            .unwrap_or(false);

        if used_after_expr || used_later_in_expr {
            result.insert(path, OccurKind::Intermediate);
            continue;
        }

        // If we didn't 'continue' out of the previous check, we know this path will never be used
        // again within the function.

        let path_fate = &fate.fates[&stack_path::to_field_path(&path)];

        let escapes_function = path_fate
            .ret_destinations
            .iter()
            .any(|ret_dest| ret_fates[ret_dest] == spec::RetFate::MaybeUsed);

        if escapes_function {
            result.insert(path, OccurKind::Final);
            continue;
        }

        let escapes_decl_block = match local_info.decl_site {
            DeclarationSite::Arg => false,
            DeclarationSite::Block(decl_block) => path_fate.blocks_escaped.contains(&decl_block),
        };

        if escapes_decl_block {
            result.insert(path, OccurKind::Final);
            continue;
        }

        match path_fate.internal {
            fate::InternalFate::Owned => {
                result.insert(path, OccurKind::Final);
            }
            fate::InternalFate::Accessed => {
                let is_extra_owned = extra_owned
                    .map(|extra_owned| extra_owned.contains(&path))
                    .unwrap_or(false);

                if is_extra_owned {
                    result.insert(path, OccurKind::Final);
                } else {
                    result.insert(path, OccurKind::Intermediate);
                }
            }
            fate::InternalFate::Unused => {
                result.insert(path, OccurKind::Unused);
            }
        }
    }

    result
}

fn mark_occur_mut<'a>(
    typedefs: &flat::CustomTypes,
    locals: &MarkOccurContext<'a>,
    occur_fates: &IdVec<fate::OccurId, fate::Fate>,
    ret_fates: &BTreeMap<alias::RetName, spec::RetFate>,
    occur: fate::Local,
    future_uses: &FutureUses,
    expr_uses: &mut ExprUses,
    occur_kinds: &mut IdVec<fate::OccurId, Option<BTreeMap<mode::StackPath, OccurKind>>>,
    extra_owned: &BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>,
) {
    let this_occur_kinds = mark_occur(
        typedefs,
        locals.local_binding(occur.1),
        &occur_fates[occur.0],
        ret_fates,
        future_uses.uses.get(&occur.1),
        expr_uses.uses.get(&occur.1),
        extra_owned.get(&occur.1),
    );

    for (path, path_occur_kind) in &this_occur_kinds {
        let new_use_kind = match path_occur_kind {
            OccurKind::Intermediate => Some(UseKind::Used),
            OccurKind::Final => Some(UseKind::Moved),
            OccurKind::Unused => None,
        };

        if let Some(new_use_kind) = new_use_kind {
            let curr_expr_use = expr_uses
                .uses
                .entry(occur.1)
                .or_insert_with(OrdMap::new)
                .entry(path.clone())
                .or_insert(UseKind::Used);

            *curr_expr_use = (*curr_expr_use).max(new_use_kind);
        }
    }

    debug_assert!(occur_kinds[occur.0].is_none());
    occur_kinds[occur.0] = Some(this_occur_kinds);
}

// Marking tentative prologue drops doesn't contribute to expression uses, because when we mark a
// prologue drop we're not sure yet whether or not it will be pruned later due to a prior `Final`
// use of the same variable.  We don't want to foreclose the possibility of the variable in the drop
// prologue being moved earlier for some other reason.
fn mark_tentative_prologue_drops(
    future_uses: &FutureUses,
    expr_uses: &ExprUses,
    to_be_mutated: &BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>,
    tentative_drop_prologue: &mut BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>,
) {
    for (local, mutated_paths) in to_be_mutated {
        for mutated_path in mutated_paths {
            let used_after_expr = future_uses
                .uses
                .get(local)
                .map(|uses| uses.contains_key(mutated_path))
                .unwrap_or(false);

            let used_later_in_expr = expr_uses
                .uses
                .get(local)
                .map(|uses| uses.contains_key(mutated_path))
                .unwrap_or(false);

            if used_after_expr || used_later_in_expr {
                continue;
            }

            tentative_drop_prologue
                .entry(*local)
                .or_insert_with(BTreeSet::new)
                .insert(mutated_path.clone());
        }
    }
}

fn mutations_from_aliases(
    typedefs: &flat::CustomTypes,
    version_aliases: &BTreeMap<alias::AliasCondition, spec::ConcreteAlias>,
    aliases: &alias::LocalAliases,
) -> BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>> {
    let mut result = BTreeMap::new();
    for ((other, other_path), cond) in &aliases.aliases {
        for other_stack_path in
            stack_path::split_stack_heap_3(typedefs, other_path.clone()).stack_paths()
        {
            if lookup_concrete_cond(version_aliases, cond) {
                result
                    .entry(*other)
                    .or_insert_with(BTreeSet::new)
                    .insert(other_stack_path.clone());
            }
        }
    }
    result
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Position {
    Tail,
    NotTail,
}

// This is a backwards data-flow pass, so all variable occurrences should be processed in reverse
// order, both across expressions and within each expression.
//
// TODO: This doesn't have great asymptotics for deeply nested expressions, e.g. long chains of
// if/else-if branches.  Can we do better?
fn mark_expr_occurs<'a>(
    orig: &spec::Program,
    scc: &BTreeSet<(first_ord::CustomFuncId, spec::FuncVersionId)>,
    this_version: &spec::FuncVersion,
    locals: &mut MarkOccurContext<'a>,
    occur_fates: &IdVec<fate::OccurId, fate::Fate>,
    future_uses: &FutureUses,
    position: Position,
    expr: &'a fate::Expr,
    occur_kinds: &mut IdVec<fate::OccurId, Option<BTreeMap<mode::StackPath, OccurKind>>>,
    tentative_drop_prologues: &mut IdVec<
        fate::ExprId,
        Option<BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>>,
    >,
) -> ExprUses {
    debug_assert!(future_uses
        .uses
        .get_max()
        .map(|(flat::LocalId(max_id), _)| *max_id < locals.len())
        .unwrap_or(true));

    let mut expr_uses = ExprUses {
        uses: OrdMap::new(),
    };

    let mut tentative_drop_prologue = BTreeMap::new();

    // We need to pass `locals`, `occur_kinds`, and `expr_uses` as arguments to appease the borrow
    // checker.
    let mark_with_extra_owned =
        |locals: &mut MarkOccurContext<'a>,
         occur_kinds: &mut IdVec<fate::OccurId, Option<BTreeMap<mode::StackPath, OccurKind>>>,
         expr_uses: &mut ExprUses,
         occur: fate::Local,
         to_be_mutated: &BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>| {
            mark_occur_mut(
                &orig.custom_types,
                locals,
                occur_fates,
                &this_version.ret_fate,
                occur,
                future_uses,
                expr_uses,
                occur_kinds,
                &to_be_mutated,
            );
        };

    let mark =
        |locals: &mut MarkOccurContext<'a>,
         occur_kinds: &mut IdVec<fate::OccurId, Option<BTreeMap<mode::StackPath, OccurKind>>>,
         expr_uses: &mut ExprUses,
         occur: fate::Local| {
            mark_with_extra_owned(locals, occur_kinds, expr_uses, occur, &BTreeMap::new());
        };

    match &expr.kind {
        fate::ExprKind::Local(local) => {
            mark(locals, occur_kinds, &mut expr_uses, *local);
        }

        fate::ExprKind::Call(call_id, _, callee, arg_aliases, _, arg) => {
            debug_assert_eq!(&this_version.calls[call_id].0, callee);
            let is_tail_rec_call =
                position == Position::Tail && scc.contains(&this_version.calls[call_id]);

            let extra_owned = if is_tail_rec_call {
                // For a tail-recursive call, we want to ensure that all drops happen *before* the
                // tail call, so in this case `extra_owned` should be *every variable in scope*.
                (0..locals.len())
                    .map(flat::LocalId)
                    .map(|local_id| {
                        let type_ = locals.local_binding(local_id).type_;
                        (
                            local_id,
                            stack_path::stack_paths_in(&orig.custom_types, type_)
                                .into_iter()
                                .collect(),
                        )
                    })
                    .collect()
            } else {
                // It's not important for `to_be_mutated` to contain directly / unconditionally
                // mutated paths in the argument, because those will already be annotated with
                // "owned" fates by fate analysis.  We only care about collecting paths which are
                // mutated *indirectly* via aliases, and which fate analysis therefore can't catch.
                let mut to_be_mutated = BTreeMap::new();
                for (alias::ArgName(arg_field_path), callee_cond) in
                    &orig.funcs[callee].mutation_sig.arg_mutation_conds
                {
                    match callee_cond {
                        Disj::True => {
                            // We don't need to consult the argument's folded aliases here, because
                            // any two argument field paths related by a folded alias will collapse
                            // down to the same stack path.
                            //
                            // Also, note that even if we were to miss a potential mutation here
                            // (which doesn't appear to be possible, but there could always be
                            // bugs...), that would only result in a precision / optimization issue,
                            // and wouldn't threaten soundness.  Even if we were to set
                            // `to_be_mutated` to the empty map for all calls, RC elision would
                            // remain perfectly sound (but could result in deoptimizations in
                            // downstream mutation optimization passes).
                            for ((other_local, other_field_path), symbolic_cond) in
                                &arg_aliases[arg_field_path].aliases
                            {
                                let concretely_aliased =
                                    lookup_concrete_cond(&this_version.aliases, symbolic_cond);

                                if concretely_aliased {
                                    for other_stack_path in stack_path::split_stack_heap_3(
                                        &orig.custom_types,
                                        other_field_path.clone(),
                                    )
                                    .stack_paths()
                                    {
                                        to_be_mutated
                                            .entry(*other_local)
                                            .or_insert_with(BTreeSet::new)
                                            .insert(other_stack_path);
                                    }
                                }
                            }
                        }
                        Disj::Any(_) => {
                            // If this mutation occurs, it's due to an alias edge, so we don't need
                            // to explicitly handle it here; if it occurs under the current set of
                            // concrete aliasing edges for this version of the function, we'll
                            // propagate it via the aliases incident on an unconditionally mutated
                            // path.
                            //
                            // TODO: Could we do this in mutation analysis as well?  Maybe mutation
                            // signatures only need to explicitly store the *unconditionally*
                            // mutated argument names?
                        }
                    }
                }

                to_be_mutated
            };

            mark_with_extra_owned(locals, occur_kinds, &mut expr_uses, *arg, &extra_owned);

            mark_tentative_prologue_drops(
                future_uses,
                &expr_uses,
                &extra_owned,
                &mut tentative_drop_prologue,
            );
        }

        fate::ExprKind::Branch(discrim, cases, _ret_type) => {
            // TODO: This was the only place where branch block ids were originally intended to be
            // used. Should we remove them now that we don't use them here?
            for (_, _cond, body, _) in cases {
                let case_uses = mark_expr_occurs(
                    orig,
                    scc,
                    this_version,
                    locals,
                    occur_fates,
                    future_uses,
                    position,
                    body,
                    occur_kinds,
                    tentative_drop_prologues,
                );

                merge_uses(&mut expr_uses.uses, &case_uses.uses);
            }

            mark(locals, occur_kinds, &mut expr_uses, *discrim);
        }

        fate::ExprKind::LetMany(block_id, bindings, _final_ctx, final_local) => {
            // We're only using `with_scope` here for its debug assertion, and to signal intent; by
            // the time the passed closure returns, we've manually truncated away all the variables
            // which it would usually be `with_scope`'s responsibility to remove.
            locals.with_scope(|sub_locals| {
                let locals_offset = sub_locals.len();

                for (type_, _) in bindings {
                    sub_locals.add_local(MarkOccurLocalInfo {
                        type_,
                        decl_site: DeclarationSite::Block(*block_id),
                    });
                }

                // This is for internal bookkeeping only.  It doesn't leave this call's scope.
                let mut internal_future_uses = future_uses.clone();

                // We can't use `mark` here because of an obscure borrow checker error.
                //
                // Actually, we *can* we use `mark` here, but only if we annotate its type signature
                // explicitly with a higher-rank trait bound, and make it a `dyn` closure (because
                // `impl Trait` on variables isn't supported).  It's not worth it.
                mark_occur_mut(
                    &orig.custom_types,
                    sub_locals,
                    occur_fates,
                    &this_version.ret_fate,
                    *final_local,
                    future_uses,
                    &mut expr_uses,
                    occur_kinds,
                    &BTreeMap::new(),
                );
                internal_future_uses.add_expr_uses(&expr_uses);

                for (idx, (_, rhs)) in bindings.iter().enumerate().rev() {
                    let binding_local = flat::LocalId(idx + locals_offset);

                    // NOTE: After truncation, `sub_locals` contains all locals *strictly* before
                    // `binding_local`.
                    sub_locals.truncate(binding_local.0);
                    internal_future_uses.uses.remove(&binding_local);

                    let rhs_position = if idx + 1 == bindings.len()
                        && flat::LocalId(locals_offset + idx) == final_local.1
                    {
                        position
                    } else {
                        Position::NotTail
                    };

                    let rhs_uses = mark_expr_occurs(
                        orig,
                        scc,
                        this_version,
                        sub_locals,
                        occur_fates,
                        &internal_future_uses,
                        rhs_position,
                        rhs,
                        occur_kinds,
                        tentative_drop_prologues,
                    );
                    internal_future_uses.add_expr_uses(&rhs_uses);
                    merge_uses(&mut expr_uses.uses, &rhs_uses.uses);
                }

                // We need to clean up `expr_uses` so it contains only variables in the enclosing
                // scope (outside this let block).
                for bound_local in
                    (locals_offset..locals_offset + bindings.len()).map(flat::LocalId)
                {
                    expr_uses.uses.remove(&bound_local);
                }
            });
        }

        fate::ExprKind::Tuple(items) => {
            for item in items {
                mark(locals, occur_kinds, &mut expr_uses, *item);
            }
        }

        fate::ExprKind::TupleField(tuple, _index) => {
            mark(locals, occur_kinds, &mut expr_uses, *tuple);
        }

        fate::ExprKind::WrapVariant(_variant_types, _variant_id, content) => {
            mark(locals, occur_kinds, &mut expr_uses, *content);
        }

        fate::ExprKind::UnwrapVariant(_variant_id, wrapped) => {
            mark(locals, occur_kinds, &mut expr_uses, *wrapped);
        }

        fate::ExprKind::WrapBoxed(content, _item_type) => {
            mark(locals, occur_kinds, &mut expr_uses, *content);
        }

        fate::ExprKind::UnwrapBoxed(wrapped, _item_type, _, _) => {
            mark(locals, occur_kinds, &mut expr_uses, *wrapped);
        }

        fate::ExprKind::WrapCustom(_custom_id, content) => {
            mark(locals, occur_kinds, &mut expr_uses, *content);
        }

        fate::ExprKind::UnwrapCustom(_custom_id, content) => {
            mark(locals, occur_kinds, &mut expr_uses, *content);
        }

        fate::ExprKind::Intrinsic(_intr, arg) => {
            mark(locals, occur_kinds, &mut expr_uses, *arg);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Get(_item_type, _aliases, array, index, _, _)) => {
            mark(locals, occur_kinds, &mut expr_uses, *array);
            mark(locals, occur_kinds, &mut expr_uses, *index);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Extract(
            _item_type,
            array_aliases,
            array,
            index,
        )) => {
            let to_be_mutated =
                mutations_from_aliases(&orig.custom_types, &this_version.aliases, array_aliases);
            mark_with_extra_owned(locals, occur_kinds, &mut expr_uses, *array, &to_be_mutated);
            mark_with_extra_owned(locals, occur_kinds, &mut expr_uses, *index, &to_be_mutated);
            mark_tentative_prologue_drops(
                future_uses,
                &expr_uses,
                &to_be_mutated,
                &mut tentative_drop_prologue,
            );
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Len(_item_type, _aliases, array)) => {
            mark(locals, occur_kinds, &mut expr_uses, *array);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Push(_item_type, array_aliases, array, item)) => {
            let to_be_mutated =
                mutations_from_aliases(&orig.custom_types, &this_version.aliases, array_aliases);
            mark_with_extra_owned(locals, occur_kinds, &mut expr_uses, *array, &to_be_mutated);
            mark_with_extra_owned(locals, occur_kinds, &mut expr_uses, *item, &to_be_mutated);
            mark_tentative_prologue_drops(
                future_uses,
                &expr_uses,
                &to_be_mutated,
                &mut tentative_drop_prologue,
            );
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Pop(_item_type, array_aliases, array)) => {
            let to_be_mutated =
                mutations_from_aliases(&orig.custom_types, &this_version.aliases, array_aliases);
            mark_with_extra_owned(locals, occur_kinds, &mut expr_uses, *array, &to_be_mutated);
            mark_tentative_prologue_drops(
                future_uses,
                &expr_uses,
                &to_be_mutated,
                &mut tentative_drop_prologue,
            );
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Replace(
            _item_type,
            hole_array_aliases,
            hole_array,
            item,
        )) => {
            let to_be_mutated = mutations_from_aliases(
                &orig.custom_types,
                &this_version.aliases,
                hole_array_aliases,
            );
            mark_with_extra_owned(
                locals,
                occur_kinds,
                &mut expr_uses,
                *hole_array,
                &to_be_mutated,
            );
            mark_with_extra_owned(locals, occur_kinds, &mut expr_uses, *item, &to_be_mutated);
            mark_tentative_prologue_drops(
                future_uses,
                &expr_uses,
                &to_be_mutated,
                &mut tentative_drop_prologue,
            );
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Reserve(
            _item_type,
            array_aliases,
            array,
            capacity,
        )) => {
            let to_be_mutated =
                mutations_from_aliases(&orig.custom_types, &this_version.aliases, array_aliases);
            mark_with_extra_owned(locals, occur_kinds, &mut expr_uses, *array, &to_be_mutated);
            mark_with_extra_owned(
                locals,
                occur_kinds,
                &mut expr_uses,
                *capacity,
                &to_be_mutated,
            );
            mark_tentative_prologue_drops(
                future_uses,
                &expr_uses,
                &to_be_mutated,
                &mut tentative_drop_prologue,
            );
        }

        fate::ExprKind::IoOp(fate::IoOp::Input) => {}

        fate::ExprKind::IoOp(fate::IoOp::Output(_aliases, byte_array)) => {
            mark(locals, occur_kinds, &mut expr_uses, *byte_array);
        }

        fate::ExprKind::Panic(_aliases, message) => {
            mark(locals, occur_kinds, &mut expr_uses, *message);
        }

        fate::ExprKind::ArrayLit(_item_type, items) => {
            for item in items {
                mark(locals, occur_kinds, &mut expr_uses, *item);
            }
        }

        fate::ExprKind::BoolLit(_) => {}
        fate::ExprKind::ByteLit(_) => {}
        fate::ExprKind::IntLit(_) => {}
        fate::ExprKind::FloatLit(_) => {}
    }

    debug_assert!(expr_uses
        .uses
        .get_max()
        .map(|(flat::LocalId(max_id), _)| *max_id < locals.len())
        .unwrap_or(true));

    debug_assert!(tentative_drop_prologues[expr.id].is_none());
    tentative_drop_prologues[expr.id] = Some(tentative_drop_prologue);

    expr_uses
}

#[derive(Clone, Debug)]
struct MarkedOccurs {
    occur_kinds: IdVec<fate::OccurId, BTreeMap<mode::StackPath, OccurKind>>,
    tentative_drop_prologues:
        IdVec<fate::ExprId, BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>>,
}

fn mark_func_occurs(
    program: &spec::Program,
    scc: &BTreeSet<(first_ord::CustomFuncId, spec::FuncVersionId)>,
    func_def: &spec::FuncDef,
    version: &spec::FuncVersion,
) -> MarkedOccurs {
    let mut occur_kinds = IdVec::from_items(vec![None; func_def.occur_fates.len()]);
    let mut tentative_drop_prologues = IdVec::from_items(vec![None; func_def.expr_annots.len()]);

    let mut locals = LocalContext::new();
    locals.add_local(MarkOccurLocalInfo {
        type_: &func_def.arg_type,
        decl_site: DeclarationSite::Arg,
    });

    let body_uses = mark_expr_occurs(
        program,
        scc,
        version,
        &mut locals,
        &func_def.occur_fates,
        &FutureUses {
            uses: OrdMap::new(),
        },
        Position::Tail,
        &func_def.body,
        &mut occur_kinds,
        &mut tentative_drop_prologues,
    );

    debug_assert!(body_uses.uses.keys().all(|&local| local == flat::ARG_LOCAL));

    MarkedOccurs {
        occur_kinds: occur_kinds.into_mapped(|_, kinds| kinds.unwrap()),
        tentative_drop_prologues: tentative_drop_prologues
            .into_mapped(|_, prologue| prologue.unwrap()),
    }
}

#[derive(Clone, Debug)]
struct PastMoves {
    moves: OrdMap<flat::LocalId, OrdSet<mode::StackPath>>,
}

/// An `ExprMoves` is conceptually a diff on a `PastMoves`
#[derive(Clone, Debug)]
struct ExprMoves {
    moves: OrdMap<flat::LocalId, OrdSet<mode::StackPath>>,
}

fn merge_moves(
    curr_moves: &mut OrdMap<flat::LocalId, OrdSet<mode::StackPath>>,
    new_moves: &OrdMap<flat::LocalId, OrdSet<mode::StackPath>>,
) {
    for (local, new_local_moves) in new_moves {
        curr_moves
            .entry(*local)
            .or_insert_with(OrdSet::new)
            .extend(new_local_moves.iter().cloned())
    }
}

fn add_move(
    occur_kinds: &IdVec<fate::OccurId, BTreeMap<mode::StackPath, OccurKind>>,
    expr_moves: &mut ExprMoves,
    occur: fate::Local,
) {
    for (path, kind) in &occur_kinds[occur.0] {
        match kind {
            OccurKind::Intermediate | OccurKind::Unused => {}
            OccurKind::Final => {
                expr_moves
                    .moves
                    .entry(occur.1)
                    .or_insert_with(OrdSet::new)
                    .insert(path.clone());
            }
        }
    }
}

fn get_missing_drops(
    typedefs: &flat::CustomTypes,
    moves_for_local: Option<&OrdSet<mode::StackPath>>,
    type_: &anon::Type,
) -> BTreeSet<mode::StackPath> {
    let mut result = BTreeSet::new();
    for path in stack_path::stack_paths_in(typedefs, type_) {
        let already_moved = moves_for_local
            .map(|moves| moves.contains(&path))
            .unwrap_or(false);
        if !already_moved {
            result.insert(path);
        }
    }
    result
}

fn repair_expr_drops<'a>(
    typedefs: &flat::CustomTypes,
    num_locals: usize,
    occur_kinds: &IdVec<fate::OccurId, BTreeMap<mode::StackPath, OccurKind>>,
    drop_prologues: &mut IdVec<fate::ExprId, BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>>,
    let_drop_epilogues: &mut IdVec<
        fate::LetBlockId,
        Option<BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>>,
    >,
    branch_drop_epilogues: &mut IdVec<
        fate::BranchBlockId,
        Option<BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>>,
    >,
    past_moves: &PastMoves,
    expr: &fate::Expr,
) -> ExprMoves {
    debug_assert!(past_moves
        .moves
        .get_max()
        .map(|(max_local, _)| max_local.0 < num_locals)
        .unwrap_or(true));

    let mut expr_moves = ExprMoves {
        moves: OrdMap::new(),
    };

    for (local, drops) in &mut drop_prologues[expr.id] {
        let mut to_remove = Vec::new();
        for path in drops.iter() {
            if past_moves
                .moves
                .get(local)
                .map(|local_moves| local_moves.contains(path))
                .unwrap_or(false)
            {
                to_remove.push(path.clone());
            } else {
                expr_moves
                    .moves
                    .entry(*local)
                    .or_insert_with(OrdSet::new)
                    .insert(path.clone());
            }
        }

        for path in to_remove {
            drops.remove(&path);
        }
    }

    match &expr.kind {
        fate::ExprKind::Local(local) => {
            add_move(occur_kinds, &mut expr_moves, *local);
        }

        fate::ExprKind::Call(_, _, _, _, _, local) => {
            add_move(occur_kinds, &mut expr_moves, *local);
        }

        fate::ExprKind::Branch(discrim, cases, _) => {
            add_move(occur_kinds, &mut expr_moves, *discrim);
            debug_assert!(expr_moves.moves.is_empty());

            let block_moves = cases
                .iter()
                .map(|(block_id, _, body, _final_ctx)| {
                    (
                        *block_id,
                        repair_expr_drops(
                            typedefs,
                            num_locals,
                            occur_kinds,
                            drop_prologues,
                            let_drop_epilogues,
                            branch_drop_epilogues,
                            past_moves,
                            body,
                        ),
                    )
                })
                .collect::<Vec<_>>();

            // Collect the union of moves across all arms
            for (_, moves) in &block_moves {
                merge_moves(&mut expr_moves.moves, &moves.moves);
            }

            // We compare each arm's individual moves to the union of all moves across all arms, and
            // add drop epilogues as necessary to ensure all arms have the same set of moves.
            for (block_id, this_block_moves) in &block_moves {
                let mut block_drop_epilogue = BTreeMap::new();

                for (local, all_block_local_moves) in &expr_moves.moves {
                    for path in all_block_local_moves {
                        let moved_by_block = this_block_moves
                            .moves
                            .get(local)
                            .map(|this_block_local_moves| this_block_local_moves.contains(path))
                            .unwrap_or(false);

                        if !moved_by_block {
                            block_drop_epilogue
                                .entry(*local)
                                .or_insert_with(BTreeSet::new)
                                .insert(path.clone());
                        }
                    }
                }

                debug_assert!(branch_drop_epilogues[block_id].is_none());
                branch_drop_epilogues[block_id] = Some(block_drop_epilogue.into_iter().collect());
            }
        }

        fate::ExprKind::LetMany(block_id, bindings, _final_ctx, final_local) => {
            let mut internal_past_moves = past_moves.clone();

            for (offset, (_type, rhs)) in bindings.iter().enumerate() {
                let rhs_moves = repair_expr_drops(
                    typedefs,
                    num_locals + offset,
                    occur_kinds,
                    drop_prologues,
                    let_drop_epilogues,
                    branch_drop_epilogues,
                    &internal_past_moves,
                    rhs,
                );

                merge_moves(&mut internal_past_moves.moves, &rhs_moves.moves);
                merge_moves(&mut expr_moves.moves, &rhs_moves.moves);
            }

            add_move(occur_kinds, &mut expr_moves, *final_local);

            let mut drop_epilogue = BTreeMap::new();
            for (offset, (type_, _)) in bindings.iter().enumerate() {
                let local_id = flat::LocalId(num_locals + offset);
                drop_epilogue.insert(
                    local_id,
                    get_missing_drops(typedefs, expr_moves.moves.get(&local_id), type_),
                );
            }

            debug_assert!(let_drop_epilogues[block_id].is_none());
            let_drop_epilogues[block_id] = Some(drop_epilogue.into_iter().collect());

            for local_id in (num_locals..num_locals + bindings.len()).map(flat::LocalId) {
                expr_moves.moves.remove(&local_id);
            }
        }

        fate::ExprKind::Tuple(items) => {
            for item in items {
                add_move(occur_kinds, &mut expr_moves, *item);
            }
        }

        fate::ExprKind::TupleField(tuple, _index) => {
            add_move(occur_kinds, &mut expr_moves, *tuple);
        }

        fate::ExprKind::WrapVariant(_variant_types, _variant_id, content) => {
            add_move(occur_kinds, &mut expr_moves, *content);
        }

        fate::ExprKind::UnwrapVariant(_variant_id, wrapped) => {
            add_move(occur_kinds, &mut expr_moves, *wrapped);
        }

        fate::ExprKind::WrapBoxed(content, _item_type) => {
            add_move(occur_kinds, &mut expr_moves, *content);
        }

        fate::ExprKind::UnwrapBoxed(wrapped, _item_type, _, _) => {
            add_move(occur_kinds, &mut expr_moves, *wrapped);
        }

        fate::ExprKind::WrapCustom(_custom_id, content) => {
            add_move(occur_kinds, &mut expr_moves, *content);
        }

        fate::ExprKind::UnwrapCustom(_custom_id, wrapped) => {
            add_move(occur_kinds, &mut expr_moves, *wrapped);
        }

        fate::ExprKind::Intrinsic(_intr, arg) => {
            add_move(occur_kinds, &mut expr_moves, *arg);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Get(_, _, array, index, _, _)) => {
            add_move(occur_kinds, &mut expr_moves, *array);
            add_move(occur_kinds, &mut expr_moves, *index);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Extract(_, _, array, index)) => {
            add_move(occur_kinds, &mut expr_moves, *array);
            add_move(occur_kinds, &mut expr_moves, *index);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Len(_, _, array)) => {
            add_move(occur_kinds, &mut expr_moves, *array);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Push(_, _, array, item)) => {
            add_move(occur_kinds, &mut expr_moves, *array);
            add_move(occur_kinds, &mut expr_moves, *item);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Pop(_, _, array)) => {
            add_move(occur_kinds, &mut expr_moves, *array);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Replace(_, _, hole_array, item)) => {
            add_move(occur_kinds, &mut expr_moves, *hole_array);
            add_move(occur_kinds, &mut expr_moves, *item);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Reserve(_, _, array, capacity)) => {
            add_move(occur_kinds, &mut expr_moves, *array);
            add_move(occur_kinds, &mut expr_moves, *capacity);
        }

        fate::ExprKind::IoOp(fate::IoOp::Input) => {}

        fate::ExprKind::IoOp(fate::IoOp::Output(_, byte_array)) => {
            add_move(occur_kinds, &mut expr_moves, *byte_array);
        }

        fate::ExprKind::Panic(_, message) => {
            add_move(occur_kinds, &mut expr_moves, *message);
        }

        fate::ExprKind::ArrayLit(_, items) => {
            for item in items {
                add_move(occur_kinds, &mut expr_moves, *item);
            }
        }

        fate::ExprKind::BoolLit(_) => {}
        fate::ExprKind::ByteLit(_) => {}
        fate::ExprKind::IntLit(_) => {}
        fate::ExprKind::FloatLit(_) => {}
    }

    debug_assert!(expr_moves
        .moves
        .get_max()
        .map(|(max_local, _)| max_local.0 < num_locals)
        .unwrap_or(true));

    expr_moves
}

#[derive(Clone, Debug)]
struct MarkedDrops {
    occur_kinds: IdVec<fate::OccurId, BTreeMap<mode::StackPath, OccurKind>>,
    drop_prologues: IdVec<fate::ExprId, BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>>,
    let_drop_epilogues: IdVec<fate::LetBlockId, BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>>,
    branch_drop_epilogues:
        IdVec<fate::BranchBlockId, BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>>,
    arg_drop_epilogue: BTreeSet<mode::StackPath>,
}

fn repair_func_drops(
    typedefs: &flat::CustomTypes,
    func_def: &spec::FuncDef,
    marked_occurs: MarkedOccurs,
) -> MarkedDrops {
    let mut drop_prologues = marked_occurs.tentative_drop_prologues;
    let mut let_drop_epilogues = IdVec::from_items(vec![None; func_def.let_block_end_events.len()]);
    let mut branch_drop_epilogues =
        IdVec::from_items(vec![None; func_def.branch_block_end_events.len()]);

    let body_moves = repair_expr_drops(
        typedefs,
        1,
        &marked_occurs.occur_kinds,
        &mut drop_prologues,
        &mut let_drop_epilogues,
        &mut branch_drop_epilogues,
        &PastMoves {
            moves: OrdMap::new(),
        },
        &func_def.body,
    );

    let arg_drop_epilogue = get_missing_drops(
        typedefs,
        body_moves.moves.get(&flat::ARG_LOCAL),
        &func_def.arg_type,
    );

    MarkedDrops {
        occur_kinds: marked_occurs.occur_kinds,
        drop_prologues,
        let_drop_epilogues: let_drop_epilogues.into_mapped(|_, epilogue| epilogue.unwrap()),
        branch_drop_epilogues: branch_drop_epilogues.into_mapped(|_, epilogue| epilogue.unwrap()),
        arg_drop_epilogue,
    }
}

#[derive(Clone, Debug)]
struct VarMoveHorizon {
    path_move_horizons: BTreeMap<mode::StackPath, event::Horizon>,
}

#[derive(Clone, Debug)]
struct MoveHorizons {
    binding_moves: IdVec<fate::LetBlockId, Vec<VarMoveHorizon>>,
    arg_moves: VarMoveHorizon,
}

fn collect_drop_events(
    var_moves: &mut IdVec<flat::LocalId, VarMoveHorizon>,
    drop_event: &event::Horizon,
    drops: &BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>,
) {
    for (local, dropped_paths) in drops {
        for path in dropped_paths {
            var_moves[local]
                .path_move_horizons
                .entry(path.clone())
                .or_insert_with(event::Horizon::new)
                .disjoint_union(drop_event);
        }
    }
}

fn collect_expr_moves(
    marked_drops: &MarkedDrops,
    expr_annots: &IdVec<fate::ExprId, fate::ExprAnnot>,
    let_block_end_events: &IdVec<fate::LetBlockId, event::Horizon>,
    branch_block_end_events: &IdVec<fate::BranchBlockId, event::Horizon>,
    expr: &fate::Expr,
    var_moves: &mut IdVec<flat::LocalId, VarMoveHorizon>,
    binding_moves: &mut IdVec<fate::LetBlockId, Option<Vec<VarMoveHorizon>>>,
) {
    let expr_event = &expr_annots[expr.id].event;

    let collect_occur_events = |var_moves: &mut IdVec<flat::LocalId, VarMoveHorizon>,
                                occur: fate::Local| {
        for (path, kind) in &marked_drops.occur_kinds[occur.0] {
            match kind {
                OccurKind::Unused | OccurKind::Intermediate => {}
                OccurKind::Final => {
                    var_moves[occur.1]
                        .path_move_horizons
                        .entry(path.clone())
                        .or_insert_with(event::Horizon::new)
                        .disjoint_union(expr_event);
                }
            }
        }
    };

    collect_drop_events(var_moves, expr_event, &marked_drops.drop_prologues[expr.id]);

    match &expr.kind {
        fate::ExprKind::Local(local) => {
            collect_occur_events(var_moves, *local);
        }

        fate::ExprKind::Call(_, _, _, _, _, arg_local) => {
            collect_occur_events(var_moves, *arg_local);
        }

        fate::ExprKind::Branch(discrim, cases, _) => {
            collect_occur_events(var_moves, *discrim);
            for (block_id, _, body, _final_ctx) in cases {
                collect_expr_moves(
                    marked_drops,
                    expr_annots,
                    let_block_end_events,
                    branch_block_end_events,
                    body,
                    var_moves,
                    binding_moves,
                );
                collect_drop_events(
                    var_moves,
                    &branch_block_end_events[block_id],
                    &marked_drops.branch_drop_epilogues[block_id],
                );
            }
        }

        fate::ExprKind::LetMany(block_id, bindings, _final_ctx, final_local) => {
            let orig_locals = var_moves.len();

            for (offset, (_type, rhs)) in bindings.iter().enumerate() {
                collect_expr_moves(
                    marked_drops,
                    expr_annots,
                    let_block_end_events,
                    branch_block_end_events,
                    rhs,
                    var_moves,
                    binding_moves,
                );
                let local_id = var_moves.push(VarMoveHorizon {
                    path_move_horizons: BTreeMap::new(),
                });
                debug_assert_eq!(local_id.0, orig_locals + offset);
            }

            collect_occur_events(var_moves, *final_local);

            collect_drop_events(
                var_moves,
                &let_block_end_events[block_id],
                &marked_drops.let_drop_epilogues[block_id],
            );

            let block_binding_moves = var_moves.items.drain(orig_locals..).collect::<Vec<_>>();
            debug_assert_eq!(block_binding_moves.len(), bindings.len());
            debug_assert!(binding_moves[block_id].is_none());
            binding_moves[block_id] = Some(block_binding_moves);
        }

        fate::ExprKind::Tuple(items) => {
            for item in items {
                collect_occur_events(var_moves, *item);
            }
        }

        fate::ExprKind::TupleField(tuple, _index) => {
            collect_occur_events(var_moves, *tuple);
        }

        fate::ExprKind::WrapVariant(_variant_types, _variant_id, content) => {
            collect_occur_events(var_moves, *content);
        }

        fate::ExprKind::UnwrapVariant(_variant_id, wrapped) => {
            collect_occur_events(var_moves, *wrapped);
        }

        fate::ExprKind::WrapBoxed(content, _item_type) => {
            collect_occur_events(var_moves, *content);
        }

        fate::ExprKind::UnwrapBoxed(wrapped, _item_type, _, _) => {
            collect_occur_events(var_moves, *wrapped);
        }

        fate::ExprKind::WrapCustom(_custom_id, content) => {
            collect_occur_events(var_moves, *content);
        }

        fate::ExprKind::UnwrapCustom(_custom_id, wrapped) => {
            collect_occur_events(var_moves, *wrapped);
        }

        fate::ExprKind::Intrinsic(_intr, arg) => {
            collect_occur_events(var_moves, *arg);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Get(_, _, array, index, _, _)) => {
            collect_occur_events(var_moves, *array);
            collect_occur_events(var_moves, *index);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Extract(_, _, array, index)) => {
            collect_occur_events(var_moves, *array);
            collect_occur_events(var_moves, *index);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Len(_, _, array)) => {
            collect_occur_events(var_moves, *array);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Push(_, _, array, item)) => {
            collect_occur_events(var_moves, *array);
            collect_occur_events(var_moves, *item);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Pop(_, _, array)) => {
            collect_occur_events(var_moves, *array);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Replace(_, _, hole_array, item)) => {
            collect_occur_events(var_moves, *hole_array);
            collect_occur_events(var_moves, *item);
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Reserve(_, _, array, capacity)) => {
            collect_occur_events(var_moves, *array);
            collect_occur_events(var_moves, *capacity);
        }

        fate::ExprKind::IoOp(fate::IoOp::Input) => {}

        fate::ExprKind::IoOp(fate::IoOp::Output(_, byte_array)) => {
            collect_occur_events(var_moves, *byte_array);
        }

        fate::ExprKind::Panic(_, message) => {
            collect_occur_events(var_moves, *message);
        }

        fate::ExprKind::ArrayLit(_, items) => {
            for item in items {
                collect_occur_events(var_moves, *item);
            }
        }

        fate::ExprKind::BoolLit(_) => {}
        fate::ExprKind::ByteLit(_) => {}
        fate::ExprKind::IntLit(_) => {}
        fate::ExprKind::FloatLit(_) => {}
    }
}

fn collect_func_moves(func_def: &spec::FuncDef, marked_drops: &MarkedDrops) -> MoveHorizons {
    let mut var_moves = IdVec::new();
    let _ = var_moves.push(VarMoveHorizon {
        path_move_horizons: BTreeMap::new(),
    });

    let mut binding_moves = IdVec::from_items(vec![None; func_def.let_block_end_events.len()]);

    collect_expr_moves(
        marked_drops,
        &func_def.expr_annots,
        &func_def.let_block_end_events,
        &func_def.branch_block_end_events,
        &func_def.body,
        &mut var_moves,
        &mut binding_moves,
    );

    debug_assert_eq!(var_moves.len(), 1);
    let mut arg_moves = var_moves.items.into_iter().next().unwrap();

    // The argument drop epilogue occurs after all other events in the function, so we don't need to
    // explicitly track move horizons associated with the argument drop epilogue for the purpose of
    // lifetime analysis.  It's safe to just mark every path in the argument which is dropped in the
    // epilogue as having an empty move horizon, which will give `false` for any `can_occur_before`
    // check.
    for arg_path in &marked_drops.arg_drop_epilogue {
        let existing = arg_moves
            .path_move_horizons
            .insert(arg_path.clone(), event::Horizon::new());
        debug_assert!(existing.is_none());
    }

    MoveHorizons {
        binding_moves: binding_moves.into_mapped(|_, moves| moves.unwrap()),
        arg_moves,
    }
}

fn find_sccs(
    funcs: &IdVec<first_ord::CustomFuncId, spec::FuncDef>,
) -> Vec<Vec<(first_ord::CustomFuncId, spec::FuncVersionId)>> {
    // To find SCCs, we need all functions in the program to be associated with concrete ids in a
    // single "address space".  This means we can't use '(function id, version id)' pairs to refer
    // to specialized function versions in these algorithms.  To work around this, we build an
    // internal table mapping those pairs to `GlobalFuncVersionId`s which are suitable for use with
    // the SCC algorithm.
    id_type!(GlobalFuncVersionId);

    let mut global_to_version: IdVec<GlobalFuncVersionId, _> = IdVec::new();
    let version_to_global = funcs.map(|func_id, func_def| {
        func_def
            .versions
            .map(|version_id, _| global_to_version.push((func_id, version_id)))
    });

    let dep_graph = Graph {
        edges_out: global_to_version.map(|_, (func_id, version_id)| {
            funcs[func_id].versions[version_id]
                .calls
                .iter()
                .map(|(_, (dep_func_id, dep_version_id))| {
                    version_to_global[dep_func_id][dep_version_id]
                })
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
        }),
    };

    strongly_connected(&dep_graph)
        .into_iter()
        .map(|global_ids| {
            global_ids
                .into_iter()
                .map(|global_id| global_to_version[global_id])
                .collect()
        })
        .collect()
}

#[derive(Clone, Debug)]
enum SolverPathOccurMode {
    Intermediate {
        src: ineq::SolverVarId,
        dest: ineq::SolverVarId,
    },
    Final,
    Unused,
}

#[derive(Clone, Debug)]
struct SolverOccurModes {
    path_modes: BTreeMap<mode::StackPath, SolverPathOccurMode>,
}

#[derive(Clone, Debug)]
struct SolverDropModes {
    dropped_paths: BTreeMap<mode::StackPath, ineq::SolverVarId>,
}

#[derive(Clone, Debug)]
struct SolverRetainModes {
    retained_paths: BTreeMap<mode::StackPath, ineq::SolverVarId>,
}

#[derive(Clone, Debug)]
struct SolverModeAnnots {
    occur_modes: IdVec<fate::OccurId, Option<SolverOccurModes>>,
    call_modes: IdVec<fate::CallId, Option<IdVec<ineq::ExternalVarId, ineq::SolverVarId>>>,
    let_drop_epilogues: IdVec<fate::LetBlockId, Option<BTreeMap<flat::LocalId, SolverDropModes>>>,
    branch_drop_epilogues:
        IdVec<fate::BranchBlockId, Option<BTreeMap<flat::LocalId, SolverDropModes>>>,
    drop_prologues: IdVec<fate::ExprId, Option<BTreeMap<flat::LocalId, SolverDropModes>>>,
    retain_epilogues: IdVec<fate::RetainPointId, Option<SolverRetainModes>>,
}

#[derive(Clone, Debug)]
struct SolverValModes {
    path_modes: OrdMap<alias::FieldPath, ineq::SolverVarId>,
}

impl SolverValModes {
    fn new() -> Self {
        SolverValModes {
            path_modes: OrdMap::new(),
        }
    }
}

#[derive(Clone, Debug)]
struct SolverLocalInfo<'a> {
    val_modes: SolverValModes,
    move_horizon: &'a VarMoveHorizon,
    type_: &'a anon::Type,
}

#[derive(Clone, Debug)]
struct SolverSccFuncSig {
    arg_modes: BTreeMap<alias::FieldPath, ineq::ExternalVarId>,
    ret_modes: BTreeMap<alias::FieldPath, ineq::ExternalVarId>,
}

#[derive(Clone, Debug)]
struct SolverSccSigs<'a> {
    extern_vars: &'a IdVec<ineq::ExternalVarId, ineq::SolverVarId>,
    func_sigs: BTreeMap<(first_ord::CustomFuncId, spec::FuncVersionId), SolverSccFuncSig>,
}

fn instantiate_sig_type(
    typedefs: &flat::CustomTypes,
    constraints: &mut ineq::ConstraintGraph<mode::Mode>,
    extern_vars: &mut IdVec<ineq::ExternalVarId, ineq::SolverVarId>,
    type_: &anon::Type,
) -> BTreeMap<alias::FieldPath, ineq::ExternalVarId> {
    field_path::get_refs_in(typedefs, type_)
        .into_iter()
        .map(|(path, _)| {
            let solver_var = constraints.new_var();
            (path, extern_vars.push(solver_var))
        })
        .collect()
}

fn instantiate_type(
    typedefs: &flat::CustomTypes,
    constraints: &mut ineq::ConstraintGraph<mode::Mode>,
    type_: &anon::Type,
) -> SolverValModes {
    SolverValModes {
        path_modes: field_path::get_refs_in(typedefs, type_)
            .into_iter()
            .map(|(path, _)| (path, constraints.new_var()))
            .collect(),
    }
}

fn equate_modes(
    constraints: &mut ineq::ConstraintGraph<mode::Mode>,
    modes1: &SolverValModes,
    modes2: &SolverValModes,
) {
    debug_assert_eq!(
        modes1.path_modes.keys().collect::<BTreeSet<_>>(),
        modes2.path_modes.keys().collect::<BTreeSet<_>>()
    );

    for (path, mode1) in &modes1.path_modes {
        let mode2 = modes2.path_modes[path];
        constraints.require_eq(*mode1, mode2);
    }
}

fn substitute_sig_modes(
    sig_vars: &IdVec<ineq::ExternalVarId, ineq::SolverVarId>,
    sig_modes: &BTreeMap<alias::FieldPath, ineq::ExternalVarId>,
) -> SolverValModes {
    SolverValModes {
        path_modes: sig_modes
            .iter()
            .map(|(path, sig_var)| (path.clone(), sig_vars[sig_var]))
            .collect(),
    }
}

fn annot_local_drops(
    local_modes: &SolverValModes,
    dropped_paths: &BTreeSet<mode::StackPath>,
) -> SolverDropModes {
    SolverDropModes {
        dropped_paths: dropped_paths
            .iter()
            .map(|path| {
                (
                    path.clone(),
                    local_modes.path_modes[&stack_path::to_field_path(path)],
                )
            })
            .collect(),
    }
}

fn annot_drops(
    locals: &LocalContext<flat::LocalId, SolverLocalInfo>,
    drops: &BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>,
) -> BTreeMap<flat::LocalId, SolverDropModes> {
    drops
        .iter()
        .map(|(dropped_local, dropped_paths)| {
            let local_modes = &locals.local_binding(*dropped_local).val_modes;
            (
                *dropped_local,
                annot_local_drops(local_modes, dropped_paths),
            )
        })
        .collect::<BTreeMap<_, _>>()
}

// TODO: This type signature *really* needs to not be like this
fn annot_expr<'a>(
    elision_mode: cli::RcMode,
    typedefs: &flat::CustomTypes,
    known_annots: &IdVec<
        first_ord::CustomFuncId,
        IdVec<spec::FuncVersionId, Option<mode::ModeAnnots>>,
    >,
    occur_fates: &IdVec<fate::OccurId, fate::Fate>, // Used only for access horizons
    call_versions: &IdVec<fate::CallId, (first_ord::CustomFuncId, spec::FuncVersionId)>,
    ret_fates: &BTreeMap<alias::RetName, spec::RetFate>,
    marked_drops: &MarkedDrops,
    move_horizons: &'a MoveHorizons,
    constraints: &mut ineq::ConstraintGraph<mode::Mode>,
    scc_sigs: &SolverSccSigs,
    locals: &mut LocalContext<flat::LocalId, SolverLocalInfo<'a>>,
    expr: &'a fate::Expr,
    solver_annots: &mut SolverModeAnnots,
) -> SolverValModes {
    let drop_prologue_modes = annot_drops(locals, &marked_drops.drop_prologues[expr.id]);
    debug_assert!(solver_annots.drop_prologues[expr.id].is_none());
    solver_annots.drop_prologues[expr.id] = Some(drop_prologue_modes);

    let annot_occur = |constraints: &mut ineq::ConstraintGraph<mode::Mode>,
                       locals: &LocalContext<flat::LocalId, SolverLocalInfo>,
                       solver_annots: &mut SolverModeAnnots,
                       occur: fate::Local|
     -> SolverValModes {
        let mut occur_modes = BTreeMap::new();
        let mut occur_val_modes = OrdMap::new();

        let binding = locals.local_binding(occur.1);
        let occur_kinds = &marked_drops.occur_kinds[occur.0];

        for (path, src_mode_var) in &binding.val_modes.path_modes {
            let truncation = stack_path::split_stack_heap_3(typedefs, path.clone());

            for stack in truncation.clone().stack_paths() {
                let (dest_mode, dest_mode_var) = match &occur_kinds[&stack] {
                    OccurKind::Unused => {
                        // TODO: When we monomorphize, `dest_mode_var` should always be `Borrowed`. Is
                        // there some way to add an assertion for this invariant?
                        //
                        // TODO [critical]: It may actually be possible to break this.  We should
                        // definintely implement the assertion defined above, and try hard to either
                        // rigorously prove that it will always succeed, or find a counterexample that
                        // causes it to fail.
                        let dest_mode_var = constraints.new_var();
                        (SolverPathOccurMode::Unused, dest_mode_var)
                    }
                    OccurKind::Final => (SolverPathOccurMode::Final, *src_mode_var),
                    OccurKind::Intermediate => {
                        let occur_fate = &occur_fates[occur.0].fates[path];

                        let escapes_to_used_ret_path = occur_fate
                            .ret_destinations
                            .iter()
                            .any(|ret_path| ret_fates[ret_path] == spec::RetFate::MaybeUsed);

                        let path_move_horizon = &binding.move_horizon.path_move_horizons[&stack];
                        let path_access_horizon =
                            &occur_fates[occur.0].fates[path].last_internal_use;

                        let borrow_would_outlive_src = escapes_to_used_ret_path
                            || path_move_horizon.can_occur_before(path_access_horizon);

                        // This is where the magic happens.
                        //
                        // The entire horizon-based borrow checking system exists to support this
                        // conditional right here.  When an occurrence of a variable path will not be
                        // accessed beyond the end of its source's lifetime, we allow the occurrence to
                        // have mode `Borrowed` even if the source has mode `Owned` (although the
                        // destination may still end up having the mode `Owned` if something else about
                        // the way it's used later forces it to be owned, such as unifying with an
                        // unconditionally owned variable).  On the other hand, when an occurrence of a
                        // variable may outlive its source, the destination needs to have the same mode
                        // as the source (which may still end up being `Borrowed` if the source is
                        // itself borrowed from another variable).
                        let dest_mode_var =
                            if elision_mode == cli::RcMode::Trivial || borrow_would_outlive_src {
                                *src_mode_var
                            } else {
                                let var = constraints.new_var();
                                constraints.require_lte(*src_mode_var, var);
                                var
                            };

                        (
                            SolverPathOccurMode::Intermediate {
                                src: *src_mode_var,
                                dest: dest_mode_var,
                            },
                            dest_mode_var,
                        )
                    }
                };

                if !matches!(&truncation, stack_path::PathTruncation::Heap(_)) {
                    let existing = occur_modes.insert(stack, dest_mode);
                    debug_assert!(existing.is_none());
                }

                occur_val_modes.insert(path.clone(), dest_mode_var);
            }
        }

        debug_assert!(solver_annots.occur_modes[occur.0].is_none());
        solver_annots.occur_modes[occur.0] = Some(SolverOccurModes {
            path_modes: occur_modes,
        });

        SolverValModes {
            path_modes: occur_val_modes,
        }
    };

    let result_modes = match &expr.kind {
        fate::ExprKind::Local(local) => annot_occur(constraints, locals, solver_annots, *local),

        fate::ExprKind::Call(call_id, _, _, _, _, local) => {
            let arg_val_modes = annot_occur(constraints, locals, solver_annots, *local);

            let (callee_id, callee_version_id) = call_versions[call_id];

            let (callee_extern_vars, callee_sig_arg_modes, callee_sig_ret_modes) =
                match scc_sigs.func_sigs.get(&(callee_id, callee_version_id)) {
                    Some(scc_sig) => (
                        scc_sigs.extern_vars.clone(),
                        &scc_sig.arg_modes,
                        &scc_sig.ret_modes,
                    ),

                    None => {
                        let callee_annots =
                            known_annots[callee_id][callee_version_id].as_ref().unwrap();

                        let callee_extern_vars =
                            constraints.instantiate_subgraph(&callee_annots.extern_constraints);

                        (
                            callee_extern_vars,
                            &callee_annots.arg_modes,
                            &callee_annots.ret_modes,
                        )
                    }
                };

            let callee_arg_modes = substitute_sig_modes(&callee_extern_vars, callee_sig_arg_modes);
            let callee_ret_modes = substitute_sig_modes(&callee_extern_vars, callee_sig_ret_modes);

            equate_modes(constraints, &arg_val_modes, &callee_arg_modes);

            debug_assert!(solver_annots.call_modes[call_id].is_none());
            solver_annots.call_modes[call_id] = Some(callee_extern_vars);

            callee_ret_modes
        }

        fate::ExprKind::Branch(discrim, cases, result_type) => {
            annot_occur(constraints, locals, solver_annots, *discrim);

            let result_modes = instantiate_type(typedefs, constraints, result_type);

            for (block_id, _cond, body, _final_ctx) in cases {
                let body_modes = annot_expr(
                    elision_mode,
                    typedefs,
                    known_annots,
                    occur_fates,
                    call_versions,
                    ret_fates,
                    marked_drops,
                    move_horizons,
                    constraints,
                    scc_sigs,
                    locals,
                    body,
                    solver_annots,
                );

                equate_modes(constraints, &body_modes, &result_modes);

                let drop_epilogue_annot =
                    annot_drops(locals, &marked_drops.branch_drop_epilogues[block_id]);

                debug_assert!(solver_annots.branch_drop_epilogues[block_id].is_none());
                solver_annots.branch_drop_epilogues[block_id] = Some(drop_epilogue_annot);
            }

            result_modes
        }

        fate::ExprKind::LetMany(block_id, bindings, _final_ctx, final_local) => {
            locals.with_scope(|sub_locals| {
                let binding_horizons = &move_horizons.binding_moves[block_id];
                debug_assert_eq!(binding_horizons.len(), bindings.len());
                for ((type_, rhs), move_horizon) in bindings.iter().zip(binding_horizons.iter()) {
                    let binding_modes = annot_expr(
                        elision_mode,
                        typedefs,
                        known_annots,
                        occur_fates,
                        call_versions,
                        ret_fates,
                        marked_drops,
                        move_horizons,
                        constraints,
                        scc_sigs,
                        sub_locals,
                        rhs,
                        solver_annots,
                    );

                    sub_locals.add_local(SolverLocalInfo {
                        val_modes: binding_modes,
                        move_horizon,
                        type_,
                    });
                }

                let drop_epilogue_annot =
                    annot_drops(sub_locals, &marked_drops.let_drop_epilogues[block_id]);

                debug_assert!(solver_annots.let_drop_epilogues[block_id].is_none());
                solver_annots.let_drop_epilogues[block_id] = Some(drop_epilogue_annot);

                annot_occur(constraints, sub_locals, solver_annots, *final_local)
            })
        }

        fate::ExprKind::Tuple(items) => {
            let mut result_modes = SolverValModes::new();
            for (i, item) in items.iter().enumerate() {
                let item_modes = annot_occur(constraints, locals, solver_annots, *item);
                for (path, mode) in item_modes.path_modes {
                    result_modes
                        .path_modes
                        .insert(path.add_front(alias::Field::Field(i)), mode);
                }
            }
            result_modes
        }

        fate::ExprKind::TupleField(tuple, idx) => {
            let mut result_modes = SolverValModes::new();

            let tuple_modes = annot_occur(constraints, locals, solver_annots, *tuple);

            let tuple_info = locals.local_binding(tuple.1);
            let item_type = if let anon::Type::Tuple(item_types) = &tuple_info.type_ {
                &item_types[*idx]
            } else {
                unreachable!()
            };

            for (item_path, _) in field_path::get_refs_in(typedefs, item_type) {
                result_modes.path_modes.insert(
                    item_path.clone(),
                    tuple_modes.path_modes[&item_path.add_front(alias::Field::Field(*idx))],
                );
            }
            result_modes
        }

        fate::ExprKind::WrapVariant(variant_types, variant_id, content) => {
            let result_modes = instantiate_type(
                typedefs,
                constraints,
                &anon::Type::Variants(variant_types.clone()),
            );

            let content_modes = annot_occur(constraints, locals, solver_annots, *content);

            for (content_path, content_mode) in content_modes.path_modes {
                constraints.require_eq(
                    result_modes.path_modes
                        [&content_path.add_front(alias::Field::Variant(*variant_id))],
                    content_mode,
                );
            }
            result_modes
        }

        fate::ExprKind::UnwrapVariant(variant_id, wrapped) => {
            let mut result_modes = SolverValModes::new();

            let wrapped_modes = annot_occur(constraints, locals, solver_annots, *wrapped);

            let wrapped_info = locals.local_binding(wrapped.1);
            let content_type = if let anon::Type::Variants(variant_types) = &wrapped_info.type_ {
                &variant_types[variant_id]
            } else {
                unreachable!()
            };

            for (content_path, _) in field_path::get_refs_in(typedefs, content_type) {
                result_modes.path_modes.insert(
                    content_path.clone(),
                    wrapped_modes.path_modes
                        [&content_path.add_front(alias::Field::Variant(*variant_id))],
                );
            }
            result_modes
        }

        fate::ExprKind::WrapBoxed(content, item_type) => {
            let content_modes = annot_occur(constraints, locals, solver_annots, *content);

            for (_, content_mode) in content_modes.path_modes {
                constraints.require_lte_const(content_mode, &mode::Mode::Owned);
            }

            let result_modes = instantiate_type(
                typedefs,
                constraints,
                &anon::Type::Boxed(Box::new(item_type.clone())),
            );

            for (_, result_mode) in &result_modes.path_modes {
                constraints.require_lte_const(*result_mode, &mode::Mode::Owned);
            }
            result_modes
        }

        fate::ExprKind::UnwrapBoxed(wrapped, item_type, _, retain_point) => {
            let mut result_modes = SolverValModes::new();

            let wrapped_modes = annot_occur(constraints, locals, solver_annots, *wrapped);

            for (content_path, _) in field_path::get_refs_in(typedefs, item_type) {
                result_modes.path_modes.insert(
                    content_path.clone(),
                    wrapped_modes.path_modes[&content_path.add_front(alias::Field::Boxed)],
                );
            }

            let mut retain_epilogue = SolverRetainModes {
                retained_paths: BTreeMap::new(),
            };
            for content_stack_path in stack_path::stack_paths_in(typedefs, item_type) {
                let content_path = stack_path::to_field_path(&content_stack_path);
                retain_epilogue
                    .retained_paths
                    .insert(content_stack_path, result_modes.path_modes[&content_path]);
            }
            debug_assert!(solver_annots.retain_epilogues[retain_point].is_none());
            solver_annots.retain_epilogues[retain_point] = Some(retain_epilogue);

            result_modes
        }

        fate::ExprKind::WrapCustom(custom_id, content) => {
            let result_modes =
                instantiate_type(typedefs, constraints, &anon::Type::Custom(*custom_id));

            let content_modes = annot_occur(constraints, locals, solver_annots, *content);

            let scc_id = typedefs.types[custom_id].scc;
            for (content_path, content_mode) in content_modes.path_modes {
                let (_, in_custom, alias::SubPath(sub_path)) =
                    field_path::split_at_fold(scc_id, *custom_id, content_path);

                constraints.require_eq(
                    result_modes.path_modes[&sub_path
                        .add_front(alias::Field::Custom(in_custom))
                        .add_front(alias::Field::CustomScc(scc_id, *custom_id))],
                    content_mode,
                );
            }
            result_modes
        }

        fate::ExprKind::UnwrapCustom(custom_id, wrapped) => {
            let result_modes =
                instantiate_type(typedefs, constraints, &typedefs.types[custom_id].content);

            let wrapped_modes = annot_occur(constraints, locals, solver_annots, *wrapped);

            let scc_id = typedefs.types[custom_id].scc;
            for (content_path, content_mode) in &result_modes.path_modes {
                let (_, in_custom, alias::SubPath(sub_path)) =
                    field_path::split_at_fold(scc_id, *custom_id, content_path.clone());

                constraints.require_eq(
                    *content_mode,
                    wrapped_modes.path_modes[&sub_path
                        .clone()
                        .add_front(alias::Field::Custom(in_custom))
                        .add_front(alias::Field::CustomScc(scc_id, *custom_id))],
                );
            }
            result_modes
        }

        // TODO [intrinsics]: If we ever add array intrinsics, we will need to modify this.
        fate::ExprKind::Intrinsic(_intr, arg) => {
            let arg_modes = annot_occur(constraints, locals, solver_annots, *arg);
            debug_assert!(arg_modes.path_modes.is_empty());
            SolverValModes::new()
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Get(
            item_type,
            _,
            array,
            index,
            _,
            retain_point,
        )) => {
            let mut result_modes = SolverValModes::new();

            let array_modes = annot_occur(constraints, locals, solver_annots, *array);
            let index_modes = annot_occur(constraints, locals, solver_annots, *index);
            debug_assert!(index_modes.path_modes.is_empty());

            for (item_path, _) in field_path::get_refs_in(typedefs, item_type) {
                result_modes.path_modes.insert(
                    item_path.clone(),
                    array_modes.path_modes
                        [&item_path.clone().add_front(alias::Field::ArrayMembers)],
                );
            }

            let mut retain_epilogue = SolverRetainModes {
                retained_paths: BTreeMap::new(),
            };

            for item_stack_path in stack_path::stack_paths_in(typedefs, item_type) {
                let item_mode =
                    array_modes.path_modes[&stack_path::to_field_path(&item_stack_path)
                        .add_front(alias::Field::ArrayMembers)];

                retain_epilogue
                    .retained_paths
                    .insert(item_stack_path, item_mode);
            }

            debug_assert!(solver_annots.retain_epilogues[retain_point].is_none());
            solver_annots.retain_epilogues[retain_point] = Some(retain_epilogue);

            result_modes
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Extract(item_type, _, array, index)) => {
            let array_modes = annot_occur(constraints, locals, solver_annots, *array);
            let index_modes = annot_occur(constraints, locals, solver_annots, *index);
            debug_assert!(index_modes.path_modes.is_empty());

            for (_, array_mode) in array_modes.path_modes {
                constraints.require_lte_const(array_mode, &mode::Mode::Owned);
            }

            let result_modes = instantiate_type(
                typedefs,
                constraints,
                &anon::Type::Tuple(vec![
                    item_type.clone(),
                    anon::Type::HoleArray(Box::new(item_type.clone())),
                ]),
            );

            for (_, result_mode) in &result_modes.path_modes {
                constraints.require_lte_const(*result_mode, &mode::Mode::Owned);
            }

            result_modes
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Len(_, _, array)) => {
            annot_occur(constraints, locals, solver_annots, *array);
            SolverValModes::new()
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Push(item_type, _, array, item)) => {
            let array_modes = annot_occur(constraints, locals, solver_annots, *array);
            let item_modes = annot_occur(constraints, locals, solver_annots, *item);

            for (_, array_mode) in array_modes.path_modes {
                constraints.require_lte_const(array_mode, &mode::Mode::Owned);
            }

            for (_, item_mode) in item_modes.path_modes {
                constraints.require_lte_const(item_mode, &mode::Mode::Owned);
            }

            let result_modes = instantiate_type(
                typedefs,
                constraints,
                &anon::Type::Array(Box::new(item_type.clone())),
            );

            for (_, result_mode) in &result_modes.path_modes {
                constraints.require_lte_const(*result_mode, &mode::Mode::Owned);
            }

            result_modes
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Pop(item_type, _, array)) => {
            let array_modes = annot_occur(constraints, locals, solver_annots, *array);

            for (_, array_mode) in array_modes.path_modes {
                constraints.require_lte_const(array_mode, &mode::Mode::Owned);
            }

            let result_modes = instantiate_type(
                typedefs,
                constraints,
                &anon::Type::Tuple(vec![
                    anon::Type::Array(Box::new(item_type.clone())),
                    item_type.clone(),
                ]),
            );

            for (_, result_mode) in &result_modes.path_modes {
                constraints.require_lte_const(*result_mode, &mode::Mode::Owned);
            }

            result_modes
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Replace(item_type, _, hole_array, item)) => {
            let hole_array_modes = annot_occur(constraints, locals, solver_annots, *hole_array);
            let item_modes = annot_occur(constraints, locals, solver_annots, *item);

            for (_, hole_array_mode) in hole_array_modes.path_modes {
                constraints.require_lte_const(hole_array_mode, &mode::Mode::Owned);
            }

            for (_, item_mode) in item_modes.path_modes {
                constraints.require_lte_const(item_mode, &mode::Mode::Owned);
            }

            let result_modes = instantiate_type(
                typedefs,
                constraints,
                &anon::Type::Array(Box::new(item_type.clone())),
            );

            for (_, result_mode) in &result_modes.path_modes {
                constraints.require_lte_const(*result_mode, &mode::Mode::Owned);
            }

            result_modes
        }

        fate::ExprKind::ArrayOp(fate::ArrayOp::Reserve(item_type, _, array, capacity)) => {
            let array_modes = annot_occur(constraints, locals, solver_annots, *array);
            let capacity_modes = annot_occur(constraints, locals, solver_annots, *capacity);

            debug_assert!(capacity_modes.path_modes.is_empty());

            for (_, array_mode) in array_modes.path_modes {
                constraints.require_lte_const(array_mode, &mode::Mode::Owned);
            }

            let result_modes = instantiate_type(
                typedefs,
                constraints,
                &anon::Type::Array(Box::new(item_type.clone())),
            );

            for (_, result_mode) in &result_modes.path_modes {
                constraints.require_lte_const(*result_mode, &mode::Mode::Owned);
            }

            result_modes
        }

        fate::ExprKind::IoOp(fate::IoOp::Input) => {
            let mut result_modes = SolverValModes::new();
            let array_mode = constraints.new_var();
            constraints.require_lte_const(array_mode, &mode::Mode::Owned);
            result_modes.path_modes.insert(Vector::new(), array_mode);
            result_modes
        }

        fate::ExprKind::IoOp(fate::IoOp::Output(_, byte_array)) => {
            annot_occur(constraints, locals, solver_annots, *byte_array);
            SolverValModes::new()
        }

        fate::ExprKind::Panic(result_type, message) => {
            annot_occur(constraints, locals, solver_annots, *message);
            instantiate_type(typedefs, constraints, result_type)
        }

        fate::ExprKind::ArrayLit(item_type, items) => {
            for item in items {
                let item_modes = annot_occur(constraints, locals, solver_annots, *item);
                for (_, item_mode) in item_modes.path_modes {
                    constraints.require_lte_const(item_mode, &mode::Mode::Owned);
                }
            }

            let result_modes = instantiate_type(
                typedefs,
                constraints,
                &anon::Type::Array(Box::new(item_type.clone())),
            );

            for (_, result_mode) in &result_modes.path_modes {
                constraints.require_lte_const(*result_mode, &mode::Mode::Owned);
            }

            result_modes
        }

        fate::ExprKind::BoolLit(_)
        | fate::ExprKind::ByteLit(_)
        | fate::ExprKind::IntLit(_)
        | fate::ExprKind::FloatLit(_) => SolverValModes::new(),
    };

    result_modes
}

fn extract_drop_modes(
    solutions: &IdVec<ineq::SolverVarId, ineq::UpperBound<mode::Mode>>,
    modes: SolverDropModes,
) -> mode::DropModes {
    mode::DropModes {
        dropped_paths: modes
            .dropped_paths
            .into_iter()
            .map(|(path, var)| (path, solutions[var].clone()))
            .collect(),
    }
}

fn extract_drops(
    solutions: &IdVec<ineq::SolverVarId, ineq::UpperBound<mode::Mode>>,
    drops: BTreeMap<flat::LocalId, SolverDropModes>,
) -> Vec<(flat::LocalId, mode::DropModes)> {
    drops
        .into_iter()
        .map(|(path, drop_modes)| (path, extract_drop_modes(solutions, drop_modes)))
        .collect()
}

fn extract_retains(
    solutions: &IdVec<ineq::SolverVarId, ineq::UpperBound<mode::Mode>>,
    modes: SolverRetainModes,
) -> mode::RetainModes {
    mode::RetainModes {
        retained_paths: modes
            .retained_paths
            .into_iter()
            .map(|(path, var)| (path, solutions[var].clone()))
            .collect(),
    }
}

fn extract_occur_modes(
    solutions: &IdVec<ineq::SolverVarId, ineq::UpperBound<mode::Mode>>,
    occur_modes: SolverOccurModes,
) -> mode::OccurModes {
    mode::OccurModes {
        path_modes: occur_modes
            .path_modes
            .into_iter()
            .map(|(path, mode)| {
                (
                    path,
                    match mode {
                        SolverPathOccurMode::Unused => mode::PathOccurMode::Unused,
                        SolverPathOccurMode::Final => mode::PathOccurMode::Final,
                        SolverPathOccurMode::Intermediate { src, dest } => {
                            mode::PathOccurMode::Intermediate {
                                src: solutions[src].clone(),
                                dest: solutions[dest].clone(),
                            }
                        }
                    },
                )
            })
            .collect(),
    }
}

fn annot_scc(
    elision_mode: cli::RcMode,
    orig: &spec::Program,
    func_annots: &mut IdVec<
        first_ord::CustomFuncId,
        IdVec<spec::FuncVersionId, Option<mode::ModeAnnots>>,
    >,
    scc: &[(first_ord::CustomFuncId, spec::FuncVersionId)],
) {
    let mut constraints = ineq::ConstraintGraph::<mode::Mode>::new();

    let mut extern_vars = IdVec::new();
    let func_sigs = scc
        .iter()
        .map(|&(func_id, version_id)| {
            let func_def = &orig.funcs[func_id];
            let arg_modes = instantiate_sig_type(
                &orig.custom_types,
                &mut constraints,
                &mut extern_vars,
                &func_def.arg_type,
            );
            let ret_modes = instantiate_sig_type(
                &orig.custom_types,
                &mut constraints,
                &mut extern_vars,
                &func_def.ret_type,
            );
            (
                (func_id, version_id),
                SolverSccFuncSig {
                    arg_modes,
                    ret_modes,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();

    let scc_sigs = SolverSccSigs {
        extern_vars: &extern_vars,
        func_sigs,
    };

    #[derive(Clone, Debug)]
    struct SolverFullModeAnnots {
        occur_modes: IdVec<fate::OccurId, SolverOccurModes>,
        call_modes: IdVec<fate::CallId, IdVec<ineq::ExternalVarId, ineq::SolverVarId>>,
        let_drop_epilogues: IdVec<fate::LetBlockId, BTreeMap<flat::LocalId, SolverDropModes>>,
        branch_drop_epilogues: IdVec<fate::BranchBlockId, BTreeMap<flat::LocalId, SolverDropModes>>,
        drop_prologues: IdVec<fate::ExprId, BTreeMap<flat::LocalId, SolverDropModes>>,
        retain_epilogues: IdVec<fate::RetainPointId, SolverRetainModes>,
        arg_drop_epilogue: SolverDropModes,
    }

    let scc_set = scc.iter().cloned().collect::<BTreeSet<_>>();

    let func_solver_annots = scc
        .iter()
        .map(|&(func_id, version_id)| {
            let func_def = &orig.funcs[func_id];
            let version = &func_def.versions[version_id];
            let func_scc_sig = &scc_sigs.func_sigs[&(func_id, version_id)];

            let marked_occurs = mark_func_occurs(orig, &scc_set, func_def, version);
            let marked_drops = repair_func_drops(&orig.custom_types, func_def, marked_occurs);
            let move_horizons = collect_func_moves(func_def, &marked_drops);

            let mut locals = LocalContext::new();
            locals.add_local(SolverLocalInfo {
                val_modes: substitute_sig_modes(&extern_vars, &func_scc_sig.arg_modes),
                move_horizon: &move_horizons.arg_moves,
                type_: &func_def.arg_type,
            });

            let mut solver_annots = SolverModeAnnots {
                occur_modes: func_def.occur_fates.map(|_, _| None),
                call_modes: version.calls.map(|_, _| None),
                let_drop_epilogues: marked_drops.let_drop_epilogues.map(|_, _| None),
                branch_drop_epilogues: marked_drops.branch_drop_epilogues.map(|_, _| None),
                drop_prologues: marked_drops.drop_prologues.map(|_, _| None),
                // `retain_epilogues` is indexed by `ExprId`, so we can obtain an empty `IdVec` of
                // the right shape from `drop_prologues`.
                retain_epilogues: IdVec::from_items(vec![None; func_def.num_retain_points]),
            };

            let ret_val_modes = annot_expr(
                elision_mode,
                &orig.custom_types,
                func_annots,
                &func_def.occur_fates,
                &version.calls,
                &version.ret_fate,
                &marked_drops,
                &move_horizons,
                &mut constraints,
                &scc_sigs,
                &mut locals,
                &func_def.body,
                &mut solver_annots,
            );

            equate_modes(
                &mut constraints,
                &ret_val_modes,
                &substitute_sig_modes(&extern_vars, &func_scc_sig.ret_modes),
            );

            let arg_drop_epilogue_annot = annot_local_drops(
                &locals.local_binding(flat::ARG_LOCAL).val_modes,
                &marked_drops.arg_drop_epilogue,
            );

            (
                (func_id, version_id),
                SolverFullModeAnnots {
                    occur_modes: solver_annots
                        .occur_modes
                        .into_mapped(|_, modes| modes.unwrap()),
                    call_modes: solver_annots
                        .call_modes
                        .into_mapped(|_, modes| modes.unwrap()),
                    let_drop_epilogues: solver_annots
                        .let_drop_epilogues
                        .into_mapped(|_, modes| modes.unwrap()),
                    branch_drop_epilogues: solver_annots
                        .branch_drop_epilogues
                        .into_mapped(|_, modes| modes.unwrap()),
                    drop_prologues: solver_annots
                        .drop_prologues
                        .into_mapped(|_, modes| modes.unwrap()),
                    retain_epilogues: solver_annots
                        .retain_epilogues
                        .into_mapped(|_, modes| modes.unwrap()),
                    arg_drop_epilogue: arg_drop_epilogue_annot,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();

    let solutions = constraints.solve(&extern_vars);

    let extern_constraints = extern_vars.map(|_, var| solutions[var].clone());

    let mut remaining_func_sigs = scc_sigs.func_sigs;
    for ((func_id, version_id), solver_annots) in func_solver_annots {
        let scc_sig = remaining_func_sigs.remove(&(func_id, version_id)).unwrap();

        let extracted_annots = mode::ModeAnnots {
            extern_constraints: extern_constraints.clone(),
            arg_modes: scc_sig.arg_modes,
            ret_modes: scc_sig.ret_modes,
            occur_modes: solver_annots
                .occur_modes
                .into_mapped(|_, modes| extract_occur_modes(&solutions, modes)),
            call_modes: solver_annots
                .call_modes
                .into_mapped(|_, modes| modes.into_mapped(|_, var| solutions[var].clone())),
            let_drop_epilogues: solver_annots
                .let_drop_epilogues
                .into_mapped(|_, drops| extract_drops(&solutions, drops)),
            branch_drop_epilogues: solver_annots
                .branch_drop_epilogues
                .into_mapped(|_, drops| extract_drops(&solutions, drops)),
            arg_drop_epilogue: extract_drop_modes(&solutions, solver_annots.arg_drop_epilogue),
            drop_prologues: solver_annots
                .drop_prologues
                .into_mapped(|_, modes| extract_drops(&solutions, modes)),
            retain_epilogues: solver_annots
                .retain_epilogues
                .into_mapped(|_, modes| extract_retains(&solutions, modes)),
        };

        debug_assert!(func_annots[func_id][version_id].is_none());
        func_annots[func_id][version_id] = Some(extracted_annots);
    }
}

pub fn annot_modes(
    program: spec::Program,
    elision_mode: cli::RcMode,
    progress: impl ProgressLogger,
) -> mode::Program {
    let mut progress = progress.start_session(Some(program.funcs.len()));

    let sccs = find_sccs(&program.funcs);

    let mut func_annots = program
        .funcs
        .map(|_, func_def| func_def.versions.map(|_, _| None));

    for scc in sccs {
        annot_scc(elision_mode, &program, &mut func_annots, &scc);
        progress.update(scc.len());
    }

    progress.finish();

    mode::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs: IdVec::from_items(
            program
                .funcs
                .into_iter()
                .zip(func_annots.into_iter())
                .map(|((_, func_def), (_, modes))| {
                    debug_assert_eq!(func_def.versions.len(), modes.len());

                    mode::FuncDef {
                        purity: func_def.purity,
                        arg_type: func_def.arg_type,
                        ret_type: func_def.ret_type,
                        alias_sig: func_def.alias_sig,
                        mutation_sig: func_def.mutation_sig,
                        arg_fate: func_def.arg_fate,
                        body: func_def.body,
                        occur_fates: func_def.occur_fates,
                        expr_annots: func_def.expr_annots,
                        versions: func_def.versions,
                        modes: modes.into_mapped(|_, version_annots| version_annots.unwrap()),
                        profile_point: func_def.profile_point,
                    }
                })
                .collect(),
        ),
        func_symbols: program.func_symbols,
        profile_points: program.profile_points,
        main: program.main,
        main_version: program.main_version,
    }
}
