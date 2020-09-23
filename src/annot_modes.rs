use im_rc::OrdMap;
use std::collections::{BTreeMap, BTreeSet};

use crate::alias_spec_flag::lookup_concrete_cond;
use crate::data::alias_annot_ast as alias;
use crate::data::alias_specialized_ast as spec;
use crate::data::anon_sum_ast as anon;
use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast as mode;
use crate::stack_path;
use crate::util::disjunction::Disj;
use crate::util::id_vec::IdVec;
use crate::util::local_context::LocalContext;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum OccurKind {
    Intermediate,
    Final,
    Unused,
}

// TODO: Should we unify this with `OccurKind`?
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
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    local_info: &MarkOccurLocalInfo,
    fate: &fate::Fate,
    ret_fates: &BTreeMap<alias::RetName, spec::RetFate>,
    future_uses_after_expr: Option<&OrdMap<mode::StackPath, UseKind>>,
    future_uses_in_expr: Option<&OrdMap<mode::StackPath, UseKind>>,
    to_be_mutated: Option<&BTreeSet<mode::StackPath>>,
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
                let is_mutated = to_be_mutated
                    .map(|mutated| mutated.contains(&path))
                    .unwrap_or(false);

                if is_mutated {
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
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    locals: &MarkOccurContext<'a>,
    occur_fates: &IdVec<fate::OccurId, fate::Fate>,
    ret_fates: &BTreeMap<alias::RetName, spec::RetFate>,
    occur: fate::Local,
    future_uses: &FutureUses,
    expr_uses: &mut ExprUses,
    occur_kinds: &mut IdVec<fate::OccurId, Option<BTreeMap<mode::StackPath, OccurKind>>>,
    to_be_mutated: &BTreeMap<flat::LocalId, BTreeSet<mode::StackPath>>,
) {
    let this_occur_kinds = mark_occur(
        typedefs,
        locals.local_binding(occur.1),
        &occur_fates[occur.0],
        ret_fates,
        future_uses.uses.get(&occur.1),
        expr_uses.uses.get(&occur.1),
        to_be_mutated.get(&occur.1),
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

// This is a backwards data-flow pass, so all variable occurrences should be processed in reverse
// order, both across expressions and within each expression.
//
// TODO: This doesn't have great asymptotics for deeply nested expressions, e.g. long chains of
// if/else-if branches.  Can we do better?
fn mark_expr_occurs<'a>(
    orig: &spec::Program,
    this_version: &spec::FuncVersion,
    locals: &mut MarkOccurContext<'a>,
    occur_fates: &IdVec<fate::OccurId, fate::Fate>,
    future_uses: &FutureUses,
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
    let mark = |locals, occur_kinds, expr_uses, occur| {
        mark_occur_mut(
            &orig.custom_types,
            locals,
            occur_fates,
            &this_version.ret_fate,
            occur,
            future_uses,
            expr_uses,
            occur_kinds,
            &BTreeMap::new(),
        );
    };

    match &expr.kind {
        fate::ExprKind::Local(local) => {
            mark(locals, occur_kinds, &mut expr_uses, *local);
        }

        fate::ExprKind::Call(_, _, callee, arg_aliases, _, _, arg) => {
            // It's not important for `to_be_mutated` to contain directly / unconditionally mutated
            // paths in the argument, because those will already be annotated with "owned" fates by
            // fate analysis.  We only care about collecting paths which are mutated *indirectly*
            // via aliases, and which fate analysis therefore can't catch.
            let mut to_be_mutated = BTreeMap::new();
            for (alias::ArgName(arg_field_path), callee_cond) in
                &orig.funcs[callee].mutation_sig.arg_mutation_conds
            {
                match callee_cond {
                    Disj::True => {
                        // We don't need to consult the argument's folded aliases here, because any
                        // two argument field paths related by a folded alias will collapse down to
                        // the same stack path.
                        //
                        // Also, note that even if we were to miss a potential mutation here (which
                        // doesn't appear to be possible, but there could always be bugs...), that
                        // would only result in a precision / optimization issue, and wouldn't
                        // threaten soundness.  Even if we were to set `to_be_mutated` to the empty
                        // map for all calls, RC elision would remain perfectly sound (but could
                        // result in deoptimizations in downstream mutation optimization passes).
                        for ((other_local, other_field_path), symbolic_cond) in
                            &arg_aliases[arg_field_path].aliases
                        {
                            let concretely_aliased =
                                lookup_concrete_cond(&this_version.aliases, symbolic_cond);

                            if concretely_aliased {
                                let (other_stack_path, _) =
                                    stack_path::split_stack_heap(other_field_path.clone());

                                to_be_mutated
                                    .entry(*other_local)
                                    .or_insert_with(BTreeSet::new)
                                    .insert(other_stack_path);
                            }
                        }
                    }
                    Disj::Any(_) => {
                        // If this mutation occurs, it's due to an alias edge, so we don't need to
                        // explicitly handle it here; if it occurs under the current set of concrete
                        // aliasing edges for this version of the function, we'll propagate it via
                        // the aliases incident on an unconditionally mutated path.
                        //
                        // TODO: Could we do this in mutation analysis as well?  Maybe mutation
                        // signatures only need to explicitly store the *unconditionally* mutated
                        // argument names?
                    }
                }
            }

            mark_occur_mut(
                &orig.custom_types,
                locals,
                occur_fates,
                &this_version.ret_fate,
                *arg,
                future_uses,
                &mut expr_uses,
                occur_kinds,
                &to_be_mutated,
            );

            mark_tentative_prologue_drops(
                future_uses,
                &expr_uses,
                &to_be_mutated,
                &mut tentative_drop_prologue,
            );
        }

        fate::ExprKind::Branch(discrim, cases, _ret_type) => {
            // TODO: This was the only place where branch block ids were originally intended to be
            // used. Should we remove them now that we don't use them here?
            for (_, _cond, body) in cases {
                let case_uses = mark_expr_occurs(
                    orig,
                    this_version,
                    locals,
                    occur_fates,
                    future_uses,
                    body,
                    occur_kinds,
                    tentative_drop_prologues,
                );

                merge_uses(&mut expr_uses.uses, &case_uses.uses);
            }

            mark(locals, occur_kinds, &mut expr_uses, *discrim);
        }

        fate::ExprKind::LetMany(block_id, bindings, final_local) => {
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

                    let rhs_uses = mark_expr_occurs(
                        orig,
                        this_version,
                        sub_locals,
                        occur_fates,
                        &internal_future_uses,
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

        _ => todo!(),
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

fn mark_program_occurs(
    program: &spec::Program,
) -> IdVec<first_ord::CustomFuncId, IdVec<spec::FuncVersionId, MarkedOccurs>> {
    program.funcs.map(|_, func_def| {
        func_def.versions.map(|_, version| {
            let mut occur_kinds = IdVec::from_items(vec![None; func_def.occur_fates.len()]);
            let mut tentative_drop_prologues =
                IdVec::from_items(vec![None; func_def.expr_fates.len()]);

            let mut locals = LocalContext::new();
            locals.add_local(MarkOccurLocalInfo {
                type_: &func_def.arg_type,
                decl_site: DeclarationSite::Arg,
            });

            let body_uses = mark_expr_occurs(
                program,
                version,
                &mut locals,
                &func_def.occur_fates,
                &FutureUses {
                    uses: OrdMap::new(),
                },
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
        })
    })
}

fn annot_modes(program: spec::Program) -> mode::Program {
    // TODO: Mark tail calls, and adapt move-marking logic to ensure all drops and moves happen
    // prior to tail calls.

    let _marked_occurs = mark_program_occurs(&program);

    todo!()
}
