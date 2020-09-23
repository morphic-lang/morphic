use im_rc::OrdMap;
use std::collections::BTreeMap;

use crate::data::alias_annot_ast as alias;
use crate::data::alias_specialized_ast as spec;
use crate::data::anon_sum_ast as anon;
use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast as mode;
use crate::stack_path;
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

/// This struct is used to represent the uses of let-bound variables *inside* the let block in which
/// they are defined.
///
/// The keys of the `uses` map should be a subset of the local ids bound in the let block; no other
/// variables should be present.
#[derive(Clone, Debug)]
struct LetUses {
    uses: BTreeMap<flat::LocalId, OrdMap<mode::StackPath, UseKind>>,
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
                result.insert(path, OccurKind::Intermediate);
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
) {
    let this_occur_kinds = mark_occur(
        typedefs,
        locals.local_binding(occur.1),
        &occur_fates[occur.0],
        ret_fates,
        future_uses.uses.get(&occur.1),
        expr_uses.uses.get(&occur.1),
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

// This is a backwards data-flow pass, so all variable occurrence should be processed in reverse
// order, both across expressions and within each expression.
//
// TODO: This doesn't have great asymptotics for deeply nested expressions, e.g. long chains of
// if/else-if branches.  Can we do better?
fn mark_expr_occurs<'a>(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    locals: &mut MarkOccurContext<'a>,
    occur_fates: &IdVec<fate::OccurId, fate::Fate>,
    ret_fates: &BTreeMap<alias::RetName, spec::RetFate>,
    future_uses: &FutureUses,
    expr: &'a fate::Expr,
    occur_kinds: &mut IdVec<fate::OccurId, Option<BTreeMap<mode::StackPath, OccurKind>>>,
    let_block_uses: &mut IdVec<fate::LetBlockId, Option<LetUses>>,
    branch_block_uses: &mut IdVec<fate::BranchBlockId, Option<ExprUses>>,
) -> ExprUses {
    debug_assert!(future_uses
        .uses
        .get_max()
        .map(|(flat::LocalId(max_id), _)| *max_id < locals.len())
        .unwrap_or(true));

    let mut expr_uses = ExprUses {
        uses: OrdMap::new(),
    };

    // We need to pass `locals`, `occur_kinds`, and `expr_uses` as arguments to appease the borrow
    // checker.
    let mark = |locals, occur_kinds, expr_uses, occur| {
        mark_occur_mut(
            typedefs,
            locals,
            occur_fates,
            ret_fates,
            occur,
            future_uses,
            expr_uses,
            occur_kinds,
        );
    };

    match &expr.kind {
        fate::ExprKind::Local(local) => {
            mark(locals, occur_kinds, &mut expr_uses, *local);
        }

        fate::ExprKind::Call(_, _, _, _, _, _, arg) => {
            mark(locals, occur_kinds, &mut expr_uses, *arg);
        }

        fate::ExprKind::Branch(discrim, cases, _ret_type) => {
            for (block_id, _cond, body) in cases {
                let case_uses = mark_expr_occurs(
                    typedefs,
                    locals,
                    occur_fates,
                    ret_fates,
                    future_uses,
                    body,
                    occur_kinds,
                    let_block_uses,
                    branch_block_uses,
                );

                debug_assert!(branch_block_uses[block_id].is_none());
                branch_block_uses[block_id] = Some(case_uses.clone());

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
                    typedefs,
                    sub_locals,
                    occur_fates,
                    ret_fates,
                    *final_local,
                    future_uses,
                    &mut expr_uses,
                    occur_kinds,
                );
                internal_future_uses.add_expr_uses(&expr_uses);

                for (idx, (_, rhs)) in bindings.iter().enumerate().rev() {
                    let binding_local = flat::LocalId(idx + locals_offset);

                    // NOTE: After truncation, `sub_locals` contains all locals *strictly* before
                    // `binding_local`.
                    sub_locals.truncate(binding_local.0);
                    internal_future_uses.uses.remove(&binding_local);

                    let rhs_uses = mark_expr_occurs(
                        typedefs,
                        sub_locals,
                        occur_fates,
                        ret_fates,
                        &internal_future_uses,
                        rhs,
                        occur_kinds,
                        let_block_uses,
                        branch_block_uses,
                    );
                    internal_future_uses.add_expr_uses(&rhs_uses);
                    merge_uses(&mut expr_uses.uses, &rhs_uses.uses);
                }

                // We need to clean up `expr_uses` so it contains only variables in the enclosing
                // scope (outside this let block), and we also need to record all the uses of
                // variables bound in this let block in `let_block_uses`.
                let mut let_uses = LetUses {
                    uses: BTreeMap::new(),
                };
                for bound_local in
                    (locals_offset..locals_offset + bindings.len()).map(flat::LocalId)
                {
                    if let Some(use_kinds) = expr_uses.uses.remove(&bound_local) {
                        let_uses.uses.insert(bound_local, use_kinds);
                    }
                }

                debug_assert!(let_block_uses[block_id].is_none());
                let_block_uses[block_id] = Some(let_uses);
            });
        }

        _ => todo!(),
    }

    debug_assert!(expr_uses
        .uses
        .get_max()
        .map(|(flat::LocalId(max_id), _)| *max_id < locals.len())
        .unwrap_or(true));

    expr_uses
}

#[derive(Clone, Debug)]
struct MarkedOccurs {
    occur_kinds: IdVec<fate::OccurId, BTreeMap<mode::StackPath, OccurKind>>,
    let_block_uses: IdVec<fate::LetBlockId, LetUses>,
    branch_block_uses: IdVec<fate::BranchBlockId, ExprUses>,
    arg_uses: OrdMap<mode::StackPath, UseKind>,
}

fn mark_program_occurs(
    program: &spec::Program,
) -> IdVec<first_ord::CustomFuncId, IdVec<spec::FuncVersionId, MarkedOccurs>> {
    program.funcs.map(|_, func_def| {
        func_def.versions.map(|_, version| {
            let mut occur_kinds = IdVec::from_items(vec![None; func_def.occur_fates.len()]);
            let mut let_block_uses = IdVec::from_items(vec![None; func_def.num_let_blocks]);
            let mut branch_block_uses = IdVec::from_items(vec![None; func_def.num_branch_blocks]);

            let mut locals = LocalContext::new();
            locals.add_local(MarkOccurLocalInfo {
                type_: &func_def.arg_type,
                decl_site: DeclarationSite::Arg,
            });

            let body_uses = mark_expr_occurs(
                &program.custom_types,
                &mut locals,
                &func_def.occur_fates,
                &version.ret_fate,
                &FutureUses {
                    uses: OrdMap::new(),
                },
                &func_def.body,
                &mut occur_kinds,
                &mut let_block_uses,
                &mut branch_block_uses,
            );

            debug_assert!(body_uses.uses.keys().all(|&local| local == flat::ARG_LOCAL));

            MarkedOccurs {
                occur_kinds: occur_kinds.into_mapped(|_, kinds| kinds.unwrap()),
                let_block_uses: let_block_uses.into_mapped(|_, uses| uses.unwrap()),
                branch_block_uses: branch_block_uses.into_mapped(|_, uses| uses.unwrap()),
                arg_uses: body_uses
                    .uses
                    .get(&flat::ARG_LOCAL)
                    .cloned()
                    .unwrap_or_else(OrdMap::new),
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
