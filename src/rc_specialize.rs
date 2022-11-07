use im_rc::{OrdMap, OrdSet, Vector};
use std::collections::{BTreeMap, BTreeSet};

use crate::data::alias_annot_ast as alias;
use crate::data::alias_specialized_ast as spec;
use crate::data::anon_sum_ast as anon;
use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast as mode;
use crate::data::mutation_annot_ast as mutation;
use crate::data::rc_specialized_ast as rc;
use crate::field_path;
use crate::util::disjunction::Disj;
use crate::util::graph::{strongly_connected, Graph};
use crate::util::id_vec::IdVec;
use crate::util::im_rc_ext::VectorExtensions;
use crate::util::inequality_graph as ineq;
use crate::util::instance_queue::InstanceQueue;
use crate::util::local_context::LocalContext;
use crate::util::norm_pair::NormPair;

id_type!(ModeSpecFuncId);

#[derive(Clone, Debug)]
struct ModeSpecialization {
    func: first_ord::CustomFuncId,
    version: spec::FuncVersionId,
    modes: IdVec<ineq::ExternalVarId, mode::Mode>,
    calls: IdVec<fate::CallId, ModeSpecFuncId>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ModeInstance {
    func: first_ord::CustomFuncId,
    version: spec::FuncVersionId,
    modes: IdVec<ineq::ExternalVarId, mode::Mode>,
}

fn specialize_modes(
    funcs: &IdVec<first_ord::CustomFuncId, mode::FuncDef>,
    main: first_ord::CustomFuncId,
    main_version: spec::FuncVersionId,
) -> (IdVec<ModeSpecFuncId, ModeSpecialization>, ModeSpecFuncId) {
    let mut insts: InstanceQueue<ModeInstance, ModeSpecFuncId> = InstanceQueue::new();

    let main_spec = insts.resolve(ModeInstance {
        func: main,
        version: main_version,
        // The main function may appear in an SCC containing functions with nontrivial mode
        // parameters, which will leak into main's signature.
        modes: funcs[main].modes[main_version]
            .extern_constraints
            .map(|_, bound| bound.lte_const),
    });

    let mut specialized = IdVec::new();

    while let Some((spec_id, instance)) = insts.pop_pending() {
        let func_def = &funcs[instance.func];

        let version_annots = &func_def.versions[instance.version];
        let mode_annots = &func_def.modes[instance.version];

        let spec_calls = version_annots
            .calls
            .map(|call_id, &(callee_id, callee_version)| {
                let callee_modes = mode_annots.call_modes[call_id]
                    .map(|_, bound| get_mode(&instance.modes, bound));

                insts.resolve(ModeInstance {
                    func: callee_id,
                    version: callee_version,
                    modes: callee_modes,
                })
            });

        let pushed_id = specialized.push(ModeSpecialization {
            func: instance.func,
            version: instance.version,
            modes: instance.modes,
            calls: spec_calls,
        });

        // We enqueue instances to resolve in the order in which their ids are generated, so this
        // should always hold.
        debug_assert_eq!(pushed_id, spec_id);
    }

    (specialized, main_spec)
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ReleasePaths {
    release_paths: BTreeSet<mode::StackPath>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RetainPaths {
    retain_paths: BTreeSet<mode::StackPath>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SccCall {
    // A call in the same SCC as the caller
    //
    // Specialized functions in an SCC are uniquely identified by their `first_ord::CustomFuncId`,
    // because both alias specialization and mode annotation should both uphold the invariant that
    // each `first_ord::CustomFuncId` appears at most once in each SCC in the mode-specialized call
    // graph.
    RecCall(first_ord::CustomFuncId),
    Call(rc::CustomFuncId),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ConcreteRcOps<Call> {
    func: first_ord::CustomFuncId,
    calls: IdVec<fate::CallId, Call>,
    release_prologues: IdVec<fate::ExprId, Vec<(flat::LocalId, ReleasePaths)>>,
    retain_epilogues: IdVec<fate::RetainPointId, RetainPaths>,
    occur_retains: IdVec<fate::OccurId, RetainPaths>,
    let_release_epilogues: IdVec<fate::LetBlockId, Vec<(flat::LocalId, ReleasePaths)>>,
    branch_release_epilogues: IdVec<fate::BranchBlockId, Vec<(flat::LocalId, ReleasePaths)>>,
    arg_release_epilogue: ReleasePaths,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ConcreteScc {
    concrete_funcs: BTreeMap<first_ord::CustomFuncId, ConcreteRcOps<SccCall>>,
}

fn get_mode(
    modes: &IdVec<ineq::ExternalVarId, mode::Mode>,
    bound: &ineq::UpperBound<mode::Mode>,
) -> mode::Mode {
    // TODO: Should we make this short-circuiting?
    bound
        .lte_vars
        .iter()
        .map(|var| modes[var])
        .min()
        .unwrap_or(bound.lte_const)
}

fn concretize_drop_modes(
    modes: &IdVec<ineq::ExternalVarId, mode::Mode>,
    drops: &mode::DropModes,
) -> ReleasePaths {
    ReleasePaths {
        release_paths: drops
            .dropped_paths
            .iter()
            .filter_map(|(path, bound)| match get_mode(modes, bound) {
                mode::Mode::Owned => Some(path.clone()),
                mode::Mode::Borrowed => None,
            })
            .collect(),
    }
}

fn concretize_drops(
    modes: &IdVec<ineq::ExternalVarId, mode::Mode>,
    drops: &Vec<(flat::LocalId, mode::DropModes)>,
) -> Vec<(flat::LocalId, ReleasePaths)> {
    drops
        .iter()
        .map(|(local, dropped_paths)| (*local, concretize_drop_modes(modes, dropped_paths)))
        .collect()
}

fn concretize_retains(
    modes: &IdVec<ineq::ExternalVarId, mode::Mode>,
    retains: &mode::RetainModes,
) -> RetainPaths {
    RetainPaths {
        retain_paths: retains
            .retained_paths
            .iter()
            .filter_map(|(path, bound)| match get_mode(modes, bound) {
                mode::Mode::Owned => Some(path.clone()),
                mode::Mode::Borrowed => None,
            })
            .collect(),
    }
}

fn concretize_occurs(
    modes: &IdVec<ineq::ExternalVarId, mode::Mode>,
    occur: &mode::OccurModes,
) -> RetainPaths {
    RetainPaths {
        retain_paths: occur
            .path_modes
            .iter()
            .filter_map(|(path, path_mode)| match path_mode {
                mode::PathOccurMode::Intermediate {
                    src: src_bound,
                    dest: dest_bound,
                } => {
                    let src = get_mode(modes, src_bound);
                    let dest = get_mode(modes, dest_bound);
                    debug_assert!(src <= dest);
                    match dest {
                        mode::Mode::Owned => Some(path.clone()),
                        mode::Mode::Borrowed => None,
                    }
                }
                mode::PathOccurMode::Final => None,
                mode::PathOccurMode::Unused => {
                    // TODO: Add an assert that this path has mode `Borrowed` (this will require
                    // tracking the mode bound in the annotations)
                    None
                }
            })
            .collect(),
    }
}

fn deduplicate_specializations(
    funcs: &IdVec<first_ord::CustomFuncId, mode::FuncDef>,
    specializations: &IdVec<ModeSpecFuncId, ModeSpecialization>,
    main_spec: ModeSpecFuncId,
) -> (
    IdVec<rc::CustomFuncId, ConcreteRcOps<rc::CustomFuncId>>,
    rc::CustomFuncId,
) {
    let sccs = strongly_connected(&Graph {
        edges_out: specializations.map(|_, specialization| specialization.calls.items.clone()),
    });

    let mut concrete_funcs: IdVec<rc::CustomFuncId, Option<ConcreteRcOps<rc::CustomFuncId>>> =
        IdVec::new();

    let mut cache: BTreeMap<ConcreteScc, BTreeMap<first_ord::CustomFuncId, rc::CustomFuncId>> =
        BTreeMap::new();

    let mut known_dedups: IdVec<ModeSpecFuncId, Option<rc::CustomFuncId>> =
        IdVec::from_items(vec![None; specializations.len()]);

    for scc in &sccs {
        let mut scc_concrete_funcs = BTreeMap::new();

        for spec_id in scc {
            let specialization = &specializations[spec_id];

            let calls =
                specialization
                    .calls
                    .map(|_, callee_spec| match known_dedups[callee_spec] {
                        Some(callee_dedup) => SccCall::Call(callee_dedup),
                        None => {
                            let callee_func = specializations[callee_spec].func;

                            debug_assert_eq!(
                                scc.iter()
                                    .filter(|&other_spec| specializations[other_spec].func
                                        == callee_func)
                                    .count(),
                                1
                            );

                            SccCall::RecCall(callee_func)
                        }
                    });

            let modes = &specialization.modes;
            let mode_annots = &funcs[specialization.func].modes[specialization.version];

            let release_prologues = mode_annots
                .drop_prologues
                .map(|_, drops| concretize_drops(modes, drops));

            let retain_epilogues = mode_annots
                .retain_epilogues
                .map(|_, retains| concretize_retains(modes, retains));

            let occur_retains = mode_annots
                .occur_modes
                .map(|_, occur_modes| concretize_occurs(modes, occur_modes));

            let let_release_epilogues = mode_annots
                .let_drop_epilogues
                .map(|_, drops| concretize_drops(modes, drops));

            let branch_release_epilogues = mode_annots
                .branch_drop_epilogues
                .map(|_, drops| concretize_drops(modes, drops));

            let arg_release_epilogue = concretize_drop_modes(modes, &mode_annots.arg_drop_epilogue);

            let existing = scc_concrete_funcs.insert(
                specialization.func,
                ConcreteRcOps {
                    func: specialization.func,
                    calls,
                    release_prologues,
                    retain_epilogues,
                    occur_retains,
                    let_release_epilogues,
                    branch_release_epilogues,
                    arg_release_epilogue,
                },
            );

            // Alias specialization and mode annotation should both uphold the invariant that each
            // `first_ord::CustomFuncId` appears at most once in each SCC in the mode-specialized
            // call graph.
            debug_assert!(existing.is_none());
        }

        let concrete_scc = ConcreteScc {
            concrete_funcs: scc_concrete_funcs,
        };

        match cache.get(&concrete_scc) {
            Some(cached_scc_dedups) => {
                for spec_id in scc {
                    debug_assert!(known_dedups[spec_id].is_none());
                    known_dedups[spec_id] = Some(cached_scc_dedups[&specializations[spec_id].func]);
                }
            }

            None => {
                // This concretization of the SCC isn't in the `cache`.
                //
                // We need to:
                // - Mint fresh `rc::CustomFuncId`s for all the function specializations in this SCC
                //   (in `concrete_funcs`)
                // - Associate those fresh deduplicated ids to the original un-deduplicated ids for
                //   this SCC (in `known_dedups`)
                // - Populate `concrete_funcs` with the actual concrete RC ops associated to each
                //   new deduplicated/concretized function we're adding
                // - Register this concretization of the SCC in the `cache`.

                let scc_fresh_ids = scc
                    .iter()
                    .map(|spec_id| {
                        let fresh_id = concrete_funcs.push(None);

                        debug_assert!(known_dedups[spec_id].is_none());
                        known_dedups[spec_id] = Some(fresh_id);

                        (specializations[spec_id].func, fresh_id)
                    })
                    .collect::<BTreeMap<_, _>>();

                for (func_id, dedup_id) in &scc_fresh_ids {
                    let ops = &concrete_scc.concrete_funcs[func_id];

                    let resolved_calls = ops.calls.map(|_, &call| match call {
                        SccCall::Call(dedup_id) => dedup_id,
                        SccCall::RecCall(func_id) => scc_fresh_ids[&func_id],
                    });

                    let resolved_ops = ConcreteRcOps {
                        func: ops.func,
                        calls: resolved_calls,
                        release_prologues: ops.release_prologues.clone(),
                        retain_epilogues: ops.retain_epilogues.clone(),
                        occur_retains: ops.occur_retains.clone(),
                        let_release_epilogues: ops.let_release_epilogues.clone(),
                        branch_release_epilogues: ops.branch_release_epilogues.clone(),
                        arg_release_epilogue: ops.arg_release_epilogue.clone(),
                    };

                    debug_assert!(concrete_funcs[dedup_id].is_none());
                    concrete_funcs[dedup_id] = Some(resolved_ops);
                }

                cache.insert(concrete_scc, scc_fresh_ids);
            }
        }
    }

    (
        concrete_funcs.into_mapped(|_, concrete| concrete.unwrap()),
        known_dedups[main_spec].unwrap(),
    )
}

// TODO: Can we unify this with the `LetManyBuilder` in `flatten`, or the `LowAstBuilder` in
// `lower_structures`?
#[derive(Clone, Debug)]
struct LetManyBuilder {
    free_locals: usize,
    bindings: Vec<(anon::Type, rc::Expr)>,
}

impl LetManyBuilder {
    fn new(free_locals: usize) -> Self {
        LetManyBuilder {
            free_locals,
            bindings: Vec::new(),
        }
    }

    fn add_binding(&mut self, type_: anon::Type, rhs: rc::Expr) -> rc::LocalId {
        let binding_id = rc::LocalId(self.free_locals + self.bindings.len());
        self.bindings.push((type_, rhs));
        binding_id
    }

    fn to_expr(self, ret: rc::LocalId) -> rc::Expr {
        debug_assert!(ret.0 < self.free_locals + self.bindings.len());
        rc::Expr::LetMany(self.bindings, ret)
    }

    fn child(&self) -> LetManyBuilder {
        LetManyBuilder::new(self.free_locals + self.bindings.len())
    }
}

#[derive(Clone, Debug)]
struct LocalInfo<'a> {
    type_: &'a anon::Type,
    new_id: rc::LocalId,
}

#[derive(Clone, Debug)]
enum RcOpPlan {
    NoOp,
    LeafOp,
    OnTupleFields(BTreeMap<usize, RcOpPlan>),
    OnVariantCases(BTreeMap<first_ord::VariantId, RcOpPlan>),
    OnCustom(first_ord::CustomTypeId, Box<RcOpPlan>),
}

impl RcOpPlan {
    fn add_leaf_path(&mut self, path: &mode::StackPath) {
        let mut curr = self;
        for field in path.iter() {
            if matches!(&curr, RcOpPlan::NoOp) {
                *curr = match field {
                    mode::StackField::Field(_) => RcOpPlan::OnTupleFields(BTreeMap::new()),
                    mode::StackField::Variant(_) => RcOpPlan::OnVariantCases(BTreeMap::new()),
                    mode::StackField::Custom(custom_id) => {
                        RcOpPlan::OnCustom(*custom_id, Box::new(RcOpPlan::NoOp))
                    }
                };
            }

            curr = match (curr, field) {
                (RcOpPlan::OnTupleFields(sub_plans), mode::StackField::Field(idx)) => {
                    sub_plans.entry(*idx).or_insert(RcOpPlan::NoOp)
                }
                (RcOpPlan::OnVariantCases(sub_plans), mode::StackField::Variant(variant_id)) => {
                    sub_plans.entry(*variant_id).or_insert(RcOpPlan::NoOp)
                }
                (
                    RcOpPlan::OnCustom(custom_id, sub_plan),
                    mode::StackField::Custom(field_custom_id),
                ) => {
                    debug_assert_eq!(custom_id, field_custom_id);
                    &mut **sub_plan
                }
                _ => unreachable!(),
            };
        }
        debug_assert!(matches!(&curr, RcOpPlan::NoOp));
        *curr = RcOpPlan::LeafOp;
    }
}

fn build_plan(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    rc_op: rc::RcOp,
    root: rc::LocalId,
    root_type: &anon::Type,
    plan: &RcOpPlan,
    prefix: alias::FieldPath,
    // These are the statuses of the top-level local variables which whose components we are
    // recursing through.  The statuses relevant to the `root` for this call appear at those paths
    // in `local_statuses` which begin with `prefix`.
    local_statuses: &OrdMap<alias::FieldPath, mutation::LocalStatus>,
    builder: &mut LetManyBuilder,
) {
    match plan {
        RcOpPlan::NoOp => {}

        RcOpPlan::LeafOp => {
            let (container_type, item_type) = match root_type {
                anon::Type::Array(item_type) => (rc::ContainerType::Array, item_type),
                anon::Type::HoleArray(item_type) => (rc::ContainerType::HoleArray, item_type),
                anon::Type::Boxed(item_type) => (rc::ContainerType::Boxed, item_type),
                _ => unreachable!(),
            };

            let leaf_statuses = field_path::get_names_in(typedefs, root_type)
                .into_iter()
                .filter_map(|(leaf_path, _)| {
                    // Due to folding, some `prefix + leaf_path` paths may not actually exist
                    local_statuses
                        .get(&(prefix.clone() + leaf_path.clone()))
                        .map(|status| (leaf_path, status.clone()))
                })
                .collect();

            builder.add_binding(
                anon::Type::Tuple(vec![]),
                rc::Expr::RcOp(
                    rc_op,
                    container_type,
                    (**item_type).clone(),
                    leaf_statuses,
                    root,
                ),
            );
        }

        RcOpPlan::OnTupleFields(sub_plans) => {
            let field_types = if let anon::Type::Tuple(field_types) = root_type {
                field_types
            } else {
                unreachable!()
            };

            for (idx, sub_plan) in sub_plans {
                let field_type = &field_types[*idx];
                let field_local =
                    builder.add_binding(field_type.clone(), rc::Expr::TupleField(root, *idx));
                build_plan(
                    typedefs,
                    rc_op,
                    field_local,
                    field_type,
                    sub_plan,
                    prefix.clone().add_back(alias::Field::Field(*idx)),
                    local_statuses,
                    builder,
                );
            }
        }

        RcOpPlan::OnVariantCases(sub_plans) => {
            let variant_types = if let anon::Type::Variants(variant_types) = root_type {
                variant_types
            } else {
                unreachable!()
            };

            let mut cases = Vec::new();
            for (variant_id, sub_plan) in sub_plans {
                let variant_type = &variant_types[variant_id];
                let cond = flat::Condition::Variant(*variant_id, Box::new(flat::Condition::Any));

                let mut case_builder = builder.child();
                let content_id = case_builder.add_binding(
                    variant_type.clone(),
                    rc::Expr::UnwrapVariant(*variant_id, root),
                );
                build_plan(
                    typedefs,
                    rc_op,
                    content_id,
                    variant_type,
                    sub_plan,
                    prefix.clone().add_back(alias::Field::Variant(*variant_id)),
                    local_statuses,
                    &mut case_builder,
                );

                // We need to return *something* from this branch arm, so we return a `()` value.
                //
                // TODO: Should we reuse the result of the generated RC op to make the generated
                // code for this case slightly easier to read?
                let unit_id =
                    case_builder.add_binding(anon::Type::Tuple(vec![]), rc::Expr::Tuple(vec![]));

                cases.push((cond, case_builder.to_expr(unit_id)))
            }
            cases.push((flat::Condition::Any, rc::Expr::Tuple(vec![])));

            builder.add_binding(
                anon::Type::Tuple(vec![]),
                rc::Expr::Branch(root, cases, anon::Type::Tuple(vec![])),
            );
        }

        RcOpPlan::OnCustom(custom_id, sub_plan) => {
            debug_assert_eq!(root_type, &anon::Type::Custom(*custom_id));

            let content_type = &typedefs[custom_id];

            let content_id = builder.add_binding(
                content_type.clone(),
                rc::Expr::UnwrapCustom(*custom_id, root),
            );
            build_plan(
                typedefs,
                rc_op,
                content_id,
                content_type,
                sub_plan,
                prefix.add_back(alias::Field::Custom(*custom_id)),
                local_statuses,
                builder,
            );
        }
    }
}

fn build_rc_ops(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    rc_op: rc::RcOp,
    local: rc::LocalId,
    local_type: &anon::Type,
    local_statuses: &OrdMap<alias::FieldPath, mutation::LocalStatus>,
    paths: &BTreeSet<mode::StackPath>,
    builder: &mut LetManyBuilder,
) {
    let mut plan = RcOpPlan::NoOp;
    for path in paths {
        plan.add_leaf_path(path);
    }
    build_plan(
        typedefs,
        rc_op,
        local,
        local_type,
        &plan,
        Vector::new(),
        local_statuses,
        builder,
    );
}

fn build_releases(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    locals: &LocalContext<flat::LocalId, LocalInfo>,
    mutation_ctx: &mutation::ContextSnapshot,
    releases: &Vec<(flat::LocalId, ReleasePaths)>,
    builder: &mut LetManyBuilder,
) {
    for (flat_local, release_paths) in releases {
        let local_info = locals.local_binding(*flat_local);
        build_rc_ops(
            typedefs,
            rc::RcOp::Release,
            local_info.new_id,
            local_info.type_,
            &mutation_ctx.locals[flat_local].statuses,
            &release_paths.release_paths,
            builder,
        );
    }
}

fn build_expr_kind<'a>(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    ops: &ConcreteRcOps<rc::CustomFuncId>,
    locals: &mut LocalContext<flat::LocalId, LocalInfo<'a>>,
    mutation_ctx: &mutation::ContextSnapshot,
    kind: &'a fate::ExprKind,
    result_type: &anon::Type,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    let build_occur_in_context = |locals: &mut LocalContext<flat::LocalId, LocalInfo<'a>>,
                                  ctx: &mutation::ContextSnapshot,
                                  occur: fate::Local,
                                  builder: &mut LetManyBuilder| {
        let local_info = locals.local_binding(occur.1);
        build_rc_ops(
            typedefs,
            rc::RcOp::Retain,
            local_info.new_id,
            local_info.type_,
            &ctx.locals[&occur.1].statuses,
            &ops.occur_retains[occur.0].retain_paths,
            builder,
        );
        local_info.new_id
    };

    let build_occur = |locals: &mut LocalContext<flat::LocalId, LocalInfo<'a>>,
                       occur: fate::Local,
                       builder: &mut LetManyBuilder| {
        build_occur_in_context(locals, mutation_ctx, occur, builder)
    };

    let array_statuses =
        |array_occur: &fate::Local| mutation_ctx.locals[&array_occur.1].statuses.clone();

    let new_expr = match kind {
        fate::ExprKind::Local(local) => {
            let rc_local = build_occur(locals, *local, builder);
            rc::Expr::Local(rc_local)
        }

        fate::ExprKind::Call(
            call_id,
            purity,
            _func,
            arg_aliases,
            arg_folded_aliases,
            arg_local,
        ) => {
            let rc_arg_local = build_occur(locals, *arg_local, builder);

            let mut arg_internal_aliases = OrdMap::new();
            for (arg_path, aliases) in arg_aliases {
                for ((other, other_path), alias_cond) in &aliases.aliases {
                    if other == &arg_local.1 {
                        arg_internal_aliases
                            .entry(NormPair::new(arg_path.clone(), other_path.clone()))
                            .and_modify(|existing_cond| {
                                // Each argument-internal edge appears twice in the original
                                // `LocalAliases` structure.  The conditions on the two symmetric
                                // occurrences should match.
                                debug_assert_eq!(existing_cond, alias_cond);
                            })
                            .or_insert_with(|| alias_cond.clone());
                    }
                }
            }

            let rc_arg_aliases = rc::ArgAliases {
                aliases: arg_internal_aliases,
                folded_aliases: arg_folded_aliases.clone(),
            };

            let rc_callee_id = ops.calls[call_id];

            let arg_statuses = mutation_ctx.locals[&arg_local.1].statuses.clone();

            rc::Expr::Call(
                *purity,
                rc_callee_id,
                rc_arg_aliases,
                arg_statuses,
                rc_arg_local,
            )
        }

        fate::ExprKind::Branch(discrim, cases, branch_result_type) => {
            debug_assert_eq!(result_type, branch_result_type);

            let rc_discrim = build_occur(locals, *discrim, builder);

            let rc_cases = cases
                .iter()
                .map(|(block_id, cond, body, final_ctx)| {
                    let mut case_builder = builder.child();

                    let final_local =
                        build_expr(typedefs, ops, locals, body, result_type, &mut case_builder);

                    build_releases(
                        typedefs,
                        locals,
                        final_ctx,
                        &ops.branch_release_epilogues[block_id],
                        &mut case_builder,
                    );

                    (cond.clone(), case_builder.to_expr(final_local))
                })
                .collect();

            rc::Expr::Branch(rc_discrim, rc_cases, result_type.clone())
        }

        fate::ExprKind::LetMany(block_id, bindings, final_ctx, final_local) => {
            let rc_final_local = locals.with_scope(|sub_locals| {
                for (type_, rhs) in bindings {
                    let new_id = build_expr(typedefs, ops, sub_locals, rhs, type_, builder);

                    sub_locals.add_local(LocalInfo { type_, new_id });
                }

                let rc_final_local =
                    build_occur_in_context(sub_locals, final_ctx, *final_local, builder);

                build_releases(
                    typedefs,
                    sub_locals,
                    final_ctx,
                    &ops.let_release_epilogues[block_id],
                    builder,
                );

                rc_final_local
            });

            // Note: Early return!  We circumvent the usual return flow because we don't actually
            // want to create an expression directly corresponding to this 'let' block.  The 'let'
            // block's bindings just get absorbed into the ambient `builder`.
            return rc_final_local;
        }

        fate::ExprKind::Tuple(items) => rc::Expr::Tuple(
            items
                .iter()
                .map(|item| build_occur(locals, *item, builder))
                .collect(),
        ),

        fate::ExprKind::TupleField(tuple, index) => {
            rc::Expr::TupleField(build_occur(locals, *tuple, builder), *index)
        }

        fate::ExprKind::WrapVariant(variant_types, variant_id, content) => rc::Expr::WrapVariant(
            variant_types.clone(),
            *variant_id,
            build_occur(locals, *content, builder),
        ),

        fate::ExprKind::UnwrapVariant(variant_id, wrapped) => {
            rc::Expr::UnwrapVariant(*variant_id, build_occur(locals, *wrapped, builder))
        }

        fate::ExprKind::WrapBoxed(content_id, content_type) => rc::Expr::WrapBoxed(
            build_occur(locals, *content_id, builder),
            content_type.clone(),
        ),

        fate::ExprKind::UnwrapBoxed(wrapped_id, wrapped_type, item_statuses, retain_point) => {
            let new_expr = rc::Expr::UnwrapBoxed(
                build_occur(locals, *wrapped_id, builder),
                wrapped_type.clone(),
            );

            let item_id = builder.add_binding(wrapped_type.clone(), new_expr);

            build_rc_ops(
                typedefs,
                rc::RcOp::Retain,
                item_id,
                result_type,
                item_statuses,
                &ops.retain_epilogues[retain_point].retain_paths,
                builder,
            );

            // Note: Early return!  We circumbent the usual return flow because we want to insert
            // expressions after the expression whose id we're returning.
            return item_id;
        }

        fate::ExprKind::WrapCustom(content_type, content_id) => {
            rc::Expr::WrapCustom(*content_type, build_occur(locals, *content_id, builder))
        }

        fate::ExprKind::UnwrapCustom(wrapped_type, wrapped_id) => {
            rc::Expr::UnwrapCustom(*wrapped_type, build_occur(locals, *wrapped_id, builder))
        }

        fate::ExprKind::Intrinsic(intrinsic, local_id) => {
            rc::Expr::Intrinsic(*intrinsic, build_occur(locals, *local_id, builder))
        }

        fate::ExprKind::ArrayOp(op) => {
            let new_op = match op {
                fate::ArrayOp::Get(item_type, _, array, index, item_statuses, retain_point) => {
                    let new_expr = rc::Expr::ArrayOp(rc::ArrayOp::Get(
                        item_type.clone(),
                        array_statuses(array),
                        build_occur(locals, *array, builder),
                        build_occur(locals, *index, builder),
                    ));

                    let item_id = builder.add_binding(item_type.clone(), new_expr);

                    build_rc_ops(
                        typedefs,
                        rc::RcOp::Retain,
                        item_id,
                        result_type,
                        item_statuses,
                        &ops.retain_epilogues[retain_point].retain_paths,
                        builder,
                    );

                    // Note: Early return!  We circumbent the usual return flow because we want to insert
                    // expressions after the expression whose id we're returning.
                    return item_id;
                }

                fate::ArrayOp::Extract(item_type, _, array, index) => rc::ArrayOp::Extract(
                    item_type.clone(),
                    array_statuses(array),
                    build_occur(locals, *array, builder),
                    build_occur(locals, *index, builder),
                ),
                fate::ArrayOp::Len(item_type, _, array) => rc::ArrayOp::Len(
                    item_type.clone(),
                    array_statuses(array),
                    build_occur(locals, *array, builder),
                ),
                fate::ArrayOp::Push(item_type, _, array, item) => rc::ArrayOp::Push(
                    item_type.clone(),
                    array_statuses(array),
                    build_occur(locals, *array, builder),
                    build_occur(locals, *item, builder),
                ),
                fate::ArrayOp::Pop(item_type, _, array) => rc::ArrayOp::Pop(
                    item_type.clone(),
                    array_statuses(array),
                    build_occur(locals, *array, builder),
                ),
                fate::ArrayOp::Replace(item_type, _, hole_array, item) => rc::ArrayOp::Replace(
                    item_type.clone(),
                    array_statuses(hole_array),
                    build_occur(locals, *hole_array, builder),
                    build_occur(locals, *item, builder),
                ),
                fate::ArrayOp::Reserve(item_type, _, array, capacity) => rc::ArrayOp::Reserve(
                    item_type.clone(),
                    array_statuses(array),
                    build_occur(locals, *array, builder),
                    build_occur(locals, *capacity, builder),
                ),
            };
            rc::Expr::ArrayOp(new_op)
        }

        fate::ExprKind::IoOp(io_op) => {
            let new_io_op = match io_op {
                fate::IoOp::Input => rc::IoOp::Input,
                fate::IoOp::Output(_aliases, byte_array) => rc::IoOp::Output(
                    array_statuses(byte_array)[&Vector::new()].clone(),
                    build_occur(locals, *byte_array, builder),
                ),
            };

            rc::Expr::IoOp(new_io_op)
        }

        fate::ExprKind::Panic(result_type, message) => rc::Expr::Panic(
            result_type.clone(),
            array_statuses(message)[&Vector::new()].clone(),
            build_occur(locals, *message, builder),
        ),

        fate::ExprKind::ArrayLit(item_type, items) => rc::Expr::ArrayLit(
            item_type.clone(),
            items
                .iter()
                .map(|item| build_occur(locals, *item, builder))
                .collect(),
        ),

        fate::ExprKind::BoolLit(val) => rc::Expr::BoolLit(*val),
        fate::ExprKind::ByteLit(val) => rc::Expr::ByteLit(*val),
        fate::ExprKind::IntLit(val) => rc::Expr::IntLit(*val),
        fate::ExprKind::FloatLit(val) => rc::Expr::FloatLit(*val),
    };

    builder.add_binding(result_type.clone(), new_expr)
}

fn build_expr<'a>(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    ops: &ConcreteRcOps<rc::CustomFuncId>,
    locals: &mut LocalContext<flat::LocalId, LocalInfo<'a>>,
    expr: &'a fate::Expr,
    result_type: &anon::Type,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    build_releases(
        typedefs,
        locals,
        &expr.prior_context,
        &ops.release_prologues[expr.id],
        builder,
    );

    let new_local = build_expr_kind(
        typedefs,
        ops,
        locals,
        &expr.prior_context,
        &expr.kind,
        result_type,
        builder,
    );

    new_local
}

fn build_func(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    func_def: &mode::FuncDef,
    ops: &ConcreteRcOps<rc::CustomFuncId>,
) -> rc::FuncDef {
    // The builder starts with one free local for the argument.
    let mut builder = LetManyBuilder::new(1);

    let mut locals = LocalContext::new();
    locals.add_local(LocalInfo {
        type_: &func_def.arg_type,
        new_id: rc::ARG_LOCAL,
    });

    let ret_local = build_expr(
        typedefs,
        ops,
        &mut locals,
        &func_def.body,
        &func_def.ret_type,
        &mut builder,
    );

    debug_assert_eq!(locals.len(), 1);

    let arg_final_statuses = func_def
        .mutation_sig
        .arg_mutation_conds
        .iter()
        .map(|(arg_name, mutation_cond)| {
            (
                arg_name.0.clone(),
                mutation::LocalStatus {
                    mutated_cond: mutation_cond
                        .clone()
                        .into_mapped(mutation::MutationCondition::AliasCondition)
                        .or(Disj::Any(OrdSet::unit(
                            mutation::MutationCondition::ArgMutated(arg_name.clone()),
                        ))),
                },
            )
        })
        .collect();

    build_rc_ops(
        typedefs,
        rc::RcOp::Release,
        rc::ARG_LOCAL,
        &func_def.arg_type,
        &arg_final_statuses,
        &ops.arg_release_epilogue.release_paths,
        &mut builder,
    );

    let rc_body = builder.to_expr(ret_local);

    rc::FuncDef {
        purity: func_def.purity,
        arg_type: func_def.arg_type.clone(),
        ret_type: func_def.ret_type.clone(),
        body: rc_body,
        profile_point: func_def.profile_point,
    }
}

pub fn rc_specialize(program: mode::Program) -> rc::Program {
    let (specializations, main_spec) =
        specialize_modes(&program.funcs, program.main, program.main_version);

    let (concrete_ops, rc_main) =
        deduplicate_specializations(&program.funcs, &specializations, main_spec);

    let rc_func_symbols = concrete_ops.map(|_, ops| program.func_symbols[ops.func].clone());

    let rc_funcs =
        concrete_ops.map(|_, ops| build_func(&program.custom_types, &program.funcs[ops.func], ops));

    rc::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs: rc_funcs,
        func_symbols: rc_func_symbols,
        profile_points: program.profile_points,
        main: rc_main,
    }
}
