use im_rc::OrdMap;
use std::collections::{BTreeMap, BTreeSet};

use crate::data::alias_specialized_ast as spec;
use crate::data::anon_sum_ast as anon;
use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast as mode;
use crate::data::rc_specialized_ast as rc;
use crate::util::graph::{strongly_connected, Graph};
use crate::util::id_vec::IdVec;
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
    calls: IdVec<fate::CallId, Call>,
    release_prologues: IdVec<fate::ExprId, Vec<(flat::LocalId, ReleasePaths)>>,
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
) -> (
    IdVec<ModeSpecFuncId, rc::CustomFuncId>,
    IdVec<rc::CustomFuncId, ConcreteRcOps<rc::CustomFuncId>>,
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
                    calls,
                    release_prologues,
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
                        calls: resolved_calls,
                        release_prologues: ops.release_prologues.clone(),
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
        known_dedups.into_mapped(|_, dedup_id| dedup_id.unwrap()),
        concrete_funcs.into_mapped(|_, concrete| concrete.unwrap()),
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

            builder.add_binding(
                anon::Type::Tuple(vec![]),
                rc::Expr::RcOp(rc_op, container_type, (**item_type).clone(), root),
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
                build_plan(typedefs, rc_op, field_local, field_type, sub_plan, builder);
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
            build_plan(typedefs, rc_op, content_id, content_type, sub_plan, builder);
        }
    }
}

fn build_rc_ops(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    rc_op: rc::RcOp,
    local: rc::LocalId,
    local_type: &anon::Type,
    paths: &BTreeSet<mode::StackPath>,
    builder: &mut LetManyBuilder,
) {
    let mut plan = RcOpPlan::NoOp;
    for path in paths {
        plan.add_leaf_path(path);
    }
    build_plan(typedefs, rc_op, local, local_type, &plan, builder);
}

fn build_releases(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    locals: &LocalContext<flat::LocalId, LocalInfo>,
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
            &release_paths.release_paths,
            builder,
        );
    }
}

fn build_expr<'a>(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    ops: &ConcreteRcOps<rc::CustomFuncId>,
    locals: &mut LocalContext<flat::LocalId, LocalInfo<'a>>,
    expr: &'a fate::Expr,
    result_type: anon::Type,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    build_releases(typedefs, locals, &ops.release_prologues[expr.id], builder);

    let build_occur = |locals: &mut LocalContext<flat::LocalId, LocalInfo<'a>>,
                       occur: fate::Local,
                       builder: &mut LetManyBuilder| {
        let local_info = locals.local_binding(occur.1);
        build_rc_ops(
            typedefs,
            rc::RcOp::Retain,
            local_info.new_id,
            local_info.type_,
            &ops.occur_retains[occur.0].retain_paths,
            builder,
        );
        local_info.new_id
    };

    let new_expr = match &expr.kind {
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
            arg_statuses,
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

            rc::Expr::Call(
                *purity,
                rc_callee_id,
                rc_arg_aliases,
                arg_statuses.clone(),
                rc_arg_local,
            )
        }

        fate::ExprKind::Branch(discrim, cases, branch_result_type) => {
            debug_assert_eq!(&result_type, branch_result_type);

            let rc_discrim = build_occur(locals, *discrim, builder);

            let rc_cases = cases
                .iter()
                .map(|(block_id, cond, body)| {
                    let mut case_builder = builder.child();

                    let final_local = build_expr(
                        typedefs,
                        ops,
                        locals,
                        body,
                        result_type.clone(),
                        &mut case_builder,
                    );

                    build_releases(
                        typedefs,
                        locals,
                        &ops.branch_release_epilogues[block_id],
                        &mut case_builder,
                    );

                    (cond.clone(), case_builder.to_expr(final_local))
                })
                .collect();

            rc::Expr::Branch(rc_discrim, rc_cases, result_type.clone())
        }

        fate::ExprKind::LetMany(block_id, bindings, final_local) => {
            let rc_final_local = locals.with_scope(|sub_locals| {
                for (type_, rhs) in bindings {
                    let new_id = build_expr(typedefs, ops, sub_locals, rhs, type_.clone(), builder);

                    sub_locals.add_local(LocalInfo { type_, new_id });
                }

                let rc_final_local = build_occur(sub_locals, *final_local, builder);

                build_releases(
                    typedefs,
                    sub_locals,
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

        _ => todo!(),
    };

    builder.add_binding(result_type, new_expr)
}

pub fn rc_specialize(_program: mode::Program) -> rc::Program {
    todo!()
}
