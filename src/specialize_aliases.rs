use im_rc::OrdMap;
use std::collections::btree_map;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::alias_spec_flag::lookup_concrete_cond;
use crate::data::alias_annot_ast as alias;
use crate::data::alias_specialized_ast as spec;
use crate::data::anon_sum_ast as anon;
use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as mutation;
use crate::field_path;
use crate::fixed_point::{iterate_fixed_point, Signature};
use crate::stack_path;
use crate::util::disjunction::Disj;
use crate::util::graph::Scc;
use crate::util::id_gen::IdGen;
use crate::util::id_vec::IdVec;
use crate::util::norm_pair::NormPair;

#[derive(Clone, Debug)]
struct SccCallSite {
    caller: first_ord::CustomFuncId,
    caller_arg_local: flat::LocalId,
    // Aliases from argument fields (keys) to other names in scope (values) (which may
    // potentially also be fields of the argument)
    arg_aliases: OrdMap<alias::FieldPath, alias::LocalAliases>,
    // Folded aliases for each argument fold point
    arg_folded_aliases: OrdMap<alias::FieldPath, alias::FoldedAliases>,
    // Fate of return value
    ret_fate: fate::Fate,
}

#[derive(Clone, Debug)]
struct SccInfo {
    scc: Scc<first_ord::CustomFuncId>,
    callers: BTreeMap<first_ord::CustomFuncId, Vec<SccCallSite>>,
}

id_type!(SccId);

fn collect_call_sites(
    curr_func: first_ord::CustomFuncId,
    expr_annots: &IdVec<fate::ExprId, fate::ExprAnnot>,
    expr: &fate::Expr,
    callers: &mut BTreeMap<first_ord::CustomFuncId, Vec<SccCallSite>>,
) {
    match &expr.kind {
        fate::ExprKind::Call(
            _call_id,
            _purity,
            callee,
            arg_aliases,
            arg_folded_aliases,
            fate::Local(_, arg),
        ) => {
            // `callers` has key `callee` iff `callee` is in the current SCC
            if let Some(callee_sites) = callers.get_mut(callee) {
                let ret_fate = expr_annots[expr.id].fate.clone();
                callee_sites.push(SccCallSite {
                    caller: curr_func,
                    caller_arg_local: *arg,
                    arg_aliases: arg_aliases.clone(),
                    arg_folded_aliases: arg_folded_aliases.clone(),
                    ret_fate,
                });
            }
        }

        fate::ExprKind::Branch(_, cases, _) => {
            for (_, _, body, _) in cases {
                collect_call_sites(curr_func, expr_annots, body, callers);
            }
        }

        fate::ExprKind::LetMany(_, bindings, _, _) => {
            for (_, binding) in bindings {
                collect_call_sites(curr_func, expr_annots, binding, callers);
            }
        }

        _ => {}
    }
}

fn collect_sccs(
    funcs: &IdVec<first_ord::CustomFuncId, fate::FuncDef>,
    sccs: Vec<Scc<first_ord::CustomFuncId>>,
) -> (IdVec<first_ord::CustomFuncId, SccId>, IdVec<SccId, SccInfo>) {
    let mut func_to_scc = IdVec::from_items(vec![None; funcs.len()]);
    let mut scc_infos = IdVec::new();

    for scc in sccs {
        match &scc {
            &Scc::Acyclic(func) => {
                let mut callers = BTreeMap::new();
                callers.insert(func, Vec::new());
                let scc_id = scc_infos.push(SccInfo { scc, callers });

                debug_assert!(func_to_scc[func].is_none());
                func_to_scc[func] = Some(scc_id);
            }

            Scc::Cyclic(scc_funcs) => {
                let mut callers = scc_funcs.iter().map(|&func| (func, Vec::new())).collect();
                for func in scc_funcs {
                    collect_call_sites(
                        *func,
                        &funcs[func].expr_annots,
                        &funcs[func].body,
                        &mut callers,
                    );
                }

                let scc_id = scc_infos.push(SccInfo {
                    scc: scc.clone(),
                    callers,
                });

                for func in scc_funcs {
                    debug_assert!(func_to_scc[func].is_none());
                    func_to_scc[func] = Some(scc_id);
                }
            }
        }
    }

    (
        func_to_scc.into_mapped(|_, scc_id| scc_id.unwrap()),
        scc_infos,
    )
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FuncInstance {
    aliases: BTreeMap<alias::AliasCondition, spec::ConcreteAlias>,
    ret_fate: BTreeMap<alias::RetName, spec::RetFate>,
}

#[derive(Clone, Debug)]
struct FuncInstances {
    version_gen: IdGen<spec::FuncVersionId>,
    cache: BTreeMap<FuncInstance, spec::FuncVersionId>,
}

// We can't use `util::InstanceQueue` here, because that structure generates global monomorphized
// ids, and we need per-function ids.  We also need the ability to generate fresh ids without
// registering entires in the cache.
#[derive(Clone, Debug)]
struct InstanceQueue {
    instances: IdVec<first_ord::CustomFuncId, FuncInstances>,
    pending: VecDeque<(first_ord::CustomFuncId, spec::FuncVersionId, FuncInstance)>,
}

impl InstanceQueue {
    fn new(num_funcs: usize) -> Self {
        InstanceQueue {
            instances: IdVec::from_items(vec![
                FuncInstances {
                    version_gen: IdGen::new(),
                    cache: BTreeMap::new(),
                };
                num_funcs
            ]),
            pending: VecDeque::new(),
        }
    }

    fn resolve(
        &mut self,
        func: first_ord::CustomFuncId,
        inst: FuncInstance,
    ) -> spec::FuncVersionId {
        let func_insts = &mut self.instances[func];
        match func_insts.cache.entry(inst.clone()) {
            btree_map::Entry::Occupied(occupied) => *occupied.get(),
            btree_map::Entry::Vacant(vacant) => {
                let version = func_insts.version_gen.fresh();
                vacant.insert(version);
                self.pending.push_back((func, version, inst));
                version
            }
        }
    }

    fn fresh_no_cache(&mut self, func: first_ord::CustomFuncId) -> spec::FuncVersionId {
        let func_insts = &mut self.instances[func];
        func_insts.version_gen.fresh()
    }

    fn pop_pending(
        &mut self,
    ) -> Option<(first_ord::CustomFuncId, spec::FuncVersionId, FuncInstance)> {
        self.pending.pop_front()
    }
}

/// Extract from a return value's symbolic mutation status a symbolic expression representing
/// whether the return value was mutated *internally* within the function.  We do not care if the
/// return value was mutated prior to the function but was not mutated inside the function.
/// Operationally, this means we ignore argument mutation flags.
fn filter_internal_mutation_cond(
    disj: &Disj<mutation::MutationCondition>,
) -> Disj<alias::AliasCondition> {
    match disj {
        Disj::True => Disj::True,
        Disj::Any(conds) => Disj::Any(
            conds
                .iter()
                .filter_map(|cond| match cond {
                    mutation::MutationCondition::AliasCondition(alias_cond) => {
                        Some(alias_cond.clone())
                    }
                    mutation::MutationCondition::ArgMutated(_) => None,
                })
                .collect(),
        ),
    }
}

// An alias is only relevant to RC elision if it is in incident on a name which is unconditionally
// mutated.
//
// TODO: What is the easiest way to prove this rigorously?
//
// TODO: The algorithm here does not use type information to prune edges, so it may introduce
// (harmless, but inefficient) spurious edges.  We should optimize this.
fn relevant_alias_conds(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    arg_type: &anon::Type,
    sig: &mutation::MutationSig,
) -> BTreeSet<alias::AliasCondition> {
    let mut relevant = BTreeSet::new();

    let names = field_path::get_names_in(typedefs, arg_type);

    for (name, _) in &names {
        if matches!(
            &sig.arg_mutation_conds[&alias::ArgName(name.clone())],
            Disj::True
        ) {
            for (other_name, _) in &names {
                if other_name != name {
                    relevant.insert(alias::AliasCondition::AliasInArg(NormPair::new(
                        alias::ArgName(name.clone()),
                        alias::ArgName(other_name.clone()),
                    )));
                }
            }
        }
    }

    for (fold_point, folded_type) in field_path::get_fold_points_in(typedefs, arg_type) {
        let mut customs_on_path = BTreeSet::new();
        for field in &fold_point {
            if let alias::Field::Custom(custom_id) = field {
                customs_on_path.insert(*custom_id);
            }
        }

        let sub_paths = field_path::get_names_in_excluding(typedefs, folded_type, customs_on_path);
        for (sub_path, _) in &sub_paths {
            let full_path = fold_point.clone() + sub_path.clone();
            if matches!(
                &sig.arg_mutation_conds[&alias::ArgName(full_path.clone())],
                Disj::True
            ) {
                for (other_sub_path, _) in &sub_paths {
                    relevant.insert(alias::AliasCondition::FoldedAliasInArg(
                        alias::ArgName(fold_point.clone()),
                        NormPair::new(
                            alias::SubPath(sub_path.clone()),
                            alias::SubPath(other_sub_path.clone()),
                        ),
                    ));
                }
            }
        }
    }

    relevant
}

fn callee_inst_for_call_site(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    caller_inst: &FuncInstance,
    caller_arg_local: flat::LocalId,
    callee_def: &fate::FuncDef,
    arg_aliases: &OrdMap<alias::FieldPath, alias::LocalAliases>,
    arg_folded_aliases: &OrdMap<alias::FieldPath, alias::FoldedAliases>,
    ret_fate: &fate::Fate,
) -> FuncInstance {
    let mut callee_relevant_aliases = BTreeMap::new();
    for callee_cond in
        relevant_alias_conds(typedefs, &callee_def.arg_type, &callee_def.mutation_sig)
    {
        let arg_cond_symbolic = field_path::translate_callee_cond(
            caller_arg_local,
            arg_aliases,
            arg_folded_aliases,
            &callee_cond,
        );

        let arg_cond_concrete = if lookup_concrete_cond(&caller_inst.aliases, &arg_cond_symbolic) {
            spec::ConcreteAlias::MayAlias
        } else {
            spec::ConcreteAlias::NoAlias
        };

        callee_relevant_aliases.insert(callee_cond.clone(), arg_cond_concrete);
    }

    let mut internally_mutated_ret_paths = BTreeSet::new();
    for (ret_name, callee_cond) in &callee_def.mutation_sig.ret_statuses {
        let arg_cond_symbolic = field_path::translate_callee_cond_disj(
            caller_arg_local,
            arg_aliases,
            arg_folded_aliases,
            &filter_internal_mutation_cond(&callee_cond.mutated_cond),
        );

        if lookup_concrete_cond(&caller_inst.aliases, &arg_cond_symbolic) {
            // Any mutation of a child of a heap structure counts as a mutation of that
            // heap structure for the purposes of RC elision, because a release
            // operation on a heap structure counts as an access of that structure *and
            // all of its children* for the purposes of mutation optimization.
            let (path, _) = stack_path::split_stack_heap(ret_name.0.clone());
            internally_mutated_ret_paths.insert(stack_path::to_field_path(&path));
        }
    }

    // Here, "relevant" means "modulo irrelevant precision".  This means we may pick an
    // unnecessarily conservative value for the fate flags here when doing so doesn't
    // affect the precision of RC elision.  Modding out by precision-irrelevant details
    // reduces the number of specializations of each function we need to analyze.
    let mut callee_relevant_ret_fates = BTreeMap::new();
    for (path, symbolic_fate) in &ret_fate.fates {
        let relevant_fate = match symbolic_fate.internal {
            fate::InternalFate::Accessed | fate::InternalFate::Owned => spec::RetFate::MaybeUsed,
            fate::InternalFate::Unused => {
                if internally_mutated_ret_paths.contains(path) {
                    if symbolic_fate
                        .ret_destinations
                        .iter()
                        .any(|dest| caller_inst.ret_fate[dest] == spec::RetFate::MaybeUsed)
                    {
                        spec::RetFate::MaybeUsed
                    } else {
                        spec::RetFate::NotUsed
                    }
                } else {
                    // When the return value isn't internally mutated, it doesn't matter
                    // (for the precision / optimality of RC elision) whether or not it
                    // is used by the caller or not, because it's fine to just always
                    // return the value owned and let the caller take responsibility for
                    // dropping it.  We use this case as an opportunity to reduce the
                    // number of specialized versions of the callee we instantiate; when
                    // a return name's fate is irrelevant, we default to marking it with
                    // the most conservative value, `MaybeUsed`.
                    spec::RetFate::MaybeUsed
                }
            }
        };
        callee_relevant_ret_fates.insert(alias::RetName(path.clone()), relevant_fate);
    }

    FuncInstance {
        aliases: callee_relevant_aliases,
        ret_fate: callee_relevant_ret_fates,
    }
}

fn resolve_expr(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    funcs: &IdVec<first_ord::CustomFuncId, fate::FuncDef>,
    insts: &mut InstanceQueue,
    inst: &FuncInstance,
    scc_versions: &BTreeMap<first_ord::CustomFuncId, spec::FuncVersionId>,
    expr_annots: &IdVec<fate::ExprId, fate::ExprAnnot>, // for current function
    expr: &fate::Expr,
    calls: &mut IdVec<fate::CallId, Option<(first_ord::CustomFuncId, spec::FuncVersionId)>>,
) {
    match &expr.kind {
        fate::ExprKind::Call(
            call_id,
            _purity,
            callee,
            arg_aliases,
            arg_folded_aliases,
            fate::Local(_, arg),
        ) => {
            if let Some(version) = scc_versions.get(callee) {
                debug_assert!(calls[call_id].is_none());
                calls[call_id] = Some((*callee, *version));
            } else {
                let ret_fate = &expr_annots[expr.id].fate;
                let callee_inst = callee_inst_for_call_site(
                    typedefs,
                    inst,
                    *arg,
                    &funcs[callee],
                    arg_aliases,
                    arg_folded_aliases,
                    ret_fate,
                );
                let callee_version = insts.resolve(*callee, callee_inst);
                debug_assert!(calls[call_id].is_none());
                calls[call_id] = Some((*callee, callee_version));
            }
        }

        fate::ExprKind::Branch(_, cases, _) => {
            for (_, _, body, _) in cases {
                resolve_expr(
                    typedefs,
                    funcs,
                    insts,
                    inst,
                    scc_versions,
                    expr_annots,
                    body,
                    calls,
                );
            }
        }

        fate::ExprKind::LetMany(_, bindings, _, _) => {
            for (_, binding) in bindings {
                resolve_expr(
                    typedefs,
                    funcs,
                    insts,
                    inst,
                    scc_versions,
                    expr_annots,
                    binding,
                    calls,
                );
            }
        }

        _ => {}
    }
}

impl Signature for Option<FuncInstance> {
    type Sig = Option<FuncInstance>;

    fn signature(&self) -> &Self::Sig {
        self
    }
}

// When we instantiate a function belonging to a cyclic SCC, we want to make sure that instantiation
// doesn't cause us to create more than one specialized copy of any function in the SCC (per
// instantiation). There's no fundamental reason we need to do this for correctness (all the
// relevant parameters have bounded domains, so infinite polymorphic recursion isn't a danger), but
// it seems like a reasonable heuristic to reduce the number of specialized function versions we
// produce, and it mirrors the behavior of other analyses and monomorphization passes in the
// compiler.
//
// To achieve this, we do a little reverse-dependency-fixed-point-iteration dance.  Essentially, we
// view a function's instantiation parameters as a function of the instantiation parameters of its
// *callers* in the SCC, and solve for a fixed point according to this 'caller -> callee' data-flow.
// This has a phi node flavor to it; we want to know all the contexts in which each function in the
// SCC might be invoked, which is similar to knowing all the contexts in which a block might be
// jumped to in SSA.
fn solve_scc_fixed_point(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    funcs: &IdVec<first_ord::CustomFuncId, fate::FuncDef>,
    entry_func: first_ord::CustomFuncId,
    entry_inst: &FuncInstance,
    scc: &SccInfo,
) -> BTreeMap<first_ord::CustomFuncId, FuncInstance> {
    iterate_fixed_point(
        &IdVec::new(),
        |sigs, func| {
            let mut inst_accum = if func == &entry_func {
                Some(entry_inst.clone())
            } else {
                None
            };

            for call_site in &scc.callers[func] {
                if let Some(Some(caller_inst)) = sigs.sig_of(&call_site.caller) {
                    let inst_from_call_site = callee_inst_for_call_site(
                        typedefs,
                        caller_inst,
                        call_site.caller_arg_local,
                        &funcs[func],
                        &call_site.arg_aliases,
                        &call_site.arg_folded_aliases,
                        &call_site.ret_fate,
                    );

                    match &mut inst_accum {
                        Some(inst_accum) => {
                            // Merge instances
                            for (cond, alias) in &mut inst_accum.aliases {
                                *alias = (*alias).max(inst_from_call_site.aliases[cond]);
                            }
                            for (path, fate) in &mut inst_accum.ret_fate {
                                *fate = (*fate).max(inst_from_call_site.ret_fate[path]);
                            }
                        }
                        None => {
                            inst_accum = Some(inst_from_call_site);
                        }
                    }
                }
            }

            inst_accum
        },
        &scc.scc,
    )
    .into_iter()
    .map(|(func, inst)| {
        (func, inst.expect(
            "Every function in the SCC should be transitively called at least once from the entry \
            function",
        ))
    })
    .collect()
}

pub fn specialize_aliases(program: fate::Program) -> spec::Program {
    let (func_to_scc, sccs) = collect_sccs(&program.funcs, program.sccs);

    let mut insts = InstanceQueue::new(program.funcs.len());

    let main_version = insts.resolve(
        program.main,
        // 'main' has signature 'proc () -> ()', so it has no argument or return heap paths
        FuncInstance {
            aliases: BTreeMap::new(),
            ret_fate: BTreeMap::new(),
        },
    );

    let mut versions: IdVec<
        first_ord::CustomFuncId,
        BTreeMap<spec::FuncVersionId, spec::FuncVersion>,
    > = IdVec::from_items(vec![BTreeMap::new(); program.funcs.len()]);

    while let Some((entry_func, entry_version, entry_inst)) = insts.pending.pop_front() {
        debug_assert!(!versions[&entry_func].contains_key(&entry_version));

        let scc = &sccs[func_to_scc[entry_func]];

        let solved_insts = solve_scc_fixed_point(
            &program.custom_types,
            &program.funcs,
            entry_func,
            &entry_inst,
            scc,
        );

        let mut scc_versions = BTreeMap::new();
        scc_versions.insert(entry_func, entry_version);

        for &scc_func in solved_insts.keys() {
            if scc_func != entry_func {
                debug_assert!(!scc_versions.contains_key(&scc_func));
                // We don't want to permanently associate these instance parameters with the version
                // of this function that we're currently generating, because this version might call
                // to versions of other functions in the SCC which have more conservative instance
                // parameters than are here than are necessary in general when called from this
                // function with these parameters.
                scc_versions.insert(scc_func, insts.fresh_no_cache(scc_func));
            }
        }

        for (scc_func, scc_func_inst) in solved_insts {
            let scc_func_version = scc_versions[&scc_func];

            let func_def = &program.funcs[scc_func];
            let mut version_calls = IdVec::from_items(vec![None; func_def.num_calls]);
            resolve_expr(
                &program.custom_types,
                &program.funcs,
                &mut insts,
                &scc_func_inst,
                &scc_versions,
                &func_def.expr_annots,
                &func_def.body,
                &mut version_calls,
            );

            debug_assert!(!versions[&scc_func].contains_key(&scc_func_version));
            versions[&scc_func].insert(
                scc_func_version,
                spec::FuncVersion {
                    calls: version_calls.into_mapped(|_, call| call.unwrap()),
                    aliases: scc_func_inst.aliases,
                    ret_fate: scc_func_inst.ret_fate,
                },
            );
        }
    }

    let orig_num_funcs = program.funcs.len();

    let resolved_funcs = IdVec::from_items(
        program
            .funcs
            .into_iter()
            .zip(versions.into_iter())
            .map(|((id1, func_def), (id2, func_versions))| {
                debug_assert_eq!(id1, id2);
                spec::FuncDef {
                    purity: func_def.purity,
                    arg_type: func_def.arg_type,
                    ret_type: func_def.ret_type,
                    alias_sig: func_def.alias_sig,
                    mutation_sig: func_def.mutation_sig,
                    arg_fate: func_def.arg_fate,
                    body: func_def.body,
                    occur_fates: func_def.occur_fates,
                    expr_annots: func_def.expr_annots,
                    num_retain_points: func_def.num_retain_points,
                    let_block_end_events: func_def.let_block_end_events,
                    branch_block_end_events: func_def.branch_block_end_events,
                    versions: IdVec::try_from_contiguous(func_versions.into_iter()).expect(
                        "A function's fully-populated version map should have contiguous keys",
                    ),
                    profile_point: func_def.profile_point,
                }
            })
            .collect(),
    );

    debug_assert_eq!(orig_num_funcs, resolved_funcs.len());

    spec::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs: resolved_funcs,
        func_symbols: program.func_symbols,
        profile_points: program.profile_points,
        main: program.main,
        main_version,
    }
}
