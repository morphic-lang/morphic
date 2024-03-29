use im_rc::{vector, OrdMap, OrdSet, Vector};
use std::collections::{BTreeMap, BTreeSet};

use crate::data::alias_annot_ast as annot;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::field_path::{
    get_fold_points_in, get_names_in, get_sub_names_in, group_unfolded_names_by_folded_form,
    split_at_all_fold_points, split_at_fold, split_fold_at_fold, translate_callee_cond,
    translate_callee_cond_disj, FoldPoint,
};
use crate::fixed_point::{annot_all, Signature, SignatureAssumptions};
use crate::util::disjunction::Disj;
use crate::util::graph::{self, Graph};
use crate::util::im_rc_ext::VectorExtensions;
use crate::util::norm_pair::NormPair;
use crate::util::progress_logger::ProgressLogger;

impl Signature for annot::FuncDef {
    type Sig = annot::AliasSig;

    fn signature(&self) -> &Self::Sig {
        &self.alias_sig
    }
}

pub fn annot_aliases(program: flat::Program, progress: impl ProgressLogger) -> annot::Program {
    let dep_graph = func_dependency_graph(&program);

    let sccs = graph::acyclic_and_cyclic_sccs(&dep_graph);

    let funcs = annot_all(
        program.funcs.len(),
        |sig_assumptions, func| annot_func(&program, sig_assumptions, &program.funcs[func]),
        &sccs,
        progress,
    );

    annot::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        func_symbols: program.func_symbols,
        profile_points: program.profile_points,
        main: program.main,
        sccs,
    }
}

fn add_func_deps(deps: &mut BTreeSet<first_ord::CustomFuncId>, expr: &flat::Expr) {
    match expr {
        flat::Expr::Call(_, other, _) => {
            deps.insert(*other);
        }

        flat::Expr::Branch(_, cases, _) => {
            for (_, body) in cases {
                add_func_deps(deps, body);
            }
        }

        flat::Expr::LetMany(bindings, _) => {
            for (_, rhs) in bindings {
                add_func_deps(deps, rhs);
            }
        }

        _ => {}
    }
}

fn func_dependency_graph(program: &flat::Program) -> Graph<first_ord::CustomFuncId> {
    Graph {
        edges_out: program.funcs.map(|_, func_def| {
            let mut deps = BTreeSet::new();
            add_func_deps(&mut deps, &func_def.body);
            deps.into_iter().collect()
        }),
    }
}

#[derive(Clone, Debug)]
struct LocalInfo {
    type_: anon::Type,
    aliases: OrdMap<annot::FieldPath, annot::LocalAliases>,
    folded_aliases: OrdMap<annot::FieldPath, annot::FoldedAliases>,
}

mod val_info {
    use super::*;

    // Aliasing information for an unnamed value
    #[derive(Clone, Debug)]
    pub struct ValInfo {
        //
        // Essential data
        //
        local_aliases: OrdMap<annot::FieldPath, annot::LocalAliases>,
        self_aliases: OrdMap<NormPair<annot::FieldPath>, Disj<annot::AliasCondition>>,
        folded_aliases: OrdMap<annot::FieldPath, annot::FoldedAliases>,

        //
        // Redundant cached data
        //

        // Invariant: `rev_aliases` should store exactly the same information as `local_aliases`, only
        // with the edges represented as references going the opposite direction.  This is useful for
        // reverse lookups.
        rev_aliases: OrdMap<
            (flat::LocalId, annot::FieldPath),
            OrdMap<annot::FieldPath, Disj<annot::AliasCondition>>,
        >,
    }

    impl ValInfo {
        pub fn new() -> Self {
            ValInfo {
                local_aliases: OrdMap::new(),
                folded_aliases: OrdMap::new(),
                self_aliases: OrdMap::new(),

                rev_aliases: OrdMap::new(),
            }
        }

        pub fn local_aliases(&self) -> &OrdMap<annot::FieldPath, annot::LocalAliases> {
            &self.local_aliases
        }

        pub fn self_aliases(
            &self,
        ) -> &OrdMap<NormPair<annot::FieldPath>, Disj<annot::AliasCondition>> {
            &self.self_aliases
        }

        pub fn folded_aliases(&self) -> &OrdMap<annot::FieldPath, annot::FoldedAliases> {
            &self.folded_aliases
        }

        pub fn rev_aliases(
            &self,
        ) -> &OrdMap<
            (flat::LocalId, annot::FieldPath),
            OrdMap<annot::FieldPath, Disj<annot::AliasCondition>>,
        > {
            &self.rev_aliases
        }

        pub fn create_path(&mut self, path: annot::FieldPath) {
            debug_assert!(
                !self.local_aliases.contains_key(&path),
                "Alias analysis attempted to create a name that already exists.  While this is in \
                 and of itself harmless, it probably indicates a logic error."
            );

            self.local_aliases.insert(
                path.clone(),
                annot::LocalAliases {
                    aliases: OrdMap::new(),
                },
            );
        }

        #[inline]
        fn assert_path(&self, path: &annot::FieldPath) {
            debug_assert!(
                self.local_aliases.contains_key(path),
                "Attempt to alias an unitilialized path: {:?}",
                path
            );
        }

        pub fn add_edge_to_local(
            &mut self,
            self_path: annot::FieldPath,
            local_name: (flat::LocalId, annot::FieldPath),
            cond: Disj<annot::AliasCondition>,
        ) {
            self.assert_path(&self_path);

            if cond.is_const_false() {
                return;
            }

            self.local_aliases[&self_path]
                .aliases
                .entry(local_name.clone())
                .or_default()
                .or_mut(cond.clone());

            self.rev_aliases
                .entry(local_name)
                .or_default()
                .entry(self_path)
                .or_default()
                .or_mut(cond);
        }

        pub fn rev_aliases_of(
            &self,
            local_name: &(flat::LocalId, annot::FieldPath),
        ) -> OrdMap<annot::FieldPath, Disj<annot::AliasCondition>> {
            self.rev_aliases
                .get(local_name)
                .cloned()
                .unwrap_or_else(|| OrdMap::new())
        }

        pub fn add_self_edge(
            &mut self,
            path1: annot::FieldPath,
            path2: annot::FieldPath,
            cond: Disj<annot::AliasCondition>,
        ) {
            // There is no immediate, material reason why we cannot add a self-edge if the
            // corresponding path in `local_aliases` has not yet bene created.  However, for the
            // sake of our sanity we require that all paths be created before edges of any kind may
            // be added between them, and co-opt the key set of `local_aliases` as a convenenient
            // way of tracking path creation.
            self.assert_path(&path1);
            self.assert_path(&path2);

            if cond.is_const_false() {
                return;
            }

            debug_assert_ne!(
                path1, path2,
                "Alias analysis attempted to create a reflexive edge.  Reflexive edges implicitly \
                 exist on all nodes in the aliasing graph, so we should never need to explicitly \
                 represent them."
            );

            self.self_aliases
                .entry(NormPair::new(path1, path2))
                .or_default()
                .or_mut(cond);
        }

        pub fn set_all_folded_aliases(
            &mut self,
            folded_aliases: OrdMap<annot::FieldPath, annot::FoldedAliases>,
        ) {
            self.folded_aliases = folded_aliases
        }

        pub fn set_folded_aliases(
            &mut self,
            fold_point: annot::FieldPath,
            folded_aliases: annot::FoldedAliases,
        ) {
            self.folded_aliases.insert(fold_point, folded_aliases);
        }

        pub fn create_folded_aliases(
            &mut self,
            fold_point: annot::FieldPath,
            folded_aliases: annot::FoldedAliases,
        ) {
            debug_assert!(
                !self.folded_aliases.contains_key(&fold_point),
                "Alias analysis attempted to create a fold point that already exists.  While this \
                 is in and of itself harmless, it probably indicates a logic error."
            );

            self.folded_aliases.insert(fold_point, folded_aliases);
        }

        pub fn add_folded_alias(
            &mut self,
            fold_point: &annot::FieldPath,
            pair: NormPair<annot::SubPath>,
            cond: Disj<annot::AliasCondition>,
        ) {
            self.folded_aliases[fold_point]
                .inter_elem_aliases
                .entry(pair)
                .or_default()
                .or_mut(cond);
        }
    }
}

use val_info::ValInfo;

fn empty_info(typedefs: &flat::CustomTypes, type_: &anon::Type) -> ValInfo {
    let mut result = ValInfo::new();

    for (path, _) in get_names_in(typedefs, type_) {
        result.create_path(path);
    }

    for (fold_point, _) in get_fold_points_in(typedefs, type_) {
        result.create_folded_aliases(
            fold_point,
            annot::FoldedAliases {
                inter_elem_aliases: OrdMap::new(),
            },
        );
    }

    result
}

// Note: This does not copy folded aliases!
fn copy_aliases(
    dest: &mut ValInfo,
    dest_path: &annot::FieldPath,
    src: &LocalInfo,
    src_id: flat::LocalId,
    src_path: &annot::FieldPath,
) {
    // Wire up transitive edges to other paths in dest
    //
    // We are careful to do this before wiring up the path in the dest directly to the
    // corresponding path in the src, as doing so would create a reflexive edge.
    for (other_dest_path, cond) in dest.rev_aliases_of(&(src_id, src_path.clone())) {
        dest.add_self_edge(dest_path.clone(), other_dest_path, cond);
    }

    // Wire up dest path directly to src path
    dest.add_edge_to_local(dest_path.clone(), (src_id, src_path.clone()), Disj::True);

    // Wire up transitive edges to locals (potentially including both the current src and other
    // locals)
    for ((other_id, other_path), cond) in &src.aliases[src_path].aliases {
        dest.add_edge_to_local(
            dest_path.clone(),
            (*other_id, other_path.clone()),
            cond.clone(),
        );
    }
}

fn union_mut(dest: &mut ValInfo, src: &ValInfo) {
    // We assume that 'dest' and 'src' both have the right "shape", which is to say that they are
    // both already initialized with the full set of names and fold points for the type of value
    // they represent.

    for (path, aliases) in src.local_aliases() {
        for (local_name, cond) in &aliases.aliases {
            dest.add_edge_to_local(path.clone(), local_name.clone(), cond.clone());
        }
    }

    for (pair, cond) in src.self_aliases() {
        dest.add_self_edge(pair.fst().clone(), pair.snd().clone(), cond.clone());
    }

    for (fold_point, aliases) in src.folded_aliases() {
        for (pair, cond) in &aliases.inter_elem_aliases {
            dest.add_folded_alias(fold_point, pair.clone(), cond.clone());
        }
    }
}

fn array_extraction_aliases(
    orig: &flat::Program,
    ctx: &OrdMap<flat::LocalId, LocalInfo>,
    item_type: &anon::Type,
    array: flat::LocalId,
    ret_array_field: annot::Field,
    ret_item_field: annot::Field,
) -> ValInfo {
    let mut expr_info = ValInfo::new();

    let array_info = &ctx[&array];

    debug_assert_eq!(
        &anon::Type::Array(Box::new(item_type.clone())),
        &array_info.type_
    );

    // Populate new array info
    //
    // TODO: This adds an edge between the old and new array.  Modeling this edge is not strictly
    // necessary, so we should consider eliminating it.
    {
        for (array_path, _) in get_names_in(&orig.custom_types, &array_info.type_) {
            let mut ret_path = array_path.clone();
            ret_path.push_front(ret_array_field);

            expr_info.create_path(ret_path.clone());
            copy_aliases(&mut expr_info, &ret_path, array_info, array, &array_path);
        }

        for (array_fold_point, _) in get_fold_points_in(&orig.custom_types, &array_info.type_) {
            let mut ret_fold_point = array_fold_point.clone();
            ret_fold_point.push_front(ret_array_field);

            expr_info.create_folded_aliases(
                ret_fold_point,
                array_info.folded_aliases[&array_fold_point].clone(),
            );
        }
    }

    // Populate item info
    {
        let item_paths = get_names_in(&orig.custom_types, item_type);

        for (item_path, _) in &item_paths {
            let mut ret_path = item_path.clone();
            ret_path.push_front(ret_item_field);

            expr_info.create_path(ret_path);
        }

        for (item_path, _) in item_paths {
            let mut ret_path = item_path.clone();
            ret_path.push_front(ret_item_field);

            let mut array_path = item_path.clone();
            array_path.push_front(annot::Field::ArrayMembers);

            // We can't use 'copy_aliases' here because we want to avoid creating edges between the
            // returned item and returned new array unless a corresponding edge exists in the folded
            // aliases of the original array.

            // Wire up directly
            expr_info.add_edge_to_local(ret_path.clone(), (array, array_path.clone()), Disj::True);

            // Wire up transitive edges
            for ((other, other_path), cond) in &array_info.aliases[&array_path].aliases {
                // Check for self-edges within the item being extracted.
                //
                // We need to check for '!other_path.is_empty()' here because it is possible for an
                // array to transitively contain itself (!), in which case 'other_path' might be a
                // zero-element path pointing to the root of the array, rather than to one of its
                // members.
                //
                // We don't need to do anything special when we extract an array from itself; the
                // necessary edges are added after this 'if' statement.
                if *other == array && !other_path.is_empty() {
                    // The only names in the array, other than the name of the array itself, are the
                    // names of its members. Hence this is an edge within each member of the array,
                    // and we need to add a self-edge to the extracted item.
                    debug_assert_eq!(other_path[0], annot::Field::ArrayMembers);

                    let other_item_path = other_path.skip(1);

                    let mut other_item_ret_path = other_item_path;
                    other_item_ret_path.push_front(ret_item_field);

                    expr_info.add_self_edge(ret_path.clone(), other_item_ret_path, cond.clone());
                }

                expr_info.add_edge_to_local(
                    ret_path.clone(),
                    (*other, other_path.clone()),
                    cond.clone(),
                );
            }
        }

        // Unfurl folded edges
        for (pair, cond) in
            &array_info.folded_aliases[&vector![annot::Field::ArrayMembers]].inter_elem_aliases
        {
            let mut ret_item_path = pair.fst().0.clone();
            ret_item_path.push_front(ret_item_field);

            let mut ret_array_path = pair.snd().0.clone();
            ret_array_path.push_front(annot::Field::ArrayMembers);
            ret_array_path.push_front(ret_array_field);

            expr_info.add_self_edge(ret_item_path, ret_array_path, cond.clone());
        }

        // Copy folded aliases
        for (item_fold_point, _) in get_fold_points_in(&orig.custom_types, item_type) {
            let mut ret_item_fold_point = item_fold_point.clone();
            ret_item_fold_point.push_front(ret_item_field);

            let mut array_fold_point = item_fold_point.clone();
            array_fold_point.push_front(annot::Field::ArrayMembers);

            expr_info.create_folded_aliases(
                ret_item_fold_point,
                array_info.folded_aliases[&array_fold_point].clone(),
            );
        }
    }

    expr_info
}

fn array_insertion_aliases(
    orig: &flat::Program,
    ctx: &OrdMap<flat::LocalId, LocalInfo>,
    item_type: &anon::Type,
    array: flat::LocalId,
    item: flat::LocalId,
) -> ValInfo {
    let mut expr_info = ValInfo::new();

    let array_info = &ctx[&array];
    let item_info = &ctx[&item];

    debug_assert_eq!(&item_info.type_, item_type);

    // The "array" into which we are inserting may be either an actual `Type::Array` or a
    // `Type::HoleArray`.  In either case, we expect its names to be the same as those of an array.

    debug_assert_eq!(
        get_names_in(&orig.custom_types, &array_info.type_)
            .into_iter()
            .map(|(path, _)| path)
            .collect::<BTreeSet<_>>(),
        get_names_in(
            &orig.custom_types,
            &anon::Type::Array(Box::new(item_type.clone()))
        )
        .into_iter()
        .map(|(path, _)| path)
        .collect::<BTreeSet<_>>()
    );

    // Wire up aliases contributed by array
    {
        for (array_path, _) in get_names_in(&orig.custom_types, &array_info.type_) {
            expr_info.create_path(array_path.clone());
            copy_aliases(&mut expr_info, &array_path, array_info, array, &array_path);
        }

        for (array_fold_point, _) in get_fold_points_in(&orig.custom_types, &array_info.type_) {
            expr_info.create_folded_aliases(
                array_fold_point.clone(),
                array_info.folded_aliases[&array_fold_point].clone(),
            );
        }
    }

    // Wire up aliases contributed by item
    {
        for (item_path, _) in get_names_in(&orig.custom_types, item_type) {
            let mut ret_array_path = item_path.clone();
            ret_array_path.push_front(annot::Field::ArrayMembers);

            // The name `ret_array_path` should already exist in `expr_info`, because we should have
            // created it when we wire up the aliases contributed by the array.

            // Wire up directly
            expr_info.add_edge_to_local(
                ret_array_path.clone(),
                (item, item_path.clone()),
                Disj::True,
            );

            // Wire up transitive edges
            for ((other, other_path), cond) in &item_info.aliases[&item_path].aliases {
                if *other == item {
                    let mut other_ret_array_path = other_path.clone();
                    other_ret_array_path.push_front(annot::Field::ArrayMembers);

                    expr_info.add_self_edge(
                        ret_array_path.clone(),
                        other_ret_array_path,
                        cond.clone(),
                    );
                }

                // Check for edges between the item being added and existing items.
                //
                // We need to check for '!other_path.is_empty()' here because it is possible for an
                // array to transitively contain itself (!), in which case 'other_path' might be a
                // zero-element path pointing to the root of the array, rather than to one of its
                // members.
                //
                // We don't need to do anything special when we add an array to itself; the
                // necessary edges are added after this 'if' statement.
                if *other == array && !other_path.is_empty() {
                    // The only names in the array, other than the name of the array itself, are the
                    // names of its members. Hence this is an edge between the *members* of the
                    // array and the item, and we need to add an internal cross-edge.
                    debug_assert_eq!(other_path[0], annot::Field::ArrayMembers);

                    let other_subpath = annot::SubPath(other_path.skip(1));

                    // TODO: Are we absolutely certain that adding a cross-edge is *all* we need to
                    // do in this case?  Is it ever necessary to also add a normal edge here?

                    // "Cross-edge" between folded copies
                    expr_info.add_folded_alias(
                        &vector![annot::Field::ArrayMembers],
                        NormPair::new(annot::SubPath(item_path.clone()), other_subpath),
                        cond.clone(),
                    );
                }

                expr_info.add_edge_to_local(
                    ret_array_path.clone(),
                    (*other, other_path.clone()),
                    cond.clone(),
                );
            }

            // Copy folded aliases
            for (item_fold_point, _) in get_fold_points_in(&orig.custom_types, item_type) {
                let mut ret_array_fold_point = item_fold_point.clone();
                ret_array_fold_point.push_front(annot::Field::ArrayMembers);

                for (pair, cond) in &item_info.folded_aliases[&item_fold_point].inter_elem_aliases {
                    expr_info.add_folded_alias(&ret_array_fold_point, pair.clone(), cond.clone());
                }
            }
        }
    }

    expr_info
}

fn annot_expr(
    orig: &flat::Program,
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, annot::FuncDef>,
    ctx: &OrdMap<flat::LocalId, LocalInfo>,
    expr: &flat::Expr,
) -> (annot::Expr, ValInfo) {
    match expr {
        flat::Expr::Local(local) => {
            let mut expr_info = ValInfo::new();

            let local_info = &ctx[local];
            for (path, _) in get_names_in(&orig.custom_types, &local_info.type_) {
                expr_info.create_path(path.clone());
                copy_aliases(&mut expr_info, &path, &local_info, *local, &path);
            }

            for (fold_point, _) in get_fold_points_in(&orig.custom_types, &local_info.type_) {
                expr_info.create_folded_aliases(
                    fold_point.clone(),
                    local_info.folded_aliases[&fold_point].clone(),
                );
            }

            (annot::Expr::Local(*local), expr_info)
        }

        flat::Expr::Call(purity, func, arg) => {
            let arg_info = &ctx[arg];

            let annot_expr = annot::Expr::Call(
                *purity,
                *func,
                arg_info.aliases.clone(),
                arg_info.folded_aliases.clone(),
                *arg,
            );

            let ret_type = &orig.funcs[func].ret_type;

            let expr_info = match sigs.sig_of(func) {
                None => {
                    // On the first iteration of fixed point analysis, we assume all recursive calls
                    // return un-aliased return values.
                    empty_info(&orig.custom_types, ret_type)
                }

                Some(sig) => {
                    let mut expr_info = ValInfo::new();

                    // Create paths and wire up edges to locals
                    for (ret_path, _) in get_names_in(&orig.custom_types, ret_type) {
                        expr_info.create_path(ret_path.clone());

                        for (annot::ArgName(arg_path), cond) in
                            &sig.ret_arg_aliases[&annot::RetName(ret_path.clone())]
                        {
                            match cond {
                                Disj::True => {
                                    // Wire up directly
                                    expr_info.add_edge_to_local(
                                        ret_path.clone(),
                                        (*arg, arg_path.clone()),
                                        Disj::True,
                                    );

                                    // Wire up transitive edges to locals not known to the callee
                                    for ((other_id, other_path), other_cond) in
                                        &arg_info.aliases[arg_path].aliases
                                    {
                                        // Self-edges within the argument are accounted for by alias
                                        // analysis in the callee.  The only edges that the caller
                                        // needs to account for are those to other locals in the
                                        // caller's scope.
                                        if other_id != arg {
                                            expr_info.add_edge_to_local(
                                                ret_path.clone(),
                                                (*other_id, other_path.clone()),
                                                other_cond.clone(),
                                            );
                                        }
                                    }
                                }

                                Disj::Any(callee_conds) => {
                                    let mut caller_conds = Disj::new();
                                    for callee_cond in callee_conds {
                                        caller_conds.or_mut(translate_callee_cond(
                                            *arg,
                                            &arg_info.aliases,
                                            &arg_info.folded_aliases,
                                            callee_cond,
                                        ));
                                    }

                                    expr_info.add_edge_to_local(
                                        ret_path.clone(),
                                        (*arg, arg_path.clone()),
                                        caller_conds,
                                    );
                                }
                            }
                        }
                    }

                    // Create fold points and populate their associated folded aliases
                    for (ret_fold_point, _) in get_fold_points_in(&orig.custom_types, ret_type) {
                        let caller_inter_elem_aliases = sig.ret_folded_aliases
                            [&annot::RetName(ret_fold_point.clone())]
                            .inter_elem_aliases
                            .iter()
                            .map(|(sub_path_pair, callee_cond)| {
                                (
                                    sub_path_pair.clone(),
                                    translate_callee_cond_disj(
                                        *arg,
                                        &arg_info.aliases,
                                        &arg_info.folded_aliases,
                                        callee_cond,
                                    ),
                                )
                            })
                            .filter(|(_, caller_cond)| !caller_cond.is_const_false())
                            .collect();

                        let caller_folded_aliases = annot::FoldedAliases {
                            inter_elem_aliases: caller_inter_elem_aliases,
                        };

                        expr_info.create_folded_aliases(ret_fold_point, caller_folded_aliases);
                    }

                    // Wire up self-edges of return value
                    for (ret_ret_pair, callee_cond) in &sig.ret_ret_aliases {
                        let caller_cond = translate_callee_cond_disj(
                            *arg,
                            &arg_info.aliases,
                            &arg_info.folded_aliases,
                            callee_cond,
                        );

                        let annot::RetName(ret_pair_fst) = ret_ret_pair.fst();
                        let annot::RetName(ret_pair_snd) = ret_ret_pair.snd();

                        expr_info.add_self_edge(
                            ret_pair_fst.clone(),
                            ret_pair_snd.clone(),
                            caller_cond,
                        );
                    }

                    // Done (!)
                    expr_info
                }
            };

            (annot_expr, expr_info)
        }

        flat::Expr::Branch(discrim, cases, result_type) => {
            let mut annot_cases = Vec::with_capacity(cases.len());
            let mut expr_info = empty_info(&orig.custom_types, result_type);

            for (cond, body) in cases {
                let (annot_body, body_info) = annot_expr(orig, sigs, ctx, body);
                annot_cases.push((cond.clone(), annot_body));
                union_mut(&mut expr_info, &body_info);
            }

            let annot_branch = annot::Expr::Branch(*discrim, annot_cases, result_type.clone());

            (annot_branch, expr_info)
        }

        flat::Expr::LetMany(bindings, final_local) => {
            let mut new_bindings = Vec::with_capacity(bindings.len());
            let mut new_ctx = ctx.clone();

            for (type_, rhs) in bindings {
                let (annot_rhs, rhs_info) = annot_expr(orig, sigs, &new_ctx, rhs);

                debug_assert_eq!(
                    rhs_info
                        .local_aliases()
                        .keys()
                        .cloned()
                        .collect::<BTreeSet<_>>(),
                    get_names_in(&orig.custom_types, type_)
                        .into_iter()
                        .map(|(path, _)| path)
                        .collect::<BTreeSet<_>>()
                );

                let lhs = flat::LocalId(new_ctx.len());
                debug_assert!(!new_ctx.contains_key(&lhs));

                // Wire up aliases from this local to others and to itself
                let mut lhs_aliases = rhs_info.local_aliases().clone();
                for (pair, cond) in rhs_info.self_aliases() {
                    let prev_fst_snd = lhs_aliases[pair.fst()]
                        .aliases
                        .insert((lhs, pair.snd().clone()), cond.clone());

                    let prev_snd_fst = lhs_aliases[pair.snd()]
                        .aliases
                        .insert((lhs, pair.fst().clone()), cond.clone());

                    debug_assert!(prev_fst_snd.is_none());
                    debug_assert!(prev_snd_fst.is_none());
                }

                // Wire up "reverse" aliases from other locals to this one
                for ((other_local, other_path), lhs_aliases) in rhs_info.rev_aliases() {
                    for (lhs_path, cond) in lhs_aliases {
                        let prev = new_ctx[other_local].aliases[other_path]
                            .aliases
                            .insert((lhs, lhs_path.clone()), cond.clone());

                        debug_assert!(prev.is_none());
                    }
                }

                let lhs_info = LocalInfo {
                    type_: type_.clone(),
                    aliases: lhs_aliases,
                    folded_aliases: rhs_info.folded_aliases().clone(),
                };

                new_ctx.insert(lhs, lhs_info);

                new_bindings.push((type_.clone(), annot_rhs));
            }

            let final_local_info = &new_ctx[final_local];
            let mut final_val_info = ValInfo::new();

            for (path, _) in &final_local_info.aliases {
                final_val_info.create_path(path.clone());
            }

            for (path, aliases) in &final_local_info.aliases {
                for ((other_local, other_path), cond) in &aliases.aliases {
                    if other_local.0 < ctx.len() {
                        final_val_info.add_edge_to_local(
                            path.clone(),
                            (*other_local, other_path.clone()),
                            cond.clone(),
                        );
                    }

                    if other_local == final_local {
                        final_val_info.add_self_edge(
                            path.clone(),
                            other_path.clone(),
                            cond.clone(),
                        );
                    }
                }
            }

            final_val_info.set_all_folded_aliases(final_local_info.folded_aliases.clone());

            (
                annot::Expr::LetMany(new_bindings, *final_local),
                final_val_info,
            )
        }

        flat::Expr::Tuple(items) => {
            let mut expr_info = ValInfo::new();

            for (i, item) in items.iter().enumerate() {
                let item_info = &ctx[item];

                for (path_in_item, _) in get_names_in(&orig.custom_types, &item_info.type_) {
                    let mut path_in_tuple = path_in_item.clone();
                    path_in_tuple.push_front(annot::Field::Field(i));

                    expr_info.create_path(path_in_tuple.clone());
                    // copy_aliases handles the creation of both aliases to locals and self-aliases
                    // within the tuple under construction.
                    copy_aliases(
                        &mut expr_info,
                        &path_in_tuple,
                        item_info,
                        *item,
                        &path_in_item,
                    );
                }

                for (fold_point_in_item, _) in
                    get_fold_points_in(&orig.custom_types, &item_info.type_)
                {
                    let mut fold_point_in_tuple = fold_point_in_item.clone();
                    fold_point_in_tuple.push_front(annot::Field::Field(i));

                    expr_info.create_folded_aliases(
                        fold_point_in_tuple,
                        item_info.folded_aliases[&fold_point_in_item].clone(),
                    );
                }
            }

            (annot::Expr::Tuple(items.clone()), expr_info)
        }

        flat::Expr::TupleField(tuple, field_idx) => {
            let tuple_info = &ctx[tuple];

            let item_type = if let anon::Type::Tuple(item_types) = &tuple_info.type_ {
                &item_types[*field_idx]
            } else {
                unreachable!()
            };

            let mut expr_info = ValInfo::new();

            for (path_in_item, _) in get_names_in(&orig.custom_types, item_type) {
                let mut path_in_tuple = path_in_item.clone();
                path_in_tuple.push_front(annot::Field::Field(*field_idx));

                expr_info.create_path(path_in_item.clone());
                copy_aliases(
                    &mut expr_info,
                    &path_in_item,
                    tuple_info,
                    *tuple,
                    &path_in_tuple,
                );
            }

            for (fold_point_in_item, _) in get_fold_points_in(&orig.custom_types, item_type) {
                let mut fold_point_in_tuple = fold_point_in_item.clone();
                fold_point_in_tuple.push_front(annot::Field::Field(*field_idx));

                expr_info.create_folded_aliases(
                    fold_point_in_item,
                    tuple_info.folded_aliases[&fold_point_in_tuple].clone(),
                );
            }

            (annot::Expr::TupleField(*tuple, *field_idx), expr_info)
        }

        flat::Expr::WrapVariant(variant_types, variant, content) => {
            let mut expr_info = empty_info(
                &orig.custom_types,
                &anon::Type::Variants(variant_types.clone()),
            );

            let content_info = &ctx[content];

            debug_assert_eq!(&content_info.type_, &variant_types[variant]);

            for (path_in_content, _) in get_names_in(&orig.custom_types, &content_info.type_) {
                let mut path_in_variant = path_in_content.clone();
                path_in_variant.push_front(annot::Field::Variant(*variant));

                copy_aliases(
                    &mut expr_info,
                    &path_in_variant,
                    &content_info,
                    *content,
                    &path_in_content,
                );
            }

            for (fold_point_in_content, _) in
                get_fold_points_in(&orig.custom_types, &content_info.type_)
            {
                let mut fold_point_in_variant = fold_point_in_content.clone();
                fold_point_in_variant.push_front(annot::Field::Variant(*variant));

                expr_info.set_folded_aliases(
                    fold_point_in_variant,
                    content_info.folded_aliases[&fold_point_in_content].clone(),
                );
            }

            (
                annot::Expr::WrapVariant(variant_types.clone(), *variant, *content),
                expr_info,
            )
        }

        flat::Expr::UnwrapVariant(variant_id, variant) => {
            let variant_info = &ctx[variant];

            let content_type = if let anon::Type::Variants(variant_types) = &variant_info.type_ {
                &variant_types[variant_id]
            } else {
                unreachable!()
            };

            let mut expr_info = ValInfo::new();

            for (path_in_content, _) in get_names_in(&orig.custom_types, content_type) {
                let mut path_in_variant = path_in_content.clone();
                path_in_variant.push_front(annot::Field::Variant(*variant_id));

                expr_info.create_path(path_in_content.clone());
                copy_aliases(
                    &mut expr_info,
                    &path_in_content,
                    variant_info,
                    *variant,
                    &path_in_variant,
                );
            }

            for (fold_point_in_content, _) in get_fold_points_in(&orig.custom_types, content_type) {
                let mut fold_point_in_variant = fold_point_in_content.clone();
                fold_point_in_variant.push_front(annot::Field::Variant(*variant_id));

                expr_info.create_folded_aliases(
                    fold_point_in_content,
                    variant_info.folded_aliases[&fold_point_in_variant].clone(),
                );
            }

            (annot::Expr::UnwrapVariant(*variant_id, *variant), expr_info)
        }

        flat::Expr::WrapBoxed(content, content_type) => {
            let content_info = &ctx[content];

            debug_assert_eq!(&content_info.type_, content_type);

            let mut expr_info = ValInfo::new();

            for (path_in_content, _) in get_names_in(&orig.custom_types, content_type) {
                let mut path_in_boxed = path_in_content.clone();
                path_in_boxed.push_front(annot::Field::Boxed);

                expr_info.create_path(path_in_boxed.clone());
                copy_aliases(
                    &mut expr_info,
                    &path_in_boxed,
                    content_info,
                    *content,
                    &path_in_content,
                );
            }

            for (fold_point_in_content, _) in get_fold_points_in(&orig.custom_types, content_type) {
                let mut fold_point_in_boxed = fold_point_in_content.clone();
                fold_point_in_boxed.push_front(annot::Field::Boxed);

                expr_info.create_folded_aliases(
                    fold_point_in_boxed,
                    content_info.folded_aliases[&fold_point_in_content].clone(),
                );
            }

            (
                annot::Expr::WrapBoxed(*content, content_type.clone()),
                expr_info,
            )
        }

        flat::Expr::UnwrapBoxed(boxed, content_type) => {
            let boxed_info = &ctx[boxed];

            let mut expr_info = ValInfo::new();

            for (path_in_content, _) in get_names_in(&orig.custom_types, content_type) {
                let mut path_in_boxed = path_in_content.clone();
                path_in_boxed.push_front(annot::Field::Boxed);

                expr_info.create_path(path_in_content.clone());
                copy_aliases(
                    &mut expr_info,
                    &path_in_content,
                    boxed_info,
                    *boxed,
                    &path_in_boxed,
                );
            }

            for (fold_point_in_content, _) in get_fold_points_in(&orig.custom_types, content_type) {
                let mut fold_point_in_boxed = fold_point_in_content.clone();
                fold_point_in_boxed.push_front(annot::Field::Boxed);

                expr_info.create_folded_aliases(
                    fold_point_in_content,
                    boxed_info.folded_aliases[&fold_point_in_boxed].clone(),
                );
            }

            (
                annot::Expr::UnwrapBoxed(*boxed, content_type.clone()),
                expr_info,
            )
        }

        flat::Expr::WrapCustom(custom_id, content) => {
            let mut expr_info = empty_info(&orig.custom_types, &anon::Type::Custom(*custom_id));

            let custom_scc = orig.custom_types.types[custom_id].scc;
            let content_type = &orig.custom_types.types[custom_id].content;

            let content_info = &ctx[content];

            debug_assert_eq!(&content_info.type_, content_type);

            for (content_path, _) in get_names_in(&orig.custom_types, content_type) {
                let (fold_point, in_custom, normalized) =
                    split_at_fold(custom_scc, *custom_id, content_path.clone());

                let mut wrapped_path = normalized.0.clone();
                wrapped_path.push_front(annot::Field::Custom(in_custom));
                wrapped_path.push_front(annot::Field::CustomScc(custom_scc, *custom_id));

                // Wire up directly
                expr_info.add_edge_to_local(
                    wrapped_path.clone(),
                    (*content, content_path.clone()),
                    Disj::True,
                );

                for ((other, other_path), cond) in &content_info.aliases[&content_path].aliases {
                    if other == content {
                        // Wire up transitive self edges (tricky)
                        let (other_fold_point, other_in_custom, other_normalized) =
                            split_at_fold(custom_scc, *custom_id, other_path.clone());

                        if other_fold_point == fold_point {
                            let mut other_wrapped = other_normalized.0;
                            other_wrapped.push_front(annot::Field::Custom(other_in_custom));
                            other_wrapped
                                .push_front(annot::Field::CustomScc(custom_scc, *custom_id));

                            expr_info.add_self_edge(
                                wrapped_path.clone(),
                                other_wrapped,
                                cond.clone(),
                            );
                        } else {
                            // TODO: Are we absolutely certain that adding a cross-edge is
                            // *all* we need to do in this case?  Is it ever necessary to
                            // also add a normal edge here?

                            // "Cross-edge" between folded copies
                            expr_info.add_folded_alias(
                                &vector![annot::Field::CustomScc(custom_scc, *custom_id)],
                                NormPair::new(
                                    annot::SubPath(
                                        normalized
                                            .0
                                            .clone()
                                            .add_front(annot::Field::Custom(in_custom)),
                                    ),
                                    annot::SubPath(
                                        other_normalized
                                            .0
                                            .clone()
                                            .add_front(annot::Field::Custom(other_in_custom)),
                                    ),
                                ),
                                cond.clone(),
                            );
                        }
                    }

                    // Write up transitive external edges
                    expr_info.add_edge_to_local(
                        wrapped_path.clone(),
                        (*other, other_path.clone()),
                        cond.clone(),
                    );
                }
            }

            for (content_fold_point, _) in get_fold_points_in(&orig.custom_types, content_type) {
                let wrapped_path =
                    split_fold_at_fold(custom_scc, *custom_id, content_fold_point.clone())
                        .add_front(annot::Field::CustomScc(custom_scc, *custom_id));

                'copy_folded: for (pair, cond) in
                    &content_info.folded_aliases[&content_fold_point].inter_elem_aliases
                {
                    for pair_path in [pair.fst(), pair.snd()] {
                        if pair_path.0.iter().any(|field| matches!(field, annot::Field::CustomScc(scc, _) if *scc == custom_scc)) {
                                    // This sub-path doesn't exist in the corresponding fold point
                                    // in the wrapped type, so we can't copy it over directly.
                                    //
                                    // TODO: Do we need to add an SCC-level cross-edge here?
                                    // (probably yes!)
                                    continue 'copy_folded;
                                }
                    }

                    expr_info.add_folded_alias(&wrapped_path, pair.clone(), cond.clone());
                }
            }

            (annot::Expr::WrapCustom(*custom_id, *content), expr_info)
        }

        flat::Expr::UnwrapCustom(custom_id, wrapped) => {
            let custom_scc = orig.custom_types.types[custom_id].scc;
            let content_type = &orig.custom_types.types[custom_id].content;

            let mut expr_info = empty_info(&orig.custom_types, content_type);

            let wrapped_info = &ctx[wrapped];

            for (content_path, _) in get_names_in(&orig.custom_types, content_type) {
                // This "fold_point" is a path prefix within the *content*, not the wrapped value.
                // As such, it does not begin with a leading `Custom(custom_id)` field.
                let (fold_point, in_custom, wrapped_subpath) =
                    split_at_fold(custom_scc, *custom_id, content_path.clone());

                let mut wrapped_path = wrapped_subpath.0.clone();
                wrapped_path.push_front(annot::Field::Custom(in_custom));
                wrapped_path.push_front(annot::Field::CustomScc(custom_scc, *custom_id));

                // Wire up directly
                expr_info.add_edge_to_local(
                    content_path.clone(),
                    (*wrapped, wrapped_path.clone()),
                    Disj::True,
                );

                for ((other, other_path), cond) in &wrapped_info.aliases[&wrapped_path].aliases {
                    if other == wrapped {
                        debug_assert_eq!(
                            &other_path[0],
                            &annot::Field::CustomScc(custom_scc, *custom_id),
                        );

                        debug_assert!(matches!(&other_path[1], annot::Field::Custom(_)));
                        if other_path[1] == annot::Field::Custom(*custom_id) {
                            let other_inner_subpath = other_path.skip(1);

                            let other_content_path = if fold_point.is_empty() {
                                debug_assert_eq!(in_custom, *custom_id);
                                other_inner_subpath.skip(1)
                            } else {
                                let mut other_content_path = fold_point.clone();
                                other_content_path.append(other_inner_subpath);
                                other_content_path
                            };

                            debug_assert_eq!(
                                split_at_fold(custom_scc, *custom_id, content_path.clone()).0,
                                split_at_fold(custom_scc, *custom_id, other_content_path.clone()).0,
                            );

                            expr_info.add_self_edge(
                                content_path.clone(),
                                other_content_path.clone(),
                                cond.clone(),
                            );
                        }
                    }

                    expr_info.add_edge_to_local(
                        content_path.clone(),
                        (*other, other_path.clone()),
                        cond.clone(),
                    );
                }
            }

            // Copy all internal fold points
            for (content_fold_point, _) in get_fold_points_in(&orig.custom_types, content_type) {
                let wrapped_path =
                    split_fold_at_fold(custom_scc, *custom_id, content_fold_point.clone())
                        .add_front(annot::Field::CustomScc(custom_scc, *custom_id));

                expr_info.set_folded_aliases(
                    content_fold_point.clone(),
                    wrapped_info.folded_aliases[&wrapped_path].clone(),
                );
            }

            // Unfurl folded edges
            {
                let fold_groups =
                    group_unfolded_names_by_folded_form(&orig.custom_types, *custom_id);

                let mut content_fold_points = BTreeMap::<_, BTreeMap<_, _>>::new();
                for (_, content_paths) in &fold_groups {
                    for content_path in content_paths {
                        content_fold_points
                            .entry(content_path)
                            .or_insert_with(|| split_at_all_fold_points(content_path));
                    }
                }

                for (pair, cond) in &wrapped_info.folded_aliases
                    [&vector![annot::Field::CustomScc(custom_scc, *custom_id)]]
                    .inter_elem_aliases
                {
                    for content_path_1 in &fold_groups[pair.fst()] {
                        for content_path_2 in &fold_groups[pair.snd()] {
                            if content_path_1 != content_path_2 {
                                expr_info.add_self_edge(
                                    content_path_1.clone(),
                                    content_path_2.clone(),
                                    cond.clone(),
                                );

                                // We need to fill in cross-edges between sub-paths which
                                // are not expressible in the wrapped type because they
                                // recursively mention the SCC.
                                let fold_points_1 = &content_fold_points[content_path_1];
                                let fold_points_2 = &content_fold_points[content_path_2];
                                for (fold_point, content_sub_path_1) in fold_points_1 {
                                    if let Some(content_sub_path_2) = fold_points_2.get(fold_point)
                                    {
                                        expr_info.add_folded_alias(
                                            fold_point,
                                            NormPair::new(
                                                content_sub_path_1.clone(),
                                                content_sub_path_2.clone(),
                                            ),
                                            cond.clone(),
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }

            (annot::Expr::UnwrapCustom(*custom_id, *wrapped), expr_info)
        }

        // NOTE [intrinsics]: If we add array intrinsics in the future, this will need to be
        // modified.
        flat::Expr::Intrinsic(intr, arg) => (annot::Expr::Intrinsic(*intr, *arg), ValInfo::new()),

        flat::Expr::ArrayOp(flat::ArrayOp::Get(item_type, array, index)) => {
            let array_info = &ctx[array];

            let mut expr_info = ValInfo::new();

            for (path_in_item, _) in get_names_in(&orig.custom_types, item_type) {
                let mut path_in_array = path_in_item.clone();
                path_in_array.push_front(annot::Field::ArrayMembers);

                expr_info.create_path(path_in_item.clone());
                copy_aliases(
                    &mut expr_info,
                    &path_in_item,
                    array_info,
                    *array,
                    &path_in_array,
                );
            }

            for (fold_point_in_item, _) in get_fold_points_in(&orig.custom_types, item_type) {
                let mut fold_point_in_array = fold_point_in_item.clone();
                fold_point_in_array.push_front(annot::Field::ArrayMembers);

                expr_info.create_folded_aliases(
                    fold_point_in_item,
                    array_info.folded_aliases[&fold_point_in_array].clone(),
                );
            }

            let array_aliases = array_info.aliases[&Vector::new()].clone();

            (
                annot::Expr::ArrayOp(annot::ArrayOp::Get(
                    item_type.clone(),
                    array_aliases,
                    *array,
                    *index,
                )),
                expr_info,
            )
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Extract(item_type, array, index)) => {
            debug_assert_eq!(
                get_names_in(
                    &orig.custom_types,
                    &anon::Type::Array(Box::new(item_type.clone()))
                )
                .into_iter()
                .map(|(path, _)| path)
                .collect::<BTreeSet<_>>(),
                get_names_in(
                    &orig.custom_types,
                    &anon::Type::HoleArray(Box::new(item_type.clone()))
                )
                .into_iter()
                .map(|(path, _)| path)
                .collect::<BTreeSet<_>>()
            );

            let expr_info = array_extraction_aliases(
                orig,
                ctx,
                item_type,
                *array,
                // Hole array is the second return value
                annot::Field::Field(1),
                // Item is the first return value
                annot::Field::Field(0),
            );

            let array_aliases = ctx[array].aliases[&Vector::new()].clone();

            (
                annot::Expr::ArrayOp(annot::ArrayOp::Extract(
                    item_type.clone(),
                    array_aliases,
                    *array,
                    *index,
                )),
                expr_info,
            )
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Pop(item_type, array)) => {
            let expr_info = array_extraction_aliases(
                orig,
                ctx,
                item_type,
                *array,
                // New array is the first return value
                annot::Field::Field(0),
                // Popped item is the second return value
                annot::Field::Field(1),
            );

            let array_aliases = ctx[array].aliases[&Vector::new()].clone();

            (
                annot::Expr::ArrayOp(annot::ArrayOp::Pop(
                    item_type.clone(),
                    array_aliases,
                    *array,
                )),
                expr_info,
            )
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Replace(item_type, hole_array, item)) => {
            let expr_info = array_insertion_aliases(orig, ctx, item_type, *hole_array, *item);

            let hole_array_aliases = ctx[hole_array].aliases[&Vector::new()].clone();

            (
                annot::Expr::ArrayOp(annot::ArrayOp::Replace(
                    item_type.clone(),
                    hole_array_aliases,
                    *hole_array,
                    *item,
                )),
                expr_info,
            )
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Push(item_type, array, item)) => {
            let expr_info = array_insertion_aliases(orig, ctx, item_type, *array, *item);

            let array_aliases = ctx[array].aliases[&Vector::new()].clone();

            (
                annot::Expr::ArrayOp(annot::ArrayOp::Push(
                    item_type.clone(),
                    array_aliases,
                    *array,
                    *item,
                )),
                expr_info,
            )
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Len(item_type, array)) => {
            let array_aliases = ctx[array].aliases[&Vector::new()].clone();

            (
                annot::Expr::ArrayOp(annot::ArrayOp::Len(
                    item_type.clone(),
                    array_aliases,
                    *array,
                )),
                ValInfo::new(),
            )
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Reserve(item_type, array, capacity)) => {
            let array_info = &ctx[array];

            let mut expr_info = ValInfo::new();

            for (path_in_item, _) in get_names_in(&orig.custom_types, item_type) {
                let mut path_in_array = path_in_item;
                path_in_array.push_front(annot::Field::ArrayMembers);

                expr_info.create_path(path_in_array.clone());
                copy_aliases(
                    &mut expr_info,
                    &path_in_array,
                    array_info,
                    *array,
                    &path_in_array,
                );
            }

            expr_info.create_path(Vector::new());

            for (fold_point_in_array, _) in get_fold_points_in(
                &orig.custom_types,
                &anon::Type::Array(Box::new(item_type.clone())),
            ) {
                expr_info.create_folded_aliases(
                    fold_point_in_array.clone(),
                    array_info.folded_aliases[&fold_point_in_array].clone(),
                );
            }

            let array_aliases = array_info.aliases[&Vector::new()].clone();

            (
                annot::Expr::ArrayOp(annot::ArrayOp::Reserve(
                    item_type.clone(),
                    array_aliases,
                    *array,
                    *capacity,
                )),
                expr_info,
            )
        }

        flat::Expr::IoOp(flat::IoOp::Input) => (
            annot::Expr::IoOp(annot::IoOp::Input),
            empty_info(
                &orig.custom_types,
                &anon::Type::Array(Box::new(anon::Type::Num(first_ord::NumType::Byte))),
            ),
        ),

        flat::Expr::IoOp(flat::IoOp::Output(array)) => {
            let array_aliases = ctx[array].aliases[&Vector::new()].clone();

            (
                annot::Expr::IoOp(annot::IoOp::Output(array_aliases, *array)),
                ValInfo::new(),
            )
        }

        flat::Expr::Panic(ret_type, array) => {
            let array_aliases = ctx[array].aliases[&Vector::new()].clone();

            (
                annot::Expr::Panic(ret_type.clone(), array_aliases, *array),
                empty_info(&orig.custom_types, ret_type),
            )
        }

        flat::Expr::ArrayLit(item_type, items) => {
            let mut expr_info = empty_info(
                &orig.custom_types,
                &anon::Type::Array(Box::new(item_type.clone())),
            );

            let item_ids = items.iter().cloned().collect::<BTreeSet<flat::LocalId>>();

            let item_paths = get_names_in(&orig.custom_types, item_type);
            let item_fold_points = get_fold_points_in(&orig.custom_types, item_type);

            for item in items {
                let item_info = &ctx[item];

                for (item_path, _) in &item_paths {
                    let mut ret_array_path = item_path.clone();
                    ret_array_path.push_front(annot::Field::ArrayMembers);

                    // Wire up directly
                    expr_info.add_edge_to_local(
                        ret_array_path.clone(),
                        (*item, item_path.clone()),
                        Disj::True,
                    );

                    // Wire up transitive edges
                    for ((other, other_path), cond) in &item_info.aliases[item_path].aliases {
                        if other == item {
                            let mut other_ret_array_path = other_path.clone();
                            other_ret_array_path.push_front(annot::Field::ArrayMembers);

                            expr_info.add_self_edge(
                                ret_array_path.clone(),
                                other_ret_array_path,
                                cond.clone(),
                            );
                        } else if item_ids.contains(other) {
                            // TODO: Are we absolutely certain that adding a cross-edge is *all* we
                            // need to do in this case?  Is it ever necessary to also add a normal
                            // edge here?

                            expr_info.add_folded_alias(
                                &vector![annot::Field::ArrayMembers],
                                NormPair::new(
                                    annot::SubPath(item_path.clone()),
                                    annot::SubPath(other_path.clone()),
                                ),
                                cond.clone(),
                            );
                        }

                        expr_info.add_edge_to_local(
                            ret_array_path.clone(),
                            (*other, other_path.clone()),
                            cond.clone(),
                        );
                    }
                }

                for (item_fold_point, _) in &item_fold_points {
                    let mut ret_array_fold_point = item_fold_point.clone();
                    ret_array_fold_point.push_front(annot::Field::ArrayMembers);

                    for (pair, cond) in
                        &item_info.folded_aliases[item_fold_point].inter_elem_aliases
                    {
                        expr_info.add_folded_alias(
                            &ret_array_fold_point,
                            pair.clone(),
                            cond.clone(),
                        );
                    }
                }
            }

            (
                annot::Expr::ArrayLit(item_type.clone(), items.clone()),
                expr_info,
            )
        }

        &flat::Expr::BoolLit(val) => (annot::Expr::BoolLit(val), ValInfo::new()),
        &flat::Expr::ByteLit(val) => (annot::Expr::ByteLit(val), ValInfo::new()),
        &flat::Expr::IntLit(val) => (annot::Expr::IntLit(val), ValInfo::new()),
        &flat::Expr::FloatLit(val) => (annot::Expr::FloatLit(val), ValInfo::new()),
    }
}

fn group_by_item_type<'a>(
    paths: impl Iterator<Item = (annot::FieldPath, &'a anon::Type)>,
) -> Vec<Vec<annot::FieldPath>> {
    let mut paths_by_type = BTreeMap::<&anon::Type, Vec<annot::FieldPath>>::new();
    for (path, type_) in paths {
        match type_ {
            anon::Type::Array(item_type) | anon::Type::HoleArray(item_type) => {
                paths_by_type.entry(item_type).or_default().push(path)
            }
            _ => unreachable!(),
        }
    }
    paths_by_type.into_iter().map(|(_, paths)| paths).collect()
}

fn get_aliasable_name_groups_in(
    typedefs: &flat::CustomTypes,
    type_: &anon::Type,
) -> Vec<Vec<annot::FieldPath>> {
    group_by_item_type(get_names_in(typedefs, type_).into_iter())
}

fn get_aliasable_name_groups_in_fold_point(
    typedefs: &flat::CustomTypes,
    fold_point: &FoldPoint<'_>,
) -> Vec<Vec<annot::SubPath>> {
    group_by_item_type(
        get_sub_names_in(typedefs, fold_point)
            .into_iter()
            .map(|(path, type_)| (path.0, type_)),
    )
    .into_iter()
    .map(|paths| paths.into_iter().map(annot::SubPath).collect())
    .collect()
}

fn annot_func(
    orig: &flat::Program,
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, annot::FuncDef>,
    func_def: &flat::FuncDef,
) -> annot::FuncDef {
    let mut arg_aliases = OrdMap::new();
    for paths in get_aliasable_name_groups_in(&orig.custom_types, &func_def.arg_type) {
        for path1 in &paths {
            let path1_aliases = paths
                .iter()
                .filter(|path2| path2 != &path1)
                .map(|path2| {
                    (
                        (flat::ARG_LOCAL, path2.clone()),
                        Disj::Any(OrdSet::unit(annot::AliasCondition::AliasInArg(
                            NormPair::new(
                                annot::ArgName(path1.clone()),
                                annot::ArgName(path2.clone()),
                            ),
                        ))),
                    )
                })
                .collect();

            arg_aliases.insert(
                path1.clone(),
                annot::LocalAliases {
                    aliases: path1_aliases,
                },
            );
        }
    }

    let arg_folded_aliases = get_fold_points_in(&orig.custom_types, &func_def.arg_type)
        .into_iter()
        .map(|(fold_point, fold_point_info)| {
            let mut folded_aliases = OrdMap::new();
            for paths in
                get_aliasable_name_groups_in_fold_point(&orig.custom_types, &fold_point_info)
            {
                for (i, path1) in paths.iter().enumerate() {
                    // Folded edges are symmetric, so we only need to insert each edge in one
                    // direction.  This means it's enough to wire each sub-path up to all the
                    // sub-paths appearing after it in the list (including itself).
                    for path2 in &paths[i..] {
                        let pair = NormPair::new(path1.clone(), path2.clone());

                        folded_aliases.insert(
                            pair.clone(),
                            Disj::Any(OrdSet::unit(annot::AliasCondition::FoldedAliasInArg(
                                annot::ArgName(fold_point.clone()),
                                pair,
                            ))),
                        );
                    }
                }
            }

            (
                fold_point,
                annot::FoldedAliases {
                    inter_elem_aliases: folded_aliases,
                },
            )
        })
        .collect();

    let arg_info = LocalInfo {
        type_: func_def.arg_type.clone(),
        aliases: arg_aliases,
        folded_aliases: arg_folded_aliases,
    };

    let init_ctx = OrdMap::unit(flat::ARG_LOCAL, arg_info);

    let (annot_body, ret_info) = annot_expr(orig, sigs, &init_ctx, &func_def.body);

    let ret_arg_aliases = ret_info
        .local_aliases()
        .iter()
        .map(|(ret_path, annot::LocalAliases { aliases })| {
            (
                annot::RetName(ret_path.clone()),
                aliases
                    .iter()
                    .map(|((local_id, local_path), cond)| {
                        debug_assert_eq!(local_id, &flat::ARG_LOCAL);
                        (annot::ArgName(local_path.clone()), cond.clone())
                    })
                    .collect::<OrdMap<_, _>>(),
            )
        })
        .collect();

    let ret_ret_aliases = ret_info
        .self_aliases()
        .iter()
        .map(|(pair, cond)| {
            (
                NormPair::new(
                    annot::RetName(pair.fst().clone()),
                    annot::RetName(pair.snd().clone()),
                ),
                cond.clone(),
            )
        })
        .collect();

    let ret_folded_aliases = ret_info
        .folded_aliases()
        .iter()
        .map(|(fold_point, folded_aliases)| {
            (annot::RetName(fold_point.clone()), folded_aliases.clone())
        })
        .collect();

    let alias_sig = annot::AliasSig {
        ret_arg_aliases,
        ret_ret_aliases,
        ret_folded_aliases,
    };

    annot::FuncDef {
        purity: func_def.purity,
        arg_type: func_def.arg_type.clone(),
        ret_type: func_def.ret_type.clone(),
        alias_sig,
        body: annot_body,
        profile_point: func_def.profile_point,
    }
}
