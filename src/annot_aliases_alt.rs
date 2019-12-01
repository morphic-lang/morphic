use im_rc::{vector, OrdMap, OrdSet, Vector};
use std::collections::{BTreeMap, BTreeSet};

use crate::data::alias_annot_ast as annot;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::graph::{self, Graph};
use crate::util::disjunction::Disj;
use crate::util::id_vec::IdVec;
use crate::util::norm_pair::NormPair;

pub fn annot_aliases(program: flat::Program) -> annot::Program {
    let mut annotated = IdVec::from_items((0..program.funcs.len()).map(|_| None).collect());

    let dep_graph = func_dependency_graph(&program);

    for scc in &graph::strongly_connected(&dep_graph) {
        if scc.len() == 1 && !dep_graph.edges_out[scc[0]].contains(&scc[0]) {
            // This SCC consists of a single non-recursive function, which means that as a
            // performance optimization we can get away with only performing a single iteration of
            // abstract interpretation.
            let annotated_func_def = annot_func(
                &program,
                &SignatureAssumptions {
                    known_defs: &annotated,
                    provisional_defs: Some(&BTreeMap::new()),
                },
                &program.funcs[scc[0]],
            );

            debug_assert!(annotated[scc[0]].is_none());
            annotated[scc[0]] = Some(annotated_func_def);
        } else {
            // This SCC consists of one or more (mutually) recursive functions, so we need to do the
            // full iterative fixed point computation.
            let annotated_defs = annot_scc_fixed_point(&program, &annotated, scc);

            debug_assert_eq!(
                annotated_defs.keys().collect::<BTreeSet<_>>(),
                scc.iter().collect::<BTreeSet<_>>()
            );

            for (func, annotated_def) in annotated_defs {
                debug_assert!(annotated[func].is_none());
                annotated[func] = Some(annotated_def);
            }
        }
    }

    annot::Program {
        custom_types: program.custom_types,
        funcs: annotated.into_mapped(|_, func_def| func_def.unwrap()),
        main: program.main,
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
struct SignatureAssumptions<'a> {
    known_defs: &'a IdVec<first_ord::CustomFuncId, Option<annot::FuncDef>>,
    provisional_defs: Option<&'a BTreeMap<first_ord::CustomFuncId, annot::FuncDef>>, // None on first pass
}

impl<'a> SignatureAssumptions<'a> {
    fn sig_of(&self, func: &first_ord::CustomFuncId) -> Option<&'a annot::AliasSig> {
        if let Some(func_def) = &self.known_defs[func] {
            Some(&func_def.alias_sig)
        } else if let Some(provisional_defs) = &self.provisional_defs {
            Some(&provisional_defs[func].alias_sig)
        } else {
            None
        }
    }
}

// Computes the fields in `type_` at which there is a name
fn get_names_in<'a>(
    type_defs: &'a IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &'a anon::Type,
) -> Vec<(annot::FieldPath, &'a anon::Type)> {
    let mut names = Vec::new();
    add_names_from_type(
        type_defs,
        &mut names,
        &mut BTreeSet::new(),
        type_,
        Vector::new(),
    );
    return names;

    // Recursively appends paths to names in `type_` to `names`
    fn add_names_from_type<'a>(
        type_defs: &'a IdVec<first_ord::CustomTypeId, anon::Type>,
        names: &mut Vec<(annot::FieldPath, &'a anon::Type)>,
        typedefs_on_path: &mut BTreeSet<first_ord::CustomTypeId>,
        type_: &'a anon::Type,
        prefix: annot::FieldPath,
    ) {
        match type_ {
            anon::Type::Bool | anon::Type::Num(_) => {}
            anon::Type::Array(item_type) | anon::Type::HoleArray(item_type) => {
                // The array itself:
                names.push((prefix.clone(), type_));
                // The names in elements of the array:
                let mut new_prefix = prefix.clone();
                new_prefix.push_back(annot::Field::ArrayMembers);
                add_names_from_type(type_defs, names, typedefs_on_path, item_type, new_prefix);
            }
            anon::Type::Tuple(item_types) => {
                for (i, item_type) in item_types.iter().enumerate() {
                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(annot::Field::Field(i));
                    add_names_from_type(type_defs, names, typedefs_on_path, item_type, new_prefix);
                }
            }
            anon::Type::Variants(variant_types) => {
                for (variant, variant_type) in variant_types {
                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(annot::Field::Variant(variant));
                    add_names_from_type(
                        type_defs,
                        names,
                        typedefs_on_path,
                        variant_type,
                        new_prefix,
                    );
                }
            }
            anon::Type::Custom(id) => {
                if !typedefs_on_path.contains(id) {
                    typedefs_on_path.insert(*id);
                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(annot::Field::Custom(*id));
                    add_names_from_type(
                        type_defs,
                        names,
                        typedefs_on_path,
                        &type_defs[id],
                        new_prefix,
                    );
                    // Remove if we added it
                    typedefs_on_path.remove(id);
                }
            }
        }
    }
}

// TODO: We currently introduce fold points even when their associated set of sub-paths is empty.
// For example, for the type `Array Int` we generate a fold point at the path `[ArrayMembers]`, even
// though `Int` contains no heap-cell names of its own.
//
// This is fine from a correctness standpoint, but it incurs a performance cost, and may be
// confusing during debugging.
fn get_fold_points_in<'a>(
    type_defs: &'a IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &'a anon::Type,
) -> Vec<(annot::FieldPath, &'a anon::Type)> {
    let mut points = Vec::new();
    add_points_from_type(
        type_defs,
        &mut points,
        &mut BTreeSet::new(),
        type_,
        Vector::new(),
    );
    return points;

    fn add_points_from_type<'a>(
        type_defs: &'a IdVec<first_ord::CustomTypeId, anon::Type>,
        points: &mut Vec<(annot::FieldPath, &'a anon::Type)>,
        typedefs_on_path: &mut BTreeSet<first_ord::CustomTypeId>,
        type_: &'a anon::Type,
        prefix: annot::FieldPath,
    ) {
        match type_ {
            anon::Type::Bool | anon::Type::Num(_) => {}
            anon::Type::Array(item_type) | anon::Type::HoleArray(item_type) => {
                let mut new_prefix = prefix.clone();
                new_prefix.push_back(annot::Field::ArrayMembers);

                // The array's elements are a fold point
                points.push((new_prefix.clone(), item_type));

                add_points_from_type(type_defs, points, typedefs_on_path, item_type, new_prefix);
            }
            anon::Type::Tuple(item_types) => {
                for (i, item_type) in item_types.iter().enumerate() {
                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(annot::Field::Field(i));
                    add_points_from_type(
                        type_defs,
                        points,
                        typedefs_on_path,
                        item_type,
                        new_prefix,
                    );
                }
            }
            anon::Type::Variants(variant_types) => {
                for (variant, variant_type) in variant_types {
                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(annot::Field::Variant(variant));
                    add_points_from_type(
                        type_defs,
                        points,
                        typedefs_on_path,
                        variant_type,
                        new_prefix,
                    );
                }
            }
            anon::Type::Custom(id) => {
                if !typedefs_on_path.contains(id) {
                    typedefs_on_path.insert(*id);

                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(annot::Field::Custom(*id));

                    // This is a fold point
                    points.push((new_prefix.clone(), &type_defs[id]));

                    add_points_from_type(
                        type_defs,
                        points,
                        typedefs_on_path,
                        &type_defs[id],
                        new_prefix,
                    );

                    // Remove if we added it
                    typedefs_on_path.remove(id);
                }
            }
        }
    }
}

fn get_content_folded_occurrences(
    type_defs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    target: first_ord::CustomTypeId,
) -> Vec<annot::FieldPath> {
    // We always have a 'root' occurrence
    let mut occurs = vec![Vector::new()];
    add_occurs_from_type(
        type_defs,
        target,
        &mut occurs,
        &mut BTreeSet::new(),
        &type_defs[target],
        &Vector::new(),
    );
    return occurs;

    fn add_occurs_from_type(
        type_defs: &IdVec<first_ord::CustomTypeId, anon::Type>,
        target: first_ord::CustomTypeId,
        occurs: &mut Vec<annot::FieldPath>,
        typedefs_on_path: &mut BTreeSet<first_ord::CustomTypeId>,
        type_: &anon::Type,
        prefix: &annot::FieldPath,
    ) {
        match type_ {
            anon::Type::Bool | anon::Type::Num(_) => {}

            anon::Type::Array(item_type) | anon::Type::HoleArray(item_type) => {
                let mut new_prefix = prefix.clone();
                new_prefix.push_back(annot::Field::ArrayMembers);
                add_occurs_from_type(
                    type_defs,
                    target,
                    occurs,
                    typedefs_on_path,
                    item_type,
                    &new_prefix,
                );
            }

            anon::Type::Tuple(item_types) => {
                for (i, item_type) in item_types.iter().enumerate() {
                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(annot::Field::Field(i));
                    add_occurs_from_type(
                        type_defs,
                        target,
                        occurs,
                        typedefs_on_path,
                        item_type,
                        &new_prefix,
                    );
                }
            }

            anon::Type::Variants(variant_types) => {
                for (variant, variant_type) in variant_types {
                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(annot::Field::Variant(variant));
                    add_occurs_from_type(
                        type_defs,
                        target,
                        occurs,
                        typedefs_on_path,
                        variant_type,
                        &new_prefix,
                    );
                }
            }

            anon::Type::Custom(id) => {
                if !typedefs_on_path.contains(id) {
                    if *id == target {
                        // Add the occurrence itself
                        let mut occurrence = prefix.clone();
                        occurrence.push_back(annot::Field::Custom(target));
                        occurs.push(occurrence);
                    // Due to type folding, there can't be any recursive occurrences, so we
                    // don't need to recurse into the content type.
                    } else {
                        typedefs_on_path.insert(*id);
                        let mut new_prefix = prefix.clone();
                        new_prefix.push_back(annot::Field::Custom(*id));
                        add_occurs_from_type(
                            type_defs,
                            target,
                            occurs,
                            typedefs_on_path,
                            &type_defs[id],
                            &new_prefix,
                        );
                        // Remove if we added it
                        typedefs_on_path.remove(id);
                    }
                }
            }
        }
    }
}

fn split_at_fold(
    to_fold: first_ord::CustomTypeId,
    path: annot::FieldPath,
) -> (annot::FieldPath, annot::SubPath) {
    match path.index_of(&annot::Field::Custom(to_fold)) {
        Some(split_point) => {
            let (fold_point, sub_path) = path.split_at(split_point + 1);
            (fold_point, annot::SubPath(sub_path))
        }
        None => (Vector::new(), annot::SubPath(path)),
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
            debug_assert!(self.local_aliases.contains_key(path));
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

fn empty_info(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &anon::Type,
) -> ValInfo {
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
    dest.create_path(dest_path.clone());

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

fn translate_callee_cond(
    arg_id: flat::LocalId,
    arg_info: &LocalInfo,
    callee_cond: &annot::AliasCondition,
) -> Disj<annot::AliasCondition> {
    match callee_cond {
        annot::AliasCondition::AliasInArg(arg_pair) => {
            let annot::ArgName(arg_pair_fst) = arg_pair.fst();
            let annot::ArgName(arg_pair_snd) = arg_pair.snd();

            arg_info.aliases[arg_pair_fst]
                .aliases
                .get(&(arg_id, arg_pair_snd.clone()))
                .cloned()
                .unwrap_or_default()
        }

        annot::AliasCondition::FoldedAliasInArg(annot::ArgName(fold_point), sub_path_pair) => {
            arg_info.folded_aliases[fold_point]
                .inter_elem_aliases
                .get(sub_path_pair)
                .cloned()
                .unwrap_or_default()
        }
    }
}

fn translate_callee_cond_disj(
    arg_id: flat::LocalId,
    arg_info: &LocalInfo,
    callee_cond_disj: &Disj<annot::AliasCondition>,
) -> Disj<annot::AliasCondition> {
    match callee_cond_disj {
        Disj::True => Disj::True,

        Disj::Any(callee_conds) => {
            let mut caller_cond_disj = Disj::new();
            for callee_cond in callee_conds {
                caller_cond_disj.or_mut(translate_callee_cond(arg_id, arg_info, callee_cond));
            }
            caller_cond_disj
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
    {
        for (array_path, _) in get_names_in(&orig.custom_types, &array_info.type_) {
            let mut ret_path = array_path.clone();
            ret_path.push_front(ret_array_field);

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
                if *other == array {
                    // It should not be possible for an array to (transitively) contain itself, so
                    // we can assume that any self-edge within the array is a self edge within its
                    // members.
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
        get_names_in(&orig.custom_types, &array_info.type_),
        get_names_in(
            &orig.custom_types,
            &anon::Type::Array(Box::new(item_type.clone()))
        )
    );

    // Wire up aliases contributed by array
    {
        for (array_path, _) in get_names_in(&orig.custom_types, &array_info.type_) {
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

                if *other == array {
                    // It should not be possible for an array to (transitively) contain itself, so
                    // we can assume that any edge between the array and the item is an edge between
                    // the *members* of the array and the item.
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
    sigs: &SignatureAssumptions,
    ctx: &OrdMap<flat::LocalId, LocalInfo>,
    expr: &flat::Expr,
) -> (annot::Expr, ValInfo) {
    match expr {
        flat::Expr::Local(local) => {
            let mut expr_info = ValInfo::new();

            let local_info = &ctx[local];
            for (path, _) in get_names_in(&orig.custom_types, &local_info.type_) {
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
                                            arg_info,
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
                                    translate_callee_cond_disj(*arg, arg_info, callee_cond),
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
                        let caller_cond = translate_callee_cond_disj(*arg, arg_info, callee_cond);

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

        flat::Expr::WrapCustom(custom_id, content) => {
            let mut expr_info = empty_info(&orig.custom_types, &anon::Type::Custom(*custom_id));

            let content_info = &ctx[content];

            debug_assert_eq!(&content_info.type_, &orig.custom_types[custom_id]);

            for (content_path, _) in get_names_in(&orig.custom_types, &orig.custom_types[custom_id])
            {
                let (fold_point, normalized) = split_at_fold(*custom_id, content_path.clone());

                let mut wrapped_path = normalized.0.clone();
                wrapped_path.push_front(annot::Field::Custom(*custom_id));

                // Wire up directly
                expr_info.add_edge_to_local(
                    wrapped_path.clone(),
                    (*content, content_path.clone()),
                    Disj::True,
                );

                for ((other, other_path), cond) in &content_info.aliases[&content_path].aliases {
                    if other == content {
                        // Wire up transitive self edges (tricky)
                        let (other_fold_point, other_normalized) =
                            split_at_fold(*custom_id, other_path.clone());

                        if other_fold_point == fold_point {
                            let mut other_wrapped = other_normalized.0;
                            other_wrapped.push_back(annot::Field::Custom(*custom_id));

                            expr_info.add_self_edge(
                                wrapped_path.clone(),
                                other_wrapped,
                                cond.clone(),
                            );
                        } else {
                            // TODO: Are we absolutely certain that adding a cross-edge is *all* we
                            // need to do in this case?  Is it ever necessary to also add a normal
                            // edge here?

                            // "Cross-edge" between folded copies
                            expr_info.add_folded_alias(
                                &vector![annot::Field::Custom(*custom_id)],
                                NormPair::new(normalized.clone(), other_normalized.clone()),
                                cond.clone(),
                            );
                        }
                    }

                    // Wire up transitive external edges
                    expr_info.add_edge_to_local(
                        wrapped_path.clone(),
                        (*other, other_path.clone()),
                        cond.clone(),
                    );
                }
            }

            for (content_fold_point, _) in
                get_fold_points_in(&orig.custom_types, &orig.custom_types[custom_id])
            {
                let (_, normalized) = split_at_fold(*custom_id, content_fold_point.clone());

                let mut wrapped_path = normalized.0.clone();
                wrapped_path.push_front(annot::Field::Custom(*custom_id));

                for (pair, cond) in
                    &content_info.folded_aliases[&content_fold_point].inter_elem_aliases
                {
                    expr_info.add_folded_alias(&wrapped_path, pair.clone(), cond.clone());
                }
            }

            (annot::Expr::WrapCustom(*custom_id, *content), expr_info)
        }

        flat::Expr::UnwrapCustom(custom_id, wrapped) => {
            let mut expr_info = empty_info(&orig.custom_types, &orig.custom_types[custom_id]);

            let occurs = get_content_folded_occurrences(&orig.custom_types, *custom_id);

            let wrapped_info = &ctx[wrapped];

            for (wrapped_path, _) in
                get_names_in(&orig.custom_types, &anon::Type::Custom(*custom_id))
            {
                debug_assert_eq!(&wrapped_path[0], &annot::Field::Custom(*custom_id));
                let content_subpath = wrapped_path.clone().skip(1);

                for occur in &occurs {
                    let mut content_path = occur.clone();
                    content_path.append(content_subpath.clone());

                    // Wire up directly
                    expr_info.add_edge_to_local(
                        content_path.clone(),
                        (*wrapped, wrapped_path.clone()),
                        Disj::True,
                    );

                    for ((other, other_path), cond) in &wrapped_info.aliases[&wrapped_path].aliases
                    {
                        if other == wrapped {
                            debug_assert_eq!(&other_path[0], &annot::Field::Custom(*custom_id));
                            let other_content_subpath = other_path.clone().skip(1);

                            let mut other_content_path = occur.clone();
                            other_content_path.append(other_content_subpath.clone());

                            expr_info.add_self_edge(
                                content_path.clone(),
                                other_content_path,
                                cond.clone(),
                            );
                        }

                        expr_info.add_edge_to_local(
                            content_path.clone(),
                            (*other, other_path.clone()),
                            cond.clone(),
                        );
                    }
                }
            }

            // Unfurl folded edges
            for (pair, cond) in &wrapped_info.folded_aliases
                [&vector![annot::Field::Custom(*custom_id)]]
                .inter_elem_aliases
            {
                for (i, occur1) in occurs.iter().enumerate() {
                    for occur2 in &occurs[..i] {
                        let mut content_path1 = occur1.clone();
                        content_path1.append(pair.fst().0.clone());

                        let mut content_path2 = occur2.clone();
                        content_path2.append(pair.snd().0.clone());

                        expr_info.add_self_edge(content_path1, content_path2, cond.clone());
                    }
                }
            }

            // Copy all internal fold points
            for (content_path, _) in
                get_fold_points_in(&orig.custom_types, &orig.custom_types[custom_id])
            {
                let (_, wrapped_subpath) = split_at_fold(*custom_id, content_path.clone());

                let mut wrapped_path = wrapped_subpath.0;
                wrapped_path.push_front(annot::Field::Custom(*custom_id));

                expr_info.set_folded_aliases(
                    content_path,
                    wrapped_info.folded_aliases[&wrapped_path].clone(),
                );
            }

            (annot::Expr::UnwrapCustom(*custom_id, *wrapped), expr_info)
        }

        flat::Expr::ArithOp(op) => (annot::Expr::ArithOp(*op), ValInfo::new()),

        flat::Expr::ArrayOp(flat::ArrayOp::Item(item_type, array, index)) => {
            debug_assert_eq!(
                get_names_in(
                    &orig.custom_types,
                    &anon::Type::Array(Box::new(item_type.clone()))
                ),
                get_names_in(
                    &orig.custom_types,
                    &anon::Type::HoleArray(Box::new(item_type.clone()))
                )
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
                annot::Expr::ArrayOp(annot::ArrayOp::Item(
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

        flat::Expr::IOOp(flat::IOOp::Input) => (
            annot::Expr::IOOp(annot::IOOp::Input),
            empty_info(
                &orig.custom_types,
                &anon::Type::Array(Box::new(anon::Type::Num(first_ord::NumType::Byte))),
            ),
        ),

        flat::Expr::IOOp(flat::IOOp::Output(array)) => {
            let array_aliases = ctx[array].aliases[&Vector::new()].clone();

            (
                annot::Expr::IOOp(annot::IOOp::Output(array_aliases, *array)),
                ValInfo::new(),
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

fn get_aliasable_name_groups_in(
    type_defs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &anon::Type,
) -> Vec<Vec<annot::FieldPath>> {
    let mut paths_by_type = BTreeMap::<&anon::Type, Vec<annot::FieldPath>>::new();

    for (path, type_) in get_names_in(type_defs, type_) {
        let item_type = match type_ {
            anon::Type::Array(item_type) | anon::Type::HoleArray(item_type) => item_type,
            _ => unreachable!(),
        };

        paths_by_type.entry(item_type).or_default().push(path);
    }

    paths_by_type
        .into_iter()
        .map(|(_item_type, paths)| paths)
        .collect()
}

#[allow(unused_variables)]
fn annot_func(
    orig: &flat::Program,
    sigs: &SignatureAssumptions,
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
        .map(|(fold_point, folded_type)| {
            let mut folded_aliases = OrdMap::new();
            for paths in get_aliasable_name_groups_in(&orig.custom_types, folded_type) {
                for (i, path1) in paths.iter().enumerate() {
                    // Folded edges are symmetric, so we only need to insert each edge in one
                    // direction.  This means it's enough to wire each sub-path up to all the
                    // sub-paths appearing after it in the list (including itself).
                    for path2 in &paths[i..] {
                        let pair = NormPair::new(
                            annot::SubPath(path1.clone()),
                            annot::SubPath(path2.clone()),
                        );

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
    }
}

fn annot_scc_fixed_point(
    orig: &flat::Program,
    annotated: &IdVec<first_ord::CustomFuncId, Option<annot::FuncDef>>,
    scc: &[first_ord::CustomFuncId],
) -> BTreeMap<first_ord::CustomFuncId, annot::FuncDef> {
    let mut defs = scc
        .iter()
        .map(|&func| {
            (
                func,
                annot_func(
                    orig,
                    &SignatureAssumptions {
                        known_defs: annotated,
                        provisional_defs: None,
                    },
                    &orig.funcs[func],
                ),
            )
        })
        .collect::<BTreeMap<_, _>>();

    loop {
        let iterated_defs = scc
            .iter()
            .map(|&func| {
                (
                    func,
                    annot_func(
                        orig,
                        &SignatureAssumptions {
                            known_defs: annotated,
                            provisional_defs: Some(&defs),
                        },
                        &orig.funcs[func],
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();

        if scc
            .iter()
            .all(|func| iterated_defs[func].alias_sig == defs[func].alias_sig)
        {
            return iterated_defs;
        }

        defs = iterated_defs;
    }
}

// TODO: make these tests ignore order where it is irrelevant (e.g. edge lists)
#[cfg(test)]
mod test {
    use super::*;
    use im_rc::vector;
    use std::collections::BTreeSet;

    #[test]
    fn test_get_names_in() {
        fn set<T: Ord>(v: impl IntoIterator<Item = T>) -> BTreeSet<T> {
            use std::iter::FromIterator;
            BTreeSet::from_iter(v)
        }
        let with_single_recursive_type =
            IdVec::from_items(vec![anon::Type::Variants(IdVec::from_items(vec![
                anon::Type::Tuple(vec![
                    anon::Type::Array(Box::new(anon::Type::Num(first_ord::NumType::Byte))),
                    anon::Type::Custom(first_ord::CustomTypeId(0)),
                ]),
                anon::Type::Num(first_ord::NumType::Byte),
                anon::Type::HoleArray(Box::new(anon::Type::Num(first_ord::NumType::Byte))),
                anon::Type::Tuple(vec![]),
            ]))]);
        let mapping: Vec<(
            IdVec<first_ord::CustomTypeId, anon::Type>,
            anon::Type,
            BTreeSet<annot::FieldPath>,
        )> = vec![
            // Types without names:
            (
                IdVec::new(),
                anon::Type::Tuple(vec![
                    anon::Type::Num(first_ord::NumType::Byte),
                    anon::Type::Num(first_ord::NumType::Float),
                ]),
                set(vec![]),
            ),
            (
                IdVec::from_items(vec![anon::Type::Variants(IdVec::from_items(vec![
                    anon::Type::Num(first_ord::NumType::Byte),
                    anon::Type::Tuple(vec![]),
                ]))]),
                anon::Type::Tuple(vec![anon::Type::Custom(first_ord::CustomTypeId(0))]),
                set(vec![]),
            ),
            // Types with names, no typedefs:
            (
                IdVec::new(),
                anon::Type::Array(Box::new(anon::Type::Num(first_ord::NumType::Byte))),
                set(vec![vector![]]),
            ),
            (
                IdVec::new(),
                anon::Type::Array(Box::new(anon::Type::Array(Box::new(anon::Type::Num(
                    first_ord::NumType::Int,
                ))))),
                set(vec![vector![], vector![annot::Field::ArrayMembers]]),
            ),
            // Recursive types:
            (
                IdVec::new(),
                anon::Type::Tuple(vec![
                    anon::Type::Num(first_ord::NumType::Float),
                    anon::Type::Array(Box::new(anon::Type::Tuple(vec![
                        anon::Type::Array(Box::new(anon::Type::Bool)),
                        anon::Type::Num(first_ord::NumType::Byte),
                        anon::Type::HoleArray(Box::new(anon::Type::Bool)),
                    ]))),
                ]),
                set(vec![
                    vector![annot::Field::Field(1)],
                    vector![
                        annot::Field::Field(1),
                        annot::Field::ArrayMembers,
                        annot::Field::Field(0)
                    ],
                    vector![
                        annot::Field::Field(1),
                        annot::Field::ArrayMembers,
                        annot::Field::Field(2)
                    ],
                ]),
            ),
            (
                with_single_recursive_type.clone(),
                anon::Type::Custom(first_ord::CustomTypeId(0)),
                set(vec![
                    vector![
                        annot::Field::Custom(first_ord::CustomTypeId(0)),
                        annot::Field::Variant(first_ord::VariantId(0)),
                        annot::Field::Field(0)
                    ],
                    vector![
                        annot::Field::Custom(first_ord::CustomTypeId(0)),
                        annot::Field::Variant(first_ord::VariantId(2))
                    ],
                ]),
            ),
            (
                with_single_recursive_type.clone(),
                anon::Type::Array(Box::new(anon::Type::Custom(first_ord::CustomTypeId(0)))),
                set(vec![
                    vector![],
                    vector![
                        annot::Field::ArrayMembers,
                        annot::Field::Custom(first_ord::CustomTypeId(0)),
                        annot::Field::Variant(first_ord::VariantId(0)),
                        annot::Field::Field(0)
                    ],
                    vector![
                        annot::Field::ArrayMembers,
                        annot::Field::Custom(first_ord::CustomTypeId(0)),
                        annot::Field::Variant(first_ord::VariantId(2))
                    ],
                ]),
            ),
        ];
        for (typedefs, type_, expected_names) in mapping {
            assert_eq!(
                set(get_names_in(&typedefs, &type_)
                    .into_iter()
                    .map(|(name, _type)| name)),
                expected_names
            );
        }
    }
}
