use im_rc::{OrdMap, Vector};
use std::collections::{BTreeMap, BTreeSet};

use crate::data::alias_annot_ast as annot;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::graph::{self, Graph};
use crate::util::disjunction::Disj;
use crate::util::id_vec::IdVec;
use crate::util::norm_pair::NormPair;

fn annot_aliases(program: flat::Program) -> annot::Program {
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
fn get_names_in(
    type_defs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &anon::Type,
) -> Vec<annot::FieldPath> {
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
    fn add_names_from_type(
        type_defs: &IdVec<first_ord::CustomTypeId, anon::Type>,
        names: &mut Vec<annot::FieldPath>,
        typedefs_on_path: &mut BTreeSet<first_ord::CustomTypeId>,
        type_: &anon::Type,
        prefix: annot::FieldPath,
    ) {
        match type_ {
            anon::Type::Bool | anon::Type::Num(_) => {}
            anon::Type::Array(item_type) | anon::Type::HoleArray(item_type) => {
                // The array itself:
                names.push(prefix.clone());
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

fn get_occurrences_of(
    type_defs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    target: first_ord::CustomTypeId,
    type_: &anon::Type,
) -> Vec<annot::FieldPath> {
    let mut occurs = Vec::new();
    add_occus_from_type(
        type_defs,
        target,
        &mut occurs,
        &mut BTreeSet::new(),
        type_,
        &Vector::new(),
    );
    return occurs;

    fn add_occus_from_type(
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
                add_occus_from_type(
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
                    add_occus_from_type(
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
                    add_occus_from_type(
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
                        add_occus_from_type(
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

        pub fn create_folded_aliases(
            &mut self,
            fold_point: annot::FieldPath,
            folded_aliases: annot::FoldedAliases,
        ) {
            debug_assert!(
                !self.folded_aliases.contains_key(&fold_point),
                "Alias analysis attempted to create a fold point that already exists.  While is \
                 is in and of itself harmless, it probably indicates a logic error."
            );

            self.folded_aliases.insert(fold_point, folded_aliases);
        }

        //     fn copy_aliases_from(
        //         &mut self,
        //         self_path: &annot::FieldPath,
        //         local_path: &annot::FieldPath,
        //         local_id: flat::LocalId,
        //         local_info: &LocalInfo,
        //     ) {
        //         self.create_path(self_path.clone());

        //         // Inherit precision flag
        //         self.precisions[self_path] = local_info.precisions[local_path].clone();

        //         // Wire up transitive edges to self
        //         //
        //         // We are careful to do this before wiring up this path in the value and the local
        //         // one-to-one, to avoid creating a redundant reflexive edge.
        //         for other_self_path in self.rev_aliases_of(local_id, local_path) {
        //             self.add_self_edge(self_path.clone(), other_self_path);
        //         }

        //         // Wire up self and local name one-to-one
        //         self.add_local_edge(self_path.clone(), (local_id, local_path.clone()));

        //         // Wire up transitive edges to locals
        //         for (other_id, other_path) in &local_info.aliases[local_path] {
        //             self.add_local_edge(self_path.clone(), (*other_id, other_path.clone()));
        //         }
        //     }
        // }
    }
}

use val_info::ValInfo;

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

fn annot_expr(
    _orig: &flat::Program,
    _sigs: &SignatureAssumptions,
    _ctx: &OrdMap<flat::LocalId, LocalInfo>,
    _expr: &flat::Expr,
) -> (annot::Expr, ValInfo) {
    unimplemented!()
}

#[allow(unused_variables)]
fn annot_func(
    orig: &flat::Program,
    sigs: &SignatureAssumptions,
    func_def: &flat::FuncDef,
) -> annot::FuncDef {
    unimplemented!()
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
        fn set<T: Ord>(v: Vec<T>) -> BTreeSet<T> {
            use std::iter::FromIterator;
            BTreeSet::from_iter(v.into_iter())
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
            assert_eq!(set(get_names_in(&typedefs, &type_)), expected_names);
        }
    }
}
