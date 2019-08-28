use im_rc::{OrdMap, OrdSet, Vector};
use std::collections::{BTreeMap, BTreeSet};

use crate::data::alias_annot_ast as annot;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::graph::{self, Graph};
use crate::util::id_vec::IdVec;

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
    fn sig_of(
        &self,
        func: &first_ord::CustomFuncId,
    ) -> OrdMap<annot::RetName, annot::ReturnAliases> {
        if let Some(func_def) = &self.known_defs[func] {
            OrdMap::clone(&func_def.ret_field_aliases)
        } else if let Some(provisional_defs) = &self.provisional_defs {
            OrdMap::clone(&provisional_defs[func].ret_field_aliases)
        } else {
            OrdMap::new()
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

#[derive(Clone, Debug)]
struct LocalInfo {
    type_: anon::Type,
    aliases: OrdMap<annot::FieldPath, OrdSet<(flat::LocalId, annot::FieldPath)>>,
    precisions: OrdMap<annot::FieldPath, annot::Precision>,
}

// Aliasing information for an unnamed value
#[derive(Clone, Debug)]
struct ValInfo {
    aliases: OrdMap<annot::FieldPath, OrdSet<(flat::LocalId, annot::FieldPath)>>,

    // Invariant: `rev_aliases` should store exactly the same information as `aliases`, only with
    // the edges represented as references going the opposite direction.  This is useful for reverse
    // lookups.
    rev_aliases: OrdMap<flat::LocalId, OrdMap<annot::FieldPath, OrdSet<annot::FieldPath>>>,

    // Invariant: edges in this graph should be symmetric (if there is an edge a -> b, there should
    // also be an edge b -> a).
    self_aliases: OrdMap<annot::FieldPath, OrdSet<annot::FieldPath>>,

    precisions: OrdMap<annot::FieldPath, annot::Precision>,
}

impl ValInfo {
    fn new() -> Self {
        ValInfo {
            aliases: OrdMap::new(),
            rev_aliases: OrdMap::new(),
            self_aliases: OrdMap::new(),
            precisions: OrdMap::new(),
        }
    }

    fn create_path(&mut self, path: annot::FieldPath) {
        debug_assert!(
            !self.aliases.contains_key(&path),
            "Alias analysis attempted to create a name that already exists.  While this is in and \
             of itself harmless, it probably indicates a logic error."
        );

        self.aliases.insert(path.clone(), OrdSet::new());
        self.self_aliases.insert(path.clone(), OrdSet::new());
        self.precisions
            .insert(path, annot::Precision::ImpreciseIfAny(OrdSet::new()));
    }

    #[inline]
    fn assert_path(&self, path: &annot::FieldPath) {
        debug_assert!(self.aliases.contains_key(path));
        debug_assert!(self.self_aliases.contains_key(path));
        debug_assert!(self.precisions.contains_key(path));
    }

    fn add_local_edge(
        &mut self,
        self_path: annot::FieldPath,
        local_name: (flat::LocalId, annot::FieldPath),
    ) {
        self.assert_path(&self_path);

        debug_assert!(
            !self.aliases[&self_path].contains(&local_name),
            "Alias analysis attempted to create an edge that already exists.  While this is in and \
            of itself harmless, it probably indicates a logic error."
        );

        self.aliases[&self_path].insert(local_name.clone());

        self.rev_aliases
            .entry(local_name.0)
            .or_default()
            .entry(local_name.1)
            .or_default()
            .insert(self_path);
    }

    fn add_self_edge(&mut self, path1: annot::FieldPath, path2: annot::FieldPath) {
        self.assert_path(&path1);
        self.assert_path(&path2);

        debug_assert_ne!(
            &path1, &path2,
            "The 'aliases' relation is reflexive by definition, so we should never need to \
             explicitly connect a name to itself."
        );

        debug_assert!(
            !self.self_aliases[&path1].contains(&path2),
            "Alias analysis attempted to create a self-edge that already exists.  While this is in \
             and of itself harmless, it probably indicates a logic error."
        );

        self.self_aliases[&path1].insert(path2.clone());
        self.self_aliases[&path2].insert(path1);
    }

    fn rev_aliases_of(
        &self,
        local_id: flat::LocalId,
        local_path: &annot::FieldPath,
    ) -> OrdSet<annot::FieldPath> {
        if let Some(rev_aliases_for_local) = self.rev_aliases.get(&local_id) {
            if let Some(rev_aliases_for_path) = rev_aliases_for_local.get(local_path) {
                return rev_aliases_for_path.clone();
            }
        }
        OrdSet::new()
    }
}

fn annot_expr(
    orig: &flat::Program,
    _sigs: &SignatureAssumptions,
    ctx: &OrdMap<flat::LocalId, LocalInfo>,
    expr: &flat::Expr,
) -> (annot::Expr, ValInfo) {
    match expr {
        flat::Expr::ArithOp(op) => (annot::Expr::ArithOp(*op), ValInfo::new()),

        flat::Expr::ArrayOp(_) => unimplemented!(),

        flat::Expr::IOOp(_) => unimplemented!(),

        flat::Expr::Local(local_id) => {
            let local_info = &ctx[local_id];

            let mut val_info = ValInfo::new();

            for path in get_names_in(&orig.custom_types, &local_info.type_) {
                val_info.create_path(path.clone());

                // Inherit precision flag
                val_info.precisions[&path] = local_info.precisions[&path].clone();

                // Wire up transitive edges to self
                //
                // We are careful to do this before wiring up this path in the value and the local
                // one-to-one, to avoid creating a redundant reflexive edge.
                for other_self_path in val_info.rev_aliases_of(*local_id, &path) {
                    val_info.add_self_edge(path.clone(), other_self_path);
                }

                // Wire up old and new names one-to-one
                val_info.add_local_edge(path.clone(), (*local_id, path.clone()));

                // Wire up transitive edges to locals
                for (other_id, other_path) in &local_info.aliases[&path] {
                    val_info.add_local_edge(path.clone(), (*other_id, other_path.clone()));
                }
            }

            (annot::Expr::Local(*local_id), val_info)
        }

        flat::Expr::Tuple(items) => {
            let mut val_info = ValInfo::new();

            for (idx, item) in items.iter().enumerate() {
                let item_info = &ctx[item];

                for item_path in get_names_in(&orig.custom_types, &item_info.type_) {
                    let mut tuple_path = item_path.clone();
                    tuple_path.push_front(annot::Field::Field(idx));

                    val_info.create_path(tuple_path.clone());

                    // Inherit precision flag
                    val_info.precisions[&tuple_path] = item_info.precisions[&item_path].clone();

                    // Wire up transitive edges to other fields of the tuple currently under
                    // construction.
                    //
                    // We are careful to do this before wiring up this path in the item and in the
                    // tuple one-to-one, to avoid creating a redundant reflexive edge.
                    for other_tuple_path in val_info.rev_aliases_of(*item, &item_path) {
                        val_info.add_self_edge(tuple_path.clone(), other_tuple_path);
                    }

                    // Wire up item and tuple names one-to-one
                    val_info.add_local_edge(tuple_path.clone(), (*item, item_path.clone()));

                    // Wire up transitive edges to locals
                    for (other_id, other_path) in &item_info.aliases[&item_path] {
                        val_info
                            .add_local_edge(tuple_path.clone(), (*other_id, other_path.clone()));
                    }
                }
            }

            (annot::Expr::Tuple(items.clone()), val_info)
        }

        flat::Expr::TupleField(tuple, idx) => {
            let tuple_info = &ctx[tuple];

            let item_type = if let anon::Type::Tuple(item_types) = &tuple_info.type_ {
                &item_types[*idx]
            } else {
                unreachable!()
            };

            let mut val_info = ValInfo::new();

            for item_path in get_names_in(&orig.custom_types, item_type) {
                val_info.create_path(item_path.clone());

                let mut tuple_path = item_path.clone();
                tuple_path.push_front(annot::Field::Field(*idx));

                // Inherit precision flag
                val_info.precisions[&item_path] = tuple_info.precisions[&tuple_path].clone();

                // Wire up transitive edges to self
                //
                // We are careful to do this before wiring up this path in the item and in the tuple
                // one-to-one, to avoid creating a redundant reflexive edge.
                for other_self_path in val_info.rev_aliases_of(*tuple, &tuple_path) {
                    val_info.add_self_edge(item_path.clone(), other_self_path);
                }

                // Wire up tuple and item names one-to-one
                val_info.add_local_edge(item_path.clone(), (*tuple, tuple_path.clone()));

                // Wire up transitive edges to locals
                for (other_id, other_path) in &tuple_info.aliases[&tuple_path] {
                    val_info.add_local_edge(item_path.clone(), (*other_id, other_path.clone()));
                }
            }

            (annot::Expr::TupleField(*tuple, *idx), val_info)
        }

        _ => unimplemented!(),
    }
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
            .all(|func| iterated_defs[func].ret_field_aliases == defs[func].ret_field_aliases)
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
