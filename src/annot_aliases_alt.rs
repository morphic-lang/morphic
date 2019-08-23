use im_rc::{OrdMap, Vector};
use std::collections::{BTreeMap, BTreeSet};

use crate::data::alias_annot_ast as annot;
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
    type_defs: &IdVec<first_ord::CustomTypeId, first_ord::TypeDef>,
    type_: &first_ord::Type,
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
        type_defs: &IdVec<first_ord::CustomTypeId, first_ord::TypeDef>,
        names: &mut Vec<annot::FieldPath>,
        typedefs_on_path: &mut BTreeSet<first_ord::CustomTypeId>,
        type_: &first_ord::Type,
        prefix: annot::FieldPath,
    ) {
        match type_ {
            first_ord::Type::Bool | first_ord::Type::Num(_) => {}
            first_ord::Type::Array(item_type) | first_ord::Type::HoleArray(item_type) => {
                // The array itself:
                names.push(prefix.clone());
                // The names in elements of the array:
                let mut new_prefix = prefix.clone();
                new_prefix.push_back(annot::Field::ArrayMembers);
                add_names_from_type(type_defs, names, typedefs_on_path, item_type, new_prefix);
            }
            first_ord::Type::Tuple(item_types) => {
                for (i, item_type) in item_types.iter().enumerate() {
                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(annot::Field::Field(i));
                    add_names_from_type(type_defs, names, typedefs_on_path, item_type, new_prefix);
                }
            }
            first_ord::Type::Custom(id) => {
                if !typedefs_on_path.contains(id) {
                    typedefs_on_path.insert(*id);
                    for (variant_id, variant) in &type_defs[id].variants {
                        if let Some(variant_type) = variant {
                            let mut variant_prefix = prefix.clone();
                            variant_prefix.push_back(annot::Field::Variant(*id, variant_id));
                            add_names_from_type(
                                type_defs,
                                names,
                                typedefs_on_path,
                                variant_type,
                                variant_prefix,
                            );
                        }
                    }
                    // Remove if we added it
                    typedefs_on_path.remove(id);
                }
            }
        }
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
        let with_single_recursive_type = IdVec::from_items(vec![first_ord::TypeDef {
            variants: IdVec::from_items(vec![
                Some(first_ord::Type::Tuple(vec![
                    first_ord::Type::Array(Box::new(first_ord::Type::Num(
                        first_ord::NumType::Byte,
                    ))),
                    first_ord::Type::Custom(first_ord::CustomTypeId(0)),
                ])),
                Some(first_ord::Type::Num(first_ord::NumType::Byte)),
                Some(first_ord::Type::HoleArray(Box::new(first_ord::Type::Num(
                    first_ord::NumType::Byte,
                )))),
                None,
            ]),
        }]);
        let mapping: Vec<(
            IdVec<first_ord::CustomTypeId, first_ord::TypeDef>,
            first_ord::Type,
            BTreeSet<annot::FieldPath>,
        )> = vec![
            // Types without names:
            (
                IdVec::new(),
                first_ord::Type::Tuple(vec![
                    first_ord::Type::Num(first_ord::NumType::Byte),
                    first_ord::Type::Num(first_ord::NumType::Float),
                ]),
                set(vec![]),
            ),
            (
                IdVec::from_items(vec![first_ord::TypeDef {
                    variants: IdVec::from_items(vec![
                        Some(first_ord::Type::Num(first_ord::NumType::Byte)),
                        None,
                    ]),
                }]),
                first_ord::Type::Tuple(vec![first_ord::Type::Custom(first_ord::CustomTypeId(0))]),
                set(vec![]),
            ),
            // Types with names, no typedefs:
            (
                IdVec::new(),
                first_ord::Type::Array(Box::new(first_ord::Type::Num(first_ord::NumType::Byte))),
                set(vec![vector![]]),
            ),
            (
                IdVec::new(),
                first_ord::Type::Array(Box::new(first_ord::Type::Array(Box::new(
                    first_ord::Type::Num(first_ord::NumType::Int),
                )))),
                set(vec![vector![], vector![annot::Field::ArrayMembers]]),
            ),
            // Recursive types:
            (
                IdVec::new(),
                first_ord::Type::Tuple(vec![
                    first_ord::Type::Num(first_ord::NumType::Float),
                    first_ord::Type::Array(Box::new(first_ord::Type::Tuple(vec![
                        first_ord::Type::Array(Box::new(first_ord::Type::Bool)),
                        first_ord::Type::Num(first_ord::NumType::Byte),
                        first_ord::Type::HoleArray(Box::new(first_ord::Type::Bool)),
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
                first_ord::Type::Custom(first_ord::CustomTypeId(0)),
                set(vec![
                    vector![
                        annot::Field::Variant(first_ord::CustomTypeId(0), first_ord::VariantId(0)),
                        annot::Field::Field(0)
                    ],
                    vector![annot::Field::Variant(
                        first_ord::CustomTypeId(0),
                        first_ord::VariantId(2)
                    )],
                ]),
            ),
            (
                with_single_recursive_type.clone(),
                first_ord::Type::Array(Box::new(first_ord::Type::Custom(first_ord::CustomTypeId(
                    0,
                )))),
                set(vec![
                    vector![],
                    vector![
                        annot::Field::ArrayMembers,
                        annot::Field::Variant(first_ord::CustomTypeId(0), first_ord::VariantId(0)),
                        annot::Field::Field(0)
                    ],
                    vector![
                        annot::Field::ArrayMembers,
                        annot::Field::Variant(first_ord::CustomTypeId(0), first_ord::VariantId(2))
                    ],
                ]),
            ),
        ];
        for (typedefs, type_, expected_names) in mapping {
            assert_eq!(set(get_names_in(&typedefs, &type_)), expected_names);
        }
    }
}
