use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use id_collections::IdVec;
use morphic_common::util::graph::{self, Graph};
use std::collections::HashMap;
use thiserror::Error;

#[derive(Clone, Debug, Error)]
pub enum Error {
    #[error("the function `{name}` requires unbounded polymorphic recursion")]
    ValNonterminating { name: String },
    #[error("the type `{name}` requires unbounded polymorphic recursion")]
    TypeNonterminating { name: String },
}

type Node<Id> = (Id, usize);
type Edge<Id> = (Node<Id>, Node<Id>);

fn free_vars(ty: &res::Type) -> Vec<usize> {
    match ty {
        &res::Type::Var(res::TypeParamId(i)) => vec![i],
        res::Type::App(_, args) => args.iter().flat_map(free_vars).collect(),
        res::Type::Tuple(items) => items.iter().flat_map(free_vars).collect(),
        res::Type::Func(_, arg, ret) => {
            free_vars(arg).into_iter().chain(free_vars(ret)).collect()
        }
    }
}

fn application_edges<Id: Copy>(source: Id, target: Id, args: &[res::Type]) -> Vec<(Edge<Id>, bool)> {
    args.iter()
        .enumerate()
        .flat_map(|(j, arg)| match arg {
            &res::Type::Var(res::TypeParamId(i)) => vec![(((source, i), (target, j)), false)],
            _ => free_vars(arg)
                .into_iter()
                .map(|i| (((source, i), (target, j)), true))
                .collect(),
        })
        .collect()
}

fn collect_global_calls(expr: &typed::Expr) -> Vec<(res::CustomGlobalId, &[res::Type])> {
    match expr {
        typed::Expr::Global(res::GlobalId::Custom(id), args) => vec![(*id, args.as_slice())],
        typed::Expr::Global(_, _) | typed::Expr::Local(_) => Vec::new(),
        typed::Expr::Tuple(items) => items.iter().flat_map(collect_global_calls).collect(),
        typed::Expr::Lam(_, _, _, _, body, _) => collect_global_calls(body),
        typed::Expr::App(_, func, arg) => collect_global_calls(func)
            .into_iter()
            .chain(collect_global_calls(arg))
            .collect(),
        typed::Expr::Match(discrim, cases, _) => collect_global_calls(discrim)
            .into_iter()
            .chain(cases.iter().flat_map(|(_, body)| collect_global_calls(body)))
            .collect(),
        typed::Expr::LetMany(bindings, body) => bindings
            .iter()
            .flat_map(|(_, rhs)| collect_global_calls(rhs))
            .chain(collect_global_calls(body))
            .collect(),
        typed::Expr::ArrayLit(_, items) => items.iter().flat_map(collect_global_calls).collect(),
        typed::Expr::ByteLit(_) | typed::Expr::IntLit(_) | typed::Expr::FloatLit(_) => Vec::new(),
        typed::Expr::Span(_, _, content) => collect_global_calls(content),
    }
}

fn collect_type_applications(ty: &res::Type) -> Vec<(res::CustomTypeId, &[res::Type])> {
    match ty {
        res::Type::Var(_) => Vec::new(),
        res::Type::App(res::TypeId::Custom(id), args) => std::iter::once((*id, args.as_slice()))
            .chain(args.iter().flat_map(collect_type_applications))
            .collect(),
        res::Type::App(_, args) => args.iter().flat_map(collect_type_applications).collect(),
        res::Type::Tuple(items) => items.iter().flat_map(collect_type_applications).collect(),
        res::Type::Func(_, arg, ret) => collect_type_applications(arg)
            .into_iter()
            .chain(collect_type_applications(ret))
            .collect(),
    }
}

fn find_polymorphic_recursion<Id: Copy + Eq + std::hash::Hash>(
    classified: Vec<(Edge<Id>, bool)>,
) -> Option<Id> {
    let mut slots = HashMap::new();
    let mut slot_of = |node: Node<Id>| {
        let next = slots.len();
        *slots.entry(node).or_insert(next)
    };

    let flat: Vec<(usize, usize, bool)> = classified
        .into_iter()
        .map(|((from, to), growing)| (slot_of(from), slot_of(to), growing))
        .collect();

    let mut edges_out = vec![Vec::new(); slots.len()];
    for &(from, to, _) in &flat {
        edges_out[from].push(to);
    }
    let sccs = graph::strongly_connected(&Graph {
        edges_out: IdVec::from_vec(edges_out),
    });

    let scc_of: HashMap<usize, usize> = sccs
        .iter()
        .enumerate()
        .flat_map(|(scc_id, nodes)| nodes.iter().map(move |&node| (node, scc_id)))
        .collect();

    let node_of: HashMap<usize, Id> = slots.into_iter().map(|(node, slot)| (slot, node.0)).collect();

    flat.into_iter()
        .find(|&(from, to, growing)| growing && scc_of[&from] == scc_of[&to])
        .map(|(from, _, _)| node_of[&from])
}

fn check_vals(
    vals: &IdVec<res::CustomGlobalId, typed::ValDef>,
    val_symbols: &IdVec<res::CustomGlobalId, res::ValSymbols>,
) -> Result<(), Error> {
    let classified = vals
        .iter()
        .flat_map(|(val_id, def)| {
            collect_global_calls(&def.body)
                .into_iter()
                .flat_map(move |(target, args)| application_edges(val_id, target, args))
        })
        .collect();

    match find_polymorphic_recursion(classified) {
        Some(culprit) => Err(Error::ValNonterminating {
            name: val_symbols[culprit].val_name.0.clone(),
        }),
        None => Ok(()),
    }
}

fn check_types(
    custom_types: &IdVec<res::CustomTypeId, res::TypeDef>,
    custom_type_symbols: &IdVec<res::CustomTypeId, res::TypeSymbols>,
) -> Result<(), Error> {
    let classified = custom_types
        .iter()
        .flat_map(|(type_id, typedef)| {
            typedef.variants.values().flatten().flat_map(move |ty| {
                collect_type_applications(ty)
                    .into_iter()
                    .flat_map(move |(target, args)| application_edges(type_id, target, args))
            })
        })
        .collect();

    match find_polymorphic_recursion(classified) {
        Some(culprit) => Err(Error::TypeNonterminating {
            name: custom_type_symbols[culprit].type_name.0.clone(),
        }),
        None => Ok(()),
    }
}

pub fn check_polymorphic_recursion(program: &typed::Program) -> Result<(), Error> {
    check_types(&program.custom_types, &program.custom_type_symbols)?;
    check_vals(&program.vals, &program.val_symbols)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::raw_ast as raw;
    use crate::data::resolved_ast::{
        CustomGlobalId, CustomTypeId, GlobalId, ModId, TypeDef, TypeId, TypeParamId, TypeScheme,
        TypeSymbols, ValSymbols, VariantSymbols,
    };
    use crate::data::typed_ast::{Expr, ValDef};

    fn val_def(num_params: usize, body: Expr) -> ValDef {
        ValDef {
            scheme: TypeScheme {
                num_params,
                body: res::Type::Tuple(vec![]),
            },
            body,
        }
    }

    fn val_symbols(name: &str) -> ValSymbols {
        ValSymbols {
            mod_: ModId(0),
            type_param_names: IdVec::new(),
            val_name: raw::ValName(name.to_string()),
        }
    }

    fn type_symbols(name: &str, num_variants: usize) -> TypeSymbols {
        TypeSymbols {
            mod_: ModId(0),
            type_name: raw::TypeName(name.to_string()),
            variant_symbols: IdVec::from_vec(
                (0..num_variants)
                    .map(|_| VariantSymbols {
                        variant_name: raw::CtorName("Ctor".to_string()),
                    })
                    .collect(),
            ),
        }
    }

    fn self_call(args: Vec<res::Type>) -> Expr {
        Expr::Global(
            GlobalId::Custom(CustomGlobalId(0)),
            IdVec::from_vec(args),
        )
    }

    #[test]
    fn growing_self_recursive_value_is_rejected() {
        let vals = IdVec::from_vec(vec![val_def(
            1,
            self_call(vec![res::Type::Tuple(vec![
                res::Type::Var(TypeParamId(0)),
                res::Type::Var(TypeParamId(0)),
            ])]),
        )]);
        let val_symbols = IdVec::from_vec(vec![val_symbols("depth")]);

        let err = check_vals(&vals, &val_symbols).unwrap_err();
        assert!(matches!(err, Error::ValNonterminating { name } if name == "depth"));
    }

    #[test]
    fn ordinary_self_recursive_value_is_accepted() {
        let vals = IdVec::from_vec(vec![val_def(
            1,
            self_call(vec![res::Type::Var(TypeParamId(0))]),
        )]);
        let val_symbols = IdVec::from_vec(vec![val_symbols("len")]);

        check_vals(&vals, &val_symbols).unwrap();
    }

    #[test]
    fn growing_recursive_type_is_rejected() {
        let custom_types = IdVec::from_vec(vec![TypeDef {
            num_params: 1,
            variants: IdVec::from_vec(vec![
                Some(res::Type::Var(TypeParamId(0))),
                Some(res::Type::App(
                    TypeId::Custom(CustomTypeId(0)),
                    vec![res::Type::Tuple(vec![
                        res::Type::Var(TypeParamId(0)),
                        res::Type::Var(TypeParamId(0)),
                    ])],
                )),
            ]),
        }]);
        let custom_type_symbols = IdVec::from_vec(vec![type_symbols("Nested", 2)]);

        let err = check_types(&custom_types, &custom_type_symbols).unwrap_err();
        assert!(matches!(err, Error::TypeNonterminating { name } if name == "Nested"));
    }

    #[test]
    fn mutually_recursive_type_parameter_swap_is_accepted() {
        let pair_id = CustomTypeId(0);
        let other_id = CustomTypeId(1);

        let custom_types = IdVec::from_vec(vec![
            TypeDef {
                num_params: 2,
                variants: IdVec::from_vec(vec![Some(res::Type::App(
                    TypeId::Custom(other_id),
                    vec![
                        res::Type::Var(TypeParamId(1)),
                        res::Type::Var(TypeParamId(0)),
                    ],
                ))]),
            },
            TypeDef {
                num_params: 2,
                variants: IdVec::from_vec(vec![Some(res::Type::App(
                    TypeId::Custom(pair_id),
                    vec![
                        res::Type::Var(TypeParamId(1)),
                        res::Type::Var(TypeParamId(0)),
                    ],
                ))]),
            },
        ]);
        let custom_type_symbols =
            IdVec::from_vec(vec![type_symbols("Pair", 1), type_symbols("Other", 1)]);

        check_types(&custom_types, &custom_type_symbols).unwrap();
    }

    #[test]
    fn a_growing_type_is_reported_over_the_function_consuming_it() {
        let nested_id = CustomTypeId(0);

        let custom_types = IdVec::from_vec(vec![TypeDef {
            num_params: 1,
            variants: IdVec::from_vec(vec![
                Some(res::Type::Var(TypeParamId(0))),
                Some(res::Type::App(
                    TypeId::Custom(nested_id),
                    vec![res::Type::Tuple(vec![
                        res::Type::Var(TypeParamId(0)),
                        res::Type::Var(TypeParamId(0)),
                    ])],
                )),
            ]),
        }]);
        let custom_type_symbols = IdVec::from_vec(vec![type_symbols("Nested", 2)]);

        let vals = IdVec::from_vec(vec![val_def(
            1,
            self_call(vec![res::Type::Tuple(vec![
                res::Type::Var(TypeParamId(0)),
                res::Type::Var(TypeParamId(0)),
            ])]),
        )]);
        let val_symbols = IdVec::from_vec(vec![val_symbols("depth")]);

        let program = typed::Program {
            mod_symbols: IdVec::new(),
            custom_types,
            custom_type_symbols,
            profile_points: IdVec::new(),
            vals,
            val_symbols,
            main: CustomGlobalId(0),
        };

        let err = check_polymorphic_recursion(&program).unwrap_err();
        assert!(matches!(err, Error::TypeNonterminating { name } if name == "Nested"));
    }
}
