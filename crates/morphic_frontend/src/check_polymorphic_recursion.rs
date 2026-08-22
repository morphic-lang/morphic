use crate::data::resolved_ast::{self as res, TypeParamId};
use crate::data::typed_ast as typed;
use crate::file_cache::FileCache;
use id_collections::IdVec;
use morphic_common::report_error::{locate_path, locate_span, Locate, Reportable};
use morphic_common::util::graph::{self, Graph};
use std::collections::BTreeMap;
use std::io;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    ValNonterminating { name: String },
    TypeNonterminating { name: String },
}

#[derive(Debug)]
pub struct Error(Locate<ErrorKind>);

impl Reportable for Error {
    fn report(&self, dest: &mut impl io::Write, files: &FileCache) -> io::Result<()> {
        self.0.report_with(dest, files, |err| {
            (
                "Unbounded Polymorphic Recursion",
                match err {
                    ErrorKind::ValNonterminating { name } => format!(
                        "The function `{}` requires unbounded polymorphic recursion.",
                        name
                    ),
                    ErrorKind::TypeNonterminating { name } => format!(
                        "The type `{}` requires unbounded polymorphic recursion.",
                        name
                    ),
                },
            )
        })
    }

    fn exit_status(&self) -> i32 {
        1
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Growth {
    Stable,
    Growing,
}

#[derive(Clone, Copy, Debug)]
struct ClassifiedEdge<N> {
    from: N,
    to: N,
    growth: Growth,
    span: Option<(usize, usize)>,
}

fn add_free_vars(ty: &res::Type, vars: &mut Vec<TypeParamId>) {
    match ty {
        &res::Type::Var(param) => vars.push(param),
        res::Type::App(_, args) => {
            for arg in args {
                add_free_vars(arg, vars);
            }
        }
        res::Type::Tuple(items) => {
            for item in items {
                add_free_vars(item, vars);
            }
        }
        res::Type::Func(_, arg, ret) => {
            add_free_vars(arg, vars);
            add_free_vars(ret, vars);
        }
    }
}

fn add_application_edges<Id: Copy>(
    source: Id,
    target: Id,
    args: &[res::Type],
    span: Option<(usize, usize)>,
    edges: &mut Vec<ClassifiedEdge<(Id, TypeParamId)>>,
) {
    // The j-th type argument in an application of `target` instantiates `target`'s j-th type
    // parameter, so each edge points at the corresponding parameter node of `target`.
    let mut vars = Vec::new();
    for (j, arg) in args.iter().enumerate() {
        match arg {
            &res::Type::Var(param) => edges.push(ClassifiedEdge {
                from: (source, param),
                to: (target, TypeParamId(j)),
                growth: Growth::Stable,
                span,
            }),
            _ => {
                vars.clear();
                add_free_vars(arg, &mut vars);
                for &param in &vars {
                    edges.push(ClassifiedEdge {
                        from: (source, param),
                        to: (target, TypeParamId(j)),
                        growth: Growth::Growing,
                        span,
                    });
                }
            }
        }
    }
}

fn add_global_calls<'a>(
    expr: &'a typed::Expr,
    span: Option<(usize, usize)>,
    calls: &mut Vec<(res::CustomGlobalId, &'a [res::Type], Option<(usize, usize)>)>,
) {
    match expr {
        typed::Expr::Global(res::GlobalId::Custom(id), args) => {
            calls.push((*id, args.as_slice(), span))
        }
        typed::Expr::Global(_, _) | typed::Expr::Local(_) => {}
        typed::Expr::Tuple(items) => {
            for item in items {
                add_global_calls(item, span, calls);
            }
        }
        typed::Expr::Lam(_, _, _, _, body, _) => add_global_calls(body, span, calls),
        typed::Expr::App(_, func, arg) => {
            add_global_calls(func, span, calls);
            add_global_calls(arg, span, calls);
        }
        typed::Expr::Match(discrim, cases, _) => {
            add_global_calls(discrim, span, calls);
            for (_, body) in cases {
                add_global_calls(body, span, calls);
            }
        }
        typed::Expr::LetMany(bindings, body) => {
            for (_, rhs) in bindings {
                add_global_calls(rhs, span, calls);
            }
            add_global_calls(body, span, calls);
        }
        typed::Expr::ArrayLit(_, items) => {
            for item in items {
                add_global_calls(item, span, calls);
            }
        }
        typed::Expr::ByteLit(_) | typed::Expr::IntLit(_) | typed::Expr::FloatLit(_) => {}
        &typed::Expr::Span(lo, hi, ref content) => add_global_calls(content, Some((lo, hi)), calls),
    }
}

fn add_type_applications<'a>(
    ty: &'a res::Type,
    apps: &mut Vec<(res::CustomTypeId, &'a [res::Type])>,
) {
    match ty {
        res::Type::Var(_) => {}
        res::Type::App(id, args) => {
            if let res::TypeId::Custom(custom) = id {
                apps.push((*custom, args.as_slice()));
            }
            for arg in args {
                add_type_applications(arg, apps);
            }
        }
        res::Type::Tuple(items) => {
            for item in items {
                add_type_applications(item, apps);
            }
        }
        res::Type::Func(_, arg, ret) => {
            add_type_applications(arg, apps);
            add_type_applications(ret, apps);
        }
    }
}

fn find_polymorphic_recursion<Id: Copy + Ord>(
    classified: Vec<ClassifiedEdge<(Id, TypeParamId)>>,
) -> Option<(Id, Option<(usize, usize)>)> {
    let mut flat_namespace: BTreeMap<(Id, TypeParamId), usize> = BTreeMap::new();
    let mut flat_name_of = |node: (Id, TypeParamId)| {
        let next = flat_namespace.len();
        *flat_namespace.entry(node).or_insert(next)
    };

    let flat: Vec<ClassifiedEdge<usize>> = classified
        .into_iter()
        .map(|edge| ClassifiedEdge {
            from: flat_name_of(edge.from),
            to: flat_name_of(edge.to),
            growth: edge.growth,
            span: edge.span,
        })
        .collect();

    let mut edges_out = vec![Vec::new(); flat_namespace.len()];
    for edge in &flat {
        edges_out[edge.from].push(edge.to);
    }
    let sccs = graph::strongly_connected(&Graph {
        edges_out: IdVec::from_vec(edges_out),
    });

    let scc_of: BTreeMap<usize, usize> = sccs
        .iter()
        .enumerate()
        .flat_map(|(scc_id, nodes)| nodes.iter().map(move |&node| (node, scc_id)))
        .collect();

    let node_of: BTreeMap<usize, Id> = flat_namespace
        .into_iter()
        .map(|(node, slot)| (slot, node.0))
        .collect();

    flat.into_iter()
        .find(|edge| edge.growth == Growth::Growing && scc_of[&edge.from] == scc_of[&edge.to])
        .map(|edge| (node_of[&edge.from], edge.span))
}

fn locate(kind: ErrorKind, file: &std::path::Path, span: Option<(usize, usize)>) -> Error {
    let mut located: Locate<ErrorKind> = kind.into();
    located = locate_path(file)(located);
    if let Some((lo, hi)) = span {
        located = locate_span(lo, hi)(located);
    }
    Error(located)
}

fn check_vals(
    mod_symbols: &IdVec<res::ModId, res::ModSymbols>,
    vals: &IdVec<res::CustomGlobalId, typed::ValDef>,
    val_symbols: &IdVec<res::CustomGlobalId, res::ValSymbols>,
) -> Result<(), Error> {
    let mut calls = Vec::new();
    let mut classified = Vec::new();
    for (val_id, def) in vals.iter() {
        calls.clear();
        add_global_calls(&def.body, None, &mut calls);
        for &(target, args, span) in &calls {
            add_application_edges(val_id, target, args, span, &mut classified);
        }
    }

    match find_polymorphic_recursion(classified) {
        Some((culprit, span)) => {
            let symbols = &val_symbols[culprit];
            Err(locate(
                ErrorKind::ValNonterminating {
                    name: symbols.val_name.0.clone(),
                },
                &mod_symbols[symbols.mod_].file,
                span,
            ))
        }
        None => Ok(()),
    }
}

fn check_types(
    mod_symbols: &IdVec<res::ModId, res::ModSymbols>,
    custom_types: &IdVec<res::CustomTypeId, res::TypeDef>,
    custom_type_symbols: &IdVec<res::CustomTypeId, res::TypeSymbols>,
) -> Result<(), Error> {
    let mut apps = Vec::new();
    let mut classified = Vec::new();
    for (type_id, typedef) in custom_types.iter() {
        for (variant_id, variant) in typedef.variants.iter() {
            if let Some(ty) = variant {
                let span = custom_type_symbols[type_id].variant_symbols[variant_id].span;
                apps.clear();
                add_type_applications(ty, &mut apps);
                for &(target, args) in &apps {
                    add_application_edges(type_id, target, args, Some(span), &mut classified);
                }
            }
        }
    }

    match find_polymorphic_recursion(classified) {
        Some((culprit, span)) => {
            let symbols = &custom_type_symbols[culprit];
            Err(locate(
                ErrorKind::TypeNonterminating {
                    name: symbols.type_name.0.clone(),
                },
                &mod_symbols[symbols.mod_].file,
                span,
            ))
        }
        None => Ok(()),
    }
}

pub fn check_polymorphic_recursion(program: &typed::Program) -> Result<(), Error> {
    check_types(
        &program.mod_symbols,
        &program.custom_types,
        &program.custom_type_symbols,
    )?;
    check_vals(&program.mod_symbols, &program.vals, &program.val_symbols)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::raw_ast as raw;
    use crate::data::resolved_ast::{
        CustomGlobalId, CustomTypeId, GlobalId, ModDeclLoc, ModId, ModSymbols, TypeDef, TypeId,
        TypeParamId, TypeScheme, TypeSymbols, ValSymbols, VariantSymbols,
    };
    use crate::data::typed_ast::{Expr, ValDef};
    use std::path::PathBuf;

    fn mod_symbols() -> IdVec<ModId, ModSymbols> {
        IdVec::from_vec(vec![ModSymbols {
            file: PathBuf::from("main.mor"),
            decl_loc: ModDeclLoc::Root,
        }])
    }

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

    fn type_symbols(name: &str, variant_spans: &[(usize, usize)]) -> TypeSymbols {
        TypeSymbols {
            mod_: ModId(0),
            type_name: raw::TypeName(name.to_string()),
            variant_symbols: IdVec::from_vec(
                variant_spans
                    .iter()
                    .map(|&span| VariantSymbols {
                        variant_name: raw::CtorName("Ctor".to_string()),
                        span,
                    })
                    .collect(),
            ),
        }
    }

    fn self_call(args: Vec<res::Type>) -> Expr {
        Expr::Global(GlobalId::Custom(CustomGlobalId(0)), IdVec::from_vec(args))
    }

    #[test]
    fn growing_self_recursive_value_is_rejected() {
        let vals = IdVec::from_vec(vec![val_def(
            1,
            Expr::Span(
                10,
                25,
                Box::new(self_call(vec![res::Type::Tuple(vec![
                    res::Type::Var(TypeParamId(0)),
                    res::Type::Var(TypeParamId(0)),
                ])])),
            ),
        )]);
        let val_symbols = IdVec::from_vec(vec![val_symbols("depth")]);

        let err = check_vals(&mod_symbols(), &vals, &val_symbols).unwrap_err();
        assert!(matches!(
            err.0.error,
            ErrorKind::ValNonterminating { ref name } if name == "depth"
        ));
        assert_eq!(err.0.path, Some(PathBuf::from("main.mor")));
        assert_eq!(err.0.span, Some((10, 25)));
    }

    #[test]
    fn ordinary_self_recursive_value_is_accepted() {
        let vals = IdVec::from_vec(vec![val_def(
            1,
            self_call(vec![res::Type::Var(TypeParamId(0))]),
        )]);
        let val_symbols = IdVec::from_vec(vec![val_symbols("len")]);

        check_vals(&mod_symbols(), &vals, &val_symbols).unwrap();
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
        let custom_type_symbols =
            IdVec::from_vec(vec![type_symbols("Nested", &[(5, 14), (20, 41)])]);

        let err = check_types(&mod_symbols(), &custom_types, &custom_type_symbols).unwrap_err();
        assert!(matches!(
            err.0.error,
            ErrorKind::TypeNonterminating { ref name } if name == "Nested"
        ));
        assert_eq!(err.0.path, Some(PathBuf::from("main.mor")));
        assert_eq!(err.0.span, Some((20, 41)));
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
        let custom_type_symbols = IdVec::from_vec(vec![
            type_symbols("Pair", &[(0, 10)]),
            type_symbols("Other", &[(15, 25)]),
        ]);

        check_types(&mod_symbols(), &custom_types, &custom_type_symbols).unwrap();
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
        let custom_type_symbols =
            IdVec::from_vec(vec![type_symbols("Nested", &[(5, 14), (20, 41)])]);

        let vals = IdVec::from_vec(vec![val_def(
            1,
            self_call(vec![res::Type::Tuple(vec![
                res::Type::Var(TypeParamId(0)),
                res::Type::Var(TypeParamId(0)),
            ])]),
        )]);
        let val_symbols = IdVec::from_vec(vec![val_symbols("depth")]);

        let program = typed::Program {
            mod_symbols: mod_symbols(),
            custom_types,
            custom_type_symbols,
            profile_points: IdVec::new(),
            vals,
            val_symbols,
            main: CustomGlobalId(0),
        };

        let err = check_polymorphic_recursion(&program).unwrap_err();
        assert!(matches!(
            err.0.error,
            ErrorKind::TypeNonterminating { ref name } if name == "Nested"
        ));
    }
}
