use crate::data::elaborated_ast as elab;
use crate::data::resolved_ast::{self as res, TraitConstrId, TypeParamId};
use crate::data::solved_ast as solved;
use crate::file_cache::FileCache;
use id_collections::IdVec;
use morphic_common::report_error::{locate_path, locate_span, ColorMode, Locate, Reportable};
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
    fn report(
        &self,
        dest: &mut impl io::Write,
        files: &FileCache,
        color: ColorMode,
    ) -> io::Result<()> {
        self.0.report_with(dest, files, color, |err| {
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

/// One position through which an instantiation flows: a type parameter, or a trait constraint,
/// whose derivation is passed along just like a type argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Slot {
    Param(TypeParamId),
    Constr(TraitConstrId),
}

#[derive(Clone, Copy, Debug)]
struct ClassifiedEdge<N> {
    from: N,
    to: N,
    growth: Growth,
    span: Option<(usize, usize)>,
}

/// The type parameters occurring in a type.  A constrained type's evidence mentions no parameter
/// beyond those in its arguments, so it is not looked into.
fn add_free_vars(ty: &solved::Type, vars: &mut Vec<TypeParamId>) {
    match ty {
        solved::Type::App(head, args) => {
            if let &res::TypeHead::Var(param) = head {
                vars.push(param);
            }
            for arg in args {
                add_free_vars(arg, vars);
            }
        }
        solved::Type::Constrained(_, args, _) => {
            for arg in args {
                add_free_vars(arg, vars);
            }
        }
        solved::Type::Tuple(items) => {
            for item in items {
                add_free_vars(item, vars);
            }
        }
        solved::Type::Func(_, arg, ret) => {
            add_free_vars(arg, vars);
            add_free_vars(ret, vars);
        }
    }
}

/// The arguments of a type application, each paired with the parameter of the head it
/// instantiates.
fn positional_args(args: &[solved::Type]) -> impl Iterator<Item = (TypeParamId, &solved::Type)> {
    args.iter()
        .enumerate()
        .map(|(index, arg)| (TypeParamId(index), arg))
}

/// Each of `args` instantiates the parameter of `target` it is paired with, so each edge points
/// at that parameter's slot.
fn add_application_edges<'a, Id: Copy>(
    source: Id,
    target: Id,
    args: impl IntoIterator<Item = (TypeParamId, &'a solved::Type)>,
    span: Option<(usize, usize)>,
    edges: &mut Vec<ClassifiedEdge<(Id, Slot)>>,
) {
    let mut vars = Vec::new();
    for (param, arg) in args {
        let to = (target, Slot::Param(param));
        match arg {
            // A bare parameter is passed along unchanged.  A parameter applied to arguments, like
            // any other compound type, is growing.
            solved::Type::App(res::TypeHead::Var(param), args) if args.is_empty() => {
                edges.push(ClassifiedEdge {
                    from: (source, Slot::Param(*param)),
                    to,
                    growth: Growth::Stable,
                    span,
                })
            }
            _ => {
                vars.clear();
                add_free_vars(arg, &mut vars);
                for &param in &vars {
                    edges.push(ClassifiedEdge {
                        from: (source, Slot::Param(param)),
                        to,
                        growth: Growth::Growing,
                        span,
                    });
                }
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum IsNested {
    Nested,
    NotNested,
}

/// The givens a derivation is built from.  A given passed along as it is stays stable; one buried
/// inside an impl derivation is being wrapped in a bigger derivation, which under the Paterson
/// conditions means a bigger type, so it is growing.
fn add_given_uses(
    deriv: &solved::Derivation,
    nested: IsNested,
    uses: &mut Vec<(TraitConstrId, Growth)>,
) {
    match deriv {
        &solved::Derivation::Given(constr) => {
            let growth = match nested {
                IsNested::Nested => Growth::Growing,
                IsNested::NotNested => Growth::Stable,
            };
            uses.push((constr, growth));
        }
        solved::Derivation::Super(inner, _) => add_given_uses(inner, nested, uses),
        solved::Derivation::Impl(_, _, subs) => {
            for (_, sub) in subs {
                add_given_uses(sub, IsNested::Nested, uses);
            }
        }
    }
}

/// Edges from the givens of `source` that flow, through `deriv`, into the constraint slot `to`.
fn add_constraint_edges<Id: Copy>(
    source: Id,
    deriv: &solved::Derivation,
    to: (Id, Slot),
    span: Option<(usize, usize)>,
    edges: &mut Vec<ClassifiedEdge<(Id, Slot)>>,
) {
    let mut uses = Vec::new();
    add_given_uses(deriv, IsNested::NotNested, &mut uses);
    for (constr, growth) in uses {
        edges.push(ClassifiedEdge {
            from: (source, Slot::Constr(constr)),
            to,
            growth,
            span,
        });
    }
}

/// The given a derivation projects from, if it is not built from an impl.
fn root_given(deriv: &solved::Derivation) -> Option<TraitConstrId> {
    match deriv {
        &solved::Derivation::Given(constr) => Some(constr),
        solved::Derivation::Super(inner, _) => root_given(inner),
        solved::Derivation::Impl(_, _, _) => None,
    }
}

/// The impl a derivation is built from, if that is known statically.  A superclass projected out
/// of an impl derivation is only resolved to an impl during monomorphization.
fn root_impl(deriv: &solved::Derivation) -> Option<res::ImplId> {
    match deriv {
        &solved::Derivation::Impl(id, _, _) => Some(id),
        solved::Derivation::Given(_) | solved::Derivation::Super(_, _) => None,
    }
}

enum Call<'a> {
    Global {
        callee: res::CustomGlobalId,
        args: &'a IdVec<TypeParamId, solved::Type>,
        derivs: &'a IdVec<TraitConstrId, solved::Derivation>,
        span: Option<(usize, usize)>,
    },
    TraitFunc {
        trait_: res::TraitId,
        func: res::TraitFuncId,
        inst: &'a elab::TraitFuncInst<solved::Derivation>,
        span: Option<(usize, usize)>,
    },
}

fn add_global_calls<'a>(
    expr: &'a solved::Expr,
    span: Option<(usize, usize)>,
    calls: &mut Vec<Call<'a>>,
) {
    match expr {
        solved::Expr::Global(res::GlobalId::Custom(callee), args, derivs) => {
            calls.push(Call::Global {
                callee: *callee,
                args,
                derivs,
                span,
            })
        }
        solved::Expr::TraitFunc(trait_, func, inst) => calls.push(Call::TraitFunc {
            trait_: *trait_,
            func: *func,
            inst,
            span,
        }),
        solved::Expr::Global(_, _, _) | solved::Expr::Local(_) => {}
        solved::Expr::Tuple(items) => {
            for item in items {
                add_global_calls(item, span, calls);
            }
        }
        solved::Expr::Lam(_, _, _, _, body, _) => add_global_calls(body, span, calls),
        solved::Expr::App(_, func, arg) => {
            add_global_calls(func, span, calls);
            add_global_calls(arg, span, calls);
        }
        solved::Expr::Match(discrim, cases, _) => {
            add_global_calls(discrim, span, calls);
            for (_, body) in cases {
                add_global_calls(body, span, calls);
            }
        }
        solved::Expr::LetMany(bindings, body) => {
            for (_, rhs) in bindings {
                add_global_calls(rhs, span, calls);
            }
            add_global_calls(body, span, calls);
        }
        solved::Expr::ArrayLit(_, items) => {
            for item in items {
                add_global_calls(item, span, calls);
            }
        }
        solved::Expr::ByteLit(_) | solved::Expr::IntLit(_) | solved::Expr::FloatLit(_) => {}
        &solved::Expr::Span(lo, hi, ref content) => {
            add_global_calls(content, Some((lo, hi)), calls)
        }
    }
}

fn add_type_applications<'a>(
    ty: &'a solved::Type,
    apps: &mut Vec<(res::CustomTypeId, &'a [solved::Type])>,
) {
    match ty {
        solved::Type::App(head, args) => {
            if let res::TypeHead::Ctor(res::TypeId::Custom(custom)) = head {
                apps.push((*custom, args.as_slice()));
            }
            for arg in args {
                add_type_applications(arg, apps);
            }
        }
        solved::Type::Constrained(custom, args, _) => {
            apps.push((*custom, args.as_slice()));
            for arg in args {
                add_type_applications(arg, apps);
            }
        }
        solved::Type::Tuple(items) => {
            for item in items {
                add_type_applications(item, apps);
            }
        }
        solved::Type::Func(_, arg, ret) => {
            add_type_applications(arg, apps);
            add_type_applications(ret, apps);
        }
    }
}

fn find_polymorphic_recursion<Id: Copy + Ord>(
    classified: Vec<ClassifiedEdge<(Id, Slot)>>,
) -> Option<(Id, Option<(usize, usize)>)> {
    let mut flat_namespace: BTreeMap<(Id, Slot), usize> = BTreeMap::new();
    let mut flat_name_of = |node: (Id, Slot)| {
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

/// Edges for every impl derivation appearing anywhere in `deriv`: instantiating an impl at some
/// type arguments and sub-derivations may instantiate any of its funcs at them.
fn add_impl_instantiation_edges(
    source: res::CustomGlobalId,
    deriv: &solved::Derivation,
    impls: &IdVec<res::CustomImplId, elab::ImplDef>,
    span: Option<(usize, usize)>,
    edges: &mut Vec<ClassifiedEdge<(res::CustomGlobalId, Slot)>>,
) {
    match deriv {
        solved::Derivation::Given(_) => {}
        solved::Derivation::Super(inner, _) => {
            add_impl_instantiation_edges(source, inner, impls, span, edges)
        }
        solved::Derivation::Impl(res::ImplId::Custom(impl_id), type_args, subs) => {
            for (_, &func) in &impls[*impl_id].funcs {
                add_application_edges(source, func, type_args.iter(), span, edges);
                for (constr, sub) in subs {
                    add_constraint_edges(source, sub, (func, Slot::Constr(constr)), span, edges);
                }
            }
            for (_, sub) in subs {
                add_impl_instantiation_edges(source, sub, impls, span, edges);
            }
        }
    }
}

fn check_vals(
    mod_symbols: &IdVec<res::ModId, res::ModSymbols>,
    vals: &IdVec<res::CustomGlobalId, solved::ValDef>,
    val_symbols: &IdVec<res::CustomGlobalId, res::ValSymbols>,
    impls: &IdVec<res::CustomImplId, elab::ImplDef>,
) -> Result<(), Error> {
    let mut calls = Vec::new();
    let mut classified = Vec::new();
    for (val_id, def) in vals.iter() {
        calls.clear();
        add_global_calls(&def.body, None, &mut calls);
        for call in &calls {
            match call {
                Call::Global {
                    callee,
                    args,
                    derivs,
                    span,
                } => {
                    add_application_edges(val_id, *callee, args.iter(), *span, &mut classified);
                    for (constr, deriv) in *derivs {
                        add_constraint_edges(
                            val_id,
                            deriv,
                            (*callee, Slot::Constr(constr)),
                            *span,
                            &mut classified,
                        );
                        add_impl_instantiation_edges(val_id, deriv, impls, *span, &mut classified);
                    }
                }

                Call::TraitFunc {
                    trait_,
                    func,
                    inst,
                    span,
                } => {
                    // The callee is the func of whichever impl discharges the trait constraint.
                    // When that is only known to the caller (a given), any impl of the trait
                    // might be it.
                    let target_impls: Vec<res::CustomImplId> = match root_impl(&inst.trait_deriv) {
                        Some(res::ImplId::Custom(impl_id)) => vec![impl_id],
                        None => impls
                            .iter()
                            .filter(|(_, def)| def.trait_ == *trait_)
                            .map(|(id, _)| id)
                            .collect(),
                    };
                    for impl_id in target_impls {
                        let impl_def = &impls[impl_id];
                        let callee = impl_def.funcs[*func];
                        let layout = impl_def.func_layout();
                        add_application_edges(
                            val_id,
                            callee,
                            inst.func_args
                                .iter()
                                .map(|(param, arg)| (layout.own_param(param), arg)),
                            *span,
                            &mut classified,
                        );
                        for (constr, deriv) in &inst.func_derivs {
                            add_constraint_edges(
                                val_id,
                                deriv,
                                (callee, Slot::Constr(layout.own_constr(constr))),
                                *span,
                                &mut classified,
                            );
                        }
                        if let Some(given) = root_given(&inst.trait_deriv) {
                            let from = (val_id, Slot::Constr(given));
                            for param in layout.num_impl_params {
                                classified.push(ClassifiedEdge {
                                    from,
                                    to: (callee, Slot::Param(param)),
                                    growth: Growth::Stable,
                                    span: *span,
                                });
                            }
                            for constr in layout.num_impl_constrs {
                                classified.push(ClassifiedEdge {
                                    from,
                                    to: (callee, Slot::Constr(constr)),
                                    growth: Growth::Stable,
                                    span: *span,
                                });
                            }
                        }
                    }

                    add_impl_instantiation_edges(
                        val_id,
                        &inst.trait_deriv,
                        impls,
                        *span,
                        &mut classified,
                    );
                    for (_, deriv) in &inst.func_derivs {
                        add_impl_instantiation_edges(val_id, deriv, impls, *span, &mut classified);
                    }
                }
            }
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
    custom_types: &IdVec<res::CustomTypeId, elab::TypeDef>,
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
                    add_application_edges(
                        type_id,
                        target,
                        positional_args(args),
                        Some(span),
                        &mut classified,
                    );
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

pub fn check_polymorphic_recursion(program: &solved::Program) -> Result<(), Error> {
    check_types(
        &program.mod_symbols,
        &program.custom_types,
        &program.custom_type_symbols,
    )?;
    check_vals(
        &program.mod_symbols,
        &program.vals,
        &program.val_symbols,
        &program.impls,
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::elaborated_ast::{self as elab, TypeDef, TypeScheme};
    use crate::data::kinded_ast as kinded;
    use crate::data::raw_ast as raw;
    use crate::data::resolved_ast::{
        CustomGlobalId, CustomTypeId, GlobalId, ModDeclLoc, ModId, ModSymbols, TypeId, TypeParamId,
        TypeSymbols, ValSymbols, VariantSymbols,
    };
    use crate::data::solved_ast::{Expr, ValDef};
    use std::path::PathBuf;

    fn mod_symbols() -> IdVec<ModId, ModSymbols> {
        IdVec::from_vec(vec![ModSymbols {
            file: PathBuf::from("main.mor"),
            decl_loc: ModDeclLoc::Root,
        }])
    }

    fn type_kinds(num_params: usize) -> IdVec<TypeParamId, kinded::Kind> {
        IdVec::from_vec(vec![kinded::Kind::TYPE; num_params])
    }

    fn val_def(num_params: usize, body: Expr) -> ValDef {
        ValDef {
            scheme: TypeScheme {
                param_kinds: type_kinds(num_params),
                trait_constrs: IdVec::new(),
                body: elab::Type::Tuple(vec![]),
            },
            body,
        }
    }

    fn val_symbols(name: &str) -> ValSymbols {
        ValSymbols {
            mod_: ModId(0),
            type_param_names: IdVec::new(),
            val_name: raw::ValName(name.to_string()),
            span: (0, 0),
            type_spans: res::TypeSpans {
                span: None,
                children: Vec::new(),
            },
            trait_constr_spans: IdVec::new(),
            impl_: None,
        }
    }

    fn type_symbols(name: &str, variant_spans: &[(usize, usize)]) -> TypeSymbols {
        TypeSymbols {
            mod_: ModId(0),
            type_name: raw::TypeName(name.to_string()),
            type_param_names: IdVec::new(),
            constr_spans: IdVec::new(),
            variant_symbols: IdVec::from_vec(
                variant_spans
                    .iter()
                    .map(|&span| VariantSymbols {
                        variant_name: raw::CtorName("Ctor".to_string()),
                        span,
                        content_spans: None,
                    })
                    .collect(),
            ),
        }
    }

    fn self_call(args: Vec<elab::Type>) -> Expr {
        Expr::Global(
            GlobalId::Custom(CustomGlobalId(0)),
            IdVec::from_vec(args),
            IdVec::new(),
        )
    }

    fn check_vals_without_traits(
        vals: &IdVec<CustomGlobalId, ValDef>,
        val_symbols: &IdVec<CustomGlobalId, ValSymbols>,
    ) -> Result<(), Error> {
        check_vals(&mod_symbols(), vals, val_symbols, &IdVec::new())
    }

    #[test]
    fn growing_self_recursive_value_is_rejected() {
        let vals = IdVec::from_vec(vec![val_def(
            1,
            Expr::Span(
                10,
                25,
                Box::new(self_call(vec![elab::Type::Tuple(vec![
                    elab::Type::param(TypeParamId(0)),
                    elab::Type::param(TypeParamId(0)),
                ])])),
            ),
        )]);
        let val_symbols = IdVec::from_vec(vec![val_symbols("depth")]);

        let err = check_vals_without_traits(&vals, &val_symbols).unwrap_err();
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
            self_call(vec![elab::Type::param(TypeParamId(0))]),
        )]);
        let val_symbols = IdVec::from_vec(vec![val_symbols("len")]);

        check_vals_without_traits(&vals, &val_symbols).unwrap();
    }

    #[test]
    fn growing_recursive_type_is_rejected() {
        let custom_types = IdVec::from_vec(vec![TypeDef {
            param_kinds: type_kinds(1),
            trait_constrs: IdVec::new(),
            variants: IdVec::from_vec(vec![
                Some(elab::Type::param(TypeParamId(0))),
                Some(elab::Type::App(
                    res::TypeHead::Ctor(TypeId::Custom(CustomTypeId(0))),
                    vec![elab::Type::Tuple(vec![
                        elab::Type::param(TypeParamId(0)),
                        elab::Type::param(TypeParamId(0)),
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
    fn a_growing_type_is_reported_over_the_function_consuming_it() {
        let nested_id = CustomTypeId(0);

        let custom_types = IdVec::from_vec(vec![TypeDef {
            param_kinds: type_kinds(1),
            trait_constrs: IdVec::new(),
            variants: IdVec::from_vec(vec![
                Some(elab::Type::param(TypeParamId(0))),
                Some(elab::Type::App(
                    res::TypeHead::Ctor(TypeId::Custom(nested_id)),
                    vec![elab::Type::Tuple(vec![
                        elab::Type::param(TypeParamId(0)),
                        elab::Type::param(TypeParamId(0)),
                    ])],
                )),
            ]),
        }]);
        let custom_type_symbols =
            IdVec::from_vec(vec![type_symbols("Nested", &[(5, 14), (20, 41)])]);

        let vals = IdVec::from_vec(vec![val_def(
            1,
            self_call(vec![elab::Type::Tuple(vec![
                elab::Type::param(TypeParamId(0)),
                elab::Type::param(TypeParamId(0)),
            ])]),
        )]);
        let val_symbols = IdVec::from_vec(vec![val_symbols("depth")]);

        let program = solved::Program {
            mod_symbols: mod_symbols(),
            custom_types,
            custom_type_symbols,
            profile_points: IdVec::new(),
            vals,
            val_symbols,
            traits: IdVec::new(),
            trait_symbols: IdVec::new(),
            impls: IdVec::new(),
            impl_symbols: IdVec::new(),
            main: CustomGlobalId(0),
        };

        let err = check_polymorphic_recursion(&program).unwrap_err();
        assert!(matches!(
            err.0.error,
            ErrorKind::TypeNonterminating { ref name } if name == "Nested"
        ));
    }

    #[test]
    fn mutually_recursive_type_parameter_swap_is_accepted() {
        let pair_id = CustomTypeId(0);
        let other_id = CustomTypeId(1);

        let custom_types = IdVec::from_vec(vec![
            TypeDef {
                param_kinds: type_kinds(2),
                trait_constrs: IdVec::new(),
                variants: IdVec::from_vec(vec![Some(elab::Type::App(
                    res::TypeHead::Ctor(TypeId::Custom(other_id)),
                    vec![
                        elab::Type::param(TypeParamId(1)),
                        elab::Type::param(TypeParamId(0)),
                    ],
                ))]),
            },
            TypeDef {
                param_kinds: type_kinds(2),
                trait_constrs: IdVec::new(),
                variants: IdVec::from_vec(vec![Some(elab::Type::App(
                    res::TypeHead::Ctor(TypeId::Custom(pair_id)),
                    vec![
                        elab::Type::param(TypeParamId(1)),
                        elab::Type::param(TypeParamId(0)),
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
}
