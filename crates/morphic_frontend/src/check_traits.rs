//! Structural checks on traits and impls that need no type inference: the superclass graph must be
//! acyclic, and every impl's constraints must satisfy the Paterson conditions, which guarantee
//! that trait solving terminates and that a derivation is never larger than the type it is for.

use crate::data::resolved_ast as res;
use crate::file_cache::FileCache;
use crate::report_type;
use morphic_common::lines;
use morphic_common::report_error::{locate_path, locate_span, ColorMode, Locate, Reportable};
use morphic_common::util::graph::{self, Graph};
use std::collections::BTreeMap;
use std::io;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    CyclicSuperclass {
        trait_: String,
    },
    ConstrRepeatsParam {
        impl_: String,
        constr: String,
        param: String,
    },
    ConstrNotSmaller {
        impl_: String,
        constr: String,
    },
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
        self.0.report_with(dest, files, color, |err| match err {
            ErrorKind::CyclicSuperclass { trait_ } => (
                "Cyclic Superclass",
                format!(
                    "The trait '{}' is, directly or indirectly, its own superclass.",
                    trait_
                ),
            ),

            ErrorKind::ConstrRepeatsParam {
                impl_,
                constr,
                param,
            } => (
                "Impl Constraint Too Large",
                format!(
                    lines![
                        "In the impl '{impl_}', the constraint",
                        "",
                        "    {constr}",
                        "",
                        "mentions the type parameter '{param}' more often than the impl head \
                         does.  An impl's constraints have to be strictly smaller than its head, \
                         so that resolving a constraint always makes progress.",
                    ],
                    impl_ = impl_,
                    constr = constr,
                    param = param,
                ),
            ),

            ErrorKind::ConstrNotSmaller { impl_, constr } => (
                "Impl Constraint Too Large",
                format!(
                    lines![
                        "In the impl '{impl_}', the constraint",
                        "",
                        "    {constr}",
                        "",
                        "is not smaller than the impl head.  Each constraint has to mention fewer \
                         type constructors and parameters (counted with repetition) than the head \
                         does, so that resolving a constraint always makes progress.  Rewrite the \
                         constraint in terms of the head's parts, or make the constrained trait a \
                         superclass.",
                    ],
                    impl_ = impl_,
                    constr = constr,
                ),
            ),
        })
    }

    fn exit_status(&self) -> i32 {
        1
    }
}

fn check_superclasses(program: &res::Program) -> Result<(), Error> {
    let supers = Graph {
        edges_out: program.traits.map_refs(|_, def| {
            def.supers
                .iter()
                .filter_map(|(_, constr)| match constr.trait_ {
                    res::TraitId::Custom(custom) => Some(custom),
                    // A builtin trait has only builtin superclasses, so it closes no cycle.
                    res::TraitId::Builtin(_) => None,
                })
                .collect()
        }),
    };

    for scc in graph::strongly_connected(&supers) {
        let has_self_edge =
            scc.len() == 1 && supers.edges_out[scc[0]].iter().any(|&dep| dep == scc[0]);
        if scc.len() > 1 || has_self_edge {
            let culprit = scc[0];
            let symbols = &program.trait_symbols[culprit];
            let mut located: Locate<ErrorKind> = ErrorKind::CyclicSuperclass {
                trait_: symbols.trait_name.0.clone(),
            }
            .into();
            located = locate_path(&program.mod_symbols[symbols.mod_].file)(located);
            if let Some(&(lo, hi)) = symbols.super_spans.values().next() {
                located = locate_span(lo, hi)(located);
            }
            return Err(Error(located));
        }
    }

    Ok(())
}

/// The number of type constructors and parameters in a type, counting repetitions.
fn size(type_: &res::Type) -> usize {
    match type_ {
        res::Type::App(_, args) => 1 + args.iter().map(size).sum::<usize>(),
        res::Type::Tuple(items) => 1 + items.iter().map(size).sum::<usize>(),
        res::Type::Func(_, arg, ret) => 1 + size(arg) + size(ret),
    }
}

fn count_params(type_: &res::Type, counts: &mut BTreeMap<res::TypeParamId, usize>) {
    match type_ {
        res::Type::App(head, args) => {
            if let res::TypeHead::Var(param) = head {
                *counts.entry(*param).or_insert(0) += 1;
            }
            for arg in args {
                count_params(arg, counts);
            }
        }
        res::Type::Tuple(items) => {
            for item in items {
                count_params(item, counts);
            }
        }
        res::Type::Func(_, arg, ret) => {
            count_params(arg, counts);
            count_params(ret, counts);
        }
    }
}

fn check_paterson(program: &res::Program) -> Result<(), Error> {
    let renderer =
        report_type::TypeRenderer::new(&program.mod_symbols, &program.custom_type_symbols);

    for (impl_id, def) in &program.impls {
        let symbols = &program.impl_symbols[impl_id];

        let head_size: usize = def.head.iter().map(size).sum();
        let mut head_counts = BTreeMap::new();
        for arg in &def.head {
            count_params(arg, &mut head_counts);
        }

        for (constr_id, constr) in &def.trait_constrs {
            let render = || {
                renderer.render_trait_app(
                    &symbols.type_param_names,
                    &report_type::TraitApp::from_resolved(constr),
                    &program.trait_symbols,
                )
            };
            let locate = |kind: ErrorKind| {
                let (lo, hi) = symbols.constr_spans[constr_id];
                Error(locate_path(&program.mod_symbols[symbols.mod_].file)(
                    locate_span(lo, hi)(kind.into()),
                ))
            };

            let mut counts = BTreeMap::new();
            for arg in &constr.args {
                count_params(arg, &mut counts);
            }
            for (&param, &count) in &counts {
                if count > head_counts.get(&param).copied().unwrap_or(0) {
                    return Err(locate(ErrorKind::ConstrRepeatsParam {
                        impl_: symbols.impl_name.0.clone(),
                        constr: render(),
                        param: symbols.type_param_names[param].0.clone(),
                    }));
                }
            }

            let constr_size: usize = constr.args.iter().map(size).sum();
            if constr_size >= head_size {
                return Err(locate(ErrorKind::ConstrNotSmaller {
                    impl_: symbols.impl_name.0.clone(),
                    constr: render(),
                }));
            }
        }
    }

    Ok(())
}

pub fn check_traits(program: &res::Program) -> Result<(), Error> {
    check_superclasses(program)?;
    check_paterson(program)?;
    Ok(())
}
