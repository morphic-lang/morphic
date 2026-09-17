//! Discharges the trait obligations recorded by type inference, producing the solved program.
//!
//! Every obligation is a trait constraint over the enclosing definition's own type parameters.  It
//! is discharged either by one of the definition's own trait constraints (a "given"), possibly
//! through a superclass, or by an impl visible in the definition's module whose head matches it,
//! whose own constraints are then discharged recursively.  Exactly one impl head may match; impl
//! constraints play no part in choosing.  Together with the Paterson conditions on impl
//! constraints (see `check_traits`) this makes solving a deterministic search that always
//! terminates.
//!
//! An impl's superclass derivations are solved here as well, in the impl's own module and relative
//! to its own constraints, since monomorphization needs them to project a superclass out of an
//! impl-derived constraint.

use crate::data::kinded_ast as kinded;
use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;
use crate::data::solved_ast as solved;
use crate::data::typed_ast as typed;
use crate::file_cache::FileCache;
use crate::report_type::{self, TypeRenderer};
use id_collections::IdVec;
use morphic_common::report_error::{locate_path, locate_span, ColorMode, Locate, Reportable};
use std::collections::BTreeSet;
use std::io;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    NoImpl {
        constr: String,
        required_by: Vec<String>,
        importable: Vec<String>,
    },
    AmbiguousImpl {
        constr: String,
        candidates: Vec<String>,
    },
}

#[derive(Debug)]
pub struct Error(Locate<ErrorKind>);

fn indented_list(items: &[String]) -> String {
    items
        .iter()
        .map(|item| format!("    {}", item))
        .collect::<Vec<_>>()
        .join("\n")
}

impl Reportable for Error {
    fn report(
        &self,
        dest: &mut impl io::Write,
        files: &FileCache,
        color: ColorMode,
    ) -> io::Result<()> {
        self.0.report_with(dest, files, color, |err| match err {
            ErrorKind::NoImpl {
                constr,
                required_by,
                importable,
            } => {
                let mut message = format!(
                    "I couldn't find an impl in scope for the trait constraint\n\n    {}\n\n",
                    constr
                );
                if !required_by.is_empty() {
                    message.push_str(&format!(
                        "It is needed in turn by:\n\n{}\n\n",
                        indented_list(required_by)
                    ));
                }
                if !importable.is_empty() {
                    message.push_str(&format!(
                        "These impls would satisfy it if you imported them:\n\n{}\n\n",
                        indented_list(importable)
                    ));
                }
                message.push_str(
                    "Only the impls declared or imported in the current module are considered, \
                     together with the trait constraints of the enclosing definition.",
                );
                ("No Impl in Scope", message)
            }

            ErrorKind::AmbiguousImpl { constr, candidates } => (
                "Ambiguous Impl",
                format!(
                    "More than one impl in scope matches the trait constraint\n\n    {}\n\n\
                     namely:\n\n{}\n\nExactly one impl has to match; adjust which impls are \
                     imported so that only one does.",
                    constr,
                    indented_list(candidates)
                ),
            ),
        })
    }

    fn exit_status(&self) -> i32 {
        1
    }
}

enum RawErrorKind {
    NoImpl {
        goal: res::TraitApp,
        chain: Vec<res::TraitApp>,
        importable: Vec<res::ImplId>,
    },
    Ambiguous {
        goal: res::TraitApp,
        candidates: Vec<res::ImplId>,
    },
}

/// Matches an impl head (a pattern over the impl's parameters) against the arguments of a goal,
/// binding the impl's parameters.  Type parameters of the goal are rigid: they only ever match a
/// bare pattern parameter.
fn match_head(
    head: &[res::Type],
    goal_args: &[res::Type],
    num_params: usize,
) -> Option<IdVec<res::TypeParamId, res::Type>> {
    debug_assert_eq!(head.len(), goal_args.len());
    let mut subst = vec![None; num_params];
    for (pattern, target) in head.iter().zip(goal_args) {
        if !match_type(pattern, target, &mut subst) {
            return None;
        }
    }
    subst
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .map(IdVec::from_vec)
}

fn bind(param: res::TypeParamId, type_: res::Type, subst: &mut [Option<res::Type>]) -> bool {
    match &subst[param.0] {
        Some(existing) => *existing == type_,
        None => {
            subst[param.0] = Some(type_);
            true
        }
    }
}

fn match_type(pattern: &res::Type, target: &res::Type, subst: &mut [Option<res::Type>]) -> bool {
    match (pattern, target) {
        // A pattern parameter, possibly applied to further patterns, absorbs the corresponding
        // prefix of the target application: `f a` against `Result Int Bool` binds `f` to
        // `Result Int` and `a` to `Bool`.
        (res::Type::App(res::TypeHead::Var(param), pattern_args), res::Type::App(head, args)) => {
            if args.len() < pattern_args.len() {
                return false;
            }
            let split = args.len() - pattern_args.len();
            for (pattern_arg, arg) in pattern_args.iter().zip(&args[split..]) {
                if !match_type(pattern_arg, arg, subst) {
                    return false;
                }
            }
            bind(*param, res::Type::App(*head, args[..split].to_vec()), subst)
        }

        (res::Type::App(res::TypeHead::Var(param), pattern_args), _) => {
            pattern_args.is_empty() && bind(*param, target.clone(), subst)
        }

        (
            res::Type::App(res::TypeHead::Ctor(pattern_id), pattern_args),
            res::Type::App(res::TypeHead::Ctor(id), args),
        ) => {
            pattern_id == id
                && pattern_args.len() == args.len()
                && pattern_args
                    .iter()
                    .zip(args)
                    .all(|(pattern_arg, arg)| match_type(pattern_arg, arg, subst))
        }

        (res::Type::Tuple(pattern_items), res::Type::Tuple(items)) => {
            pattern_items.len() == items.len()
                && pattern_items
                    .iter()
                    .zip(items)
                    .all(|(pattern_item, item)| match_type(pattern_item, item, subst))
        }

        (
            res::Type::Func(pattern_purity, pattern_arg, pattern_ret),
            res::Type::Func(purity, arg, ret),
        ) => {
            pattern_purity == purity
                && match_type(pattern_arg, arg, subst)
                && match_type(pattern_ret, ret, subst)
        }

        _ => false,
    }
}

/// The givens of an item, closed under superclass projection: each is paired with its
/// derivation relative to the item's own trait constraints.
fn closed_givens(
    traits: &IdVec<res::CustomTraitId, kinded::TraitDef>,
    constrs: &IdVec<res::TraitConstrId, res::TraitApp>,
) -> Vec<(res::TraitApp, solved::Derivation)> {
    let mut result: Vec<(res::TraitApp, solved::Derivation)> = constrs
        .iter()
        .map(|(constr_id, constr)| (constr.clone(), solved::Derivation::Given(constr_id)))
        .collect();

    // The superclass graph is acyclic (see `check_traits`), so this terminates.
    let mut index = 0;
    while index < result.len() {
        let (constr, deriv) = result[index].clone();
        let res::TraitId::Custom(custom) = constr.trait_;
        let subst = IdVec::from_vec(constr.args.clone());
        for (super_id, super_) in &traits[custom].supers {
            result.push((
                super_.subst(&subst),
                solved::Derivation::Super(Box::new(deriv.clone()), super_id),
            ));
        }
        index += 1;
    }

    result
}

struct Solver<'a> {
    program: &'a typed::Program,
    scope: &'a BTreeSet<res::ImplId>,
    givens: Vec<(res::TraitApp, solved::Derivation)>,
}

impl<'a> Solver<'a> {
    fn impl_def(&self, id: res::ImplId) -> &'a kinded::ImplDef {
        let res::ImplId::Custom(custom) = id;
        &self.program.impls[custom]
    }

    fn matching_impls(
        &self,
        goal: &res::TraitApp,
        candidates: impl Iterator<Item = res::ImplId>,
    ) -> Vec<(res::ImplId, IdVec<res::TypeParamId, res::Type>)> {
        candidates
            .filter_map(|id| {
                let def = self.impl_def(id);
                if def.trait_ != goal.trait_ {
                    return None;
                }
                match_head(&def.head, &goal.args, def.param_kinds.len()).map(|subst| (id, subst))
            })
            .collect()
    }

    fn solve(
        &self,
        goal: &res::TraitApp,
        chain: &mut Vec<res::TraitApp>,
    ) -> Result<solved::Derivation, RawErrorKind> {
        if let Some((_, deriv)) = self.givens.iter().find(|(constr, _)| constr == goal) {
            return Ok(deriv.clone());
        }

        let mut candidates = self.matching_impls(goal, self.scope.iter().copied());

        match candidates.len() {
            0 => {
                let elsewhere = self
                    .program
                    .impls
                    .iter()
                    .map(|(id, _)| res::ImplId::Custom(id))
                    .filter(|id| !self.scope.contains(id));
                let importable = self
                    .matching_impls(goal, elsewhere)
                    .into_iter()
                    .map(|(id, _)| id)
                    .collect();
                Err(RawErrorKind::NoImpl {
                    goal: goal.clone(),
                    chain: chain.clone(),
                    importable,
                })
            }

            1 => {
                let (id, subst) = candidates.pop().unwrap();
                let def = self.impl_def(id);
                chain.push(goal.clone());
                let subs = def
                    .trait_constrs
                    .try_map_refs(|_, constr| self.solve(&constr.subst(&subst), chain));
                chain.pop();
                Ok(solved::Derivation::Impl(id, subst, subs?))
            }

            _ => Err(RawErrorKind::Ambiguous {
                goal: goal.clone(),
                candidates: candidates.into_iter().map(|(id, _)| id).collect(),
            }),
        }
    }
}

fn render_impl(program: &typed::Program, id: res::ImplId) -> String {
    let res::ImplId::Custom(custom) = id;
    let symbols = &program.impl_symbols[custom];
    format!(
        "{} (in {})",
        symbols.impl_name.0,
        program.mod_symbols[symbols.mod_].file.display()
    )
}

fn render_error(
    program: &typed::Program,
    renderer: &TypeRenderer,
    params: &IdVec<res::TypeParamId, raw::TypeParam>,
    err: RawErrorKind,
) -> ErrorKind {
    let render_constr = |constr: &res::TraitApp| {
        renderer.render_trait_app(
            params,
            &report_type::TraitApp::from_resolved(constr),
            &program.trait_symbols,
        )
    };
    match err {
        RawErrorKind::NoImpl {
            goal,
            chain,
            importable,
        } => ErrorKind::NoImpl {
            constr: render_constr(&goal),
            required_by: chain.iter().rev().map(render_constr).collect(),
            importable: importable
                .into_iter()
                .map(|id| render_impl(program, id))
                .collect(),
        },
        RawErrorKind::Ambiguous { goal, candidates } => ErrorKind::AmbiguousImpl {
            constr: render_constr(&goal),
            candidates: candidates
                .into_iter()
                .map(|id| render_impl(program, id))
                .collect(),
        },
    }
}

fn convert_pattern(pat: &typed::Pattern) -> solved::Pattern {
    match pat {
        typed::Pattern::Any(type_) => solved::Pattern::Any(type_.clone()),
        typed::Pattern::Var(type_) => solved::Pattern::Var(type_.clone()),
        typed::Pattern::Tuple(items) => {
            solved::Pattern::Tuple(items.iter().map(convert_pattern).collect())
        }
        typed::Pattern::Ctor(id, args, variant, content) => solved::Pattern::Ctor(
            *id,
            args.clone(),
            *variant,
            content
                .as_ref()
                .map(|content| Box::new(convert_pattern(content))),
        ),
        &typed::Pattern::ByteConst(val) => solved::Pattern::ByteConst(val),
        &typed::Pattern::IntConst(val) => solved::Pattern::IntConst(val),
        &typed::Pattern::FloatConst(val) => solved::Pattern::FloatConst(val),
        &typed::Pattern::Span(lo, hi, ref content) => {
            solved::Pattern::Span(lo, hi, Box::new(convert_pattern(content)))
        }
    }
}

fn subst_expr(
    expr: &typed::Expr,
    solutions: &IdVec<typed::ObligationId, solved::Derivation>,
) -> solved::Expr {
    match expr {
        typed::Expr::Global(id, type_args, obligations) => solved::Expr::Global(
            *id,
            type_args.clone(),
            obligations.map_refs(|_, &obligation| solutions[obligation].clone()),
        ),
        typed::Expr::TraitFunc(trait_, func, inst) => solved::Expr::TraitFunc(
            *trait_,
            *func,
            res::TraitFuncInst {
                trait_args: inst.trait_args.clone(),
                trait_deriv: solutions[inst.trait_deriv].clone(),
                func_args: inst.func_args.clone(),
                func_derivs: inst
                    .func_derivs
                    .map_refs(|_, &obligation| solutions[obligation].clone()),
            },
        ),
        &typed::Expr::Local(id) => solved::Expr::Local(id),
        typed::Expr::Tuple(items) => solved::Expr::Tuple(
            items
                .iter()
                .map(|item| subst_expr(item, solutions))
                .collect(),
        ),
        typed::Expr::Lam(purity, arg_type, ret_type, pat, body, prof_id) => solved::Expr::Lam(
            *purity,
            arg_type.clone(),
            ret_type.clone(),
            convert_pattern(pat),
            Box::new(subst_expr(body, solutions)),
            *prof_id,
        ),
        typed::Expr::App(purity, func, arg) => solved::Expr::App(
            *purity,
            Box::new(subst_expr(func, solutions)),
            Box::new(subst_expr(arg, solutions)),
        ),
        typed::Expr::Match(discrim, cases, result_type) => solved::Expr::Match(
            Box::new(subst_expr(discrim, solutions)),
            cases
                .iter()
                .map(|(pat, body)| (convert_pattern(pat), subst_expr(body, solutions)))
                .collect(),
            result_type.clone(),
        ),
        typed::Expr::LetMany(bindings, body) => solved::Expr::LetMany(
            bindings
                .iter()
                .map(|(lhs, rhs)| (convert_pattern(lhs), subst_expr(rhs, solutions)))
                .collect(),
            Box::new(subst_expr(body, solutions)),
        ),
        typed::Expr::ArrayLit(type_, items) => solved::Expr::ArrayLit(
            type_.clone(),
            items
                .iter()
                .map(|item| subst_expr(item, solutions))
                .collect(),
        ),
        &typed::Expr::ByteLit(val) => solved::Expr::ByteLit(val),
        &typed::Expr::IntLit(val) => solved::Expr::IntLit(val),
        &typed::Expr::FloatLit(val) => solved::Expr::FloatLit(val),
        &typed::Expr::Span(lo, hi, ref body) => {
            solved::Expr::Span(lo, hi, Box::new(subst_expr(body, solutions)))
        }
    }
}

pub fn solve_traits_in_bodies(program: typed::Program) -> Result<solved::Program, Error> {
    let (impls, vals) = {
        let renderer = TypeRenderer::new(&program.mod_symbols, &program.custom_type_symbols);

        let impls = program.impls.try_map_refs(|impl_id, def| {
            let symbols = &program.impl_symbols[impl_id];
            let file = &program.mod_symbols[symbols.mod_].file;
            let solver = Solver {
                program: &program,
                scope: &program.impl_scope[symbols.mod_],
                givens: closed_givens(&program.traits, &def.trait_constrs),
            };

            let res::TraitId::Custom(custom_trait) = def.trait_;
            let head_subst = IdVec::from_vec(def.head.clone());
            let supers = program.traits[custom_trait]
                .supers
                .try_map_refs(|_, super_| {
                    solver
                        .solve(&super_.subst(&head_subst), &mut Vec::new())
                        .map_err(|err| {
                            let kind =
                                render_error(&program, &renderer, &symbols.type_param_names, err);
                            let (lo, hi) = symbols.head_span;
                            Error(locate_path(file)(locate_span(lo, hi)(kind.into())))
                        })
                })?;

            Ok(solved::ImplDef {
                trait_: def.trait_,
                param_kinds: def.param_kinds.clone(),
                head: def.head.clone(),
                trait_constrs: def.trait_constrs.clone(),
                supers,
                funcs: def.funcs.clone(),
            })
        })?;

        let vals = program.vals.try_map_refs(|val_id, def| {
            let symbols = &program.val_symbols[val_id];
            let file = &program.mod_symbols[symbols.mod_].file;
            let solver = Solver {
                program: &program,
                scope: &program.impl_scope[symbols.mod_],
                givens: closed_givens(&program.traits, &def.scheme.trait_constrs),
            };

            let solutions = def.obligations.try_map_refs(|_, obligation| {
                solver
                    .solve(&obligation.trait_constr, &mut Vec::new())
                    .map_err(|err| {
                        let kind =
                            render_error(&program, &renderer, &symbols.type_param_names, err);
                        let mut located: Locate<ErrorKind> = kind.into();
                        located = locate_path(file)(located);
                        if let Some((lo, hi)) = obligation.span {
                            located = locate_span(lo, hi)(located);
                        }
                        Error(located)
                    })
            })?;

            Ok(solved::ValDef {
                scheme: def.scheme.clone(),
                body: subst_expr(&def.body, &solutions),
            })
        })?;

        (impls, vals)
    };

    Ok(solved::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        profile_points: program.profile_points,
        vals,
        val_symbols: program.val_symbols,
        traits: program.traits,
        trait_symbols: program.trait_symbols,
        impls,
        impl_symbols: program.impl_symbols,
        main: program.main,
    })
}
