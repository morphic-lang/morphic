//! Discharges the trait obligations recorded by type inference, producing the solved program.
//!
//! Every obligation is a trait constraint over the enclosing definition's own type parameters.
//! Where unification determined its evidence, by equating the evidence of constrained types,
//! that evidence is used.  Otherwise it is discharged either by one of the definition's own
//! trait constraints (a "given"), possibly through a superclass, or by an impl visible in the
//! definition's module whose head matches it, whose own constraints are then discharged
//! recursively.  Exactly one impl head may match; impl constraints play no part in choosing.
//! Together with the Paterson conditions on impl constraints (see `check_traits`) this makes
//! solving a deterministic search that always terminates.
//!
//! Equations between evidence that inference had to defer, because a superclass projection is
//! not injective, are checked once everything is solved.

use crate::data::builtin_traits::{
    builtin_impl_supers, elab_trait_def, trait_func_name, trait_name,
};
use crate::data::elaborated_ast as elab;
use crate::data::elaborated_ast::{Derivation, Subst, TraitApp, TraitSelfConstr, Type};
use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;
use crate::data::solved_ast as solved;
use crate::data::typed_ast as typed;
use crate::file_cache::FileCache;
use crate::report_type::{self, TypeRenderer};
use crate::trait_solver::{
    closed_givens, impl_facts_of, normalize_derivation, normalize_trait_app, Facts, ImplFacts,
    SolveError, Solver,
};
use id_collections::{Count, IdVec};
use morphic_common::report_error::{locate_path, locate_span, ColorMode, Locate, Reportable};
use std::convert::Infallible;
use std::io;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    NoImpl {
        constr: String,
        required_by: Vec<String>,
        importable: Vec<String>,
        covered: Vec<String>,
    },
    AmbiguousImpl {
        constr: String,
        candidates: Vec<String>,
    },
    CyclicConstrs {
        impl_: String,
    },
    ConflictingEvidence {
        constr: String,
        /// The evidence at the reported expression, and the evidence it is expected to agree with.
        located: String,
        other: String,
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

/// A note that the builtin impls `covered`, which is not empty, would satisfy a constraint but
/// are covered up.
fn covered_up_note(covered: &[String]) -> String {
    if let [name] = covered {
        format!(
            "The builtin impl\n\n    {}\n\nwould satisfy it, but an impl of the same name \
             declared or imported in the current module covers it up.\n\n",
            name
        )
    } else {
        format!(
            "These builtin impls would satisfy it, but impls of the same names declared or \
             imported in the current module cover them up:\n\n{}\n\n",
            indented_list(covered)
        )
    }
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
                covered,
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
                if !covered.is_empty() {
                    message.push_str(&covered_up_note(covered));
                }
                message.push_str(
                    "Only the builtin impls and the impls declared or imported in the current \
                     module are considered, together with the trait constraints of the enclosing \
                     definition.",
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

            ErrorKind::CyclicConstrs { impl_ } => (
                "Cyclic Impl Constraints",
                format!(
                    "The constraints of the impl '{}' refer to each other's evidence in a cycle, \
                     so none of them can be established first.",
                    impl_
                ),
            ),

            ErrorKind::ConflictingEvidence {
                constr,
                located,
                other,
            } => (
                "Conflicting Impls",
                format!(
                    "This expression's type carries evidence for the trait constraint\n\n    \
                     {}\n\nfrom {}.\n\nBut here the same type is expected with evidence from \
                     {}.\n\nA type declared with trait constraints is a different type under \
                     each impl of those constraints, so a value built under one impl cannot be \
                     used where the other is expected.",
                    constr, located, other
                ),
            ),
        })
    }

    fn exit_status(&self) -> i32 {
        1
    }
}

/// The solver's facts, read off the program.
struct ProgramFacts<'a> {
    program: &'a typed::Program,
}

impl<'a> Facts for ProgramFacts<'a> {
    type Error = Infallible;

    fn supers(
        &self,
        trait_: res::TraitId,
    ) -> Result<IdVec<res::SuperId, TraitApp<Derivation<elab::TraitSelfConstr>>>, Infallible> {
        Ok(elab_trait_def(&self.program.traits, trait_).supers.clone())
    }

    fn impl_facts(&self, id: res::ImplId) -> Result<ImplFacts, Infallible> {
        Ok(impl_facts_of(&self.program.impls, id))
    }

    fn impl_supers(&self, id: res::ImplId) -> Result<IdVec<res::SuperId, Derivation>, Infallible> {
        match id {
            res::ImplId::Builtin(builtin) => Ok(builtin_impl_supers(builtin)),
            res::ImplId::Custom(custom) => Ok(self.program.impls[custom].supers.clone()),
        }
    }

    fn all_impls(&self) -> Vec<res::ImplId> {
        self.program
            .impls
            .iter()
            .map(|(id, _)| res::ImplId::Custom(id))
            .collect()
    }

    fn constrained_prefix(&self, id: res::CustomTypeId) -> Count<res::TypeParamId> {
        self.program.custom_types[id].constrained_prefix()
    }
}

fn infallible<T>(result: Result<T, Infallible>) -> T {
    match result {
        Ok(value) => value,
        Err(never) => match never {},
    }
}

enum RawErrorKind {
    Solve(SolveError<res::TraitConstrId, Infallible>),
    /// Two obligations whose evidence had to agree but does not; the error is located at the
    /// first, and the message explains both.
    ConflictingEvidence {
        located: typed::ObligationId,
        other: typed::ObligationId,
        solutions: IdVec<typed::ObligationId, Derivation>,
    },
}

struct RawError {
    kind: RawErrorKind,
    span: (usize, usize),
}

enum Memo {
    Pending,
    InProgress,
    Done(Derivation),
}

/// Resolves the obligations of one definition to derivations, each after the obligations its
/// goal and evidence refer to.
struct Resolver<'a> {
    def: &'a typed::ValDef,
    facts: &'a ProgramFacts<'a>,
    solver: &'a Solver<'a, res::TraitConstrId, ProgramFacts<'a>>,
    solutions: IdVec<typed::ObligationId, Memo>,
}

impl<'a> Resolver<'a> {
    fn resolve(&mut self, id: typed::ObligationId) -> Result<Derivation, RawError> {
        match &self.solutions[id] {
            Memo::Done(deriv) => return Ok(deriv.clone()),
            // An obligation's goal and evidence only refer to obligations for smaller
            // constraints, so the references are acyclic.
            Memo::InProgress => unreachable!("obligations refer to each other acyclically"),
            Memo::Pending => {}
        }
        self.solutions[id] = Memo::InProgress;

        let obligation = &self.def.obligations[id];
        let goal = self.trait_app(&obligation.goal)?;
        let deriv = match &obligation.evidence {
            typed::Evidence::Unknown => {
                let goal = infallible(normalize_trait_app(self.facts, &goal));
                self.solver
                    .solve(&goal, &mut Vec::new())
                    .map_err(|err| RawError {
                        kind: RawErrorKind::Solve(err),
                        span: obligation.span,
                    })?
            }
            &typed::Evidence::Given(given) => Derivation::Given(given),
            typed::Evidence::Impl(impl_id, args, subs) => Derivation::Impl(
                *impl_id,
                args.try_map_refs(|_, arg| self.type_(arg))?,
                subs.try_map_refs(|_, &sub| self.resolve(sub))?,
            ),
            &typed::Evidence::Super(inner, index) => {
                let inner = self.resolve(inner)?;
                infallible(normalize_derivation(
                    self.facts,
                    &Derivation::Super(Box::new(inner), index),
                ))
            }
        };

        self.solutions[id] = Memo::Done(deriv.clone());
        Ok(deriv)
    }

    fn type_(&mut self, type_: &Type<typed::ObligationId>) -> Result<elab::Type, RawError> {
        match type_ {
            Type::App(head, args) => Ok(Type::App(
                *head,
                args.iter()
                    .map(|arg| self.type_(arg))
                    .collect::<Result<_, _>>()?,
            )),
            Type::Constrained(id, args, evidence) => Ok(Type::Constrained(
                *id,
                args.iter()
                    .map(|arg| self.type_(arg))
                    .collect::<Result<_, _>>()?,
                evidence.try_map_refs(|_, &obligation| self.resolve(obligation))?,
            )),
            Type::Tuple(items) => Ok(Type::Tuple(
                items
                    .iter()
                    .map(|item| self.type_(item))
                    .collect::<Result<_, _>>()?,
            )),
            Type::Func(purity, arg, ret) => Ok(Type::Func(
                *purity,
                Box::new(self.type_(arg)?),
                Box::new(self.type_(ret)?),
            )),
        }
    }

    fn trait_app(
        &mut self,
        app: &TraitApp<typed::ObligationId>,
    ) -> Result<elab::TraitApp, RawError> {
        Ok(TraitApp {
            trait_: app.trait_,
            args: app
                .args
                .iter()
                .map(|arg| self.type_(arg))
                .collect::<Result<_, _>>()?,
        })
    }
}

fn render_impl(program: &typed::Program, id: res::ImplId) -> String {
    match id {
        res::ImplId::Builtin(builtin) => builtin.name(),
        res::ImplId::Custom(custom) => {
            let symbols = &program.impl_symbols[custom];
            format!(
                "{} (in {})",
                symbols.impl_name.0,
                program.mod_symbols[symbols.mod_].file.display()
            )
        }
    }
}

fn render_constr<E>(
    program: &typed::Program,
    renderer: &TypeRenderer,
    params: &IdVec<res::TypeParamId, raw::TypeParam>,
    constr: &TraitApp<E>,
) -> String {
    renderer.render_trait_app(
        params,
        &report_type::TraitApp::from_elab(constr),
        &program.trait_symbols,
    )
}

/// Explains where the evidence of an obligation came from, for the conflict error.
struct Explainer<'a> {
    program: &'a typed::Program,
    renderer: &'a TypeRenderer<'a>,
    params: &'a IdVec<res::TypeParamId, raw::TypeParam>,
    def: &'a typed::ValDef,
    solutions: &'a IdVec<typed::ObligationId, Derivation>,
}

impl Explainer<'_> {
    fn constr<E>(&self, app: &TraitApp<E>) -> String {
        render_constr(self.program, self.renderer, self.params, app)
    }

    fn impl_name(&self, id: res::ImplId) -> String {
        match id {
            res::ImplId::Builtin(builtin) => builtin.name(),
            res::ImplId::Custom(custom) => self.program.impl_symbols[custom].impl_name.0.clone(),
        }
    }

    fn global_name(&self, id: res::GlobalId) -> String {
        match id {
            res::GlobalId::Custom(custom) => {
                format!("'{}'", self.program.val_symbols[custom].val_name.0)
            }
            res::GlobalId::Ctor(type_, variant) => {
                let (_, ctor) = self.renderer.render_ctor(type_, variant);
                format!("the constructor '{}'", ctor)
            }
            res::GlobalId::Intrinsic(_)
            | res::GlobalId::ArrayOp(_)
            | res::GlobalId::IoOp(_)
            | res::GlobalId::Panic => "a builtin".to_owned(),
        }
    }

    fn trait_func_name(&self, trait_: res::TraitId, func: res::TraitFuncId) -> String {
        format!(
            "'{}' of the trait '{}'",
            trait_func_name(&self.program.trait_symbols, trait_, func),
            trait_name(&self.program.trait_symbols, trait_)
        )
    }

    /// The constraint a given-rooted derivation proves.
    fn given_goal(&self, deriv: &Derivation) -> Option<elab::TraitApp> {
        match deriv {
            Derivation::Given(given) => Some(self.def.scheme.trait_constrs[*given].clone()),
            Derivation::Super(inner, index) => {
                let inner_goal = self.given_goal(inner)?;
                let super_ =
                    &elab_trait_def(&self.program.traits, inner_goal.trait_).supers[*index];
                let types = IdVec::from_vec(inner_goal.args);
                let subst = Subst {
                    types: &types,
                    givens: &|TraitSelfConstr| (**inner).clone(),
                };
                Some(subst.trait_app(super_))
            }
            Derivation::Impl(_, _, _) => None,
        }
    }

    /// Names a derivation: an impl, or a given and the superclasses projected out of it.
    fn describe(&self, deriv: &Derivation) -> String {
        match deriv {
            Derivation::Given(given) => format!(
                "the constraint '{}' of this definition",
                self.constr(&self.def.scheme.trait_constrs[*given])
            ),
            Derivation::Impl(id, _, _) => format!("the impl '{}'", self.impl_name(*id)),
            Derivation::Super(inner, _) => {
                let goal = self
                    .given_goal(deriv)
                    .expect("a normalized projection is out of a given");
                format!(
                    "the '{}' superclass of {}",
                    self.constr(&goal),
                    self.describe(inner)
                )
            }
        }
    }

    /// What required the constraint of an obligation that was solved in scope.
    fn subject(&self, origin: &typed::Origin) -> String {
        match origin {
            typed::Origin::OwnConstr(_) => "this definition".to_owned(),
            typed::Origin::GlobalConstr(id, _) => self.global_name(*id),
            typed::Origin::TraitFuncTrait(trait_, func)
            | typed::Origin::TraitFuncConstr(trait_, func, _) => {
                self.trait_func_name(*trait_, *func)
            }
            typed::Origin::Carried(signature) => self.source(*signature),
            typed::Origin::Annotation(_, _) => "this type annotation".to_owned(),
            typed::Origin::Pattern(_, _) => "this pattern".to_owned(),
        }
    }

    /// The signature that fixed the evidence an obligation carries.
    fn source(&self, signature: typed::Signature) -> String {
        match signature {
            typed::Signature::Own => "this definition's own signature".to_owned(),
            typed::Signature::Global(id) => {
                format!("the declared type of {}", self.global_name(id))
            }
            typed::Signature::TraitFunc(trait_, func) => {
                format!("the signature of {}", self.trait_func_name(trait_, func))
            }
            typed::Signature::TypeDecl(id) => format!(
                "the declaration of the type '{}'",
                self.program.custom_type_symbols[id].type_name.0
            ),
        }
    }

    /// Describes the evidence an obligation ended up with, and why.
    fn explain(&self, id: typed::ObligationId) -> String {
        let obligation = &self.def.obligations[id];
        let solution = &self.solutions[id];
        let goal = self.constr(&obligation.goal);
        match &obligation.evidence {
            typed::Evidence::Unknown => match solution {
                Derivation::Impl(_, _, _) => format!(
                    "{}, the impl in scope for the '{}' that {} requires",
                    self.describe(solution),
                    goal,
                    self.subject(&obligation.origin)
                ),
                _ => format!(
                    "{}, which provides the '{}' that {} requires",
                    self.describe(solution),
                    goal,
                    self.subject(&obligation.origin)
                ),
            },
            typed::Evidence::Given(_) => self.describe(solution),
            typed::Evidence::Impl(_, _, _) => match &obligation.origin {
                typed::Origin::Carried(signature) => format!(
                    "{}, as {} specifies",
                    self.describe(solution),
                    self.source(*signature)
                ),
                _ => self.describe(solution),
            },
            typed::Evidence::Super(inner, _) => {
                let projection = format!(
                    "the '{}' superclass evidence of {}",
                    goal,
                    self.explain(*inner)
                );
                match solution {
                    Derivation::Impl(_, _, _) => {
                        format!("{}, {}", self.describe(solution), projection)
                    }
                    _ => projection,
                }
            }
        }
    }
}

fn render_error(
    program: &typed::Program,
    renderer: &TypeRenderer,
    params: &IdVec<res::TypeParamId, raw::TypeParam>,
    def: &typed::ValDef,
    err: RawErrorKind,
) -> ErrorKind {
    let render_goal = |constr: &elab::TraitApp| render_constr(program, renderer, params, constr);
    match err {
        RawErrorKind::Solve(SolveError::NoImpl {
            goal,
            chain,
            importable,
            covered,
        }) => ErrorKind::NoImpl {
            constr: render_goal(&goal),
            required_by: chain.iter().rev().map(render_goal).collect(),
            importable: importable
                .into_iter()
                .map(|id| render_impl(program, id))
                .collect(),
            covered: covered
                .into_iter()
                .map(|id| render_impl(program, id))
                .collect(),
        },
        RawErrorKind::Solve(SolveError::Ambiguous { goal, candidates }) => {
            ErrorKind::AmbiguousImpl {
                constr: render_goal(&goal),
                candidates: candidates
                    .into_iter()
                    .map(|id| render_impl(program, id))
                    .collect(),
            }
        }
        RawErrorKind::Solve(SolveError::CyclicConstrs { impl_ }) => ErrorKind::CyclicConstrs {
            impl_: render_impl(program, impl_),
        },
        RawErrorKind::Solve(SolveError::Facts(never)) => match never {},
        RawErrorKind::ConflictingEvidence {
            located,
            other,
            solutions,
        } => {
            let explainer = Explainer {
                program,
                renderer,
                params,
                def,
                solutions: &solutions,
            };
            ErrorKind::ConflictingEvidence {
                constr: render_constr(program, renderer, params, &def.obligations[located].goal),
                located: explainer.explain(located),
                other: explainer.explain(other),
            }
        }
    }
}

/// Replaces every obligation in a body type by its derivation.
fn subst_type(
    type_: &typed::Type,
    solutions: &IdVec<typed::ObligationId, Derivation>,
) -> solved::Type {
    type_.map_evidence(&mut |&obligation| solutions[obligation].clone())
}

fn subst_pattern(
    pat: &typed::Pattern,
    solutions: &IdVec<typed::ObligationId, Derivation>,
) -> solved::Pattern {
    match pat {
        typed::Pattern::Any(type_) => solved::Pattern::Any(subst_type(type_, solutions)),
        typed::Pattern::Var(type_) => solved::Pattern::Var(subst_type(type_, solutions)),
        typed::Pattern::Tuple(items) => solved::Pattern::Tuple(
            items
                .iter()
                .map(|item| subst_pattern(item, solutions))
                .collect(),
        ),
        typed::Pattern::Ctor(id, args, variant, content) => solved::Pattern::Ctor(
            *id,
            args.iter().map(|arg| subst_type(arg, solutions)).collect(),
            *variant,
            content
                .as_ref()
                .map(|content| Box::new(subst_pattern(content, solutions))),
        ),
        &typed::Pattern::NumConst(lit) => solved::Pattern::NumConst(lit),
        typed::Pattern::Span(lo, hi, content) => {
            solved::Pattern::Span(*lo, *hi, Box::new(subst_pattern(content, solutions)))
        }
    }
}

/// Replaces every obligation in a body by its derivation.
fn subst_expr(
    expr: &typed::Expr,
    solutions: &IdVec<typed::ObligationId, Derivation>,
) -> solved::Expr {
    match expr {
        typed::Expr::Global(id, type_args, obligations) => solved::Expr::Global(
            *id,
            type_args.map_refs(|_, arg| subst_type(arg, solutions)),
            obligations.map_refs(|_, &obligation| solutions[obligation].clone()),
        ),
        typed::Expr::TraitFunc(trait_, func, inst) => solved::Expr::TraitFunc(
            *trait_,
            *func,
            elab::TraitFuncInst {
                trait_args: inst
                    .trait_args
                    .map_refs(|_, arg| subst_type(arg, solutions)),
                trait_deriv: solutions[inst.trait_deriv].clone(),
                func_args: inst.func_args.map_refs(|_, arg| subst_type(arg, solutions)),
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
            subst_type(arg_type, solutions),
            subst_type(ret_type, solutions),
            subst_pattern(pat, solutions),
            Box::new(subst_expr(body, solutions)),
            *prof_id,
        ),
        typed::Expr::App(purity, func, arg) => solved::Expr::App(
            *purity,
            Box::new(subst_expr(func, solutions)),
            Box::new(subst_expr(arg, solutions)),
        ),
        typed::Expr::Match(discrim, cases, type_) => solved::Expr::Match(
            Box::new(subst_expr(discrim, solutions)),
            cases
                .iter()
                .map(|(pat, body)| (subst_pattern(pat, solutions), subst_expr(body, solutions)))
                .collect(),
            subst_type(type_, solutions),
        ),
        typed::Expr::LetMany(bindings, body) => solved::Expr::LetMany(
            bindings
                .iter()
                .map(|(pat, rhs)| (subst_pattern(pat, solutions), subst_expr(rhs, solutions)))
                .collect(),
            Box::new(subst_expr(body, solutions)),
        ),
        typed::Expr::ArrayLit(type_, items) => solved::Expr::ArrayLit(
            subst_type(type_, solutions),
            items
                .iter()
                .map(|item| subst_expr(item, solutions))
                .collect(),
        ),
        &typed::Expr::NumLit(lit) => solved::Expr::NumLit(lit),
        typed::Expr::Span(lo, hi, body) => {
            solved::Expr::Span(*lo, *hi, Box::new(subst_expr(body, solutions)))
        }
    }
}

fn solve_def(
    program: &typed::Program,
    facts: &ProgramFacts,
    val_id: res::CustomGlobalId,
    def: &typed::ValDef,
) -> Result<solved::ValDef, RawError> {
    let symbols = &program.val_symbols[val_id];
    let givens = infallible(closed_givens(
        facts,
        def.scheme
            .trait_constrs
            .iter()
            .map(|(given, constr)| (constr.clone(), Derivation::Given(given)))
            .collect(),
    ));
    let solver = Solver {
        facts,
        scope: &program.impl_scope[symbols.mod_],
        givens: &givens,
    };
    let mut resolver = Resolver {
        def,
        facts,
        solver: &solver,
        solutions: def.obligations.map_refs(|_, _| Memo::Pending),
    };

    let solutions = def.obligations.try_map_refs(|id, _| resolver.resolve(id))?;

    // The derivations are normalized, so structural equality is equality of evidence.
    for &(expected, actual) in &def.evidence_equations {
        if solutions[expected] != solutions[actual] {
            // Point at a side that arose in the body if there is one, since an obligation from
            // the definition's own signature is located at the whole definition.
            let from_own_signature = |id: typed::ObligationId| {
                matches!(
                    def.obligations[id].origin,
                    typed::Origin::OwnConstr(_) | typed::Origin::Carried(typed::Signature::Own)
                )
            };
            let (located, other) = if from_own_signature(actual) && !from_own_signature(expected) {
                (expected, actual)
            } else {
                (actual, expected)
            };
            return Err(RawError {
                kind: RawErrorKind::ConflictingEvidence {
                    located,
                    other,
                    solutions: solutions.clone(),
                },
                span: def.obligations[located].span,
            });
        }
    }

    Ok(solved::ValDef {
        scheme: def.scheme.clone(),
        body: subst_expr(&def.body, &solutions),
    })
}

pub fn solve_traits_in_bodies(program: typed::Program) -> Result<solved::Program, Error> {
    let vals = {
        let renderer = TypeRenderer::new(&program.mod_symbols, &program.custom_type_symbols);
        let facts = ProgramFacts { program: &program };

        program.vals.try_map_refs(|val_id, def| {
            let symbols = &program.val_symbols[val_id];
            let file = &program.mod_symbols[symbols.mod_].file;
            solve_def(&program, &facts, val_id, def).map_err(|err| {
                let kind = render_error(
                    &program,
                    &renderer,
                    &symbols.type_param_names,
                    def,
                    err.kind,
                );
                let (lo, hi) = err.span;
                Error(locate_path(file)(locate_span(lo, hi)(kind.into())))
            })
        })?
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
        impls: program.impls,
        impl_symbols: program.impl_symbols,
        main: program.main,
    })
}
