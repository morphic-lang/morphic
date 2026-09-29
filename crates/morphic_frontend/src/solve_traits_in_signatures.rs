//! Solves the evidence every written type carries.  A type constructor declared with trait
//! constraints, like `type Set a where Ord a`, carries evidence for each of them wherever it
//! occurs, so that a
//! `Set Int` built under one `Ord Int` impl is a different type from one built under another.
//! This pass solves for that evidence in every signature, type declaration, trait and impl,
//! before inference, so that inference can unify the evidence structurally.
//!
//! Each item's own trait constraints are its givens.  A constraint whose arguments mention no
//! constrained type needs no evidence itself; those constraints, closed under superclasses, are the
//! givens available to the others, and all of them together are the givens for the item's types.
//! Impl heads, type constraints and trait superclasses are elaborated on demand, since solving may
//! need them in any order, and a dependency of one on itself is an error.

use crate::data::elaborated_ast as elab;
use crate::data::elaborated_ast::{Derivation, Subst, TraitApp, TraitGiven, TraitSelfConstr, Type};
use crate::data::kinded_ast as kinded;
use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;
use crate::data::resolved_ast::{
    CustomGlobalId, CustomImplId, CustomTraitId, CustomTypeId, ImplId, SuperId, TraitConstrId,
    TraitFuncId, TraitId, TypeParamId,
};
use crate::file_cache::FileCache;
use crate::report_type::{self, TypeRenderer};
use crate::trait_solver::{
    add_referenced_givens, closed_givens, normalize_trait_app, normalize_type, Facts, ImplFacts,
    SolveError, Solver,
};
use id_collections::{Count, Id, IdVec};
use morphic_common::report_error::{locate_path, locate_span, ColorMode, Locate, Reportable};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::path::Path;

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
    CyclicConstrs {
        impl_: String,
    },
    PartialConstrained {
        type_: String,
        given: usize,
        expected: usize,
    },
    Cyclic {
        item: String,
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
                    "This type mentions a type constructor with trait constraints, so it needs evidence \
                     for the trait constraint\n\n    {}\n\nbut I couldn't find an impl in scope \
                     for it.\n\n",
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
                     together with the trait constraints of the enclosing item that mention no \
                     constrained type.",
                );
                ("No Impl in Scope", message)
            }

            ErrorKind::AmbiguousImpl { constr, candidates } => (
                "Ambiguous Impl",
                format!(
                    "This type needs evidence for the trait constraint\n\n    {}\n\nbut more \
                     than one impl in scope matches it, namely:\n\n{}\n\nExactly one impl has to \
                     match; adjust which impls are imported so that only one does.",
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

            ErrorKind::PartialConstrained {
                type_,
                given,
                expected,
            } => (
                "Partially Applied Constrained Type",
                format!(
                    "The type '{}' is declared with trait constraints that mention its first {} \
                     parameters, so it has to be applied to at least that many arguments wherever \
                     it occurs, but here it is applied to {}.\n\nA type with constraints carries \
                     evidence for them, which is only determined once the arguments the \
                     constraints mention are known.",
                    type_, expected, given
                ),
            ),

            ErrorKind::Cyclic { item } => (
                "Cyclic Signature",
                format!(
                    "Working out the evidence that {} carries requires {} itself.",
                    item, item
                ),
            ),
        })
    }

    fn exit_status(&self) -> i32 {
        1
    }
}

/// An error found while elaborating one type, located by a path into that type.
#[derive(Clone, Debug)]
enum RawErrorKind<G> {
    NoImpl {
        goal: TraitApp<Derivation<G>>,
        chain: Vec<TraitApp<Derivation<G>>>,
        importable: Vec<ImplId>,
    },
    Ambiguous {
        goal: TraitApp<Derivation<G>>,
        candidates: Vec<ImplId>,
    },
    CyclicConstrs {
        impl_: ImplId,
    },
    PartialConstrained {
        type_: CustomTypeId,
        given: usize,
    },
    /// The constraints of a type refer to each other's evidence in a cycle.
    CyclicTypeConstrs {
        type_: CustomTypeId,
    },
}

#[derive(Clone, Debug)]
struct RawError<G> {
    kind: RawErrorKind<G>,
    path: Vec<usize>,
}

/// Either an error in the type being elaborated, or one already located in some other item
/// that this one depends on.
#[derive(Debug)]
enum ElabError<G> {
    Raw(RawError<G>),
    Nested(Error),
}

impl<G> From<Error> for ElabError<G> {
    fn from(err: Error) -> Self {
        ElabError::Nested(err)
    }
}

fn raw<G>(kind: RawErrorKind<G>, path: &[usize]) -> ElabError<G> {
    ElabError::Raw(RawError {
        kind,
        path: path.to_vec(),
    })
}

fn raw_solve<G>(err: SolveError<G, Error>, path: &[usize]) -> ElabError<G> {
    match err {
        SolveError::NoImpl {
            goal,
            chain,
            importable,
        } => raw(
            RawErrorKind::NoImpl {
                goal,
                chain,
                importable,
            },
            path,
        ),
        SolveError::Ambiguous { goal, candidates } => {
            raw(RawErrorKind::Ambiguous { goal, candidates }, path)
        }
        SolveError::CyclicConstrs { impl_ } => raw(RawErrorKind::CyclicConstrs { impl_ }, path),
        SolveError::Facts(err) => ElabError::Nested(err),
    }
}

fn with_child<R>(
    path: &mut Vec<usize>,
    index: usize,
    body: impl FnOnce(&mut Vec<usize>) -> R,
) -> R {
    path.push(index);
    let result = body(path);
    path.pop();
    result
}

enum Memo<T> {
    Pending,
    InProgress,
    Done(T),
}

/// The givens available while elaborating types in one item, closed under superclasses.
type Givens<G> = Vec<(TraitApp<Derivation<G>>, Derivation<G>)>;

struct Elaborator<'a> {
    program: &'a kinded::Program,
    /// The impl func each value definition implements, if any.
    impl_funcs: BTreeMap<CustomGlobalId, (CustomImplId, TraitFuncId)>,
    typedef_constrs: RefCell<IdVec<CustomTypeId, Memo<IdVec<TraitConstrId, elab::TraitApp>>>>,
    trait_supers:
        RefCell<IdVec<CustomTraitId, Memo<IdVec<SuperId, TraitApp<Derivation<TraitSelfConstr>>>>>>,
    impl_facts: RefCell<IdVec<CustomImplId, Memo<ImplFacts>>>,
    impl_supers: RefCell<IdVec<CustomImplId, Memo<IdVec<SuperId, elab::Derivation>>>>,
}

/// Runs `compute` once for `id`, remembering its result; a request for `id` while it is being
/// computed is a cycle, reported by `cycle`.
fn memoized<I: Id, T: Clone>(
    table: &RefCell<IdVec<I, Memo<T>>>,
    id: I,
    cycle: impl FnOnce() -> Error,
    compute: impl FnOnce() -> Result<T, Error>,
) -> Result<T, Error> {
    match &table.borrow()[id] {
        Memo::Done(value) => return Ok(value.clone()),
        Memo::InProgress => return Err(cycle()),
        Memo::Pending => {}
    }
    table.borrow_mut()[id] = Memo::InProgress;
    let result = compute();
    table.borrow_mut()[id] = match &result {
        Ok(value) => Memo::Done(value.clone()),
        Err(_) => Memo::Pending,
    };
    result
}

impl<'a> Facts for Elaborator<'a> {
    type Error = Error;

    fn supers(
        &self,
        trait_: TraitId,
    ) -> Result<IdVec<SuperId, TraitApp<Derivation<TraitSelfConstr>>>, Error> {
        let TraitId::Custom(custom) = trait_;
        self.trait_supers_of(custom)
    }

    fn impl_facts(&self, id: ImplId) -> Result<ImplFacts, Error> {
        let ImplId::Custom(custom) = id;
        self.impl_facts_of(custom)
    }

    fn impl_supers(&self, id: ImplId) -> Result<IdVec<SuperId, elab::Derivation>, Error> {
        let ImplId::Custom(custom) = id;
        self.impl_supers_of(custom)
    }

    fn all_impls(&self) -> Vec<ImplId> {
        self.program
            .impls
            .iter()
            .map(|(id, _)| ImplId::Custom(id))
            .collect()
    }

    fn constrained_prefix(&self, id: CustomTypeId) -> Count<TypeParamId> {
        self.program.custom_types[id].constrained_prefix()
    }
}

impl<'a> Elaborator<'a> {
    fn new(program: &'a kinded::Program) -> Self {
        let mut impl_funcs = BTreeMap::new();
        for (impl_id, def) in &program.impls {
            for (func_id, &val_id) in &def.funcs {
                impl_funcs.insert(val_id, (impl_id, func_id));
            }
        }
        Elaborator {
            program,
            impl_funcs,
            typedef_constrs: RefCell::new(program.custom_types.map_refs(|_, _| Memo::Pending)),
            trait_supers: RefCell::new(program.traits.map_refs(|_, _| Memo::Pending)),
            impl_facts: RefCell::new(program.impls.map_refs(|_, _| Memo::Pending)),
            impl_supers: RefCell::new(program.impls.map_refs(|_, _| Memo::Pending)),
        }
    }

    fn file(&self, mod_: res::ModId) -> &'a Path {
        &self.program.mod_symbols[mod_].file
    }

    fn is_constrained(&self, id: CustomTypeId) -> bool {
        !self.program.custom_types[id].trait_constrs.is_empty()
    }

    fn mentions_constrained(&self, type_: &res::Type) -> bool {
        match type_ {
            res::Type::App(head, args) => {
                matches!(head, res::TypeHead::Ctor(res::TypeId::Custom(id)) if self.is_constrained(*id))
                    || args.iter().any(|arg| self.mentions_constrained(arg))
            }
            res::Type::Tuple(items) => items.iter().any(|item| self.mentions_constrained(item)),
            res::Type::Func(_, arg, ret) => {
                self.mentions_constrained(arg) || self.mentions_constrained(ret)
            }
        }
    }

    // ---- error rendering ----

    fn render_impl(&self, id: ImplId) -> String {
        let ImplId::Custom(custom) = id;
        let symbols = &self.program.impl_symbols[custom];
        format!(
            "{} (in {})",
            symbols.impl_name.0,
            self.file(symbols.mod_).display()
        )
    }

    fn render_constr<G>(
        &self,
        params: &IdVec<TypeParamId, raw::TypeParam>,
        app: &TraitApp<Derivation<G>>,
    ) -> String {
        let renderer =
            TypeRenderer::new(&self.program.mod_symbols, &self.program.custom_type_symbols);
        renderer.render_trait_app(
            params,
            &report_type::TraitApp::from_elab(app),
            &self.program.trait_symbols,
        )
    }

    fn error(&self, kind: ErrorKind, file: &Path, span: Option<(usize, usize)>) -> Error {
        let mut located: Locate<ErrorKind> = kind.into();
        located = locate_path(file)(located);
        if let Some((lo, hi)) = span {
            located = locate_span(lo, hi)(located);
        }
        Error(located)
    }

    /// Locates an error found in a type, using the type's spans if it has any.
    fn locate<G>(
        &self,
        err: ElabError<G>,
        params: &IdVec<TypeParamId, raw::TypeParam>,
        file: &Path,
        type_spans: Option<&res::TypeSpans>,
        fallback: Option<(usize, usize)>,
    ) -> Error {
        let RawError { kind, path } = match err {
            ElabError::Nested(err) => return err,
            ElabError::Raw(raw) => raw,
        };
        let span = type_spans
            .and_then(|spans| spans.span_at(&path))
            .or(fallback);
        let kind = match kind {
            RawErrorKind::NoImpl {
                goal,
                chain,
                importable,
            } => ErrorKind::NoImpl {
                constr: self.render_constr(params, &goal),
                required_by: chain
                    .iter()
                    .rev()
                    .map(|constr| self.render_constr(params, constr))
                    .collect(),
                importable: importable
                    .into_iter()
                    .map(|id| self.render_impl(id))
                    .collect(),
            },
            RawErrorKind::Ambiguous { goal, candidates } => ErrorKind::AmbiguousImpl {
                constr: self.render_constr(params, &goal),
                candidates: candidates
                    .into_iter()
                    .map(|id| self.render_impl(id))
                    .collect(),
            },
            RawErrorKind::CyclicConstrs { impl_ } => ErrorKind::CyclicConstrs {
                impl_: self.render_impl(impl_),
            },
            RawErrorKind::PartialConstrained { type_, given } => ErrorKind::PartialConstrained {
                type_: self.program.custom_type_symbols[type_].type_name.0.clone(),
                given,
                expected: self.constrained_prefix(type_).to_value(),
            },
            RawErrorKind::CyclicTypeConstrs { type_ } => ErrorKind::Cyclic {
                item: format!(
                    "the constrs of the type '{}'",
                    self.program.custom_type_symbols[type_].type_name.0
                ),
            },
        };
        self.error(kind, file, span)
    }

    // ---- elaborating types ----

    fn elab_type<G: Clone + Eq + Ord>(
        &self,
        solver: &Solver<G, Self>,
        path: &mut Vec<usize>,
        type_: &res::Type,
    ) -> Result<Type<Derivation<G>>, ElabError<G>> {
        match type_ {
            res::Type::App(head, args) => {
                let args = self.elab_children(solver, path, args)?;
                match head {
                    res::TypeHead::Ctor(res::TypeId::Custom(id)) if self.is_constrained(*id) => {
                        if args.len() < self.constrained_prefix(*id).to_value() {
                            return Err(raw(
                                RawErrorKind::PartialConstrained {
                                    type_: *id,
                                    given: args.len(),
                                },
                                path,
                            ));
                        }
                        let evidence = self.type_evidence(solver, path, *id, &args)?;
                        Ok(Type::Constrained(*id, args, evidence))
                    }
                    _ => Ok(Type::App(*head, args)),
                }
            }
            res::Type::Tuple(items) => Ok(Type::Tuple(self.elab_children(solver, path, items)?)),
            res::Type::Func(purity, arg, ret) => {
                let arg = with_child(path, 0, |path| self.elab_type(solver, path, arg))?;
                let ret = with_child(path, 1, |path| self.elab_type(solver, path, ret))?;
                Ok(Type::Func(*purity, Box::new(arg), Box::new(ret)))
            }
        }
    }

    fn elab_children<G: Clone + Eq + Ord>(
        &self,
        solver: &Solver<G, Self>,
        path: &mut Vec<usize>,
        types: &[res::Type],
    ) -> Result<Vec<Type<Derivation<G>>>, ElabError<G>> {
        types
            .iter()
            .enumerate()
            .map(|(index, type_)| {
                with_child(path, index, |path| self.elab_type(solver, path, type_))
            })
            .collect()
    }

    /// Elaborates a trait constraint; the path of each argument starts at its index.
    fn elab_trait_app<G: Clone + Eq + Ord>(
        &self,
        solver: &Solver<G, Self>,
        app: &res::TraitApp,
    ) -> Result<TraitApp<Derivation<G>>, ElabError<G>> {
        Ok(TraitApp {
            trait_: app.trait_,
            args: self.elab_children(solver, &mut Vec::new(), &app.args)?,
        })
    }

    /// The evidence for each constraint of a constrained type at the given arguments.  A
    /// constraint may refer to the evidence of another (see `typedef_constrs_of`), which is
    /// established first.
    fn type_evidence<G: Clone + Eq + Ord>(
        &self,
        solver: &Solver<G, Self>,
        path: &[usize],
        id: CustomTypeId,
        args: &[Type<Derivation<G>>],
    ) -> Result<IdVec<TraitConstrId, Derivation<G>>, ElabError<G>> {
        // The constraints mention no parameter beyond the arguments given.
        let args = IdVec::from_vec(args.to_vec());
        let constrs = self.typedef_constrs_of(id)?;
        let mut evidence: IdVec<TraitConstrId, Option<Derivation<G>>> =
            constrs.map_refs(|_, _| None);
        let mut in_progress = BTreeSet::new();
        for (constr, _) in &constrs {
            self.constr_evidence(
                solver,
                path,
                id,
                &constrs,
                &args,
                &mut evidence,
                &mut in_progress,
                constr,
            )?;
        }
        Ok(evidence.map(|_, deriv| deriv.expect("every constraint was solved")))
    }

    fn constr_evidence<G: Clone + Eq + Ord>(
        &self,
        solver: &Solver<G, Self>,
        path: &[usize],
        id: CustomTypeId,
        constrs: &IdVec<TraitConstrId, elab::TraitApp>,
        args: &IdVec<TypeParamId, Type<Derivation<G>>>,
        evidence: &mut IdVec<TraitConstrId, Option<Derivation<G>>>,
        in_progress: &mut BTreeSet<TraitConstrId>,
        constr: TraitConstrId,
    ) -> Result<(), ElabError<G>> {
        if evidence[constr].is_some() {
            return Ok(());
        }
        if !in_progress.insert(constr) {
            return Err(raw(RawErrorKind::CyclicTypeConstrs { type_: id }, path));
        }
        let mut referenced = BTreeSet::new();
        add_referenced_givens(&constrs[constr], &mut referenced);
        for other in referenced {
            self.constr_evidence(
                solver,
                path,
                id,
                constrs,
                args,
                evidence,
                in_progress,
                other,
            )?;
        }
        let goal = {
            let subst = Subst {
                types: args,
                givens: &|other: &TraitConstrId| {
                    evidence[*other]
                        .clone()
                        .expect("referenced constraints were solved first")
                },
            };
            normalize_trait_app(self, &subst.trait_app(&constrs[constr]))?
        };
        let deriv = solver
            .solve(&goal, &mut Vec::new())
            .map_err(|err| raw_solve(err, path))?;
        evidence[constr] = Some(deriv);
        Ok(())
    }

    /// Elaborates the constraints of an item.  Those whose arguments mention no constrained type
    /// need no evidence themselves and, closed under superclasses and together with `base`, are
    /// the givens for the others.  Returns the constraints and the givens for the item's types:
    /// all of its constraints closed under superclasses, together with `base`.  An error names
    /// the constraint it was found in.
    fn elab_constrs<G: Clone + Eq + Ord, I: Id + Copy>(
        &self,
        scope: &BTreeSet<ImplId>,
        base: &Givens<G>,
        constrs: &IdVec<I, res::TraitApp>,
        given_of: impl Fn(I) -> Derivation<G>,
    ) -> Result<(IdVec<I, TraitApp<Derivation<G>>>, Givens<G>), (Option<I>, ElabError<G>)> {
        let nested = |err: Error| (None, ElabError::Nested(err));

        // `base` is already closed by the caller, and closing it again could require the
        // item's own superclasses, which may be what is being elaborated.
        let no_givens = Solver {
            facts: self,
            scope,
            givens: &[],
        };
        let mut simple = Vec::new();
        let mut elaborated: IdVec<I, Option<TraitApp<Derivation<G>>>> =
            constrs.map_refs(|_, _| None);
        for (id, constr) in constrs {
            if !constr.args.iter().any(|arg| self.mentions_constrained(arg)) {
                let app = self
                    .elab_trait_app(&no_givens, constr)
                    .map_err(|err| (Some(id), err))?;
                simple.push((app.clone(), given_of(id)));
                elaborated[id] = Some(app);
            }
        }
        let simple: Givens<G> = base
            .iter()
            .cloned()
            .chain(closed_givens(self, simple).map_err(nested)?)
            .collect();

        let solver = Solver {
            facts: self,
            scope,
            givens: &simple,
        };
        for (id, constr) in constrs {
            if elaborated[id].is_none() {
                let app = self
                    .elab_trait_app(&solver, constr)
                    .map_err(|err| (Some(id), err))?;
                elaborated[id] = Some(app);
            }
        }
        let elaborated = elaborated.map(|_, app| app.expect("every constraint was elaborated"));

        let all = elaborated
            .iter()
            .map(|(id, app)| (app.clone(), given_of(id)))
            .collect();
        let givens = base
            .iter()
            .cloned()
            .chain(closed_givens(self, all).map_err(nested)?)
            .collect();
        Ok((elaborated, givens))
    }

    // ---- items ----

    fn typedef_constrs_of(
        &self,
        id: CustomTypeId,
    ) -> Result<IdVec<TraitConstrId, elab::TraitApp>, Error> {
        let symbols = &self.program.custom_type_symbols[id];
        let file = self.file(symbols.mod_);
        memoized(
            &self.typedef_constrs,
            id,
            || {
                self.error(
                    ErrorKind::Cyclic {
                        item: format!("the constrs of the type '{}'", symbols.type_name.0),
                    },
                    file,
                    symbols.constr_spans.values().next().copied(),
                )
            },
            || {
                let def = &self.program.custom_types[id];
                let (constrs, _) = self
                    .elab_constrs(
                        &self.program.impl_scope[symbols.mod_],
                        &Vec::new(),
                        &def.trait_constrs,
                        Derivation::Given,
                    )
                    .map_err(|(constr, err)| {
                        let span = constr.map(|constr| symbols.constr_spans[constr]);
                        self.locate(err, &symbols.type_param_names, file, None, span)
                    })?;
                Ok(constrs)
            },
        )
    }

    fn typedef_variants_of(
        &self,
        id: CustomTypeId,
    ) -> Result<IdVec<res::VariantId, Option<elab::Type>>, Error> {
        let def = &self.program.custom_types[id];
        let symbols = &self.program.custom_type_symbols[id];
        let file = self.file(symbols.mod_);
        let constrs = self.typedef_constrs_of(id)?;
        let givens = closed_givens(
            self,
            constrs
                .iter()
                .map(|(constr, app)| (app.clone(), Derivation::Given(constr)))
                .collect(),
        )?;
        let solver = Solver {
            facts: self,
            scope: &self.program.impl_scope[symbols.mod_],
            givens: &givens,
        };
        def.variants
            .try_map_refs(|variant_id, variant| match variant {
                None => Ok(None),
                Some(type_) => {
                    let variant_symbols = &symbols.variant_symbols[variant_id];
                    self.elab_type(&solver, &mut Vec::new(), type_)
                        .map(Some)
                        .map_err(|err| {
                            self.locate(
                                err,
                                &symbols.type_param_names,
                                file,
                                variant_symbols.content_spans.as_ref(),
                                Some(variant_symbols.span),
                            )
                        })
                }
            })
    }

    /// The trait's own constraint, over its parameters.
    fn self_constr<G>(&self, id: CustomTraitId) -> TraitApp<Derivation<G>> {
        TraitApp {
            trait_: TraitId::Custom(id),
            args: self.program.traits[id]
                .param_kinds
                .iter()
                .map(|(param, _)| Type::param(param))
                .collect(),
        }
    }

    fn trait_supers_of(
        &self,
        id: CustomTraitId,
    ) -> Result<IdVec<SuperId, TraitApp<Derivation<TraitSelfConstr>>>, Error> {
        let symbols = &self.program.trait_symbols[id];
        let file = self.file(symbols.mod_);
        memoized(
            &self.trait_supers,
            id,
            || {
                self.error(
                    ErrorKind::Cyclic {
                        item: format!("the superclasses of the trait '{}'", symbols.trait_name.0),
                    },
                    file,
                    symbols.super_spans.values().next().copied(),
                )
            },
            || {
                let def = &self.program.traits[id];
                // The trait's own constraint is available as evidence, but its superclasses
                // are what is being elaborated, so it is not closed under them.
                let base = vec![(self.self_constr(id), Derivation::Given(TraitSelfConstr))];
                let (supers, _) = self
                    .elab_constrs(
                        &self.program.impl_scope[symbols.mod_],
                        &base,
                        &def.supers,
                        |super_id| {
                            Derivation::Super(
                                Box::new(Derivation::Given(TraitSelfConstr)),
                                super_id,
                            )
                        },
                    )
                    .map_err(|(super_id, err)| {
                        let span = super_id.map(|super_id| symbols.super_spans[super_id]);
                        self.locate(err, &symbols.type_param_names, file, None, span)
                    })?;
                Ok(supers)
            },
        )
    }

    fn trait_func_sig(
        &self,
        trait_id: CustomTraitId,
        func_id: TraitFuncId,
    ) -> Result<elab::TraitFuncSig, Error> {
        let def = &self.program.traits[trait_id];
        let sig = &def.funcs[func_id];
        let symbols = &self.program.trait_symbols[trait_id];
        let func_symbols = &symbols.func_symbols[func_id];
        let file = self.file(symbols.mod_);
        let scope = &self.program.impl_scope[symbols.mod_];

        // The givens: the trait's own constraint, its superclasses, and the func's own
        // constraints, all closed under superclasses.
        let identity: IdVec<TypeParamId, Type<Derivation<TraitGiven>>> =
            def.param_kinds.map_refs(|param, _| Type::param(param));
        let to_func_given = Subst {
            types: &identity,
            givens: &|TraitSelfConstr| Derivation::Given(TraitGiven::SelfConstr),
        };
        let mut base = vec![(
            self.self_constr(trait_id),
            Derivation::Given(TraitGiven::SelfConstr),
        )];
        for (super_id, super_) in &self.trait_supers_of(trait_id)? {
            base.push((
                to_func_given.trait_app(super_),
                Derivation::Super(
                    Box::new(Derivation::Given(TraitGiven::SelfConstr)),
                    super_id,
                ),
            ));
        }
        let base = closed_givens(self, base)?;

        let (own_constrs, givens) = self
            .elab_constrs(scope, &base, &sig.own_constrs, |constr| {
                Derivation::Given(TraitGiven::Own(constr))
            })
            .map_err(|(constr, err)| {
                let span = constr.map(|constr| func_symbols.constr_spans[constr]);
                self.locate(err, &func_symbols.type_param_names, file, None, span)
            })?;

        let solver = Solver {
            facts: self,
            scope,
            givens: &givens,
        };
        let body = self
            .elab_type(&solver, &mut Vec::new(), &sig.body)
            .map_err(|err| {
                self.locate(
                    err,
                    &func_symbols.type_param_names,
                    file,
                    Some(&func_symbols.type_spans),
                    Some(func_symbols.span),
                )
            })?;

        Ok(elab::TraitFuncSig {
            own_param_kinds: sig.own_param_kinds.clone(),
            own_constrs,
            body,
        })
    }

    fn impl_facts_of(&self, id: CustomImplId) -> Result<ImplFacts, Error> {
        let symbols = &self.program.impl_symbols[id];
        let file = self.file(symbols.mod_);
        memoized(
            &self.impl_facts,
            id,
            || {
                self.error(
                    ErrorKind::Cyclic {
                        item: format!("the head of the impl '{}'", symbols.impl_name.0),
                    },
                    file,
                    Some(symbols.head_span),
                )
            },
            || {
                let def = &self.program.impls[id];
                let scope = &self.program.impl_scope[symbols.mod_];
                let (trait_constrs, givens) = self
                    .elab_constrs(scope, &Vec::new(), &def.trait_constrs, Derivation::Given)
                    .map_err(|(constr, err)| {
                        let span = constr.map(|constr| symbols.constr_spans[constr]);
                        self.locate(err, &symbols.type_param_names, file, None, span)
                    })?;
                let solver = Solver {
                    facts: self,
                    scope,
                    givens: &givens,
                };
                let head = self
                    .elab_children(&solver, &mut Vec::new(), &def.head)
                    .map_err(|err| {
                        self.locate(
                            err,
                            &symbols.type_param_names,
                            file,
                            None,
                            Some(symbols.head_span),
                        )
                    })?;
                Ok(ImplFacts {
                    trait_: def.trait_,
                    num_params: def.param_kinds.count(),
                    head,
                    trait_constrs,
                })
            },
        )
    }

    /// The derivation an impl stands for, over its own parameters and givens.
    fn self_derivation(&self, id: CustomImplId, facts: &ImplFacts) -> elab::Derivation {
        Derivation::Impl(
            ImplId::Custom(id),
            IdVec::from_count_with(facts.num_params, Type::param),
            facts
                .trait_constrs
                .map_refs(|given, _| Derivation::Given(given)),
        )
    }

    fn impl_supers_of(&self, id: CustomImplId) -> Result<IdVec<SuperId, elab::Derivation>, Error> {
        let symbols = &self.program.impl_symbols[id];
        let file = self.file(symbols.mod_);
        memoized(
            &self.impl_supers,
            id,
            || {
                self.error(
                    ErrorKind::Cyclic {
                        item: format!(
                            "the superclass evidence of the impl '{}'",
                            symbols.impl_name.0
                        ),
                    },
                    file,
                    Some(symbols.head_span),
                )
            },
            || {
                let facts = self.impl_facts_of(id)?;
                let givens = closed_givens(
                    self,
                    facts
                        .trait_constrs
                        .iter()
                        .map(|(given, app)| (app.clone(), Derivation::Given(given)))
                        .collect(),
                )?;
                let solver = Solver {
                    facts: self,
                    scope: &self.program.impl_scope[symbols.mod_],
                    givens: &givens,
                };
                let head = IdVec::from_vec(facts.head.clone());
                let self_deriv = self.self_derivation(id, &facts);
                let at_head = Subst {
                    types: &head,
                    givens: &|TraitSelfConstr| self_deriv.clone(),
                };
                self.supers(facts.trait_)?.try_map_refs(|_, super_| {
                    let goal = normalize_trait_app(self, &at_head.trait_app(super_))?;
                    solver.solve(&goal, &mut Vec::new()).map_err(|err| {
                        self.locate(
                            raw_solve(err, &[]),
                            &symbols.type_param_names,
                            file,
                            None,
                            Some(symbols.head_span),
                        )
                    })
                })
            },
        )
    }

    /// The scheme of the definition implementing a trait func: the trait's signature at the
    /// impl's head, where the trait's own constraint is the impl itself and the func's own
    /// constraints follow the impl's, as `ImplFuncLayout` describes.
    fn impl_func_scheme(
        &self,
        impl_id: CustomImplId,
        func_id: TraitFuncId,
        sig: &elab::TraitFuncSig,
    ) -> Result<elab::TypeScheme, Error> {
        let def = &self.program.impls[impl_id];
        let facts = self.impl_facts_of(impl_id)?;
        let layout = def.func_layout();
        let TraitId::Custom(custom_trait) = def.trait_;
        let trait_layout = self.program.traits[custom_trait].func_layout(func_id);

        let types = trait_layout.params(
            IdVec::from_vec(facts.head.clone()),
            IdVec::from_count_with(trait_layout.num_own_params, |param| {
                Type::param(layout.own_param(param))
            }),
        );
        let self_deriv = self.self_derivation(impl_id, &facts);
        let subst = Subst {
            types: &types,
            givens: &|given: &TraitGiven| match given {
                TraitGiven::SelfConstr => self_deriv.clone(),
                TraitGiven::Own(constr) => Derivation::Given(layout.own_constr(*constr)),
            },
        };

        // Substituting the impl for the trait's own constraint puts an impl derivation under
        // the superclass projections the signature refers to, which normalization resolves.
        let own_constrs = sig
            .own_constrs
            .try_map_refs(|_, constr| normalize_trait_app(self, &subst.trait_app(constr)))?;
        let body = normalize_type(self, &subst.type_(&sig.body))?;

        Ok(elab::TypeScheme {
            param_kinds: layout.params(def.param_kinds.clone(), sig.own_param_kinds.clone()),
            trait_constrs: layout.constrs(facts.trait_constrs.clone(), own_constrs),
            body,
        })
    }

    fn val_scheme(
        &self,
        val_id: CustomGlobalId,
        trait_sigs: &IdVec<CustomTraitId, IdVec<TraitFuncId, elab::TraitFuncSig>>,
    ) -> Result<elab::TypeScheme, Error> {
        if let Some(&(impl_id, func_id)) = self.impl_funcs.get(&val_id) {
            let TraitId::Custom(custom_trait) = self.program.impls[impl_id].trait_;
            return self.impl_func_scheme(impl_id, func_id, &trait_sigs[custom_trait][func_id]);
        }

        let def = &self.program.vals[val_id];
        let symbols = &self.program.val_symbols[val_id];
        let file = self.file(symbols.mod_);
        let scope = &self.program.impl_scope[symbols.mod_];

        let (trait_constrs, givens) = self
            .elab_constrs(
                scope,
                &Vec::new(),
                &def.scheme.trait_constrs,
                Derivation::Given,
            )
            .map_err(|(constr, err)| {
                let span = constr.map(|constr| symbols.trait_constr_spans[constr]);
                self.locate(err, &symbols.type_param_names, file, None, span)
            })?;
        let solver = Solver {
            facts: self,
            scope,
            givens: &givens,
        };
        let body = self
            .elab_type(&solver, &mut Vec::new(), &def.scheme.body)
            .map_err(|err| {
                self.locate(
                    err,
                    &symbols.type_param_names,
                    file,
                    Some(&symbols.type_spans),
                    None,
                )
            })?;

        Ok(elab::TypeScheme {
            param_kinds: def.scheme.param_kinds.clone(),
            trait_constrs,
            body,
        })
    }
}

pub fn solve_traits_in_signatures(program: kinded::Program) -> Result<elab::Program, Error> {
    let (custom_types, traits, impls, val_schemes) = {
        let elaborator = Elaborator::new(&program);

        let custom_types = program.custom_types.try_map_refs(|id, def| {
            Ok::<_, Error>(elab::TypeDef {
                param_kinds: def.param_kinds.clone(),
                trait_constrs: elaborator.typedef_constrs_of(id)?,
                variants: elaborator.typedef_variants_of(id)?,
            })
        })?;

        let trait_sigs = program.traits.try_map_refs(|trait_id, def| {
            def.funcs
                .try_map_refs(|func_id, _| elaborator.trait_func_sig(trait_id, func_id))
        })?;
        let traits = program.traits.try_map_refs(|id, def| {
            Ok::<_, Error>(elab::TraitDef {
                param_kinds: def.param_kinds.clone(),
                supers: elaborator.trait_supers_of(id)?,
                funcs: trait_sigs[id].clone(),
            })
        })?;

        let impls = program.impls.try_map_refs(|id, def| {
            let facts = elaborator.impl_facts_of(id)?;
            Ok::<_, Error>(elab::ImplDef {
                trait_: def.trait_,
                param_kinds: def.param_kinds.clone(),
                head: facts.head,
                trait_constrs: facts.trait_constrs,
                supers: elaborator.impl_supers_of(id)?,
                funcs: def.funcs.clone(),
            })
        })?;

        let val_schemes = program
            .vals
            .try_map_refs(|id, _| elaborator.val_scheme(id, &trait_sigs))?;

        (custom_types, traits, impls, val_schemes)
    };

    let mut val_schemes = val_schemes.into_values();
    Ok(elab::Program {
        mod_symbols: program.mod_symbols,
        custom_types,
        custom_type_symbols: program.custom_type_symbols,
        profile_points: program.profile_points,
        vals: program.vals.map(|_, def| elab::ValDef {
            scheme: val_schemes.next().expect("one scheme per definition"),
            body: def.body,
        }),
        val_symbols: program.val_symbols,
        traits,
        trait_symbols: program.trait_symbols,
        impls,
        impl_symbols: program.impl_symbols,
        impl_scope: program.impl_scope,
        main: program.main,
    })
}
