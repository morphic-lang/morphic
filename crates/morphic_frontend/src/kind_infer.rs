//! Kind inference and checking for type declarations and value signatures.
//!
//! Kinds are simple. A type parameter applied to arguments gets a kind determined by those
//! arguments, a parameter that is never applied has kind `Type`, and there is no kind polymorphism.
//!
//! Every item is inferred in isolation from everything that does not precede it in the dependency
//! order, exactly as type checking works for values.  Type declarations are processed one
//! dependency group (strongly connected component) at a time: the group's parameters get fresh
//! kind variables, its variants are checked, and any variable still unconstrained afterwards is
//! defaulted to `Type` before the next group can see it.  So `type Phantom a { Phantom }` has kind
//! `Type -> Type` by virtue of its own declaration alone, and a later `Phantom Array` is an error
//! at that use rather than a retroactive change of `Phantom`'s kind.  Value signatures are then
//! checked one at a time against the fixed constructor kinds; a signature's kind variables are
//! local to it, so nothing outside a signature can influence it or be influenced by it.
//!
//! Type inference itself never needs kinds: unification is kind-agnostic provided its inputs are
//! well-kinded, which is exactly what this pass establishes.  The pass consumes the resolved
//! program and produces the kinded one, whose parameter lists record the inferred kinds for the
//! benefit of later passes.

use crate::data::kinded_ast as kinded;
use crate::data::resolved_ast as res;
use crate::file_cache::FileCache;
use id_collections::{id_type, Count, IdVec};
use morphic_common::lines;
use morphic_common::report_error::{locate_path, locate_span, ColorMode, Locate, Reportable};
use morphic_common::util::graph::{self, Graph};
use std::collections::{BTreeMap, BTreeSet};
use std::io;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    Mismatch {
        item: String,
        expected: String,
        actual: String,
    },
    Cyclic {
        item: String,
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
            ErrorKind::Mismatch {
                item,
                expected,
                actual,
            } => (
                "Kind Mismatch",
                format!(
                    lines![
                        "In {item}, I expected a type of kind",
                        "",
                        "    {expected}",
                        "",
                        "but found one of kind",
                        "",
                        "    {actual}",
                        "",
                        "A type parameter has to be used consistently: either always as an \
                         ordinary type, or always applied to the same number of arguments of the \
                         same kinds.  Here, 'Type' is the kind of ordinary types like Bool, 'Type -> Type' \
                         is the kind of types like 'Array', which need to be applied to one ordinary \
                         type to become an ordinary type, and so on.",
                    ],
                    item = item,
                    expected = expected,
                    actual = actual,
                ),
            ),

            ErrorKind::Cyclic { item } => (
                "Cyclic Kind",
                format!(
                    "In {}, a type parameter is applied to itself (directly or indirectly), so \
                     its kind would have to be infinitely big.",
                    item
                ),
            ),
        })
    }

    fn exit_status(&self) -> i32 {
        1
    }
}

#[id_type]
struct KindVar(usize);

// Kinds are represented in curried form during inference, because applying a head to one more
// argument only fixes the first parameter kind and leaves the rest to be discovered later.
#[derive(Clone, Debug)]
enum KindTerm {
    Type,
    Arrow(Box<KindTerm>, Box<KindTerm>),
    Var(KindVar),
}

#[derive(Clone, Copy, Debug)]
enum UnifyError {
    Mismatch,
    Cyclic,
}

/// The unification state for a single item or dependency group.  A fresh context is used for
/// each, so kind variables can never leak between items.
struct Context {
    bindings: IdVec<KindVar, Option<KindTerm>>,
}

impl Context {
    fn new() -> Self {
        Context {
            bindings: IdVec::new(),
        }
    }

    fn fresh(&mut self) -> KindTerm {
        KindTerm::Var(self.bindings.push(None))
    }

    fn shallow_resolve(&self, term: &KindTerm) -> KindTerm {
        let mut term = term.clone();
        while let KindTerm::Var(var) = &term {
            match &self.bindings[*var] {
                Some(bound) => term = bound.clone(),
                None => break,
            }
        }
        term
    }

    fn occurs(&self, var: KindVar, term: &KindTerm) -> bool {
        match self.shallow_resolve(term) {
            KindTerm::Type => false,
            KindTerm::Arrow(arg, ret) => self.occurs(var, &arg) || self.occurs(var, &ret),
            KindTerm::Var(other) => other == var,
        }
    }

    fn unify(&mut self, term1: &KindTerm, term2: &KindTerm) -> Result<(), UnifyError> {
        let term1 = self.shallow_resolve(term1);
        let term2 = self.shallow_resolve(term2);

        match (term1, term2) {
            (KindTerm::Var(var1), KindTerm::Var(var2)) if var1 == var2 => Ok(()),

            (KindTerm::Var(var), term) | (term, KindTerm::Var(var)) => {
                if self.occurs(var, &term) {
                    return Err(UnifyError::Cyclic);
                }
                self.bindings[var] = Some(term);
                Ok(())
            }

            (KindTerm::Type, KindTerm::Type) => Ok(()),

            (KindTerm::Arrow(arg1, ret1), KindTerm::Arrow(arg2, ret2)) => {
                self.unify(&arg1, &arg2)?;
                self.unify(&ret1, &ret2)
            }

            (KindTerm::Type, KindTerm::Arrow(_, _)) | (KindTerm::Arrow(_, _), KindTerm::Type) => {
                Err(UnifyError::Mismatch)
            }
        }
    }

    /// Converts a kind term to a `kinded::Kind`, defaulting any still-unconstrained variable to
    /// `Type`.
    fn to_kind(&self, term: &KindTerm) -> kinded::Kind {
        match self.shallow_resolve(term) {
            KindTerm::Type | KindTerm::Var(_) => kinded::Kind::TYPE,
            KindTerm::Arrow(arg, ret) => {
                let mut params = vec![self.to_kind(&arg)];
                params.extend(self.to_kind(&ret).0);
                kinded::Kind(params)
            }
        }
    }

    fn render(&self, term: &KindTerm) -> String {
        let mut result = String::new();
        self.render_to(term, &mut result, false);
        result
    }

    fn render_to(&self, term: &KindTerm, dest: &mut String, is_arrow_arg: bool) {
        match self.shallow_resolve(term) {
            KindTerm::Type | KindTerm::Var(_) => dest.push_str("Type"),
            KindTerm::Arrow(arg, ret) => {
                if is_arrow_arg {
                    dest.push('(');
                }
                self.render_to(&arg, dest, true);
                dest.push_str(" -> ");
                self.render_to(&ret, dest, false);
                if is_arrow_arg {
                    dest.push(')');
                }
            }
        }
    }
}

fn arrow_chain(params: impl DoubleEndedIterator<Item = KindTerm>) -> KindTerm {
    params.rev().fold(KindTerm::Type, |ret, arg| {
        KindTerm::Arrow(Box::new(arg), Box::new(ret))
    })
}

fn kind_to_term(kind: &kinded::Kind) -> KindTerm {
    arrow_chain(kind.0.iter().map(kind_to_term))
}

/// Where in an item an error occurred: either a path (sequence of child indices) into the type
/// being checked, which the caller maps to a span using the type's `TypeSpans`, or a span found
/// directly, as for annotations inside a body.
enum RawLocation {
    Path(Vec<usize>),
    Span(Option<(usize, usize)>),
}

/// An error at a particular point in a type, before it is attached to the item it occurred in.
struct RawError {
    kind: UnifyError,
    expected: String,
    actual: String,
    location: RawLocation,
}

struct Inference {
    ctx: Context,
    // The kinds of the type declarations whose dependency groups have already been processed.
    fixed: IdVec<res::CustomTypeId, Option<IdVec<res::TypeParamId, kinded::Kind>>>,
    // The parameters of the dependency group currently being inferred.
    pending: BTreeMap<res::CustomTypeId, IdVec<res::TypeParamId, KindTerm>>,
    // Likewise for traits, whose groups are processed after all type declarations.
    fixed_traits: IdVec<res::CustomTraitId, Option<IdVec<res::TypeParamId, kinded::Kind>>>,
    pending_traits: BTreeMap<res::CustomTraitId, IdVec<res::TypeParamId, KindTerm>>,
    // The position, within the type currently being checked, of the sub-term being visited (see
    // `RawLocation`).  Only ever modified through `with_child`, which keeps it balanced.
    path: Vec<usize>,
}

impl Inference {
    fn ctor_kind(&self, id: res::TypeId) -> KindTerm {
        match id {
            res::TypeId::Bool | res::TypeId::Num(_) => KindTerm::Type,
            res::TypeId::Array => {
                KindTerm::Arrow(Box::new(KindTerm::Type), Box::new(KindTerm::Type))
            }
            res::TypeId::Custom(custom) => match self.pending.get(&custom) {
                Some(params) => arrow_chain(params.iter().map(|(_, kind)| kind.clone())),
                None => {
                    let params = self.fixed[custom]
                        .as_ref()
                        .expect("dependency groups are processed before their dependents");
                    arrow_chain(params.iter().map(|(_, kind)| kind_to_term(kind)))
                }
            },
        }
    }

    /// Runs `body` while visiting the `index`-th child of the current sub-term, restoring the
    /// position afterwards whether or not `body` succeeds.
    fn with_child<R>(&mut self, index: usize, body: impl FnOnce(&mut Self) -> R) -> R {
        self.path.push(index);
        let result = body(self);
        self.path.pop();
        result
    }

    /// An error at the sub-term currently being visited.
    fn error(&self, kind: UnifyError, expected: &KindTerm, actual: &KindTerm) -> RawError {
        RawError {
            kind,
            expected: self.ctx.render(expected),
            actual: self.ctx.render(actual),
            location: RawLocation::Path(self.path.clone()),
        }
    }

    fn expect(&mut self, expected: &KindTerm, actual: &KindTerm) -> Result<(), RawError> {
        self.ctx
            .unify(expected, actual)
            .map_err(|kind| self.error(kind, expected, actual))
    }

    fn trait_param_kinds(&self, trait_: res::TraitId) -> Vec<KindTerm> {
        let custom = match trait_ {
            // Every builtin trait has one parameter, of kind `Type`.
            res::TraitId::Builtin(_) => return vec![KindTerm::Type],
            res::TraitId::Custom(custom) => custom,
        };
        match self.pending_traits.get(&custom) {
            Some(params) => params.iter().map(|(_, kind)| kind.clone()).collect(),
            None => self.fixed_traits[custom]
                .as_ref()
                .expect("trait dependency groups are processed before their dependents")
                .iter()
                .map(|(_, kind)| kind_to_term(kind))
                .collect(),
        }
    }

    /// Checks that a trait constraint applies its trait to arguments of the trait's parameter
    /// kinds.  Callers locate any error at the constraint as a whole.
    fn check_constr(
        &mut self,
        env: &IdVec<res::TypeParamId, KindTerm>,
        constr: &res::TraitApp,
    ) -> Result<(), RawError> {
        let param_kinds = self.trait_param_kinds(constr.trait_);
        debug_assert_eq!(param_kinds.len(), constr.args.len());
        for (param_kind, arg) in param_kinds.iter().zip(&constr.args) {
            let arg_kind = self.infer(env, arg)?;
            self.expect(param_kind, &arg_kind)?;
        }
        Ok(())
    }

    /// Infers the kind of a type, checking that every application inside it is well-kinded.
    fn infer(
        &mut self,
        env: &IdVec<res::TypeParamId, KindTerm>,
        type_: &res::Type,
    ) -> Result<KindTerm, RawError> {
        match type_ {
            res::Type::App(head, args) => {
                let mut kind = match head {
                    res::TypeHead::Ctor(id) => self.ctor_kind(*id),
                    res::TypeHead::Var(param) => env[param].clone(),
                };

                for (index, arg) in args.iter().enumerate() {
                    let arg_kind = self.with_child(index, |this| this.infer(env, arg))?;

                    match self.ctx.shallow_resolve(&kind) {
                        // The head's parameter kind is known, so the argument is checked against
                        // it and any error points at the argument.
                        KindTerm::Arrow(param_kind, rest) => {
                            self.with_child(index, |this| this.expect(&param_kind, &arg_kind))?;
                            kind = *rest;
                        }

                        // The head's kind is still being discovered, so this application is
                        // what determines it.  The variable is bound by unifying through `kind`
                        // rather than directly, so that the occurs check still runs: in `f f`
                        // the argument's kind is the very variable being bound.
                        KindTerm::Var(_) => {
                            let result = self.ctx.fresh();
                            let applied =
                                KindTerm::Arrow(Box::new(arg_kind), Box::new(result.clone()));
                            self.expect(&applied, &kind)?;
                            kind = result;
                        }

                        // The head is an ordinary type, which cannot be applied to anything.
                        KindTerm::Type => {
                            let applied =
                                KindTerm::Arrow(Box::new(arg_kind), Box::new(self.ctx.fresh()));
                            return Err(self.error(
                                UnifyError::Mismatch,
                                &applied,
                                &KindTerm::Type,
                            ));
                        }
                    }
                }

                Ok(kind)
            }

            res::Type::Tuple(items) => {
                for (index, item) in items.iter().enumerate() {
                    self.with_child(index, |this| this.check_is_type(env, item))?;
                }
                Ok(KindTerm::Type)
            }

            res::Type::Func(_, arg, ret) => {
                self.with_child(0, |this| this.check_is_type(env, arg))?;
                self.with_child(1, |this| this.check_is_type(env, ret))?;
                Ok(KindTerm::Type)
            }
        }
    }

    /// Checks that a type in value position has kind `Type`.
    fn check_is_type(
        &mut self,
        env: &IdVec<res::TypeParamId, KindTerm>,
        type_: &res::Type,
    ) -> Result<(), RawError> {
        let kind = self.infer(env, type_)?;
        self.expect(&KindTerm::Type, &kind)
    }

    fn check_pattern(
        &mut self,
        env: &IdVec<res::TypeParamId, KindTerm>,
        pat: &res::Pattern,
        enclosing: Option<(usize, usize)>,
    ) -> Result<(), RawError> {
        match pat {
            res::Pattern::Any | res::Pattern::Var | res::Pattern::NumConst(_) => Ok(()),

            res::Pattern::Tuple(items) => {
                for item in items {
                    self.check_pattern(env, item, enclosing)?;
                }
                Ok(())
            }

            res::Pattern::Ctor(_, _, content) => match content {
                Some(content) => self.check_pattern(env, content, enclosing),
                None => Ok(()),
            },

            res::Pattern::Annot(content, type_) => {
                self.check_is_type(env, type_).map_err(|err| RawError {
                    location: RawLocation::Span(enclosing),
                    ..err
                })?;
                self.check_pattern(env, content, enclosing)
            }

            &res::Pattern::Span(lo, hi, ref content) => {
                self.check_pattern(env, content, Some((lo, hi)))
            }
        }
    }

    /// Checks the type annotations inside a body.  Annotations refer to the parameters of the
    /// enclosing signature, so they are checked in the same environment.
    fn check_expr(
        &mut self,
        env: &IdVec<res::TypeParamId, KindTerm>,
        expr: &res::Expr,
    ) -> Result<(), RawError> {
        match expr {
            res::Expr::Global(_) | res::Expr::Local(_) | res::Expr::NumLit(_) => Ok(()),

            res::Expr::Tuple(items) | res::Expr::ArrayLit(items) => {
                for item in items {
                    self.check_expr(env, item)?;
                }
                Ok(())
            }

            res::Expr::Lam(_, pat, body, _) => {
                self.check_pattern(env, pat, None)?;
                self.check_expr(env, body)
            }

            res::Expr::App(_, func, arg) => {
                self.check_expr(env, func)?;
                self.check_expr(env, arg)
            }

            res::Expr::Match(discrim, cases) => {
                self.check_expr(env, discrim)?;
                for (pat, body) in cases {
                    self.check_pattern(env, pat, None)?;
                    self.check_expr(env, body)?;
                }
                Ok(())
            }

            res::Expr::LetMany(bindings, body) => {
                for (pat, rhs) in bindings {
                    self.check_pattern(env, pat, None)?;
                    self.check_expr(env, rhs)?;
                }
                self.check_expr(env, body)
            }

            res::Expr::Span(_, _, content) => self.check_expr(env, content),
        }
    }
}

fn at_span(span: (usize, usize)) -> impl FnOnce(RawError) -> RawError {
    move |err| RawError {
        location: RawLocation::Span(Some(span)),
        ..err
    }
}

fn locate(
    err: RawError,
    item: String,
    file: &std::path::Path,
    type_spans: Option<&res::TypeSpans>,
    fallback: Option<(usize, usize)>,
) -> Error {
    let span = match &err.location {
        RawLocation::Path(path) => type_spans
            .and_then(|spans| spans.span_at(path))
            .or(fallback),
        RawLocation::Span(span) => span.or(fallback),
    };

    let kind = match err.kind {
        UnifyError::Mismatch => ErrorKind::Mismatch {
            item,
            expected: err.expected,
            actual: err.actual,
        },
        UnifyError::Cyclic => ErrorKind::Cyclic { item },
    };

    let mut located: Locate<ErrorKind> = kind.into();
    located = locate_path(file)(located);
    if let Some((lo, hi)) = span {
        located = locate_span(lo, hi)(located);
    }
    Error(located)
}

fn add_custom_type_deps(type_: &res::Type, deps: &mut BTreeSet<res::CustomTypeId>) {
    match type_ {
        res::Type::App(head, args) => {
            if let res::TypeHead::Ctor(res::TypeId::Custom(custom)) = head {
                deps.insert(*custom);
            }
            for arg in args {
                add_custom_type_deps(arg, deps);
            }
        }
        res::Type::Tuple(items) => {
            for item in items {
                add_custom_type_deps(item, deps);
            }
        }
        res::Type::Func(_, arg, ret) => {
            add_custom_type_deps(arg, deps);
            add_custom_type_deps(ret, deps);
        }
    }
}

/// The dependency groups of the program's type declarations, each group before any group that
/// depends on it.
/// A type or trait declaration.  The kinds of a declaration's parameters are inferred together
/// with those of the declarations it depends on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Item {
    Type(res::CustomTypeId),
    Trait(res::CustomTraitId),
}

#[id_type]
struct ItemId(usize);

fn add_constr_deps(
    constr: &res::TraitApp,
    types: &mut BTreeSet<res::CustomTypeId>,
    traits: &mut BTreeSet<res::CustomTraitId>,
) {
    if let res::TraitId::Custom(custom) = constr.trait_ {
        traits.insert(custom);
    }
    for arg in &constr.args {
        add_custom_type_deps(arg, types);
    }
}

/// The dependency groups of the program's type and trait declarations, each group before any
/// group that depends on it.  A type depends on the types its variants mention and on
/// everything its constraints mention; a trait depends on everything its superclasses and its funcs'
/// signatures mention.  A group is inferred jointly, so a constraint can determine a parameter's
/// kind whether it is a type's constraint or a trait's superclass.
fn dependency_groups(program: &res::Program) -> Vec<Vec<Item>> {
    let mut items: IdVec<ItemId, Item> = IdVec::new();
    let mut ids: BTreeMap<Item, ItemId> = BTreeMap::new();
    for (type_id, _) in &program.custom_types {
        let item = Item::Type(type_id);
        ids.insert(item, items.push(item));
    }
    for (trait_id, _) in &program.traits {
        let item = Item::Trait(trait_id);
        ids.insert(item, items.push(item));
    }

    let edges_out = items.map_refs(|_, item| {
        let mut types = BTreeSet::new();
        let mut traits = BTreeSet::new();
        match *item {
            Item::Type(type_id) => {
                let def = &program.custom_types[type_id];
                for (_, variant) in &def.variants {
                    if let Some(type_) = variant {
                        add_custom_type_deps(type_, &mut types);
                    }
                }
                for (_, constr) in &def.trait_constrs {
                    add_constr_deps(constr, &mut types, &mut traits);
                }
            }
            Item::Trait(trait_id) => {
                let def = &program.traits[trait_id];
                for (_, super_) in &def.supers {
                    add_constr_deps(super_, &mut types, &mut traits);
                }
                for (_, func) in &def.funcs {
                    add_custom_type_deps(&func.body, &mut types);
                    for (_, constr) in &func.own_constrs {
                        add_constr_deps(constr, &mut types, &mut traits);
                    }
                }
            }
        }
        types
            .into_iter()
            .map(|type_id| ids[&Item::Type(type_id)])
            .chain(
                traits
                    .into_iter()
                    .map(|trait_id| ids[&Item::Trait(trait_id)]),
            )
            .collect()
    });

    graph::strongly_connected(&Graph { edges_out })
        .into_iter()
        .map(|group| group.into_iter().map(|id| items[id]).collect())
        .collect()
}

fn fresh_params(
    ctx: &mut Context,
    num_params: Count<res::TypeParamId>,
) -> IdVec<res::TypeParamId, KindTerm> {
    IdVec::from_count_with(num_params, |_| ctx.fresh())
}

/// Infers and checks kinds for the whole program, producing the kinded program.
pub fn infer_kinds(program: res::Program) -> Result<kinded::Program, Error> {
    let mut inference = Inference {
        ctx: Context::new(),
        fixed: program.custom_types.map_refs(|_, _| None),
        pending: BTreeMap::new(),
        fixed_traits: program.traits.map_refs(|_, _| None),
        pending_traits: BTreeMap::new(),
        path: Vec::new(),
    };

    // A func's own parameters belong to its trait's group too, since they are only ever
    // constrained within the group.
    let mut trait_func_kinds: BTreeMap<
        res::CustomTraitId,
        IdVec<res::TraitFuncId, IdVec<res::TypeParamId, kinded::Kind>>,
    > = BTreeMap::new();

    for group in dependency_groups(&program) {
        inference.ctx = Context::new();

        let mut pending = BTreeMap::new();
        let mut pending_traits = BTreeMap::new();
        for &item in &group {
            match item {
                Item::Type(type_id) => {
                    let params =
                        fresh_params(&mut inference.ctx, program.custom_types[type_id].num_params);
                    pending.insert(type_id, params);
                }
                Item::Trait(trait_id) => {
                    let params =
                        fresh_params(&mut inference.ctx, program.traits[trait_id].num_params);
                    pending_traits.insert(trait_id, params);
                }
            }
        }
        inference.pending = pending;
        inference.pending_traits = pending_traits;

        let mut func_envs: BTreeMap<
            res::CustomTraitId,
            IdVec<res::TraitFuncId, IdVec<res::TypeParamId, KindTerm>>,
        > = BTreeMap::new();

        for &item in &group {
            match item {
                Item::Type(type_id) => {
                    let def = &program.custom_types[type_id];
                    let symbols = &program.custom_type_symbols[type_id];
                    let file = &program.mod_symbols[symbols.mod_].file;
                    let item = || format!("the type declaration '{}'", symbols.type_name.0);
                    let env = inference.pending[&type_id].clone();

                    for (variant_id, variant) in &def.variants {
                        if let Some(type_) = variant {
                            let variant_symbols = &symbols.variant_symbols[variant_id];
                            inference.check_is_type(&env, type_).map_err(|err| {
                                locate(
                                    err,
                                    item(),
                                    file,
                                    variant_symbols.content_spans.as_ref(),
                                    Some(variant_symbols.span),
                                )
                            })?;
                        }
                    }

                    for (constr_id, constr) in &def.trait_constrs {
                        let span = symbols.constr_spans[constr_id];
                        inference
                            .check_constr(&env, constr)
                            .map_err(at_span(span))
                            .map_err(|err| locate(err, item(), file, None, None))?;
                    }
                }

                Item::Trait(trait_id) => {
                    let def = &program.traits[trait_id];
                    let symbols = &program.trait_symbols[trait_id];
                    let file = &program.mod_symbols[symbols.mod_].file;
                    let item = || format!("the trait '{}'", symbols.trait_name.0);
                    let env = inference.pending_traits[&trait_id].clone();

                    for (super_id, constr) in &def.supers {
                        let span = symbols.super_spans[super_id];
                        inference
                            .check_constr(&env, constr)
                            .map_err(at_span(span))
                            .map_err(|err| locate(err, item(), file, None, None))?;
                    }

                    let mut envs = IdVec::new();
                    for (func_id, func) in &def.funcs {
                        let func_symbols = &symbols.func_symbols[func_id];
                        let layout = def.func_layout(func_id);
                        let func_env = layout.params(
                            env.clone(),
                            IdVec::from_count_with(layout.num_own_params, |_| {
                                inference.ctx.fresh()
                            }),
                        );

                        let func_item = || {
                            format!(
                                "the signature of '{}' in {}",
                                func_symbols.func_name.0,
                                item()
                            )
                        };

                        inference
                            .check_is_type(&func_env, &func.body)
                            .map_err(|err| {
                                locate(
                                    err,
                                    func_item(),
                                    file,
                                    Some(&func_symbols.type_spans),
                                    Some(func_symbols.span),
                                )
                            })?;

                        for (constr_id, constr) in &func.own_constrs {
                            let span = func_symbols.constr_spans[constr_id];
                            inference
                                .check_constr(&func_env, constr)
                                .map_err(at_span(span))
                                .map_err(|err| locate(err, func_item(), file, None, None))?;
                        }

                        let _ = envs.push(func_env);
                    }
                    func_envs.insert(trait_id, envs);
                }
            }
        }

        // Default whatever the group left unconstrained, and fix the group's kinds before any
        // later group or signature can see them.
        for (type_id, params) in std::mem::take(&mut inference.pending) {
            let kinds = params.map_refs(|_, kind| inference.ctx.to_kind(kind));
            inference.fixed[type_id] = Some(kinds);
        }
        for (trait_id, params) in std::mem::take(&mut inference.pending_traits) {
            let kinds = params.map_refs(|_, kind| inference.ctx.to_kind(kind));
            inference.fixed_traits[trait_id] = Some(kinds);
        }
        for (trait_id, envs) in func_envs {
            let kinds = envs.map(|_, env| env.map_refs(|_, kind| inference.ctx.to_kind(kind)));
            trait_func_kinds.insert(trait_id, kinds);
        }
    }

    // Impls: each in isolation, against the fixed trait kinds.
    let mut impl_kinds = Vec::new();

    for (impl_id, def) in &program.impls {
        inference.ctx = Context::new();

        let symbols = &program.impl_symbols[impl_id];
        let file = &program.mod_symbols[symbols.mod_].file;
        let item = || format!("the impl '{}'", symbols.impl_name.0);
        let env = fresh_params(&mut inference.ctx, def.num_params);

        let head = res::TraitApp {
            trait_: def.trait_,
            args: def.head.clone(),
        };
        inference
            .check_constr(&env, &head)
            .map_err(at_span(symbols.head_span))
            .map_err(|err| locate(err, item(), file, None, None))?;

        for (constr_id, constr) in &def.trait_constrs {
            let span = symbols.constr_spans[constr_id];
            inference
                .check_constr(&env, constr)
                .map_err(at_span(span))
                .map_err(|err| locate(err, item(), file, None, None))?;
        }

        impl_kinds.push((impl_id, env.map_refs(|_, kind| inference.ctx.to_kind(kind))));
    }

    // Values: each in isolation, against the fixed constructor and trait kinds.
    let mut val_kinds = Vec::new();

    for (val_id, def) in &program.vals {
        inference.ctx = Context::new();

        let symbols = &program.val_symbols[val_id];
        let env = fresh_params(&mut inference.ctx, def.scheme.num_params);
        let item = || format!("the signature of '{}'", symbols.val_name.0);
        let file = &program.mod_symbols[symbols.mod_].file;

        inference
            .check_is_type(&env, &def.scheme.body)
            .map_err(|err| locate(err, item(), file, Some(&symbols.type_spans), None))?;

        for (constr_id, constr) in &def.scheme.trait_constrs {
            let span = symbols.trait_constr_spans[constr_id];
            inference
                .check_constr(&env, constr)
                .map_err(at_span(span))
                .map_err(|err| locate(err, item(), file, None, None))?;
        }

        inference
            .check_expr(&env, &def.body)
            .map_err(|err| locate(err, item(), file, None, None))?;

        val_kinds.push((val_id, env.map_refs(|_, kind| inference.ctx.to_kind(kind))));
    }

    let type_kinds = inference
        .fixed
        .map(|_, kinds| kinds.expect("every type declaration belongs to some dependency group"));
    let trait_kinds = inference
        .fixed_traits
        .map(|_, kinds| kinds.expect("every trait belongs to some dependency group"));

    let mut val_kinds = val_kinds.into_iter();
    let mut impl_kinds = impl_kinds.into_iter();

    Ok(kinded::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types.map(|type_id, def| kinded::TypeDef {
            param_kinds: type_kinds[type_id].clone(),
            trait_constrs: def.trait_constrs,
            variants: def.variants,
        }),
        custom_type_symbols: program.custom_type_symbols,
        profile_points: program.profile_points,
        vals: program.vals.map(|val_id, def| {
            let (kinds_id, param_kinds) = val_kinds
                .next()
                .expect("kinds were inferred for every value definition");
            debug_assert_eq!(kinds_id, val_id);
            kinded::ValDef {
                scheme: kinded::TypeScheme {
                    param_kinds,
                    trait_constrs: def.scheme.trait_constrs,
                    body: def.scheme.body,
                },
                body: def.body,
            }
        }),
        val_symbols: program.val_symbols,
        traits: program.traits.map(|trait_id, def| {
            let func_kinds = trait_func_kinds
                .remove(&trait_id)
                .expect("kinds were inferred for every trait");
            let layouts = def.funcs.map_refs(|func_id, _| def.func_layout(func_id));
            kinded::TraitDef {
                param_kinds: trait_kinds[trait_id].clone(),
                supers: def.supers,
                funcs: def.funcs.map(|func_id, func| {
                    let param_kinds = &func_kinds[func_id];
                    let layout = layouts[func_id];
                    kinded::TraitFuncSig {
                        own_param_kinds: IdVec::from_count_with(layout.num_own_params, |param| {
                            param_kinds[layout.own_param(param)].clone()
                        }),
                        own_constrs: func.own_constrs,
                        body: func.body,
                    }
                }),
            }
        }),
        trait_symbols: program.trait_symbols,
        impls: program.impls.map(|impl_id, def| {
            let (kinds_id, param_kinds) = impl_kinds.next().expect("one per impl");
            debug_assert_eq!(kinds_id, impl_id);
            kinded::ImplDef {
                trait_: def.trait_,
                param_kinds,
                head: def.head,
                trait_constrs: def.trait_constrs,
                funcs: def.funcs,
            }
        }),
        impl_symbols: program.impl_symbols,
        impl_scope: program.impl_scope,
        main: program.main,
    })
}
