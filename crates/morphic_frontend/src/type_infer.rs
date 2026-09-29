use std::borrow::Cow;
use std::cell::{RefCell, RefMut};
use std::io;
use std::ops::{Deref, DerefMut};

use crate::data::elaborated_ast as elab;
use crate::data::elaborated_ast::{Derivation, TraitGiven, TraitSelfConstr};
use crate::data::intrinsics as intrs;
use crate::data::kinded_ast as kinded;
use crate::data::num_type::NumType;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use crate::file_cache::FileCache;
use crate::report_type;
use id_collections::{id_type, Count, IdVec};
use morphic_common::intrinsic_config::intrinsic_sig;
use morphic_common::lines;
use morphic_common::report_error::{locate_path, locate_span, ColorMode, Locate, Reportable};

#[id_type]
struct TypeVar(usize);

/// An obligation during inference: a trait constraint over inference variables that some part
/// of the body requires, together with the evidence for it as far as unification has determined.
#[id_type]
struct ObligationVar(usize);

#[derive(Clone, Copy, Debug)]
enum RawErrorKind {
    Recursive,
    Ambiguous {
        type_: TypeVar,
    },
    AmbiguousConstr {
        obligation: ObligationVar,
    },
    Mismatch {
        expected: TypeVar,
        actual: TypeVar,
    },
    /// A constrained type constructor applied to fewer arguments than its constraints mention.
    PartialConstrained {
        type_: res::CustomTypeId,
        given: usize,
    },
    /// A constrained type where a type constructor variable applied to arguments was expected.
    SplitConstrained {
        type_: res::CustomTypeId,
    },
    ExpectedCtorArg {
        id: res::TypeId,
        variant: res::VariantId,
    },
    UnexpectedCtorArg {
        id: res::TypeId,
        variant: res::VariantId,
    },
}

type RawError = Locate<RawErrorKind>;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    Recursive,
    Ambiguous {
        type_: String,
    },
    AmbiguousConstr {
        constr: String,
    },
    Mismatch {
        expected: String,
        expected_is_concrete: bool,
        actual: String,
        actual_is_concrete: bool,
    },
    PartialConstrained {
        type_: String,
        given: usize,
        expected: usize,
    },
    SplitConstrained {
        type_: String,
    },
    ExpectedCtorArg {
        id: String,
        variant: String,
    },
    UnexpectedCtorArg {
        id: String,
        variant: String,
    },
}

#[derive(Debug)]
pub struct Error(Locate<ErrorKind>);

impl RawErrorKind {
    fn render(
        &self,
        program: &elab::Program,
        params: &IdVec<res::TypeParamId, raw::TypeParam>,
        ctx: &Context,
    ) -> ErrorKind {
        let renderer =
            report_type::TypeRenderer::new(&program.mod_symbols, &program.custom_type_symbols);
        let render_constr = |obligation: ObligationVar| {
            let obligation = &ctx.obligations[obligation];
            let app = report_type::TraitApp {
                trait_: obligation.trait_,
                args: obligation
                    .args
                    .iter()
                    .map(|&arg| ctx.extract_report(arg))
                    .collect(),
            };
            renderer.render_trait_app(params, &app, &program.trait_symbols)
        };

        match self {
            RawErrorKind::Recursive => ErrorKind::Recursive,

            RawErrorKind::Ambiguous { type_: type_var } => {
                let type_ = renderer.render(params, &ctx.extract_report(*type_var));
                ErrorKind::Ambiguous { type_ }
            }

            RawErrorKind::AmbiguousConstr { obligation } => ErrorKind::AmbiguousConstr {
                constr: render_constr(*obligation),
            },

            RawErrorKind::Mismatch {
                expected: expected_var,
                actual: actual_var,
            } => {
                let expected_type = ctx.extract_report(*expected_var);
                let actual_type = ctx.extract_report(*actual_var);

                let expected = renderer.render(params, &expected_type);
                let actual = renderer.render(params, &actual_type);

                let expected_is_concrete = report_type::is_concrete(&expected_type);
                let actual_is_concrete = report_type::is_concrete(&actual_type);

                ErrorKind::Mismatch {
                    expected,
                    expected_is_concrete,
                    actual,
                    actual_is_concrete,
                }
            }

            RawErrorKind::PartialConstrained { type_, given } => ErrorKind::PartialConstrained {
                type_: program.custom_type_symbols[*type_].type_name.0.clone(),
                given: *given,
                expected: ctx.constrained_prefix[*type_].to_value(),
            },

            RawErrorKind::SplitConstrained { type_ } => ErrorKind::SplitConstrained {
                type_: program.custom_type_symbols[*type_].type_name.0.clone(),
            },

            RawErrorKind::ExpectedCtorArg { id, variant } => {
                let (id_rendered, variant_rendered) = renderer.render_ctor(*id, *variant);
                ErrorKind::ExpectedCtorArg {
                    id: id_rendered,
                    variant: variant_rendered,
                }
            }

            RawErrorKind::UnexpectedCtorArg { id, variant } => {
                let (id_rendered, variant_rendered) = renderer.render_ctor(*id, *variant);
                ErrorKind::UnexpectedCtorArg {
                    id: id_rendered,
                    variant: variant_rendered,
                }
            }
        }
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
            ErrorKind::Recursive => (
                "Cyclic Type",
                lines![
                    "I couldn't infer a type for this expression.",
                    "",
                    "Any type you could try to give this expression would need to mention itself \
                     cyclically in order to type-check. So a hypothetical type that could make \
                     this expression type-check would need to be infinitely big!"
                ]
                .to_owned(),
            ),

            ErrorKind::Ambiguous { type_ } => (
                "Ambiguous Type",
                format!(
                    lines![
                        "I couldn't fully determine the type of this expression. The type looks like:",
                        "",
                        "    {type_}",
                        "",
                        "where each '{unknown}' stands for something that this definition \
                         doesn't pin down. You can fix this by adding a type annotation. For \
                         example, 'let x: Int = ...' would tell me that 'x' is of type 'Int'.",
                    ],
                    type_ = type_,
                    unknown = report_type::UNKNOWN_TYPE,
                ),
            ),

            ErrorKind::AmbiguousConstr { constr } => (
                "Ambiguous Trait Constraint",
                format!(
                    lines![
                        "I couldn't fully determine what type this trait constraint applies to.  The \
                         most I could work out is:",
                        "",
                        "    {constr}",
                        "",
                        "where each '{unknown}' stands for something that this definition \
                         doesn't pin down.  You can fix this by adding a type annotation.",
                    ],
                    constr = constr,
                    unknown = report_type::UNKNOWN_TYPE,
                ),
            ),

            ErrorKind::Mismatch {
                expected,
                expected_is_concrete,
                actual,
                actual_is_concrete,
            } => (
                "Type Mismatch",
                format!(
                    lines![
                        "I expected to find an expression here with {expected_intro}:",
                        "",
                        "    {expected}",
                        "",
                        "Instead, this expression has {actual_intro}:",
                        "",
                        "    {actual}",
                    ],
                    expected_intro = if *expected_is_concrete {
                        "the type"
                    } else {
                        "a type that looks like"
                    },
                    expected = expected,
                    actual_intro = if *actual_is_concrete {
                        "the type"
                    } else {
                        "a type that looks like"
                    },
                    actual = actual,
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
                     it occurs, but here it is applied to {}.",
                    type_, expected, given
                ),
            ),

            ErrorKind::SplitConstrained { type_ } => (
                "Constrained Type as Constructor",
                format!(
                    "The type '{}' is declared with trait constraints, so it can only stand for a \
                     type constructor variable while it is applied to the parameters those \
                     constraints mention, which this expression would need it not to be.\n\nA \
                     type with constraints carries evidence for them, which is only determined \
                     once the arguments the constraints mention are known.",
                    type_
                ),
            ),

            ErrorKind::ExpectedCtorArg { id, variant } => (
                "Missing Constructor Argument",
                format!(
                    "The constructor '{}' for the type '{}' is supposed to take an argument.",
                    variant, id,
                ),
            ),

            ErrorKind::UnexpectedCtorArg { id, variant } => (
                "Unexpected Constructor Argument",
                format!(
                    "The constructor '{}' for the type '{}' is not supposed to take an argument.",
                    variant, id,
                ),
            ),
        })
    }

    fn exit_status(&self) -> i32 {
        1
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Assign {
    Unknown,
    Equal(TypeVar),
    // A rigid type parameter of the enclosing definition of any kind.
    Param(res::TypeParamId),
    // A bare type constructor of any kind.
    Ctor(res::TypeId),
    // A head applied to one or more arguments.  A bare head is never wrapped in an empty
    // application, but a head may itself resolve to an application (see 'unify_head_with_app'),
    // in which case the two argument lists concatenate.
    App(TypeVar, Vec<TypeVar>),
    // A constrained type constructor applied to at least the parameters its constraints mention,
    // with an obligation for each constraint.  Splitting it into a head and arguments stops there,
    // since the evidence depends on those parameters.
    Constrained(
        res::CustomTypeId,
        Vec<TypeVar>,
        IdVec<res::TraitConstrId, ObligationVar>,
    ),
    Tuple(Vec<TypeVar>),
    Func(Purity, TypeVar, TypeVar),
}

/// The evidence for an obligation, as far as unification has determined it; see
/// `typed::Evidence`.
#[derive(Clone, Debug)]
enum DerivAssign {
    Unknown,
    Equal(ObligationVar),
    Given(res::TraitConstrId),
    Impl(
        res::ImplId,
        IdVec<res::TypeParamId, TypeVar>,
        IdVec<res::TraitConstrId, ObligationVar>,
    ),
    Super(ObligationVar, res::SuperId),
}

/// A trait constraint required by some part of the body being inferred, over inference
/// variables.  Nothing about it influences the types inferred, except through the evidence
/// constrained types carry, which unification equates structurally.
#[derive(Clone, Debug)]
struct RawObligation {
    trait_: res::TraitId,
    args: Vec<TypeVar>,
    span: (usize, usize),
    origin: typed::Origin,
    assign: RefCell<DerivAssign>,
}

#[derive(Clone, Debug)]
struct Context<'a> {
    obligations: IdVec<ObligationVar, RawObligation>,
    // The dynamic borrowing state of each 'RefCell' in 'vars' is "load-bearing," because we use it
    // during unification to track whether or not we are currently processing a given type variable
    // higher up in the call stack.
    //
    // If the user writes a program that fails the "occurs check" -- that is, a program that forces
    // the type inference system to attempt to unify a type variable 'x' with some type 'f(x)'
    // mentioning that variable -- we want to report an "invalid recursive type" error.  The borrow
    // state of each 'RefCell' is how we detect these cycles and report these errors.  If
    // unification attempts to mutably borrow one of these 'RefCell's twice simultaneously, this
    // does *not* represent a logic error in the compiler; instead, it indicates a type error in the
    // user's program.
    //
    // In fact, the *only* reason we use 'RefCell's here is to implement this "occurs check"
    // internally within unification (in a way the borrow checker understands).  The 'Context'
    // struct shouldn't behave as if it has interior mutability; in particular, the public interface
    // to unification takes 'Context' by '&mut'.
    vars: IdVec<TypeVar, RefCell<Assign>>,
    // Obligations found as corresponding evidence of two constrained types and yet to be unified.
    evidence_pairs: RefCell<Vec<(ObligationVar, ObligationVar)>>,
    // Obligations whose evidence is required to be equal but was not identified, because it
    // differs or involves a superclass projection; see `typed::ValDef::evidence_equations`.
    evidence_equations: RefCell<Vec<(ObligationVar, ObligationVar)>>,
    // See `res::constrained_prefix`.
    constrained_prefix: &'a IdVec<res::CustomTypeId, Count<res::TypeParamId>>,
}

#[derive(Clone, Copy, Debug)]
enum UnifyError {
    Recursive,
    Mismatch,
    SplitConstrained(res::CustomTypeId),
}

#[derive(Clone, Copy, Debug)]
enum ExtractError {
    Recursive,
    Unknown,
}

impl<'a> Context<'a> {
    fn new(constrained_prefix: &'a IdVec<res::CustomTypeId, Count<res::TypeParamId>>) -> Self {
        Context {
            obligations: IdVec::new(),
            vars: IdVec::new(),
            evidence_pairs: RefCell::new(Vec::new()),
            evidence_equations: RefCell::new(Vec::new()),
            constrained_prefix,
        }
    }

    fn new_var(&mut self, assign: Assign) -> TypeVar {
        self.vars.push(RefCell::new(assign))
    }

    fn new_obligation(
        &mut self,
        trait_: res::TraitId,
        args: Vec<TypeVar>,
        span: (usize, usize),
        origin: typed::Origin,
        assign: DerivAssign,
    ) -> ObligationVar {
        self.obligations.push(RawObligation {
            trait_,
            args,
            span,
            origin,
            assign: RefCell::new(assign),
        })
    }

    fn obtain(&self, var: TypeVar) -> Result<RefMut<'_, Assign>, UnifyError> {
        self.vars[var]
            .try_borrow_mut()
            .map_err(|_| UnifyError::Recursive)
    }

    fn follow(&self, var: TypeVar) -> Result<TypeVar, UnifyError> {
        let mut assign = self.obtain(var)?;
        if let Assign::Equal(curr_dest) = assign.deref_mut() {
            *curr_dest = self.follow(*curr_dest)?;
            Ok(*curr_dest)
        } else {
            Ok(var)
        }
    }

    fn unify_rec(&self, root_var1: TypeVar, root_var2: TypeVar) -> Result<(), UnifyError> {
        let var1 = self.follow(root_var1)?;
        let var2 = self.follow(root_var2)?;

        if var1 == var2 {
            return Ok(());
        }

        let mut assign1 = self.obtain(var1)?;
        let mut assign2 = self.obtain(var2)?;

        match (assign1.deref(), assign2.deref()) {
            (Assign::Equal(_), _) => unreachable!(),
            (_, Assign::Equal(_)) => unreachable!(),

            (Assign::Unknown, _) => {
                *assign1 = Assign::Equal(var2);
                return Ok(());
            }

            (_, Assign::Unknown) => {
                *assign2 = Assign::Equal(var1);
                return Ok(());
            }

            (Assign::Param(param1), Assign::Param(param2)) => {
                if param1 != param2 {
                    return Err(UnifyError::Mismatch);
                }
            }

            (Assign::Ctor(id1), Assign::Ctor(id2)) => {
                if id1 != id2 {
                    return Err(UnifyError::Mismatch);
                }
            }

            (&Assign::App(head1, ref args1), &Assign::App(head2, ref args2)) => {
                self.unify_apps(head1, args1, head2, args2)?;
            }

            (
                &Assign::Constrained(id1, ref args1, ref evidence1),
                &Assign::Constrained(id2, ref args2, ref evidence2),
            ) => {
                self.unify_constrained(id1, args1, evidence1, id2, args2, evidence2)?;
            }

            (
                &Assign::Constrained(id, ref args, ref evidence),
                &Assign::App(head, ref app_args),
            )
            | (
                &Assign::App(head, ref app_args),
                &Assign::Constrained(id, ref args, ref evidence),
            ) => {
                self.unify_constrained_with_app(id, args, evidence, head, app_args)?;
            }

            (Assign::Tuple(items1), Assign::Tuple(items2)) => {
                if items1.len() != items2.len() {
                    return Err(UnifyError::Mismatch);
                }

                for (&item1, &item2) in items1.iter().zip(items2.iter()) {
                    self.unify_rec(item1, item2)?;
                }
            }

            (Assign::Func(purity1, arg1, ret1), Assign::Func(purity2, arg2, ret2)) => {
                if purity1 != purity2 {
                    return Err(UnifyError::Mismatch);
                }

                self.unify_rec(*arg1, *arg2)?;
                self.unify_rec(*ret1, *ret2)?;
            }

            _ => {
                return Err(UnifyError::Mismatch);
            }
        }

        // This is purely an optimization
        *assign1 = Assign::Equal(var2);

        Ok(())
    }

    fn unify_constrained(
        &self,
        id1: res::CustomTypeId,
        args1: &[TypeVar],
        evidence1: &IdVec<res::TraitConstrId, ObligationVar>,
        id2: res::CustomTypeId,
        args2: &[TypeVar],
        evidence2: &IdVec<res::TraitConstrId, ObligationVar>,
    ) -> Result<(), UnifyError> {
        // Two applications of one constructor that unify have the same kind, so the same number
        // of arguments.
        if id1 != id2 || args1.len() != args2.len() {
            return Err(UnifyError::Mismatch);
        }
        for (&arg1, &arg2) in args1.iter().zip(args2.iter()) {
            self.unify_rec(arg1, arg2)?;
        }
        let mut pairs = self.evidence_pairs.borrow_mut();
        for (&obligation1, &obligation2) in evidence1.values().zip(evidence2.values()) {
            pairs.push((obligation1, obligation2));
        }
        Ok(())
    }

    // A constrained application unifies with an application from the right like any other (see
    // `unify_apps`), except that what is left of it has to stay applied to the parameters its
    // constraints mention, so that it keeps carrying its evidence.
    fn unify_constrained_with_app(
        &self,
        id: res::CustomTypeId,
        args: &[TypeVar],
        evidence: &IdVec<res::TraitConstrId, ObligationVar>,
        app_head: TypeVar,
        app_args: &[TypeVar],
    ) -> Result<(), UnifyError> {
        let shared = args.len().min(app_args.len());
        let (prefix, suffix) = args.split_at(args.len() - shared);
        let (app_prefix, app_suffix) = app_args.split_at(app_args.len() - shared);

        for (&arg, &app_arg) in suffix.iter().zip(app_suffix.iter()) {
            self.unify_rec(arg, app_arg)?;
        }

        if prefix.len() < self.constrained_prefix[id].to_value() {
            return Err(UnifyError::SplitConstrained(id));
        }
        if app_prefix.is_empty() {
            self.unify_head_with_constrained(app_head, id, prefix, evidence)
        } else if prefix.is_empty() {
            // A head applied to arguments cannot be a bare constructor.
            Err(UnifyError::Mismatch)
        } else {
            self.unify_constrained_with_app(id, prefix, evidence, app_head, app_prefix)
        }
    }

    // Unifies a bare head with a constrained application; compare `unify_head_with_app`.
    fn unify_head_with_constrained(
        &self,
        head: TypeVar,
        id: res::CustomTypeId,
        args: &[TypeVar],
        evidence: &IdVec<res::TraitConstrId, ObligationVar>,
    ) -> Result<(), UnifyError> {
        let head = self.follow(head)?;
        let mut assign = self.obtain(head)?;

        match assign.deref() {
            Assign::Equal(_) => unreachable!(),

            Assign::Unknown => {
                *assign = Assign::Constrained(id, args.to_vec(), evidence.clone());
                Ok(())
            }

            &Assign::App(inner_head, ref inner_args) => {
                self.unify_constrained_with_app(id, args, evidence, inner_head, inner_args)
            }

            &Assign::Constrained(inner_id, ref inner_args, ref inner_evidence) => {
                self.unify_constrained(id, args, evidence, inner_id, inner_args, inner_evidence)
            }

            Assign::Param(_) | Assign::Ctor(_) | Assign::Tuple(_) | Assign::Func(_, _, _) => {
                Err(UnifyError::Mismatch)
            }
        }
    }

    // Applications unify from the right: the last min(n1, n2) arguments pair up, and whatever is
    // left of the longer application is unified with the head of the shorter one.  This is what
    // lets `f a` unify with `Result Int Bool`, giving `f := Result Int`.  It is sound because type
    // constructor application is injective.
    fn unify_apps(
        &self,
        head1: TypeVar,
        args1: &[TypeVar],
        head2: TypeVar,
        args2: &[TypeVar],
    ) -> Result<(), UnifyError> {
        let shared = args1.len().min(args2.len());
        let (prefix1, suffix1) = args1.split_at(args1.len() - shared);
        let (prefix2, suffix2) = args2.split_at(args2.len() - shared);

        for (&arg1, &arg2) in suffix1.iter().zip(suffix2.iter()) {
            self.unify_rec(arg1, arg2)?;
        }

        match (prefix1.is_empty(), prefix2.is_empty()) {
            (true, true) => self.unify_rec(head1, head2),
            (true, false) => self.unify_head_with_app(head1, head2, prefix2),
            (false, true) => self.unify_head_with_app(head2, head1, prefix1),
            (false, false) => unreachable!(),
        }
    }

    // Unifies a bare head with the (nonempty) prefix of a longer application.  A head that is
    // still unknown simply becomes that application.  A head that is already an application
    // recurses, anything else has no arguments to absorb and is a mismatch.
    fn unify_head_with_app(
        &self,
        head: TypeVar,
        app_head: TypeVar,
        app_args: &[TypeVar],
    ) -> Result<(), UnifyError> {
        debug_assert!(!app_args.is_empty());

        let head = self.follow(head)?;
        let mut assign = self.obtain(head)?;

        match assign.deref() {
            Assign::Equal(_) => unreachable!(),

            Assign::Unknown => {
                *assign = Assign::App(app_head, app_args.to_vec());
                Ok(())
            }

            &Assign::App(inner_head, ref inner_args) => {
                self.unify_apps(inner_head, inner_args, app_head, app_args)
            }

            &Assign::Constrained(id, ref args, ref evidence) => {
                self.unify_constrained_with_app(id, args, evidence, app_head, app_args)
            }

            Assign::Param(_) | Assign::Ctor(_) | Assign::Tuple(_) | Assign::Func(_, _, _) => {
                Err(UnifyError::Mismatch)
            }
        }
    }

    fn follow_deriv(&self, mut var: ObligationVar) -> ObligationVar {
        loop {
            let next = match *self.obligations[var].assign.borrow() {
                DerivAssign::Equal(next) => next,
                _ => return var,
            };
            var = next;
        }
    }

    fn set_deriv(&self, var: ObligationVar, assign: DerivAssign) {
        *self.obligations[var].assign.borrow_mut() = assign;
    }

    /// Unifies the evidence of two obligations found at corresponding positions of two
    /// constrained types.  Evidence that agrees structurally is identified.  Evidence that
    /// differs, or that involves a superclass projection and so cannot be compared here since
    /// projection is not injective, is recorded as an equation for the body solver to check once
    /// both sides are solved, so that the conflict can be explained in terms of the solutions.
    fn unify_deriv(&self, var1: ObligationVar, var2: ObligationVar) -> Result<(), UnifyError> {
        let var1 = self.follow_deriv(var1);
        let var2 = self.follow_deriv(var2);

        if var1 == var2 {
            return Ok(());
        }

        let assign1 = self.obligations[var1].assign.borrow().clone();
        let assign2 = self.obligations[var2].assign.borrow().clone();

        match (&assign1, &assign2) {
            (DerivAssign::Equal(_), _) | (_, DerivAssign::Equal(_)) => unreachable!(),

            (DerivAssign::Unknown, _) => {
                self.set_deriv(var1, DerivAssign::Equal(var2));
                return Ok(());
            }

            (_, DerivAssign::Unknown) => {
                self.set_deriv(var2, DerivAssign::Equal(var1));
                return Ok(());
            }

            (DerivAssign::Given(given1), DerivAssign::Given(given2)) if given1 == given2 => {}

            (DerivAssign::Impl(impl1, args1, subs1), DerivAssign::Impl(impl2, args2, subs2))
                if impl1 == impl2 =>
            {
                for ((_, &arg1), (_, &arg2)) in args1.iter().zip(args2.iter()) {
                    self.unify_rec(arg1, arg2)?;
                }
                let mut pairs = self.evidence_pairs.borrow_mut();
                for (&sub1, &sub2) in subs1.values().zip(subs2.values()) {
                    pairs.push((sub1, sub2));
                }
            }

            _ => {
                self.evidence_equations.borrow_mut().push((var1, var2));
                return Ok(());
            }
        }

        self.set_deriv(var1, DerivAssign::Equal(var2));
        Ok(())
    }

    /// Unifies the evidence pairs that unifying types produced, which may produce more.
    fn unify_evidence_pairs(&self) -> Result<(), UnifyError> {
        loop {
            let pair = self.evidence_pairs.borrow_mut().pop();
            match pair {
                Some((var1, var2)) => self.unify_deriv(var1, var2)?,
                None => return Ok(()),
            }
        }
    }

    fn unify(&mut self, expected: TypeVar, actual: TypeVar) -> Result<(), RawError> {
        let to_raw = |err| match err {
            UnifyError::Recursive => RawErrorKind::Recursive.into(),
            UnifyError::Mismatch => RawErrorKind::Mismatch { expected, actual }.into(),
            UnifyError::SplitConstrained(type_) => RawErrorKind::SplitConstrained { type_ }.into(),
        };
        self.unify_rec(expected, actual).map_err(to_raw)?;
        self.unify_evidence_pairs().map_err(to_raw)
    }

    // Extracts the fully solved type rooted at 'root_var', with its evidence as obligations.
    // If any part of that type is still unconstrained, the whole type is reported as ambiguous,
    // so that the error message can show the user which parts of the type they need to pin
    // down with an annotation. We never silently pick a type for an unconstrained variable
    // since, in the presence of traits (ad hoc polymorphism), this can lead to some pretty
    // confusing behavior.
    fn extract(&self, root_var: TypeVar, ids: &ObligationIds) -> Result<typed::Type, RawError> {
        self.extract_rec(root_var, ids).map_err(|err| match err {
            ExtractError::Recursive => RawErrorKind::Recursive.into(),
            ExtractError::Unknown => RawErrorKind::Ambiguous { type_: root_var }.into(),
        })
    }

    fn extract_rec(
        &self,
        root_var: TypeVar,
        id_of: &ObligationIds,
    ) -> Result<typed::Type, ExtractError> {
        let var = self.follow(root_var).map_err(|_| ExtractError::Recursive)?;
        let assign = self.obtain(var).map_err(|_| ExtractError::Recursive)?;

        match assign.deref() {
            Assign::Unknown => Err(ExtractError::Unknown),

            &Assign::Equal(_) => unreachable!(),

            &Assign::Param(param) => Ok(elab::Type::param(param)),

            &Assign::Ctor(id) => Ok(elab::Type::ctor(id)),

            Assign::App(head, args) => {
                let head_type = self.extract_rec(*head, id_of)?;
                let arg_types = args
                    .iter()
                    .map(|&arg| self.extract_rec(arg, id_of))
                    .collect::<Result<Vec<_>, _>>()?;
                match head_type {
                    elab::Type::App(head, mut head_args) => {
                        head_args.extend(arg_types);
                        Ok(elab::Type::App(head, head_args))
                    }
                    elab::Type::Constrained(id, mut head_args, evidence) => {
                        head_args.extend(arg_types);
                        Ok(elab::Type::Constrained(id, head_args, evidence))
                    }
                    elab::Type::Tuple(_) | elab::Type::Func(_, _, _) => unreachable!(),
                }
            }

            Assign::Constrained(id, args, evidence) => Ok(elab::Type::Constrained(
                *id,
                args.iter()
                    .map(|&arg| self.extract_rec(arg, id_of))
                    .collect::<Result<_, _>>()?,
                evidence.map_refs(|_, &obligation| id_of(obligation)),
            )),

            Assign::Tuple(items) => Ok(elab::Type::Tuple(
                items
                    .iter()
                    .map(|&item| self.extract_rec(item, id_of))
                    .collect::<Result<_, _>>()?,
            )),

            &Assign::Func(purity, arg, ret) => Ok(elab::Type::Func(
                purity,
                Box::new(self.extract_rec(arg, id_of)?),
                Box::new(self.extract_rec(ret, id_of)?),
            )),
        }
    }

    fn extract_report(&self, root_var: TypeVar) -> report_type::Type {
        use report_type::{Head, Type};

        let var = match self.follow(root_var) {
            Ok(var) => var,
            Err(_) => {
                return Type::App(Head::RecursiveOccurrence, Vec::new());
            }
        };

        let assign = match self.obtain(var) {
            Ok(assign) => assign,
            Err(_) => {
                return Type::App(Head::RecursiveOccurrence, Vec::new());
            }
        };

        match assign.deref() {
            Assign::Unknown => Type::App(Head::Unknown, Vec::new()),

            Assign::Equal(_) => unreachable!(),

            &Assign::Param(param) => Type::App(Head::Var(param), Vec::new()),

            &Assign::Ctor(id) => Type::App(Head::Ctor(id), Vec::new()),

            Assign::App(head, args) => {
                let head_type = self.extract_report(*head);
                let arg_types = args.iter().map(|&arg| self.extract_report(arg)).collect();
                apply_report_type(head_type, arg_types)
            }

            Assign::Constrained(id, args, _) => Type::App(
                Head::Ctor(res::TypeId::Custom(*id)),
                args.iter().map(|&arg| self.extract_report(arg)).collect(),
            ),

            Assign::Tuple(items) => report_type::Type::Tuple(
                items
                    .iter()
                    .map(|&item| self.extract_report(item))
                    .collect(),
            ),

            Assign::Func(purity, arg, ret) => report_type::Type::Func(
                *purity,
                Box::new(self.extract_report(*arg)),
                Box::new(self.extract_report(*ret)),
            ),
        }
    }
}

fn apply_report_type(head: report_type::Type, args: Vec<report_type::Type>) -> report_type::Type {
    match head {
        report_type::Type::App(head, mut head_args) => {
            head_args.extend(args);
            report_type::Type::App(head, head_args)
        }
        report_type::Type::Tuple(_) | report_type::Type::Func(_, _, _) => unreachable!(),
    }
}

// Applies a head variable to argument variables, without wrapping a bare head in an empty
// application.
fn app_var(ctx: &mut Context, head: TypeVar, args: Vec<TypeVar>) -> TypeVar {
    if args.is_empty() {
        head
    } else {
        ctx.new_var(Assign::App(head, args))
    }
}

fn ctor_app_var(ctx: &mut Context, id: res::TypeId, args: Vec<TypeVar>) -> TypeVar {
    let head = ctx.new_var(Assign::Ctor(id));
    app_var(ctx, head, args)
}

#[derive(Clone, Debug)]
struct Scope {
    // The rigid type variables standing in for the enclosing definition's type parameters. Type
    // annotations inside the body refer to these.
    rigid_params: IdVec<res::TypeParamId, TypeVar>,
    locals: IdVec<res::LocalId, TypeVar>,
    // The innermost enclosing span, initially that of the whole definition and updated as
    // inference traverses expression trees.  Attached to `RawObligation`s so that errors can
    // report where obligations arose.
    span: (usize, usize),
}

impl Scope {
    fn new(rigid_params: IdVec<res::TypeParamId, TypeVar>, span: (usize, usize)) -> Self {
        Scope {
            rigid_params,
            locals: IdVec::new(),
            span,
        }
    }

    fn add_local(&mut self, var: TypeVar) {
        let _ = self.locals.push(var);
    }

    fn local(&self, id: res::LocalId) -> TypeVar {
        self.locals[id]
    }

    fn with_subscope<F, R>(&mut self, body: F) -> R
    where
        F: for<'a> FnOnce(&'a mut Scope) -> R,
    {
        let len = self.locals.count();
        let result = body(self);
        self.locals.truncate(len);
        result
    }
}

#[derive(Clone, Debug)]
enum AnnotExpr {
    // The final 'TypeVar' in each of 'Global', 'Lam', and 'ArrayLit' is the type of the whole
    // expression.  It is only used to report ambiguities in terms of the type the user sees at
    // the reported span, rather than in terms of an internal component of that type.
    Global(
        res::GlobalId,
        IdVec<res::TypeParamId, TypeVar>,
        TypeVar,
        IdVec<res::TraitConstrId, ObligationVar>,
    ),
    TraitFunc(res::TraitId, res::TraitFuncId, AnnotTraitFuncInst),
    Local(res::LocalId),
    Tuple(Vec<AnnotExpr>),
    Lam(
        Purity,
        TypeVar, // Argument type
        TypeVar, // Return type
        AnnotPattern,
        Box<AnnotExpr>,
        Option<prof::ProfilePointId>,
        TypeVar, // Whole function type
    ),
    App(Purity, Box<AnnotExpr>, Box<AnnotExpr>),
    Match(Box<AnnotExpr>, Vec<(AnnotPattern, AnnotExpr)>, TypeVar),
    LetMany(Vec<(AnnotPattern, AnnotExpr)>, Box<AnnotExpr>),

    ArrayLit(
        TypeVar, // Item type
        Vec<AnnotExpr>,
        TypeVar, // Whole array type
    ),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),

    Span(usize, usize, Box<AnnotExpr>),
}

/// A reference to a trait func during inference, see `res::TraitFuncInst`.
#[derive(Clone, Debug)]
struct AnnotTraitFuncInst {
    // Inherited from the trait the function belongs to.
    trait_vars: IdVec<res::TypeParamId, TypeVar>,
    trait_obligation: ObligationVar,
    func_vars: IdVec<res::TraitFuncParamId, TypeVar>,
    func_obligations: IdVec<res::TraitFuncConstrId, ObligationVar>,
    // The type of the whole reference, for reporting ambiguities.
    whole: TypeVar,
}

#[derive(Clone, Debug)]
enum AnnotPattern {
    Any(TypeVar),
    Var(TypeVar),
    Tuple(Vec<AnnotPattern>),
    Ctor(
        res::TypeId,
        Vec<TypeVar>,
        res::VariantId,
        Option<Box<AnnotPattern>>,
        TypeVar, // Whole pattern type, for reporting ambiguities (see 'AnnotExpr')
    ),

    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),

    Span(usize, usize, Box<AnnotPattern>),
}

fn intrinsic_sig_to_scheme(sig: &intrs::Signature) -> elab::TypeScheme {
    fn trans_type(type_: &intrs::Type) -> elab::Type {
        match type_ {
            intrs::Type::Bool => elab::Type::ctor(res::TypeId::Bool),
            intrs::Type::Num(NumType::Byte) => elab::Type::ctor(res::TypeId::Byte),
            intrs::Type::Num(NumType::Int) => elab::Type::ctor(res::TypeId::Int),
            intrs::Type::Num(NumType::Float) => elab::Type::ctor(res::TypeId::Float),
            intrs::Type::Tuple(items) => elab::Type::Tuple(items.iter().map(trans_type).collect()),
        }
    }

    elab::TypeScheme {
        param_kinds: IdVec::new(),
        trait_constrs: IdVec::new(),
        body: elab::Type::Func(
            sig.purity,
            Box::new(trans_type(&sig.arg)),
            Box::new(trans_type(&sig.ret)),
        ),
    }
}

// Sounds ominous...
pub fn global_scheme(program: &elab::Program, global: res::GlobalId) -> Cow<'_, elab::TypeScheme> {
    use crate::data::elaborated_ast::Type::*;
    use crate::data::resolved_ast::TypeHead::Ctor;
    use crate::data::resolved_ast::TypeId::*;

    fn bool_() -> elab::Type {
        elab::Type::ctor(Bool)
    }

    fn byte() -> elab::Type {
        elab::Type::ctor(Byte)
    }

    fn int() -> elab::Type {
        elab::Type::ctor(Int)
    }

    fn array(arg: elab::Type) -> elab::Type {
        App(Ctor(Array), vec![arg])
    }

    fn func(arg: elab::Type, ret: elab::Type) -> elab::Type {
        Func(Purity::Pure, Box::new(arg), Box::new(ret))
    }

    fn impure_func(arg: elab::Type, ret: elab::Type) -> elab::Type {
        Func(Purity::Impure, Box::new(arg), Box::new(ret))
    }

    fn pair(fst: elab::Type, snd: elab::Type) -> elab::Type {
        Tuple(vec![fst, snd])
    }

    // The parameters of builtin globals all have kind `Type`.
    fn scheme(num_params: usize, body: elab::Type) -> elab::TypeScheme {
        elab::TypeScheme {
            param_kinds: IdVec::from_vec(vec![kinded::Kind::TYPE; num_params]),
            trait_constrs: IdVec::new(),
            body,
        }
    }

    fn param(index: usize) -> elab::Type {
        elab::Type::param(res::TypeParamId(index))
    }

    match global {
        res::GlobalId::Intrinsic(intr) => Cow::Owned(intrinsic_sig_to_scheme(&intrinsic_sig(intr))),

        res::GlobalId::ArrayOp(op) => {
            use crate::data::resolved_ast::ArrayOp::*;
            let result = match op {
                Get => scheme(1, func(pair(array(param(0)), int()), param(0))),
                Extract => scheme(
                    1,
                    func(
                        pair(array(param(0)), int()),
                        pair(param(0), func(param(0), array(param(0)))),
                    ),
                ),
                Len => scheme(1, func(array(param(0)), int())),
                Push => scheme(1, func(pair(array(param(0)), param(0)), array(param(0)))),
                Pop => scheme(1, func(array(param(0)), pair(array(param(0)), param(0)))),
                Reserve => scheme(1, func(pair(array(param(0)), int()), array(param(0)))),
            };
            Cow::Owned(result)
        }

        res::GlobalId::IoOp(op) => match op {
            res::IoOp::Input => Cow::Owned(scheme(0, impure_func(Tuple(vec![]), array(byte())))),
            res::IoOp::Output => Cow::Owned(scheme(0, impure_func(array(byte()), Tuple(vec![])))),
        },

        res::GlobalId::Panic => Cow::Owned(scheme(1, func(array(byte()), param(0)))),

        // A constructor of a constrained type carries the type's constraints as its own, and the
        // evidence of its result type is exactly those constraints.
        res::GlobalId::Ctor(Custom(custom), variant) => {
            let typedef = &program.custom_types[custom];
            let params = typedef
                .param_kinds
                .map_refs(|param, _| elab::Type::param(param));
            let ret = if typedef.trait_constrs.is_empty() {
                App(Ctor(Custom(custom)), params.into_vec())
            } else {
                Constrained(
                    custom,
                    params.into_vec(),
                    typedef
                        .trait_constrs
                        .map_refs(|constr, _| Derivation::Given(constr)),
                )
            };
            let body = match typedef.variants[variant].clone() {
                Some(arg) => func(arg, ret),
                None => ret,
            };
            Cow::Owned(elab::TypeScheme {
                param_kinds: typedef.param_kinds.clone(),
                trait_constrs: typedef.trait_constrs.clone(),
                body,
            })
        }

        res::GlobalId::Ctor(Bool, variant) => {
            debug_assert!(variant == res::VariantId(0) || variant == res::VariantId(1));
            Cow::Owned(scheme(0, bool_()))
        }

        res::GlobalId::Ctor(_, _) => unreachable!(),

        res::GlobalId::Custom(custom) => Cow::Borrowed(&program.vals[custom].scheme),
    }
}

/// Instantiates elaborated types at fresh or rigid variables: type parameters become
/// `param_vars`, and the givens the types' evidence refers to become the obligations `given_of`
/// supplies.  Each piece of evidence becomes an obligation for the constraint it discharges,
/// carrying that evidence.
struct Inst<'a, 'b, 'c, G> {
    ctx: &'a mut Context<'c>,
    program: &'b elab::Program,
    span: (usize, usize),
    // The signature the types come from, which is where the evidence they carry was fixed.
    signature: typed::Signature,
    param_vars: &'a IdVec<res::TypeParamId, TypeVar>,
    given_of: &'a dyn Fn(&G) -> ObligationVar,
}

impl<'a, 'b, 'c, G> Inst<'a, 'b, 'c, G> {
    fn type_(&mut self, body: &elab::Type<Derivation<G>>) -> TypeVar {
        match body {
            elab::Type::App(head, args) => {
                let head_var = match head {
                    res::TypeHead::Var(param) => self.param_vars[param],
                    res::TypeHead::Ctor(id) => self.ctx.new_var(Assign::Ctor(*id)),
                };
                let arg_vars = args.iter().map(|arg| self.type_(arg)).collect();
                app_var(self.ctx, head_var, arg_vars)
            }

            elab::Type::Constrained(id, args, evidence) => {
                let arg_vars: Vec<TypeVar> = args.iter().map(|arg| self.type_(arg)).collect();
                let signature = self.signature;
                let evidence_vars = constr_obligations(
                    self.ctx,
                    self.program,
                    self.span,
                    *id,
                    &arg_vars,
                    &move |_| typed::Origin::Carried(signature),
                );
                for ((_, deriv), (_, &var)) in evidence.iter().zip(evidence_vars.iter()) {
                    let known = self.derivation(deriv);
                    self.ctx.set_deriv(var, DerivAssign::Equal(known));
                }
                self.ctx
                    .new_var(Assign::Constrained(*id, arg_vars, evidence_vars))
            }

            elab::Type::Tuple(items) => {
                let item_vars = items.iter().map(|item| self.type_(item)).collect();
                self.ctx.new_var(Assign::Tuple(item_vars))
            }

            elab::Type::Func(purity, arg, ret) => {
                let arg_var = self.type_(arg);
                let ret_var = self.type_(ret);
                self.ctx.new_var(Assign::Func(*purity, arg_var, ret_var))
            }
        }
    }

    fn types(&mut self, types: &[elab::Type<Derivation<G>>]) -> Vec<TypeVar> {
        types.iter().map(|type_| self.type_(type_)).collect()
    }

    /// The obligation a derivation stands for, with the derivation as its evidence and the
    /// constraint it proves as its goal.
    fn derivation(&mut self, deriv: &Derivation<G>) -> ObligationVar {
        match deriv {
            Derivation::Given(given) => (self.given_of)(given),

            Derivation::Impl(id, args, subs) => {
                let arg_vars = args.map_refs(|_, arg| self.type_(arg));
                let sub_vars = subs.map_refs(|_, sub| self.derivation(sub));
                let res::ImplId::Custom(custom) = id;
                let impl_def = &self.program.impls[*custom];
                let goal_args = Inst {
                    ctx: &mut *self.ctx,
                    program: self.program,
                    span: self.span,
                    signature: self.signature,
                    param_vars: &arg_vars,
                    given_of: &|given: &res::TraitConstrId| sub_vars[*given],
                }
                .types(&impl_def.head);
                self.ctx.new_obligation(
                    impl_def.trait_,
                    goal_args,
                    self.span,
                    typed::Origin::Carried(self.signature),
                    DerivAssign::Impl(*id, arg_vars, sub_vars),
                )
            }

            Derivation::Super(inner, index) => {
                let inner_var = self.derivation(inner);
                let (inner_trait, inner_args) = {
                    let inner_obligation = &self.ctx.obligations[inner_var];
                    (
                        inner_obligation.trait_,
                        IdVec::from_vec(inner_obligation.args.clone()),
                    )
                };
                let res::TraitId::Custom(custom) = inner_trait;
                let super_ = &self.program.traits[custom].supers[*index];
                let goal_args = Inst {
                    ctx: &mut *self.ctx,
                    program: self.program,
                    span: self.span,
                    signature: self.signature,
                    param_vars: &inner_args,
                    given_of: &|TraitSelfConstr| inner_var,
                }
                .types(&super_.args);
                self.ctx.new_obligation(
                    super_.trait_,
                    goal_args,
                    self.span,
                    typed::Origin::Carried(self.signature),
                    DerivAssign::Super(inner_var, *index),
                )
            }
        }
    }
}

/// Fresh, undetermined obligations for each constraint of a constrained type at the given
/// arguments, which cover at least the parameters the constraints mention.
fn constr_obligations(
    ctx: &mut Context,
    program: &elab::Program,
    span: (usize, usize),
    id: res::CustomTypeId,
    arg_vars: &[TypeVar],
    origin_of: &dyn Fn(res::TraitConstrId) -> typed::Origin,
) -> IdVec<res::TraitConstrId, ObligationVar> {
    let typedef = &program.custom_types[id];
    let arg_vars = IdVec::from_vec(arg_vars.to_vec());
    // The goals refer to each other's evidence, so all are allocated before any is filled in.
    let evidence = typedef.trait_constrs.map_refs(|constr_id, constr| {
        ctx.new_obligation(
            constr.trait_,
            Vec::new(),
            span,
            origin_of(constr_id),
            DerivAssign::Unknown,
        )
    });
    for (constr_id, constr) in &typedef.trait_constrs {
        let args = Inst {
            ctx: &mut *ctx,
            program,
            span,
            signature: typed::Signature::TypeDecl(id),
            param_vars: &arg_vars,
            given_of: &|given: &res::TraitConstrId| evidence[*given],
        }
        .types(&constr.args);
        ctx.obligations[evidence[constr_id]].args = args;
    }
    evidence
}

/// Instantiates a written type from a body, over the enclosing definition's rigid parameters.
/// A constrained type in it gets undetermined obligations, solved after inference unless
/// unification determines them.
fn instantiate_annotation(
    ctx: &mut Context,
    program: &elab::Program,
    span: (usize, usize),
    rigid_params: &IdVec<res::TypeParamId, TypeVar>,
    type_: &res::Type,
) -> Result<TypeVar, RawError> {
    match type_ {
        res::Type::App(head, args) => {
            let arg_vars = args
                .iter()
                .map(|arg| instantiate_annotation(ctx, program, span, rigid_params, arg))
                .collect::<Result<Vec<_>, _>>()?;
            match head {
                res::TypeHead::Ctor(res::TypeId::Custom(id))
                    if !program.custom_types[*id].trait_constrs.is_empty() =>
                {
                    if arg_vars.len() < ctx.constrained_prefix[*id].to_value() {
                        return Err(RawErrorKind::PartialConstrained {
                            type_: *id,
                            given: arg_vars.len(),
                        }
                        .into());
                    }
                    let evidence =
                        constr_obligations(ctx, program, span, *id, &arg_vars, &|constr| {
                            typed::Origin::Annotation(*id, constr)
                        });
                    Ok(ctx.new_var(Assign::Constrained(*id, arg_vars, evidence)))
                }
                res::TypeHead::Ctor(id) => Ok(ctor_app_var(ctx, *id, arg_vars)),
                res::TypeHead::Var(param) => Ok(app_var(ctx, rigid_params[param], arg_vars)),
            }
        }

        res::Type::Tuple(items) => {
            let item_vars = items
                .iter()
                .map(|item| instantiate_annotation(ctx, program, span, rigid_params, item))
                .collect::<Result<_, _>>()?;
            Ok(ctx.new_var(Assign::Tuple(item_vars)))
        }

        res::Type::Func(purity, arg, ret) => {
            let arg_var = instantiate_annotation(ctx, program, span, rigid_params, arg)?;
            let ret_var = instantiate_annotation(ctx, program, span, rigid_params, ret)?;
            Ok(ctx.new_var(Assign::Func(*purity, arg_var, ret_var)))
        }
    }
}

/// Instantiates a scheme at the given parameter variables, with one obligation per trait
/// constraint of the scheme, whose evidence is `evidence_of`.  The constraints' own evidence refers
/// to each other, so all obligations are allocated before any goal is filled in.
fn instantiate_scheme_at(
    ctx: &mut Context,
    program: &elab::Program,
    span: (usize, usize),
    scheme: &elab::TypeScheme,
    signature: typed::Signature,
    param_vars: &IdVec<res::TypeParamId, TypeVar>,
    origin_of: impl Fn(res::TraitConstrId) -> typed::Origin,
    evidence_of: impl Fn(res::TraitConstrId) -> DerivAssign,
) -> (TypeVar, IdVec<res::TraitConstrId, ObligationVar>) {
    let obligations = scheme.trait_constrs.map_refs(|constr_id, constr| {
        ctx.new_obligation(
            constr.trait_,
            Vec::new(),
            span,
            origin_of(constr_id),
            evidence_of(constr_id),
        )
    });
    for (constr_id, constr) in &scheme.trait_constrs {
        let args = Inst {
            ctx: &mut *ctx,
            program,
            span,
            signature,
            param_vars,
            given_of: &|given: &res::TraitConstrId| obligations[*given],
        }
        .types(&constr.args);
        ctx.obligations[obligations[constr_id]].args = args;
    }
    let root = Inst {
        ctx: &mut *ctx,
        program,
        span,
        signature,
        param_vars,
        given_of: &|given: &res::TraitConstrId| obligations[*given],
    }
    .type_(&scheme.body);
    (root, obligations)
}

/// Instantiates a scheme with fresh variables, recording one undetermined obligation per trait
/// constraint of the scheme.  They are discharged by the trait solver once the whole definition
/// has been inferred, unless unification determines their evidence first.
fn instantiate_scheme(
    ctx: &mut Context,
    program: &elab::Program,
    span: (usize, usize),
    global: res::GlobalId,
    scheme: &elab::TypeScheme,
) -> (
    IdVec<res::TypeParamId, TypeVar>,
    TypeVar,
    IdVec<res::TraitConstrId, ObligationVar>,
) {
    let param_vars =
        IdVec::from_count_with(scheme.param_kinds.count(), |_| ctx.new_var(Assign::Unknown));
    let (root, obligations) = instantiate_scheme_at(
        ctx,
        program,
        span,
        scheme,
        typed::Signature::Global(global),
        &param_vars,
        |constr| typed::Origin::GlobalConstr(global, constr),
        |_| DerivAssign::Unknown,
    );
    (param_vars, root, obligations)
}

/// Instantiates the enclosing definition's own scheme: its parameters are rigid, and its
/// constraints are the givens.  Its obligations are located at the whole definition.
fn instantiate_rigid(
    ctx: &mut Context,
    program: &elab::Program,
    span: (usize, usize),
    scheme: &elab::TypeScheme,
) -> (IdVec<res::TypeParamId, TypeVar>, TypeVar) {
    let rigid_params = scheme
        .param_kinds
        .map_refs(|param, _| ctx.new_var(Assign::Param(param)));
    let (root, _) = instantiate_scheme_at(
        ctx,
        program,
        span,
        scheme,
        typed::Signature::Own,
        &rigid_params,
        typed::Origin::OwnConstr,
        DerivAssign::Given,
    );
    (rigid_params, root)
}

fn infer_pat(
    program: &elab::Program,
    ctx: &mut Context,
    scope: &mut Scope,
    expected: TypeVar,
    pat: &res::Pattern,
) -> Result<AnnotPattern, RawError> {
    match pat {
        res::Pattern::Any => Ok(AnnotPattern::Any(expected)),

        res::Pattern::Var => {
            scope.add_local(expected);
            Ok(AnnotPattern::Var(expected))
        }

        res::Pattern::Tuple(items) => {
            let item_vars: Vec<TypeVar> = (0..items.len())
                .map(|_| ctx.new_var(Assign::Unknown))
                .collect();
            let tuple_var = ctx.new_var(Assign::Tuple(item_vars.clone()));

            ctx.unify(expected, tuple_var)?;

            let items_annot = items
                .iter()
                .zip(item_vars)
                .map(|(item, item_var)| infer_pat(program, ctx, scope, item_var, item))
                .collect::<Result<_, _>>()?;

            Ok(AnnotPattern::Tuple(items_annot))
        }

        res::Pattern::Ctor(id, variant, content) => {
            // The type of the whole pattern, and the type its content is expected to have,
            // which for a constrained type refers to the evidence the whole pattern's type carries.
            let (param_vars, ctor_var, expected_content) = match id {
                res::TypeId::Custom(custom) => {
                    let typedef = &program.custom_types[custom];
                    let param_vars = typedef
                        .param_kinds
                        .map_refs(|_, _| ctx.new_var(Assign::Unknown));
                    let evidence = if typedef.trait_constrs.is_empty() {
                        IdVec::new()
                    } else {
                        constr_obligations(
                            ctx,
                            program,
                            scope.span,
                            *custom,
                            param_vars.as_slice(),
                            &|constr| typed::Origin::Pattern(*custom, constr),
                        )
                    };
                    let ctor_var = if typedef.trait_constrs.is_empty() {
                        ctor_app_var(ctx, *id, param_vars.clone().into_vec())
                    } else {
                        ctx.new_var(Assign::Constrained(
                            *custom,
                            param_vars.clone().into_vec(),
                            evidence.clone(),
                        ))
                    };
                    let expected_content = typedef.variants[variant].as_ref().map(|content| {
                        Inst {
                            ctx: &mut *ctx,
                            program,
                            span: scope.span,
                            signature: typed::Signature::TypeDecl(*custom),
                            param_vars: &param_vars,
                            given_of: &|given: &res::TraitConstrId| evidence[*given],
                        }
                        .type_(content)
                    });
                    (param_vars, ctor_var, expected_content)
                }

                res::TypeId::Bool => {
                    let ctor_var = ctor_app_var(ctx, *id, Vec::new());
                    (IdVec::new(), ctor_var, None)
                }

                _ => unreachable!(),
            };

            ctx.unify(expected, ctor_var)?;

            let content_annot = match (expected_content, content) {
                (Some(expected_var), Some(content)) => {
                    let content_annot = infer_pat(program, ctx, scope, expected_var, content)?;
                    Some(Box::new(content_annot))
                }

                (None, None) => None,

                (Some(_), None) => {
                    return Err(RawErrorKind::ExpectedCtorArg {
                        id: *id,
                        variant: *variant,
                    }
                    .into());
                }

                (None, Some(_)) => {
                    return Err(RawErrorKind::UnexpectedCtorArg {
                        id: *id,
                        variant: *variant,
                    }
                    .into());
                }
            };

            let ctor_annot = AnnotPattern::Ctor(
                *id,
                param_vars.into_vec(),
                *variant,
                content_annot,
                ctor_var,
            );

            Ok(ctor_annot)
        }

        res::Pattern::Annot(content, type_) => {
            // The annotation is what the user declared, so it plays the role of the expected
            // type; whatever the surrounding context provides is the actual type.  Unify before
            // descending so that nested patterns see the annotated structure.
            let annot_var =
                instantiate_annotation(ctx, program, scope.span, &scope.rigid_params, type_)?;
            ctx.unify(annot_var, expected)?;
            infer_pat(program, ctx, scope, expected, content)
        }

        &res::Pattern::ByteConst(val) => {
            let const_var = ctx.new_var(Assign::Ctor(res::TypeId::Byte));
            ctx.unify(expected, const_var)?;
            Ok(AnnotPattern::ByteConst(val))
        }

        &res::Pattern::IntConst(val) => {
            let const_var = ctx.new_var(Assign::Ctor(res::TypeId::Int));
            ctx.unify(expected, const_var)?;
            Ok(AnnotPattern::IntConst(val))
        }

        &res::Pattern::FloatConst(val) => {
            let const_var = ctx.new_var(Assign::Ctor(res::TypeId::Float));
            ctx.unify(expected, const_var)?;
            Ok(AnnotPattern::FloatConst(val))
        }

        res::Pattern::Span(lo, hi, content) => Ok(AnnotPattern::Span(
            *lo,
            *hi,
            Box::new(
                infer_pat(program, ctx, scope, expected, content).map_err(locate_span(*lo, *hi))?,
            ),
        )),
    }
}

fn infer_expr(
    program: &elab::Program,
    ctx: &mut Context,
    scope: &mut Scope,
    expected: TypeVar,
    expr: &res::Expr,
) -> Result<AnnotExpr, RawError> {
    match expr {
        &res::Expr::Global(res::GlobalRef::Global(id)) => {
            let scheme = global_scheme(program, id);
            let (param_vars, var, obligations) =
                instantiate_scheme(ctx, program, scope.span, id, &scheme);
            ctx.unify(expected, var)?;
            Ok(AnnotExpr::Global(id, param_vars, var, obligations))
        }

        &res::Expr::Global(res::GlobalRef::TraitFunc(trait_, func)) => {
            let res::TraitId::Custom(custom) = trait_;
            let trait_def = &program.traits[custom];
            let sig = &trait_def.funcs[func];
            let layout = trait_def.func_layout(func);

            let trait_vars =
                IdVec::from_count_with(layout.num_trait_params, |_| ctx.new_var(Assign::Unknown));
            let func_vars =
                IdVec::from_count_with(layout.num_own_params, |_| ctx.new_var(Assign::Unknown));
            let all_vars = layout.params(trait_vars.clone(), func_vars.clone());

            // The signature's evidence refers to the trait's own constraint and to the func's own
            // constraints, so those obligations exist before anything is instantiated.
            let trait_obligation = ctx.new_obligation(
                trait_,
                trait_vars.values().copied().collect(),
                scope.span,
                typed::Origin::TraitFuncTrait(trait_, func),
                DerivAssign::Unknown,
            );
            let func_obligations = sig.own_constrs.map_refs(|constr_id, constr| {
                ctx.new_obligation(
                    constr.trait_,
                    Vec::new(),
                    scope.span,
                    typed::Origin::TraitFuncConstr(trait_, func, constr_id),
                    DerivAssign::Unknown,
                )
            });
            let given_of = |given: &TraitGiven| match given {
                TraitGiven::SelfConstr => trait_obligation,
                TraitGiven::Own(constr) => func_obligations[*constr],
            };
            for (constr_id, constr) in &sig.own_constrs {
                let args = Inst {
                    ctx: &mut *ctx,
                    program,
                    span: scope.span,
                    signature: typed::Signature::TraitFunc(trait_, func),
                    param_vars: &all_vars,
                    given_of: &given_of,
                }
                .types(&constr.args);
                ctx.obligations[func_obligations[constr_id]].args = args;
            }
            let whole = Inst {
                ctx: &mut *ctx,
                program,
                span: scope.span,
                signature: typed::Signature::TraitFunc(trait_, func),
                param_vars: &all_vars,
                given_of: &given_of,
            }
            .type_(&sig.body);

            ctx.unify(expected, whole)?;
            Ok(AnnotExpr::TraitFunc(
                trait_,
                func,
                AnnotTraitFuncInst {
                    trait_vars,
                    trait_obligation,
                    func_vars,
                    func_obligations,
                    whole,
                },
            ))
        }

        &res::Expr::Local(id) => {
            ctx.unify(expected, scope.local(id))?;
            Ok(AnnotExpr::Local(id))
        }

        res::Expr::Tuple(items) => {
            let item_vars: Vec<TypeVar> = (0..items.len())
                .map(|_| ctx.new_var(Assign::Unknown))
                .collect();
            let tuple_var = ctx.new_var(Assign::Tuple(item_vars.clone()));

            ctx.unify(expected, tuple_var)?;

            let items_annot = items
                .iter()
                .zip(item_vars)
                .map(|(item, item_var)| infer_expr(program, ctx, scope, item_var, item))
                .collect::<Result<_, _>>()?;

            Ok(AnnotExpr::Tuple(items_annot))
        }

        res::Expr::Lam(purity, pat, body, prof_id) => scope.with_subscope(|subscope| {
            let arg_var = ctx.new_var(Assign::Unknown);
            let ret_var = ctx.new_var(Assign::Unknown);
            let lam_var = ctx.new_var(Assign::Func(*purity, arg_var, ret_var));

            ctx.unify(expected, lam_var)?;

            let pat_annot = infer_pat(program, ctx, subscope, arg_var, pat)?;

            let body_annot = infer_expr(program, ctx, subscope, ret_var, &body)?;

            let lam_annot = AnnotExpr::Lam(
                *purity,
                arg_var,
                ret_var,
                pat_annot,
                Box::new(body_annot),
                *prof_id,
                lam_var,
            );

            Ok(lam_annot)
        }),

        res::Expr::App(purity, func, arg) => {
            let arg_var = ctx.new_var(Assign::Unknown);
            let ret_var = ctx.new_var(Assign::Unknown);
            let func_var = ctx.new_var(Assign::Func(*purity, arg_var, ret_var));

            let func_annot = infer_expr(program, ctx, scope, func_var, func)?;

            ctx.unify(expected, ret_var)?;

            let arg_annot = infer_expr(program, ctx, scope, arg_var, arg)?;

            let app_annot = AnnotExpr::App(*purity, Box::new(func_annot), Box::new(arg_annot));

            Ok(app_annot)
        }

        res::Expr::Match(discrim, cases) => {
            let discrim_var = ctx.new_var(Assign::Unknown);

            let discrim_annot = infer_expr(program, ctx, scope, discrim_var, discrim)?;

            let cases_annot = cases
                .iter()
                .map(|(pat, body)| {
                    scope.with_subscope(|subscope| {
                        let pat_annot = infer_pat(program, ctx, subscope, discrim_var, pat)?;

                        let body_annot = infer_expr(program, ctx, subscope, expected, &body)?;

                        Ok((pat_annot, body_annot))
                    })
                })
                .collect::<Result<_, RawError>>()?;

            Ok(AnnotExpr::Match(
                Box::new(discrim_annot),
                cases_annot,
                expected,
            ))
        }

        res::Expr::LetMany(bindings, body) => scope.with_subscope(|subscope| {
            let mut new_bindings = Vec::new();

            for (lhs, rhs) in bindings {
                let rhs_var = ctx.new_var(Assign::Unknown);
                let rhs_annot = infer_expr(program, ctx, subscope, rhs_var, rhs)?;

                let lhs_annot = infer_pat(program, ctx, subscope, rhs_var, lhs)?;

                new_bindings.push((lhs_annot, rhs_annot));
            }

            let body_annot = infer_expr(program, ctx, subscope, expected, body)?;

            Ok(AnnotExpr::LetMany(new_bindings, Box::new(body_annot)))
        }),

        res::Expr::ArrayLit(items) => {
            let param_var = ctx.new_var(Assign::Unknown);
            let array_var = ctor_app_var(ctx, res::TypeId::Array, vec![param_var]);

            ctx.unify(expected, array_var)?;

            let items_annot = items
                .iter()
                .map(|item| infer_expr(program, ctx, scope, param_var, item))
                .collect::<Result<_, RawError>>()?;

            let array_annot = AnnotExpr::ArrayLit(param_var, items_annot, array_var);
            Ok(array_annot)
        }

        &res::Expr::ByteLit(val) => {
            let lit_var = ctx.new_var(Assign::Ctor(res::TypeId::Byte));
            ctx.unify(expected, lit_var)?;
            Ok(AnnotExpr::ByteLit(val))
        }

        &res::Expr::IntLit(val) => {
            let lit_var = ctx.new_var(Assign::Ctor(res::TypeId::Int));
            ctx.unify(expected, lit_var)?;
            Ok(AnnotExpr::IntLit(val))
        }

        &res::Expr::FloatLit(val) => {
            let lit_var = ctx.new_var(Assign::Ctor(res::TypeId::Float));
            ctx.unify(expected, lit_var)?;
            Ok(AnnotExpr::FloatLit(val))
        }

        res::Expr::Span(lo, hi, body) => {
            let enclosing = std::mem::replace(&mut scope.span, (*lo, *hi));
            let body_annot =
                infer_expr(program, ctx, scope, expected, body).map_err(locate_span(*lo, *hi));
            scope.span = enclosing;
            Ok(AnnotExpr::Span(*lo, *hi, Box::new(body_annot?)))
        }
    }
}

/// Maps the obligations of the inferred body to the typed program's, in which obligations that
/// unification identified are one.
type ObligationIds<'a> = dyn Fn(ObligationVar) -> typed::ObligationId + 'a;

fn extract_pat_solution(
    ctx: &Context,
    ids: &ObligationIds,
    body: AnnotPattern,
) -> Result<typed::Pattern, RawError> {
    match body {
        AnnotPattern::Any(var) => Ok(typed::Pattern::Any(ctx.extract(var, ids)?)),

        AnnotPattern::Var(var) => Ok(typed::Pattern::Var(ctx.extract(var, ids)?)),

        AnnotPattern::Tuple(items) => Ok(typed::Pattern::Tuple(
            items
                .into_iter()
                .map(|item| extract_pat_solution(ctx, ids, item))
                .collect::<Result<_, _>>()?,
        )),

        AnnotPattern::Ctor(id, vars, variant, content, whole) => Ok(typed::Pattern::Ctor(
            id,
            vars.into_iter()
                .map(|var| ctx.extract(var, ids))
                .collect::<Result<_, _>>()
                .map_err(|err| report_ambiguity_at(err, whole))?,
            variant,
            content
                .map::<Result<_, RawError>, _>(|content| {
                    Ok(Box::new(extract_pat_solution(ctx, ids, *content)?))
                })
                .transpose()?,
        )),

        AnnotPattern::ByteConst(val) => Ok(typed::Pattern::ByteConst(val)),
        AnnotPattern::IntConst(val) => Ok(typed::Pattern::IntConst(val)),
        AnnotPattern::FloatConst(val) => Ok(typed::Pattern::FloatConst(val)),

        AnnotPattern::Span(lo, hi, content) => Ok(typed::Pattern::Span(
            lo,
            hi,
            Box::new(extract_pat_solution(ctx, ids, *content).map_err(locate_span(lo, hi))?),
        )),
    }
}

// An ambiguity found while extracting one component of an expression's type (an instantiation
// parameter of a global, the argument type of a lambda, ...) is reported in terms of the whole
// expression's type, since that is what the user sees at the reported span.
fn report_ambiguity_at(err: RawError, whole: TypeVar) -> RawError {
    err.map(|kind| match kind {
        RawErrorKind::Ambiguous { .. } => RawErrorKind::Ambiguous { type_: whole },
        other => other,
    })
}

fn annot_expr_span(expr: &AnnotExpr) -> Option<(usize, usize)> {
    match expr {
        &AnnotExpr::Span(lo, hi, _) => Some((lo, hi)),
        _ => None,
    }
}

fn extract_solution(
    ctx: &Context,
    ids: &ObligationIds,
    body: AnnotExpr,
) -> Result<typed::Expr, RawError> {
    match body {
        AnnotExpr::Global(id, vars, whole, obligations) => Ok(typed::Expr::Global(
            id,
            vars.try_map(|_param_id, var| ctx.extract(var, ids))
                .map_err(|err| report_ambiguity_at(err, whole))?,
            obligations.map_refs(|_, &obligation| ids(obligation)),
        )),

        AnnotExpr::TraitFunc(trait_, func, inst) => Ok(typed::Expr::TraitFunc(
            trait_,
            func,
            elab::TraitFuncInst {
                trait_args: inst
                    .trait_vars
                    .try_map(|_param_id, var| ctx.extract(var, ids))
                    .map_err(|err| report_ambiguity_at(err, inst.whole))?,
                trait_deriv: ids(inst.trait_obligation),
                func_args: inst
                    .func_vars
                    .try_map(|_param_id, var| ctx.extract(var, ids))
                    .map_err(|err| report_ambiguity_at(err, inst.whole))?,
                func_derivs: inst
                    .func_obligations
                    .map_refs(|_, &obligation| ids(obligation)),
            },
        )),

        AnnotExpr::Local(id) => Ok(typed::Expr::Local(id)),

        AnnotExpr::Tuple(items) => Ok(typed::Expr::Tuple(
            items
                .into_iter()
                .map(|item| extract_solution(ctx, ids, item))
                .collect::<Result<_, _>>()?,
        )),

        AnnotExpr::Lam(purity, arg_type, ret_type, pat, body, prof_id, whole) => {
            Ok(typed::Expr::Lam(
                purity,
                ctx.extract(arg_type, ids)
                    .map_err(|err| report_ambiguity_at(err, whole))?,
                ctx.extract(ret_type, ids)
                    .map_err(|err| report_ambiguity_at(err, whole))?,
                extract_pat_solution(ctx, ids, pat)?,
                Box::new(extract_solution(ctx, ids, *body)?),
                prof_id,
            ))
        }

        AnnotExpr::App(purity, func, arg) => {
            // Extract the argument before the function so that an ambiguity caused by a dead
            // polymorphic argument (e.g. passing `id` to something that ignores it) is reported at
            // the argument rather than at the callee whose instantiation merely mentions it.
            let arg_typed = extract_solution(ctx, ids, *arg)?;
            let func_typed = extract_solution(ctx, ids, *func)?;
            Ok(typed::Expr::App(
                purity,
                Box::new(func_typed),
                Box::new(arg_typed),
            ))
        }

        AnnotExpr::Match(discrim, cases, result_var) => Ok(typed::Expr::Match(
            Box::new(extract_solution(ctx, ids, *discrim)?),
            cases
                .into_iter()
                .map(|(pat, body)| {
                    Ok((
                        extract_pat_solution(ctx, ids, pat)?,
                        extract_solution(ctx, ids, body)?,
                    ))
                })
                .collect::<Result<_, RawError>>()?,
            ctx.extract(result_var, ids)?,
        )),

        AnnotExpr::LetMany(bindings, body) => Ok(typed::Expr::LetMany(
            bindings
                .into_iter()
                .map(|(lhs, rhs)| {
                    // Extract the right-hand side first so that an ambiguity inside it is
                    // reported at the most specific span available.  If the ambiguity only
                    // surfaces through the pattern (as with a desugared `then`, whose pattern
                    // has no span of its own), fall back to the span of the right-hand side.
                    let rhs_span = annot_expr_span(&rhs);
                    let rhs_typed = extract_solution(ctx, ids, rhs)?;
                    let lhs_typed =
                        extract_pat_solution(ctx, ids, lhs).map_err(|err| match rhs_span {
                            Some((lo, hi)) => locate_span(lo, hi)(err),
                            None => err,
                        })?;
                    Ok((lhs_typed, rhs_typed))
                })
                .collect::<Result<_, RawError>>()?,
            Box::new(extract_solution(ctx, ids, *body)?),
        )),

        AnnotExpr::ArrayLit(item_var, items, whole) => Ok(typed::Expr::ArrayLit(
            ctx.extract(item_var, ids)
                .map_err(|err| report_ambiguity_at(err, whole))?,
            items
                .into_iter()
                .map(|item| extract_solution(ctx, ids, item))
                .collect::<Result<_, _>>()?,
        )),

        AnnotExpr::ByteLit(val) => Ok(typed::Expr::ByteLit(val)),

        AnnotExpr::IntLit(val) => Ok(typed::Expr::IntLit(val)),

        AnnotExpr::FloatLit(val) => Ok(typed::Expr::FloatLit(val)),

        AnnotExpr::Span(lo, hi, body) => Ok(typed::Expr::Span(
            lo,
            hi,
            Box::new(extract_solution(ctx, ids, *body).map_err(locate_span(lo, hi))?),
        )),
    }
}

/// Extracts the obligations of an inferred definition.  Obligations that unification identified
/// become one, and every reference to any of them is to that one.
fn extract_obligations(
    ctx: &Context,
) -> Result<
    (
        IdVec<ObligationVar, typed::ObligationId>,
        IdVec<typed::ObligationId, typed::Obligation>,
    ),
    RawError,
> {
    let mut representative_ids: IdVec<ObligationVar, Option<typed::ObligationId>> =
        ctx.obligations.map_refs(|_, _| None);
    let mut representatives = Vec::new();
    for (var, _) in &ctx.obligations {
        if ctx.follow_deriv(var) == var {
            representative_ids[var] = Some(typed::ObligationId(representatives.len()));
            representatives.push(var);
        }
    }
    let ids = ctx.obligations.map_refs(|var, _| {
        representative_ids[ctx.follow_deriv(var)].expect("every representative has an id")
    });
    let id_of = |var: ObligationVar| ids[var];

    let mut obligations = IdVec::new();
    for &var in &representatives {
        let obligation = &ctx.obligations[var];
        let at_obligation = |err: ExtractError| -> RawError {
            let kind = match err {
                ExtractError::Recursive => RawErrorKind::Recursive,
                ExtractError::Unknown => RawErrorKind::AmbiguousConstr { obligation: var },
            };
            let (lo, hi) = obligation.span;
            locate_span(lo, hi)(kind.into())
        };
        let goal = elab::TraitApp {
            trait_: obligation.trait_,
            args: obligation
                .args
                .iter()
                .map(|&arg| ctx.extract_rec(arg, &id_of))
                .collect::<Result<_, _>>()
                .map_err(at_obligation)?,
        };
        let evidence = match obligation.assign.borrow().deref() {
            DerivAssign::Equal(_) => unreachable!("representatives are not equal to others"),
            DerivAssign::Unknown => typed::Evidence::Unknown,
            &DerivAssign::Given(given) => typed::Evidence::Given(given),
            DerivAssign::Impl(id, args, subs) => typed::Evidence::Impl(
                *id,
                args.try_map_refs(|_, &arg| ctx.extract_rec(arg, &id_of))
                    .map_err(at_obligation)?,
                subs.map_refs(|_, &sub| id_of(sub)),
            ),
            &DerivAssign::Super(inner, index) => typed::Evidence::Super(id_of(inner), index),
        };
        let pushed = obligations.push(typed::Obligation {
            goal,
            span: obligation.span,
            origin: obligation.origin.clone(),
            evidence,
        });
        debug_assert_eq!(pushed, ids[var]);
    }

    Ok((ids, obligations))
}

// The 'Context' argument provided to this function should always be empty initially.  We take it as
// an argument rather than constructing it internally so that the caller can consult the context for
// reporting information if an error occurs.
fn infer_def(
    ctx: &mut Context,
    program: &elab::Program,
    def: &elab::ValDef,
    span: (usize, usize),
) -> Result<typed::ValDef, RawError> {
    let (rigid_params, declared_type_var) = instantiate_rigid(ctx, program, span, &def.scheme);

    let mut scope = Scope::new(rigid_params, span);

    let body_annot = infer_expr(program, ctx, &mut scope, declared_type_var, &def.body)?;

    // Obligations are extracted before the body, so that a variable left undetermined in a trait
    // constraint is reported as an ambiguous constraint, naming the trait, rather than merely as
    // an ambiguous type.
    let (ids, obligations) = extract_obligations(ctx)?;
    let id_of = |var: ObligationVar| ids[var];

    let evidence_equations = ctx
        .evidence_equations
        .borrow()
        .iter()
        .map(|&(var1, var2)| (id_of(var1), id_of(var2)))
        .collect();

    let body_typed = extract_solution(ctx, &id_of, body_annot)?;

    Ok(typed::ValDef {
        scheme: def.scheme.clone(),
        body: body_typed,
        obligations,
        evidence_equations,
    })
}

pub fn type_infer(program: elab::Program) -> Result<typed::Program, Error> {
    let constrained_prefix = program
        .custom_types
        .map_refs(|_, def| def.constrained_prefix());

    let vals_inferred = program
        .vals
        .try_map_refs(|id, def| {
            let val_symbols = &program.val_symbols[id];

            let mut ctx = Context::new(&constrained_prefix);

            infer_def(&mut ctx, &program, &def, val_symbols.span)
                .map_err(locate_path(&program.mod_symbols[val_symbols.mod_].file))
                .map_err(|located| {
                    located.map(|err| err.render(&program, &val_symbols.type_param_names, &ctx))
                })
        })
        .map_err(Error)?;

    Ok(typed::Program {
        mod_symbols: program.mod_symbols.clone(),
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        profile_points: program.profile_points,
        vals: vals_inferred,
        val_symbols: program.val_symbols,
        traits: program.traits,
        trait_symbols: program.trait_symbols,
        impls: program.impls,
        impl_symbols: program.impl_symbols,
        impl_scope: program.impl_scope,
        main: program.main,
    })
}
