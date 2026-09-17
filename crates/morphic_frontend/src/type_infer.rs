use std::borrow::Cow;
use std::cell::{RefCell, RefMut};
use std::io;
use std::ops::{Deref, DerefMut};

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
use id_collections::{id_type, IdVec};
use morphic_common::intrinsic_config::intrinsic_sig;
use morphic_common::lines;
use morphic_common::report_error::{locate_path, locate_span, ColorMode, Locate, Reportable};

#[id_type]
struct TypeVar(usize);

#[derive(Clone, Copy, Debug)]
enum RawErrorKind {
    Recursive,
    Ambiguous {
        type_: TypeVar,
    },
    AmbiguousConstr {
        obligation: typed::ObligationId,
    },
    Mismatch {
        expected: TypeVar,
        actual: TypeVar,
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
        program: &kinded::Program,
        params: &IdVec<res::TypeParamId, raw::TypeParam>,
        ctx: &Context,
    ) -> ErrorKind {
        match self {
            RawErrorKind::Recursive => ErrorKind::Recursive,

            RawErrorKind::Ambiguous { type_: type_var } => {
                let renderer = report_type::TypeRenderer::new(
                    &program.mod_symbols,
                    &program.custom_type_symbols,
                );
                let type_ = renderer.render(params, &ctx.extract_report(*type_var));
                ErrorKind::Ambiguous { type_ }
            }

            RawErrorKind::AmbiguousConstr { obligation } => {
                let renderer = report_type::TypeRenderer::new(
                    &program.mod_symbols,
                    &program.custom_type_symbols,
                );
                let obligation = &ctx.obligations[*obligation];
                let app = report_type::TraitApp {
                    trait_: obligation.trait_,
                    args: obligation
                        .args
                        .iter()
                        .map(|&arg| ctx.extract_report(arg))
                        .collect(),
                };
                let constr = renderer.render_trait_app(params, &app, &program.trait_symbols);
                ErrorKind::AmbiguousConstr { constr }
            }

            RawErrorKind::Mismatch {
                expected: expected_var,
                actual: actual_var,
            } => {
                let renderer = report_type::TypeRenderer::new(
                    &program.mod_symbols,
                    &program.custom_type_symbols,
                );

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

            RawErrorKind::ExpectedCtorArg { id, variant } => {
                let renderer = report_type::TypeRenderer::new(
                    &program.mod_symbols,
                    &program.custom_type_symbols,
                );

                let (id_rendered, variant_rendered) = renderer.render_ctor(*id, *variant);

                ErrorKind::ExpectedCtorArg {
                    id: id_rendered,
                    variant: variant_rendered,
                }
            }

            RawErrorKind::UnexpectedCtorArg { id, variant } => {
                let renderer = report_type::TypeRenderer::new(
                    &program.mod_symbols,
                    &program.custom_type_symbols,
                );

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
    Tuple(Vec<TypeVar>),
    Func(Purity, TypeVar, TypeVar),
}

/// A trait constraint required by some reference in the body being inferred, over inference
/// variables.  It is extracted to an obligation once inference of the definition is complete.
#[derive(Clone, Debug)]
struct RawObligation {
    trait_: res::TraitId,
    args: Vec<TypeVar>,
    span: Option<(usize, usize)>,
}

#[derive(Clone, Debug)]
struct Context {
    obligations: IdVec<typed::ObligationId, RawObligation>,
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
}

#[derive(Clone, Copy, Debug)]
enum UnifyError {
    Recursive,
    Mismatch,
}

#[derive(Clone, Copy, Debug)]
enum ExtractError {
    Recursive,
    Unknown,
}

impl Context {
    fn new() -> Self {
        Context {
            obligations: IdVec::new(),
            vars: IdVec::new(),
        }
    }

    fn new_var(&mut self, assign: Assign) -> TypeVar {
        self.vars.push(RefCell::new(assign))
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

            Assign::Param(_) | Assign::Ctor(_) | Assign::Tuple(_) | Assign::Func(_, _, _) => {
                Err(UnifyError::Mismatch)
            }
        }
    }

    fn unify(&mut self, expected: TypeVar, actual: TypeVar) -> Result<(), RawError> {
        self.unify_rec(expected, actual).map_err(|err| match err {
            UnifyError::Recursive => RawErrorKind::Recursive.into(),
            UnifyError::Mismatch => RawErrorKind::Mismatch { expected, actual }.into(),
        })
    }

    // Extracts the fully solved type rooted at 'root_var'. If any part of that type is still
    // unconstrained, the whole type is reported as ambiguous, so that the error message can show
    // the user which parts of the type they need to pin down with an annotation. We never
    // silently pick a type for an unconstrained variable since, in the presence of traits (ad hoc
    // polymorphism), this can lead to some pretty confusing behavior.
    fn extract(&self, root_var: TypeVar) -> Result<res::Type, RawError> {
        self.extract_rec(root_var).map_err(|err| match err {
            ExtractError::Recursive => RawErrorKind::Recursive.into(),
            ExtractError::Unknown => RawErrorKind::Ambiguous { type_: root_var }.into(),
        })
    }

    fn extract_rec(&self, root_var: TypeVar) -> Result<res::Type, ExtractError> {
        let var = self.follow(root_var).map_err(|_| ExtractError::Recursive)?;
        let assign = self.obtain(var).map_err(|_| ExtractError::Recursive)?;

        match assign.deref() {
            Assign::Unknown => Err(ExtractError::Unknown),

            &Assign::Equal(_) => unreachable!(),

            &Assign::Param(param) => Ok(res::Type::param(param)),

            &Assign::Ctor(id) => Ok(res::Type::ctor(id)),

            Assign::App(head, args) => {
                let head_type = self.extract_rec(*head)?;
                let arg_types = args
                    .iter()
                    .map(|&arg| self.extract_rec(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(apply_type(head_type, arg_types))
            }

            Assign::Tuple(items) => Ok(res::Type::Tuple(
                items
                    .iter()
                    .map(|&item| self.extract_rec(item))
                    .collect::<Result<_, _>>()?,
            )),

            &Assign::Func(purity, arg, ret) => Ok(res::Type::Func(
                purity,
                Box::new(self.extract_rec(arg)?),
                Box::new(self.extract_rec(ret)?),
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

// Applies an extracted head to further arguments.  A head only ever unifies with another head or
// with an application (see 'unify_head_with_app'), never with a tuple or function type.
fn apply_type(head: res::Type, args: Vec<res::Type>) -> res::Type {
    match head {
        res::Type::App(head, mut head_args) => {
            head_args.extend(args);
            res::Type::App(head, head_args)
        }
        res::Type::Tuple(_) | res::Type::Func(_, _, _) => unreachable!(),
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
    // The innermost enclosing span, updated as inference traverses expressions trees.  Used to
    // attach spans to `RawObligations` so that errors can report where obligtaions arose.
    span: Option<(usize, usize)>,
}

impl Scope {
    fn new(rigid_params: IdVec<res::TypeParamId, TypeVar>) -> Self {
        Scope {
            rigid_params,
            locals: IdVec::new(),
            span: None,
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
        IdVec<res::TraitConstrId, typed::ObligationId>,
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
    trait_obligation: typed::ObligationId,
    func_vars: IdVec<res::TraitFuncParamId, TypeVar>,
    func_obligations: IdVec<res::TraitFuncConstrId, typed::ObligationId>,
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

fn intrinsic_sig_to_scheme(sig: &intrs::Signature) -> kinded::TypeScheme {
    fn trans_type(type_: &intrs::Type) -> res::Type {
        match type_ {
            intrs::Type::Bool => res::Type::ctor(res::TypeId::Bool),
            intrs::Type::Num(NumType::Byte) => res::Type::ctor(res::TypeId::Byte),
            intrs::Type::Num(NumType::Int) => res::Type::ctor(res::TypeId::Int),
            intrs::Type::Num(NumType::Float) => res::Type::ctor(res::TypeId::Float),
            intrs::Type::Tuple(items) => res::Type::Tuple(items.iter().map(trans_type).collect()),
        }
    }

    kinded::TypeScheme {
        param_kinds: IdVec::new(),
        trait_constrs: IdVec::new(),
        body: res::Type::Func(
            sig.purity,
            Box::new(trans_type(&sig.arg)),
            Box::new(trans_type(&sig.ret)),
        ),
    }
}

// Sounds ominous...
pub fn global_scheme(
    program: &kinded::Program,
    global: res::GlobalId,
) -> Cow<'_, kinded::TypeScheme> {
    use crate::data::resolved_ast::Type::*;
    use crate::data::resolved_ast::TypeHead::Ctor;
    use crate::data::resolved_ast::TypeId::*;

    fn bool_() -> res::Type {
        res::Type::ctor(Bool)
    }

    fn byte() -> res::Type {
        res::Type::ctor(Byte)
    }

    fn int() -> res::Type {
        res::Type::ctor(Int)
    }

    fn array(arg: res::Type) -> res::Type {
        App(Ctor(Array), vec![arg])
    }

    fn func(arg: res::Type, ret: res::Type) -> res::Type {
        Func(Purity::Pure, Box::new(arg), Box::new(ret))
    }

    fn impure_func(arg: res::Type, ret: res::Type) -> res::Type {
        Func(Purity::Impure, Box::new(arg), Box::new(ret))
    }

    fn pair(fst: res::Type, snd: res::Type) -> res::Type {
        Tuple(vec![fst, snd])
    }

    // The parameters of builtin globals all have kind `Type`.
    fn scheme(num_params: usize, body: res::Type) -> kinded::TypeScheme {
        kinded::TypeScheme {
            param_kinds: IdVec::from_vec(vec![kinded::Kind::TYPE; num_params]),
            trait_constrs: IdVec::new(),
            body,
        }
    }

    fn param(index: usize) -> res::Type {
        res::Type::param(res::TypeParamId(index))
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

        res::GlobalId::Ctor(Custom(custom), variant) => {
            let typedef = &program.custom_types[custom];
            let ret = App(
                Ctor(Custom(custom)),
                (0..typedef.param_kinds.len()).map(param).collect(),
            );
            let body = match typedef.variants[variant].clone() {
                Some(arg) => func(arg, ret),
                None => ret,
            };
            Cow::Owned(kinded::TypeScheme {
                param_kinds: typedef.param_kinds.clone(),
                trait_constrs: IdVec::new(),
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

fn instantiate_with(
    ctx: &mut Context,
    param_vars: &IdVec<res::TypeParamId, TypeVar>,
    body: &res::Type,
) -> TypeVar {
    match body {
        res::Type::App(head, args) => {
            let head_var = match head {
                res::TypeHead::Var(param) => param_vars[param],
                res::TypeHead::Ctor(id) => ctx.new_var(Assign::Ctor(*id)),
            };

            let arg_vars = args
                .iter()
                .map(|arg| instantiate_with(ctx, param_vars, arg))
                .collect();

            app_var(ctx, head_var, arg_vars)
        }

        res::Type::Tuple(items) => {
            let item_vars = items
                .iter()
                .map(|item| instantiate_with(ctx, param_vars, item))
                .collect();

            ctx.new_var(Assign::Tuple(item_vars))
        }

        res::Type::Func(purity, arg, ret) => {
            let arg_var = instantiate_with(ctx, param_vars, arg);
            let ret_var = instantiate_with(ctx, param_vars, ret);

            ctx.new_var(Assign::Func(*purity, arg_var, ret_var))
        }
    }
}

/// Instantiates a scheme with fresh variables, recording one obligation per trait constraint of
/// the scheme.  Nothing about the obligations influences inference. They are discharged by the
/// trait solver once the whole definition has been inferred.
fn instantiate_scheme(
    ctx: &mut Context,
    span: Option<(usize, usize)>,
    scheme: &kinded::TypeScheme,
) -> (
    IdVec<res::TypeParamId, TypeVar>,
    TypeVar,
    IdVec<res::TraitConstrId, typed::ObligationId>,
) {
    let param_vars = IdVec::from_vec(
        (0..scheme.param_kinds.len())
            .map(|_| ctx.new_var(Assign::Unknown))
            .collect(),
    );

    let root = instantiate_with(ctx, &param_vars, &scheme.body);

    let obligations = scheme.trait_constrs.map_refs(|_, constr| {
        let args = constr
            .args
            .iter()
            .map(|arg| instantiate_with(ctx, &param_vars, arg))
            .collect();
        ctx.obligations.push(RawObligation {
            trait_: constr.trait_,
            args,
            span,
        })
    });

    (param_vars, root, obligations)
}

fn infer_pat(
    program: &kinded::Program,
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
            let (num_params, expected_content) = match id {
                res::TypeId::Custom(custom) => {
                    let typedef = &program.custom_types[custom];
                    let expected_content = typedef.variants[variant].clone();
                    (typedef.param_kinds.len(), expected_content)
                }

                res::TypeId::Bool => (0, None),

                _ => unreachable!(),
            };

            let param_vars = IdVec::from_vec(
                (0..num_params)
                    .map(|_| ctx.new_var(Assign::Unknown))
                    .collect(),
            );

            let ctor_var = ctor_app_var(ctx, *id, param_vars.clone().into_vec());

            ctx.unify(expected, ctor_var)?;

            let content_annot = match (expected_content, content) {
                (Some(ref expected), Some(content)) => {
                    let expected_var = instantiate_with(ctx, &param_vars, expected);
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
            let annot_var = instantiate_with(ctx, &scope.rigid_params, type_);
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
    program: &kinded::Program,
    ctx: &mut Context,
    scope: &mut Scope,
    expected: TypeVar,
    expr: &res::Expr,
) -> Result<AnnotExpr, RawError> {
    match expr {
        &res::Expr::Global(res::GlobalRef::Global(id)) => {
            let scheme = global_scheme(program, id);
            let (param_vars, var, obligations) = instantiate_scheme(ctx, scope.span, &scheme);
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
            let whole = instantiate_with(ctx, &all_vars, &sig.body);

            let trait_obligation = ctx.obligations.push(RawObligation {
                trait_,
                args: trait_vars.iter().map(|(_, &var)| var).collect(),
                span: scope.span,
            });
            let func_obligations = sig.own_constrs.map_refs(|_, constr| {
                let args = constr
                    .args
                    .iter()
                    .map(|arg| instantiate_with(ctx, &all_vars, arg))
                    .collect();
                ctx.obligations.push(RawObligation {
                    trait_: constr.trait_,
                    args,
                    span: scope.span,
                })
            });

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
            let enclosing = scope.span.replace((*lo, *hi));
            let body_annot =
                infer_expr(program, ctx, scope, expected, body).map_err(locate_span(*lo, *hi));
            scope.span = enclosing;
            Ok(AnnotExpr::Span(*lo, *hi, Box::new(body_annot?)))
        }
    }
}

fn instantiate_rigid(
    ctx: &mut Context,
    scheme: &kinded::TypeScheme,
) -> (IdVec<res::TypeParamId, TypeVar>, TypeVar) {
    let rigid_params = scheme
        .param_kinds
        .map_refs(|param, _| ctx.new_var(Assign::Param(param)));

    let root = instantiate_with(ctx, &rigid_params, &scheme.body);

    (rigid_params, root)
}

fn extract_pat_solution(ctx: &Context, body: AnnotPattern) -> Result<typed::Pattern, RawError> {
    match body {
        AnnotPattern::Any(var) => Ok(typed::Pattern::Any(ctx.extract(var)?)),

        AnnotPattern::Var(var) => Ok(typed::Pattern::Var(ctx.extract(var)?)),

        AnnotPattern::Tuple(items) => Ok(typed::Pattern::Tuple(
            items
                .into_iter()
                .map(|item| extract_pat_solution(ctx, item))
                .collect::<Result<_, _>>()?,
        )),

        AnnotPattern::Ctor(id, vars, variant, content, whole) => Ok(typed::Pattern::Ctor(
            id,
            vars.into_iter()
                .map(|var| ctx.extract(var))
                .collect::<Result<_, _>>()
                .map_err(|err| report_ambiguity_at(err, whole))?,
            variant,
            content
                .map::<Result<_, RawError>, _>(|content| {
                    Ok(Box::new(extract_pat_solution(ctx, *content)?))
                })
                .transpose()?,
        )),

        AnnotPattern::ByteConst(val) => Ok(typed::Pattern::ByteConst(val)),
        AnnotPattern::IntConst(val) => Ok(typed::Pattern::IntConst(val)),
        AnnotPattern::FloatConst(val) => Ok(typed::Pattern::FloatConst(val)),

        AnnotPattern::Span(lo, hi, content) => Ok(typed::Pattern::Span(
            lo,
            hi,
            Box::new(extract_pat_solution(ctx, *content).map_err(locate_span(lo, hi))?),
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

fn extract_solution(ctx: &Context, body: AnnotExpr) -> Result<typed::Expr, RawError> {
    match body {
        AnnotExpr::Global(id, vars, whole, obligations) => Ok(typed::Expr::Global(
            id,
            vars.try_map(|_param_id, var| ctx.extract(var))
                .map_err(|err| report_ambiguity_at(err, whole))?,
            obligations,
        )),

        AnnotExpr::TraitFunc(trait_, func, inst) => Ok(typed::Expr::TraitFunc(
            trait_,
            func,
            res::TraitFuncInst {
                trait_args: inst
                    .trait_vars
                    .try_map(|_param_id, var| ctx.extract(var))
                    .map_err(|err| report_ambiguity_at(err, inst.whole))?,
                trait_deriv: inst.trait_obligation,
                func_args: inst
                    .func_vars
                    .try_map(|_param_id, var| ctx.extract(var))
                    .map_err(|err| report_ambiguity_at(err, inst.whole))?,
                func_derivs: inst.func_obligations,
            },
        )),

        AnnotExpr::Local(id) => Ok(typed::Expr::Local(id)),

        AnnotExpr::Tuple(items) => Ok(typed::Expr::Tuple(
            items
                .into_iter()
                .map(|item| extract_solution(ctx, item))
                .collect::<Result<_, _>>()?,
        )),

        AnnotExpr::Lam(purity, arg_type, ret_type, pat, body, prof_id, whole) => {
            Ok(typed::Expr::Lam(
                purity,
                ctx.extract(arg_type)
                    .map_err(|err| report_ambiguity_at(err, whole))?,
                ctx.extract(ret_type)
                    .map_err(|err| report_ambiguity_at(err, whole))?,
                extract_pat_solution(ctx, pat)?,
                Box::new(extract_solution(ctx, *body)?),
                prof_id,
            ))
        }

        AnnotExpr::App(purity, func, arg) => {
            // Extract the argument before the function so that an ambiguity caused by a dead
            // polymorphic argument (e.g. passing `id` to something that ignores it) is reported at
            // the argument rather than at the callee whose instantiation merely mentions it.
            let arg_typed = extract_solution(ctx, *arg)?;
            let func_typed = extract_solution(ctx, *func)?;
            Ok(typed::Expr::App(
                purity,
                Box::new(func_typed),
                Box::new(arg_typed),
            ))
        }

        AnnotExpr::Match(discrim, cases, result_var) => Ok(typed::Expr::Match(
            Box::new(extract_solution(ctx, *discrim)?),
            cases
                .into_iter()
                .map(|(pat, body)| {
                    Ok((
                        extract_pat_solution(ctx, pat)?,
                        extract_solution(ctx, body)?,
                    ))
                })
                .collect::<Result<_, RawError>>()?,
            ctx.extract(result_var)?,
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
                    let rhs_typed = extract_solution(ctx, rhs)?;
                    let lhs_typed =
                        extract_pat_solution(ctx, lhs).map_err(|err| match rhs_span {
                            Some((lo, hi)) => locate_span(lo, hi)(err),
                            None => err,
                        })?;
                    Ok((lhs_typed, rhs_typed))
                })
                .collect::<Result<_, RawError>>()?,
            Box::new(extract_solution(ctx, *body)?),
        )),

        AnnotExpr::ArrayLit(item_var, items, whole) => Ok(typed::Expr::ArrayLit(
            ctx.extract(item_var)
                .map_err(|err| report_ambiguity_at(err, whole))?,
            items
                .into_iter()
                .map(|item| extract_solution(ctx, item))
                .collect::<Result<_, _>>()?,
        )),

        AnnotExpr::ByteLit(val) => Ok(typed::Expr::ByteLit(val)),

        AnnotExpr::IntLit(val) => Ok(typed::Expr::IntLit(val)),

        AnnotExpr::FloatLit(val) => Ok(typed::Expr::FloatLit(val)),

        AnnotExpr::Span(lo, hi, body) => Ok(typed::Expr::Span(
            lo,
            hi,
            Box::new(extract_solution(ctx, *body).map_err(locate_span(lo, hi))?),
        )),
    }
}

// The 'Context' argument provided to this function should always be empty initially.  We take it as
// an argument rather than constructing it internally so that the caller can consult the context for
// reporting information if an error occurs.
fn infer_def(
    ctx: &mut Context,
    program: &kinded::Program,
    def: &kinded::ValDef,
) -> Result<typed::ValDef, RawError> {
    let (rigid_params, declared_type_var) = instantiate_rigid(ctx, &def.scheme);

    let mut scope = Scope::new(rigid_params);

    let body_annot = infer_expr(program, ctx, &mut scope, declared_type_var, &def.body)?;

    // Obligations are extracted before the body, so that a variable left undetermined in a trait
    // constraint is reported as an ambiguous constraint, naming the trait, rather than merely as
    // an ambiguous type.
    let obligations = ctx.obligations.try_map_refs(|id, obligation| {
        let args = obligation
            .args
            .iter()
            .map(|&arg| ctx.extract(arg))
            .collect::<Result<_, _>>()
            .map_err(|err: RawError| {
                err.map(|kind| match kind {
                    RawErrorKind::Ambiguous { .. } => {
                        RawErrorKind::AmbiguousConstr { obligation: id }
                    }
                    other => other,
                })
            })
            .map_err(|err| match obligation.span {
                Some((lo, hi)) => locate_span(lo, hi)(err),
                None => err,
            })?;
        Ok::<_, RawError>(typed::Obligation {
            trait_constr: res::TraitApp {
                trait_: obligation.trait_,
                args,
            },
            span: obligation.span,
        })
    })?;

    let body_typed = extract_solution(ctx, body_annot)?;

    Ok(typed::ValDef {
        scheme: def.scheme.clone(),
        body: body_typed,
        obligations,
    })
}

pub fn type_infer(program: kinded::Program) -> Result<typed::Program, Error> {
    let vals_inferred = program
        .vals
        .try_map_refs(|id, def| {
            let val_symbols = &program.val_symbols[id];

            let mut ctx = Context::new();

            infer_def(&mut ctx, &program, &def)
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
