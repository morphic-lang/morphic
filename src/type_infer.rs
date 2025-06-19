use std::borrow::Cow;
use std::cell::{RefCell, RefMut};
use std::ops::{Deref, DerefMut};

use crate::data::intrinsics as intrs;
use crate::data::num_type::NumType;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use crate::intrinsic_config::intrinsic_sig;
use crate::util::lines::lines;
use crate::{report_type, ErrorId};
use id_collections::{id_type, IdVec};

#[id_type]
struct TypeVar(usize);

#[derive(Clone, Copy, Debug)]
enum RawError {
    Recursive,
    Mismatch {
        expected: TypeVar,
        actual: TypeVar,
    },
    ExpectedCtorArg {
        id: res::NominalType,
        variant: res::VariantId,
    },
    UnexpectedCtorArg {
        id: res::NominalType,
        variant: res::VariantId,
    },
}

#[derive(Clone, Debug)]
pub enum Error {
    Recursive,
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

impl Error {
    fn new(
        program: &res::Program,
        params: &IdVec<res::TypeParamId, raw::TypeParam>,
        ctx: &Context,
        raw_error: RawError,
    ) -> Error {
        match raw_error {
            RawError::Recursive => Error::Recursive,

            RawError::Mismatch {
                expected: expected_var,
                actual: actual_var,
            } => {
                let renderer = report_type::TypeRenderer::new(program);

                let expected_type = ctx.extract_report(expected_var);
                let actual_type = ctx.extract_report(actual_var);

                let expected = renderer.render(params, &expected_type);
                let actual = renderer.render(params, &actual_type);

                let expected_is_concrete = report_type::is_concrete(&expected_type);
                let actual_is_concrete = report_type::is_concrete(&actual_type);

                Error::Mismatch {
                    expected,
                    expected_is_concrete,
                    actual,
                    actual_is_concrete,
                }
            }

            RawError::ExpectedCtorArg { id, variant } => {
                let renderer = report_type::TypeRenderer::new(program);

                let (id_rendered, variant_rendered) = renderer.render_ctor(id, variant);

                Error::ExpectedCtorArg {
                    id: id_rendered,
                    variant: variant_rendered,
                }
            }

            RawError::UnexpectedCtorArg { id, variant } => {
                let renderer = report_type::TypeRenderer::new(program);

                let (id_rendered, variant_rendered) = renderer.render_ctor(id, variant);

                Error::UnexpectedCtorArg {
                    id: id_rendered,
                    variant: variant_rendered,
                }
            }
        }
    }

    pub fn report(&self) -> Report {
        match self {
            Error::Recursive => Report {
                title: "Cyclic Type".to_string(),
                message: Some(lines![
                    "I couldn't infer a type for this expression.",
                    "",
                    "Any type you could try to give this expression would need to mention itself \
                     cyclically in order to type-check.  So a hypothetical type that could make \
                     this expression type-check would need to be infinitely big!"
                ]),
            },

            Error::Mismatch {
                expected,
                expected_is_concrete,
                actual,
                actual_is_concrete,
            } => Report {
                title: "Type Mismatch".to_string(),
                message: Some(format!(
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
                )),
            },

            Error::ExpectedCtorArg { id, variant } => Report {
                title: "Missing Constructor Argument".to_string(),
                message: Some(format!(
                    "The constructor '{}' for the type '{}' is supposed to take an argument.",
                    variant, id,
                )),
            },

            Error::UnexpectedCtorArg { id, variant } => Report {
                title: "Unexpected Constructor Argument".to_string(),
                message: Some(format!(
                    "The constructor '{}' for the type '{}' is not supposed to take an argument.",
                    variant, id,
                )),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Assign {
    Unknown,
    Equal(TypeVar),
    Param(res::TypeParamId),
    App(res::NominalType, Vec<TypeVar>),
    Tuple(Vec<TypeVar>),
    Func(Purity, TypeVar, TypeVar),
    Error(ErrorId),
}

#[derive(Clone, Debug)]
struct Context {
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

impl Context {
    fn new() -> Self {
        Context { vars: IdVec::new() }
    }

    fn new_var(&mut self, assign: Assign) -> TypeVar {
        self.vars.push(RefCell::new(assign))
    }

    fn obtain(&self, var: TypeVar) -> Result<RefMut<Assign>, UnifyError> {
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

            (Assign::App(id1, args1), Assign::App(id2, args2)) => {
                if id1 != id2 {
                    return Err(UnifyError::Mismatch);
                }

                if args1.len() != args2.len() {
                    return Err(UnifyError::Mismatch);
                }

                for (&arg1, &arg2) in args1.iter().zip(args2.iter()) {
                    self.unify_rec(arg1, arg2)?;
                }
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

    fn unify(&mut self, expected: TypeVar, actual: TypeVar) -> Result<(), RawError> {
        self.unify_rec(expected, actual).map_err(|err| match err {
            UnifyError::Recursive => RawErrorKind::Recursive.into(),
            UnifyError::Mismatch => RawErrorKind::Mismatch { expected, actual }.into(),
        })
    }

    fn extract(&self, root_var: TypeVar) -> Result<res::Type, RawError> {
        let var = self.follow(root_var).map_err(|_| RawErrorKind::Recursive)?;
        let assign = self.obtain(var).map_err(|_| RawErrorKind::Recursive)?;

        match assign.deref() {
            Assign::Unknown => {
                // Unconstrained, so we can choose any type we like
                Ok(res::Type::Tuple(vec![]))
            }

            &Assign::Equal(_) => unreachable!(),

            &Assign::Param(param) => Ok(res::Type::Var(param)),

            Assign::App(id, args) => Ok(res::Type::App(
                *id,
                args.iter()
                    .map(|&arg| self.extract(arg))
                    .collect::<Result<_, _>>()?,
            )),

            Assign::Tuple(items) => Ok(res::Type::Tuple(
                items
                    .iter()
                    .map(|&item| self.extract(item))
                    .collect::<Result<_, _>>()?,
            )),

            &Assign::Func(purity, arg, ret) => Ok(res::Type::Func(
                purity,
                Box::new(self.extract(arg)?),
                Box::new(self.extract(ret)?),
            )),
        }
    }

    fn extract_report(&self, root_var: TypeVar) -> report_type::Type {
        let var = match self.follow(root_var) {
            Ok(var) => var,
            Err(_) => {
                return report_type::Type::RecursiveOccurrence;
            }
        };

        let assign = match self.obtain(var) {
            Ok(assign) => assign,
            Err(_) => {
                return report_type::Type::RecursiveOccurrence;
            }
        };

        match assign.deref() {
            Assign::Unknown => report_type::Type::Unknown,

            Assign::Equal(_) => unreachable!(),

            Assign::Param(param) => report_type::Type::Var(*param),

            Assign::App(id, args) => report_type::Type::App(
                *id,
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

#[derive(Clone, Debug)]
struct Scope {
    locals: IdVec<res::LocalId, TypeVar>,
}

impl Scope {
    fn new() -> Self {
        Scope {
            locals: IdVec::new(),
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
    Global(res::Global, IdVec<res::TypeParamId, TypeVar>),
    Local(res::LocalId),
    Tuple(Vec<AnnotExpr>),
    Lam(
        Purity,
        TypeVar, // Argument type
        TypeVar, // Return type
        AnnotPattern,
        Box<AnnotExpr>,
        Option<prof::ProfilePointId>,
    ),
    App(Purity, Box<AnnotExpr>, Box<AnnotExpr>),
    Match(Box<AnnotExpr>, Vec<(AnnotPattern, AnnotExpr)>, TypeVar),
    LetMany(Vec<(AnnotPattern, AnnotExpr)>, Box<AnnotExpr>),

    ArrayLit(TypeVar, Vec<AnnotExpr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),

    Error(ErrorId),
}

#[derive(Clone, Debug)]
enum AnnotPattern {
    Any(TypeVar),
    Var(TypeVar),
    Tuple(Vec<AnnotPattern>),
    Ctor(
        res::NominalType,
        Vec<TypeVar>,
        res::VariantId,
        Option<Box<AnnotPattern>>,
    ),

    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),

    Error(ErrorId),
}

fn intrinsic_sig_to_scheme(sig: &intrs::Signature) -> res::TypeScheme {
    fn trans_type(type_: &intrs::Type) -> res::Type {
        match type_ {
            intrs::Type::Bool => res::Type::App(res::NominalType::Bool, vec![]),
            intrs::Type::Num(NumType::Byte) => res::Type::App(res::NominalType::Byte, vec![]),
            intrs::Type::Num(NumType::Int) => res::Type::App(res::NominalType::Int, vec![]),
            intrs::Type::Num(NumType::Float) => res::Type::App(res::NominalType::Float, vec![]),
            intrs::Type::Tuple(items) => res::Type::Tuple(items.iter().map(trans_type).collect()),
        }
    }

    res::TypeScheme {
        num_params: 0,
        body: res::Type::Func(
            sig.purity,
            Box::new(trans_type(&sig.arg)),
            Box::new(trans_type(&sig.ret)),
        ),
    }
}

// Sounds ominous...
pub fn global_scheme(program: &res::Program, global: res::Global) -> Cow<res::TypeScheme> {
    use crate::data::resolved_ast::NominalType::*;
    use crate::data::resolved_ast::Type::*;

    fn bool_() -> res::Type {
        App(Bool, vec![])
    }

    fn byte() -> res::Type {
        App(Byte, vec![])
    }

    fn int() -> res::Type {
        App(Int, vec![])
    }

    fn array(arg: res::Type) -> res::Type {
        App(Array, vec![arg])
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

    fn scheme(num_params: usize, body: res::Type) -> res::TypeScheme {
        res::TypeScheme { num_params, body }
    }

    fn param(index: usize) -> res::Type {
        Var(res::TypeParamId(index))
    }

    match global {
        res::Global::Intrinsic(intr) => Cow::Owned(intrinsic_sig_to_scheme(&intrinsic_sig(intr))),

        res::Global::ArrayOp(op) => {
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

        res::Global::IoOp(op) => match op {
            res::IoOp::Input => Cow::Owned(scheme(0, impure_func(Tuple(vec![]), array(byte())))),
            res::IoOp::Output => Cow::Owned(scheme(0, impure_func(array(byte()), Tuple(vec![])))),
        },

        res::Global::Panic => Cow::Owned(scheme(1, func(array(byte()), param(0)))),

        res::Global::Ctor(Custom(custom), variant) => {
            let typedef = &program.custom_types[custom];
            let ret = App(Custom(custom), (0..typedef.num_params).map(param).collect());
            if let Some(arg) = typedef.variants[variant].clone() {
                Cow::Owned(scheme(typedef.num_params, func(arg, ret)))
            } else {
                Cow::Owned(scheme(typedef.num_params, ret))
            }
        }

        res::Global::Ctor(Bool, variant) => {
            debug_assert!(variant == res::VariantId(0) || variant == res::VariantId(1));
            Cow::Owned(scheme(0, bool_()))
        }

        res::Global::Ctor(_, _) => unreachable!(),

        res::Global::Custom(custom) => Cow::Borrowed(&program.vals[custom].scheme),
    }
}

fn instantiate_with(
    ctx: &mut Context,
    param_vars: &IdVec<res::TypeParamId, TypeVar>,
    body: &res::Type,
) -> TypeVar {
    match &*body.data {
        res::TypeData::Var(param) => param_vars[param],

        res::TypeData::App(id, args) => {
            let arg_vars = args
                .iter()
                .map(|arg| instantiate_with(ctx, param_vars, arg))
                .collect();

            ctx.new_var(Assign::App(*id, arg_vars))
        }

        res::TypeData::Tuple(items) => {
            let item_vars = items
                .iter()
                .map(|item| instantiate_with(ctx, param_vars, item))
                .collect();

            ctx.new_var(Assign::Tuple(item_vars))
        }

        res::TypeData::Func(purity, arg, ret) => {
            let arg_var = instantiate_with(ctx, param_vars, arg);
            let ret_var = instantiate_with(ctx, param_vars, ret);

            ctx.new_var(Assign::Func(*purity, arg_var, ret_var))
        }

        res::TypeData::Error(id) => ctx.new_var(Assign::Error(*id)),
    }
}

fn instantiate_scheme(
    ctx: &mut Context,
    scheme: &res::TypeScheme,
) -> (IdVec<res::TypeParamId, TypeVar>, TypeVar) {
    let param_vars = IdVec::from_vec(
        (0..scheme.num_params)
            .map(|_| ctx.new_var(Assign::Unknown))
            .collect(),
    );

    let root = instantiate_with(ctx, &param_vars, &scheme.body);

    (param_vars, root)
}

fn infer_pat(
    program: &res::Program,
    ctx: &mut Context,
    scope: &mut Scope,
    expected: TypeVar,
    pat: &res::Pattern,
) -> Result<AnnotPattern, RawError> {
    match &*pat.data {
        res::PatternData::Any => Ok(AnnotPattern::Any(expected)),

        res::PatternData::Var => {
            scope.add_local(expected);
            Ok(AnnotPattern::Var(expected))
        }

        res::PatternData::Tuple(items) => {
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

        res::PatternData::Ctor(id, variant, content) => {
            let (num_params, expected_content) = match id {
                res::NominalType::Custom(custom) => {
                    let typedef = &program.custom_types[custom];
                    let expected_content = typedef.variants[variant].clone();
                    (typedef.num_params, expected_content)
                }

                res::NominalType::Bool => (0, None),

                _ => unreachable!(),
            };

            let param_vars = IdVec::from_vec(
                (0..num_params)
                    .map(|_| ctx.new_var(Assign::Unknown))
                    .collect(),
            );

            let ctor_var = ctx.new_var(Assign::App(*id, param_vars.clone().into_vec()));

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

            let ctor_annot =
                AnnotPattern::Ctor(*id, param_vars.into_vec(), *variant, content_annot);

            Ok(ctor_annot)
        }

        &res::PatternData::ByteConst(val) => {
            let const_var = ctx.new_var(Assign::App(res::NominalType::Byte, vec![]));
            ctx.unify(expected, const_var)?;
            Ok(AnnotPattern::ByteConst(val))
        }

        &res::PatternData::IntConst(val) => {
            let const_var = ctx.new_var(Assign::App(res::NominalType::Int, vec![]));
            ctx.unify(expected, const_var)?;
            Ok(AnnotPattern::IntConst(val))
        }

        &res::PatternData::FloatConst(val) => {
            let const_var = ctx.new_var(Assign::App(res::NominalType::Float, vec![]));
            ctx.unify(expected, const_var)?;
            Ok(AnnotPattern::FloatConst(val))
        }

        &res::PatternData::Error(id) => Ok(AnnotPattern::Error(id)),
    }
}

fn infer_expr(
    program: &res::Program,
    ctx: &mut Context,
    scope: &mut Scope,
    expected: TypeVar,
    expr: &res::Expr,
) -> Result<AnnotExpr, RawError> {
    match &*expr.data {
        &res::ExprData::Global(id) => {
            let scheme = global_scheme(program, id);
            let (param_vars, var) = instantiate_scheme(ctx, &scheme);
            ctx.unify(expected, var)?;
            Ok(AnnotExpr::Global(id, param_vars))
        }

        &res::ExprData::Local(id) => {
            ctx.unify(expected, scope.local(id))?;
            Ok(AnnotExpr::Local(id))
        }

        res::ExprData::Tuple(items) => {
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

        res::ExprData::Lam(purity, pat, body, prof_id) => scope.with_subscope(|subscope| {
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
            );

            Ok(lam_annot)
        }),

        res::ExprData::App(purity, func, arg) => {
            let arg_var = ctx.new_var(Assign::Unknown);
            let ret_var = ctx.new_var(Assign::Unknown);
            let func_var = ctx.new_var(Assign::Func(*purity, arg_var, ret_var));

            let func_annot = infer_expr(program, ctx, scope, func_var, func)?;

            ctx.unify(expected, ret_var)?;

            let arg_annot = infer_expr(program, ctx, scope, arg_var, arg)?;

            let app_annot = AnnotExpr::App(*purity, Box::new(func_annot), Box::new(arg_annot));

            Ok(app_annot)
        }

        res::ExprData::Match(discrim, cases) => {
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

        res::ExprData::LetMany(bindings, body) => scope.with_subscope(|subscope| {
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

        res::ExprData::ArrayLit(items) => {
            let param_var = ctx.new_var(Assign::Unknown);
            let array_var = ctx.new_var(Assign::App(res::NominalType::Array, vec![param_var]));

            ctx.unify(expected, array_var)?;

            let items_annot = items
                .iter()
                .map(|item| infer_expr(program, ctx, scope, param_var, item))
                .collect::<Result<_, RawError>>()?;

            let array_annot = AnnotExpr::ArrayLit(param_var, items_annot);
            Ok(array_annot)
        }

        &res::ExprData::ByteLit(val) => {
            let lit_var = ctx.new_var(Assign::App(res::NominalType::Byte, vec![]));
            ctx.unify(expected, lit_var)?;
            Ok(AnnotExpr::ByteLit(val))
        }

        &res::ExprData::IntLit(val) => {
            let lit_var = ctx.new_var(Assign::App(res::NominalType::Int, vec![]));
            ctx.unify(expected, lit_var)?;
            Ok(AnnotExpr::IntLit(val))
        }

        &res::ExprData::FloatLit(val) => {
            let lit_var = ctx.new_var(Assign::App(res::NominalType::Float, vec![]));
            ctx.unify(expected, lit_var)?;
            Ok(AnnotExpr::FloatLit(val))
        }

        &res::ExprData::Error(id) => Ok(AnnotExpr::Error(id)),
    }
}

fn instantiate_rigid(ctx: &mut Context, scheme: &res::TypeScheme) -> TypeVar {
    let rigid_params = IdVec::from_vec(
        (0..scheme.num_params)
            .map(|idx| ctx.new_var(Assign::Param(res::TypeParamId(idx))))
            .collect(),
    );

    instantiate_with(ctx, &rigid_params, &scheme.body)
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

        AnnotPattern::Ctor(id, vars, variant, content) => Ok(typed::Pattern::Ctor(
            id,
            vars.into_iter()
                .map(|var| ctx.extract(var))
                .collect::<Result<_, _>>()?,
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

        AnnotPattern::Error(id) => Ok(typed::Pattern::Error(id)),
    }
}

fn extract_solution(ctx: &Context, body: AnnotExpr) -> Result<typed::Expr, RawError> {
    match body {
        AnnotExpr::Global(id, vars) => Ok(typed::Expr::Global(
            id,
            vars.try_map(|_param_id, var| ctx.extract(var))?,
        )),

        AnnotExpr::Local(id) => Ok(typed::Expr::Local(id)),

        AnnotExpr::Tuple(items) => Ok(typed::Expr::Tuple(
            items
                .into_iter()
                .map(|item| extract_solution(ctx, item))
                .collect::<Result<_, _>>()?,
        )),

        AnnotExpr::Lam(purity, arg_type, ret_type, pat, body, prof_id) => Ok(typed::Expr::Lam(
            purity,
            ctx.extract(arg_type)?,
            ctx.extract(ret_type)?,
            extract_pat_solution(ctx, pat)?,
            Box::new(extract_solution(ctx, *body)?),
            prof_id,
        )),

        AnnotExpr::App(purity, func, arg) => Ok(typed::Expr::App(
            purity,
            Box::new(extract_solution(ctx, *func)?),
            Box::new(extract_solution(ctx, *arg)?),
        )),

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
                    Ok((extract_pat_solution(ctx, lhs)?, extract_solution(ctx, rhs)?))
                })
                .collect::<Result<_, RawError>>()?,
            Box::new(extract_solution(ctx, *body)?),
        )),

        AnnotExpr::ArrayLit(item_var, items) => Ok(typed::Expr::ArrayLit(
            ctx.extract(item_var)?,
            items
                .into_iter()
                .map(|item| extract_solution(ctx, item))
                .collect::<Result<_, _>>()?,
        )),

        AnnotExpr::ByteLit(val) => Ok(typed::Expr::ByteLit(val)),

        AnnotExpr::IntLit(val) => Ok(typed::Expr::IntLit(val)),

        AnnotExpr::FloatLit(val) => Ok(typed::Expr::FloatLit(val)),

        AnnotExpr::Error(id) => Ok(typed::Expr::Error(id)),
    }
}

// The 'Context' argument provided to this function should always be empty initially.  We take it as
// an argument rather than constructing it internally so that the caller can consult the context for
// reporting information if an error occurs.
fn infer_def(
    ctx: &mut Context,
    program: &res::Program,
    def: &res::ValDef,
) -> Result<typed::ValDef, RawError> {
    let mut scope = Scope::new();

    let declared_type_var = instantiate_rigid(ctx, &def.scheme);

    let body_annot = infer_expr(program, ctx, &mut scope, declared_type_var, &def.body)?;

    let body_typed = extract_solution(ctx, body_annot)?;

    Ok(typed::ValDef {
        scheme: def.scheme.clone(),
        body: body_typed,
    })
}

pub fn type_infer(program: res::Program) -> Result<typed::Program, Error> {
    let vals_inferred = program.vals.try_map_refs(|id, def| {
        let val_symbols = &program.val_symbols[id];

        let mut ctx = Context::new();

        infer_def(&mut ctx, &program, &def)
            .map_err(locate_path(&program.mod_symbols[val_symbols.mod_].file))
            .map_err(|located| {
                located.map(|err| err.render(&program, &val_symbols.type_param_names, &ctx))
            })
    })?;

    Ok(typed::Program {
        mod_symbols: program.mod_symbols.clone(),
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        profile_points: program.profile_points,
        vals: vals_inferred,
        val_symbols: program.val_symbols,
        main: program.main,
    })
}
