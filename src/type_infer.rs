use std::borrow::Cow;
use std::cell::{RefCell, RefMut};
use std::io;
use std::ops::{Deref, DerefMut};

use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use crate::file_cache::FileCache;
use crate::report_error::{locate_path, locate_span, Locate};
use crate::report_type;
use crate::util::id_vec::IdVec;

id_type!(TypeVar);

#[derive(Clone, Copy, Debug)]
enum RawErrorKind {
    Recursive,
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

pub type Error = Locate<ErrorKind>;

impl RawErrorKind {
    fn render(
        &self,
        program: &res::Program,
        params: &IdVec<res::TypeParamId, raw::TypeParam>,
        ctx: &Context,
    ) -> ErrorKind {
        match self {
            RawErrorKind::Recursive => ErrorKind::Recursive,

            RawErrorKind::Mismatch {
                expected: expected_var,
                actual: actual_var,
            } => {
                let renderer = report_type::TypeRenderer::new(program);

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
                let renderer = report_type::TypeRenderer::new(program);

                let (id_rendered, variant_rendered) = renderer.render_ctor(*id, *variant);

                ErrorKind::ExpectedCtorArg {
                    id: id_rendered,
                    variant: variant_rendered,
                }
            }

            RawErrorKind::UnexpectedCtorArg { id, variant } => {
                let renderer = report_type::TypeRenderer::new(program);

                let (id_rendered, variant_rendered) = renderer.render_ctor(*id, *variant);

                ErrorKind::UnexpectedCtorArg {
                    id: id_rendered,
                    variant: variant_rendered,
                }
            }
        }
    }
}

impl Error {
    pub fn report(&self, dest: &mut impl io::Write, files: &FileCache) -> io::Result<()> {
        self.report_with(dest, files, |err| match err {
            ErrorKind::Recursive => (
                "Cyclic Type",
                lines![
                    "I couldn't infer a type for this expression.",
                    "",
                    "Any type you could try to give this expression would need to mention itself \
                     cyclically in order to type-check.  So a hypothetical type that could make \
                     this expression type-check would need to be infinitely big!"
                ]
                .to_owned(),
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Assign {
    Unknown,
    Equal(TypeVar),
    Param(res::TypeParamId),
    App(res::TypeId, Vec<TypeVar>),
    Tuple(Vec<TypeVar>),
    Func(Purity, TypeVar, TypeVar),
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
        let len = self.locals.len();
        let result = body(self);
        self.locals.truncate(len);
        result
    }
}

#[derive(Clone, Debug)]
enum AnnotExpr {
    Global(res::GlobalId, IdVec<res::TypeParamId, TypeVar>),
    Local(res::LocalId),
    Tuple(Vec<AnnotExpr>),
    Lam(
        Purity,
        TypeVar, // Argument type
        TypeVar, // Return type
        AnnotPattern,
        Box<AnnotExpr>,
    ),
    App(Purity, Box<AnnotExpr>, Box<AnnotExpr>),
    Match(Box<AnnotExpr>, Vec<(AnnotPattern, AnnotExpr)>, TypeVar),
    Let(AnnotPattern, Box<AnnotExpr>, Box<AnnotExpr>),

    ArrayLit(TypeVar, Vec<AnnotExpr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),

    Span(usize, usize, Box<AnnotExpr>),
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
    ),

    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

// Sounds ominous...
pub fn global_scheme(program: &res::Program, global: res::GlobalId) -> Cow<res::TypeScheme> {
    use crate::data::resolved_ast::Type::*;
    use crate::data::resolved_ast::TypeId::*;

    fn bool_() -> res::Type {
        App(Bool, vec![])
    }

    fn byte() -> res::Type {
        App(Byte, vec![])
    }

    fn int() -> res::Type {
        App(Int, vec![])
    }

    fn float() -> res::Type {
        App(Float, vec![])
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

    fn byte_binop() -> res::Type {
        func(pair(byte(), byte()), byte())
    }

    fn byte_comp() -> res::Type {
        func(pair(byte(), byte()), bool_())
    }

    fn int_binop() -> res::Type {
        func(pair(int(), int()), int())
    }

    fn int_comp() -> res::Type {
        func(pair(int(), int()), bool_())
    }

    fn float_binop() -> res::Type {
        func(pair(float(), float()), float())
    }

    fn float_comp() -> res::Type {
        func(pair(float(), float()), bool_())
    }

    fn scheme(num_params: usize, body: res::Type) -> res::TypeScheme {
        res::TypeScheme { num_params, body }
    }

    fn param(index: usize) -> res::Type {
        Var(res::TypeParamId(index))
    }

    match global {
        res::GlobalId::ArithOp(op) => {
            use crate::data::raw_ast::Op::*;
            let body = match op {
                AddByte => byte_binop(),
                SubByte => byte_binop(),
                MulByte => byte_binop(),
                DivByte => byte_binop(),
                NegByte => func(byte(), byte()),

                EqByte => byte_comp(),
                LtByte => byte_comp(),
                LteByte => byte_comp(),

                AddInt => int_binop(),
                SubInt => int_binop(),
                MulInt => int_binop(),
                DivInt => int_binop(),
                NegInt => func(int(), int()),

                EqInt => int_comp(),
                LtInt => int_comp(),
                LteInt => int_comp(),

                AddFloat => float_binop(),
                SubFloat => float_binop(),
                MulFloat => float_binop(),
                DivFloat => float_binop(),
                NegFloat => func(float(), float()),

                EqFloat => float_comp(),
                LtFloat => float_comp(),
                LteFloat => float_comp(),
            };
            Cow::Owned(scheme(0, body))
        }

        res::GlobalId::ArrayOp(op) => {
            use crate::data::resolved_ast::ArrayOp::*;
            let result = match op {
                Item => scheme(
                    1,
                    func(
                        pair(array(param(0)), int()),
                        pair(param(0), func(param(0), array(param(0)))),
                    ),
                ),
                Len => scheme(1, func(array(param(0)), int())),
                Push => scheme(1, func(pair(array(param(0)), param(0)), array(param(0)))),
                Pop => scheme(1, func(array(param(0)), pair(array(param(0)), param(0)))),
            };
            Cow::Owned(result)
        }

        res::GlobalId::IOOp(op) => match op {
            res::IOOp::Input => Cow::Owned(scheme(0, impure_func(Tuple(vec![]), array(byte())))),
            res::IOOp::Output => Cow::Owned(scheme(0, impure_func(array(byte()), Tuple(vec![])))),
        },

        res::GlobalId::Ctor(Custom(custom), variant) => {
            let typedef = &program.custom_types[custom];
            let ret = App(Custom(custom), (0..typedef.num_params).map(param).collect());
            if let Some(arg) = typedef.variants[variant].clone() {
                Cow::Owned(scheme(typedef.num_params, func(arg, ret)))
            } else {
                Cow::Owned(scheme(typedef.num_params, ret))
            }
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
        res::Type::Var(param) => param_vars[param],

        res::Type::App(id, args) => {
            let arg_vars = args
                .iter()
                .map(|arg| instantiate_with(ctx, param_vars, arg))
                .collect();

            ctx.new_var(Assign::App(*id, arg_vars))
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

fn instantiate_scheme(
    ctx: &mut Context,
    scheme: &res::TypeScheme,
) -> (IdVec<res::TypeParamId, TypeVar>, TypeVar) {
    let param_vars = IdVec::from_items(
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
    pat: &res::Pattern,
) -> Result<(AnnotPattern, TypeVar), RawError> {
    match pat {
        res::Pattern::Any => {
            let var = ctx.new_var(Assign::Unknown);
            Ok((AnnotPattern::Any(var), var))
        }

        res::Pattern::Var => {
            let var = ctx.new_var(Assign::Unknown);
            scope.add_local(var);
            Ok((AnnotPattern::Var(var), var))
        }

        res::Pattern::Tuple(items) => {
            let mut items_annot = Vec::new();
            let mut item_vars = Vec::new();
            for item in items {
                let (item_annot, item_var) = infer_pat(program, ctx, scope, item)?;
                items_annot.push(item_annot);
                item_vars.push(item_var);
            }

            let tuple_annot = AnnotPattern::Tuple(items_annot);
            let tuple_var = ctx.new_var(Assign::Tuple(item_vars));
            Ok((tuple_annot, tuple_var))
        }

        res::Pattern::Ctor(id, variant, content) => {
            let (num_params, expected_content) = match id {
                res::TypeId::Custom(custom) => {
                    let typedef = &program.custom_types[custom];
                    let expected_content = typedef.variants[variant].clone();
                    (typedef.num_params, expected_content)
                }

                res::TypeId::Bool => (0, None),

                _ => unreachable!(),
            };

            let param_vars = IdVec::from_items(
                (0..num_params)
                    .map(|_| ctx.new_var(Assign::Unknown))
                    .collect(),
            );

            let content_annot = match (expected_content, content) {
                (Some(ref expected), Some(content)) => {
                    let (content_annot, content_var) = infer_pat(program, ctx, scope, content)?;
                    let expected_var = instantiate_with(ctx, &param_vars, expected);
                    ctx.unify(content_var, expected_var)?;
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
                AnnotPattern::Ctor(*id, param_vars.items.clone(), *variant, content_annot);

            let ctor_var = ctx.new_var(Assign::App(*id, param_vars.items));

            Ok((ctor_annot, ctor_var))
        }

        &res::Pattern::ByteConst(val) => Ok((
            AnnotPattern::ByteConst(val),
            ctx.new_var(Assign::App(res::TypeId::Byte, vec![])),
        )),

        &res::Pattern::IntConst(val) => Ok((
            AnnotPattern::IntConst(val),
            ctx.new_var(Assign::App(res::TypeId::Int, vec![])),
        )),

        &res::Pattern::FloatConst(val) => Ok((
            AnnotPattern::FloatConst(val),
            ctx.new_var(Assign::App(res::TypeId::Float, vec![])),
        )),
    }
}

fn infer_expr(
    program: &res::Program,
    ctx: &mut Context,
    scope: &mut Scope,
    expected: TypeVar,
    expr: &res::Expr,
) -> Result<AnnotExpr, RawError> {
    match expr {
        &res::Expr::Global(id) => {
            let scheme = global_scheme(program, id);
            let (param_vars, var) = instantiate_scheme(ctx, &scheme);
            ctx.unify(expected, var)?;
            Ok(AnnotExpr::Global(id, param_vars))
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

        res::Expr::Lam(purity, pat, body) => scope.with_subscope(|subscope| {
            let arg_var = ctx.new_var(Assign::Unknown);
            let ret_var = ctx.new_var(Assign::Unknown);
            let lam_var = ctx.new_var(Assign::Func(*purity, arg_var, ret_var));

            ctx.unify(expected, lam_var)?;

            let (pat_annot, pat_var) = infer_pat(program, ctx, subscope, pat)?;

            ctx.unify(arg_var, pat_var)?;

            let body_annot = infer_expr(program, ctx, subscope, ret_var, &body)?;

            let lam_annot =
                AnnotExpr::Lam(*purity, arg_var, ret_var, pat_annot, Box::new(body_annot));

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
                        let (pat_annot, pat_var) = infer_pat(program, ctx, subscope, pat)?;

                        ctx.unify(discrim_var, pat_var)?;

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

        res::Expr::Let(lhs, rhs, body) => {
            let rhs_var = ctx.new_var(Assign::Unknown);
            let rhs_annot = infer_expr(program, ctx, scope, rhs_var, rhs)?;

            let (lhs_annot, body_annot) = (scope.with_subscope(|subscope| {
                let (lhs_annot, lhs_var) = infer_pat(program, ctx, subscope, lhs)?;
                ctx.unify(rhs_var, lhs_var)?;
                Ok((
                    lhs_annot,
                    infer_expr(program, ctx, subscope, expected, body)?,
                ))
            }) as Result<_, RawError>)?;

            let let_annot = AnnotExpr::Let(lhs_annot, Box::new(rhs_annot), Box::new(body_annot));
            Ok(let_annot)
        }

        res::Expr::ArrayLit(items) => {
            let param_var = ctx.new_var(Assign::Unknown);
            let array_var = ctx.new_var(Assign::App(res::TypeId::Array, vec![param_var]));

            ctx.unify(expected, array_var)?;

            let items_annot = items
                .iter()
                .map(|item| infer_expr(program, ctx, scope, param_var, item))
                .collect::<Result<_, RawError>>()?;

            let array_annot = AnnotExpr::ArrayLit(param_var, items_annot);
            Ok(array_annot)
        }

        &res::Expr::ByteLit(val) => {
            let lit_var = ctx.new_var(Assign::App(res::TypeId::Byte, vec![]));
            ctx.unify(expected, lit_var)?;
            Ok(AnnotExpr::ByteLit(val))
        }

        &res::Expr::IntLit(val) => {
            let lit_var = ctx.new_var(Assign::App(res::TypeId::Int, vec![]));
            ctx.unify(expected, lit_var)?;
            Ok(AnnotExpr::IntLit(val))
        }

        &res::Expr::FloatLit(val) => {
            let lit_var = ctx.new_var(Assign::App(res::TypeId::Float, vec![]));
            ctx.unify(expected, lit_var)?;
            Ok(AnnotExpr::FloatLit(val))
        }

        res::Expr::Span(lo, hi, body) => Ok(AnnotExpr::Span(
            *lo,
            *hi,
            Box::new(
                infer_expr(program, ctx, scope, expected, body).map_err(locate_span(*lo, *hi))?,
            ),
        )),
    }
}

fn instantiate_rigid(ctx: &mut Context, scheme: &res::TypeScheme) -> TypeVar {
    let rigid_params = IdVec::from_items(
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
    }
}

fn extract_solution(ctx: &Context, body: AnnotExpr) -> Result<typed::Expr, RawError> {
    match body {
        AnnotExpr::Global(id, vars) => Ok(typed::Expr::Global(
            id,
            vars.try_map(|_param_id, &var| ctx.extract(var))?,
        )),

        AnnotExpr::Local(id) => Ok(typed::Expr::Local(id)),

        AnnotExpr::Tuple(items) => Ok(typed::Expr::Tuple(
            items
                .into_iter()
                .map(|item| extract_solution(ctx, item))
                .collect::<Result<_, _>>()?,
        )),

        AnnotExpr::Lam(purity, arg_type, ret_type, pat, body) => Ok(typed::Expr::Lam(
            purity,
            ctx.extract(arg_type)?,
            ctx.extract(ret_type)?,
            extract_pat_solution(ctx, pat)?,
            Box::new(extract_solution(ctx, *body)?),
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

        AnnotExpr::Let(lhs, rhs, body) => Ok(typed::Expr::Let(
            extract_pat_solution(ctx, lhs)?,
            Box::new(extract_solution(ctx, *rhs)?),
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

        AnnotExpr::Span(lo, hi, body) => extract_solution(ctx, *body).map_err(locate_span(lo, hi)),
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
    let vals_inferred = program.vals.try_map(|id, def| {
        let val_symbols = &program.val_symbols[id];

        let mut ctx = Context::new();

        infer_def(&mut ctx, &program, def)
            .map_err(locate_path(&program.mod_symbols[val_symbols.mod_].file))
            .map_err(|located| {
                located.map(|err| err.render(&program, &val_symbols.type_param_names, &ctx))
            })
    })?;

    Ok(typed::Program {
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        vals: vals_inferred,
        val_symbols: program.val_symbols,
        main: program.main,
    })
}
