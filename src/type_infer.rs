use failure::Fail;
use std::borrow::Cow;
use std::mem::replace;

use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;

// TODO: Improve these error messages!
#[derive(Clone, Debug, Fail)]
pub enum Error {
    #[fail(display = "Illegal recursive type")]
    RecursiveType,

    #[fail(display = "Cannot match distinct type parameters")]
    ParamMismatch(res::TypeParamId, res::TypeParamId),

    #[fail(display = "Cannot match distinct type constructors")]
    AppMismatch(res::TypeId, res::TypeId),

    #[fail(
        display = "Cannot match type constructor of arity {} with one of arity {}",
        _1, _2
    )]
    ArityMismatch(res::TypeId, usize, usize),

    #[fail(display = "Cannot match tuple of size {} with one of size {}", _0, _1)]
    TupleArityMismatch(usize, usize),

    // TODO: These are all bad, but this is inexcusable
    #[fail(display = "Cannot unify types of different forms")]
    FormMismatch,

    #[fail(display = "Expected constructor argument")]
    ExpectedCtorArg(res::TypeId, res::VariantId),

    #[fail(display = "Unexpected constructor argument")]
    UnexpectedCtorArg(res::TypeId, res::VariantId),

    #[fail(display = "Function purity mismatch")]
    PurityMismatch,
}

#[derive(Clone, Debug, Fail)]
#[fail(display = "Type error in {}: {}", def, error)]
pub struct LocatedError {
    def: String,
    #[cause]
    error: Error,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TypeVar(usize);

#[derive(Clone, Debug, PartialEq, Eq)]
enum Assign {
    Unknown,
    Equal(TypeVar),
    Param(res::TypeParamId),
    App(res::TypeId, Vec<TypeVar>),
    Tuple(Vec<TypeVar>),
    Func(Purity, TypeVar, TypeVar),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum AssignState {
    Available(Assign),
    Recursing,
}

#[derive(Clone, Debug)]
struct Context {
    vars: Vec<AssignState>,
}

impl Context {
    fn new() -> Self {
        Context { vars: Vec::new() }
    }

    fn new_var(&mut self, assign: Assign) -> TypeVar {
        let id = TypeVar(self.vars.len());
        self.vars.push(AssignState::Available(assign));
        id
    }

    fn obtain(&mut self, var: TypeVar) -> Result<Assign, Error> {
        let state = replace(&mut self.vars[var.0], AssignState::Recursing);
        match state {
            AssignState::Available(assign) => Ok(assign),
            AssignState::Recursing => Err(Error::RecursiveType),
        }
    }

    fn assign(&mut self, var: TypeVar, assign: Assign) {
        debug_assert_eq!(self.vars[var.0], AssignState::Recursing);
        self.vars[var.0] = AssignState::Available(assign);
    }

    fn follow(&mut self, var: TypeVar) -> Result<TypeVar, Error> {
        let assign = self.obtain(var)?;
        if let Assign::Equal(other) = assign {
            let dest = self.follow(other)?;
            self.assign(var, Assign::Equal(dest));
            Ok(dest)
        } else {
            self.assign(var, assign);
            Ok(var)
        }
    }

    fn unify(&mut self, root_var1: TypeVar, root_var2: TypeVar) -> Result<(), Error> {
        let var1 = self.follow(root_var1)?;
        let var2 = self.follow(root_var2)?;

        if var1 == var2 {
            return Ok(());
        }

        let assign1 = self.obtain(var1)?;
        let assign2 = self.obtain(var2)?;

        match (&assign1, &assign2) {
            (Assign::Equal(_), _) => unreachable!(),
            (_, Assign::Equal(_)) => unreachable!(),

            (Assign::Unknown, _) => {
                self.assign(var1, Assign::Equal(var2));
                self.assign(var2, assign2);
                return Ok(());
            }

            (_, Assign::Unknown) => {
                self.assign(var1, assign1);
                self.assign(var2, Assign::Equal(var1));
                return Ok(());
            }

            (Assign::Param(param1), Assign::Param(param2)) => {
                if param1 != param2 {
                    return Err(Error::ParamMismatch(*param1, *param2));
                }
            }

            (Assign::App(id1, args1), Assign::App(id2, args2)) => {
                if id1 != id2 {
                    return Err(Error::AppMismatch(*id1, *id2));
                }

                if args1.len() != args2.len() {
                    return Err(Error::ArityMismatch(*id1, args1.len(), args2.len()));
                }

                for (&arg1, &arg2) in args1.iter().zip(args2.iter()) {
                    self.unify(arg1, arg2)?;
                }
            }

            (Assign::Tuple(items1), Assign::Tuple(items2)) => {
                if items1.len() != items2.len() {
                    return Err(Error::TupleArityMismatch(items1.len(), items2.len()));
                }

                for (&item1, &item2) in items1.iter().zip(items2.iter()) {
                    self.unify(item1, item2)?;
                }
            }

            (Assign::Func(purity1, arg1, ret1), Assign::Func(purity2, arg2, ret2)) => {
                if purity1 != purity2 {
                    return Err(Error::PurityMismatch);
                }

                self.unify(*arg1, *arg2)?;
                self.unify(*ret1, *ret2)?;
            }

            _ => {
                return Err(Error::FormMismatch);
            }
        }

        // This is purely an optimization
        self.assign(var1, Assign::Equal(var2));
        self.assign(var2, assign2);

        Ok(())
    }

    fn extract(&self, var: TypeVar) -> res::Type {
        let assign = match &self.vars[var.0] {
            AssignState::Available(assign) => assign,
            AssignState::Recursing => unreachable!(),
        };

        match assign {
            Assign::Unknown => {
                // Unconstrained, so we can choose any type we like
                res::Type::Tuple(vec![])
            }

            &Assign::Equal(other) => self.extract(other),

            &Assign::Param(param) => res::Type::Var(param),

            Assign::App(id, args) => {
                res::Type::App(*id, args.iter().map(|&arg| self.extract(arg)).collect())
            }

            Assign::Tuple(items) => {
                res::Type::Tuple(items.iter().map(|&item| self.extract(item)).collect())
            }

            &Assign::Func(purity, arg, ret) => res::Type::Func(
                purity,
                Box::new(self.extract(arg)),
                Box::new(self.extract(ret)),
            ),
        }
    }
}

#[derive(Clone, Debug)]
struct Scope {
    // Indexed by LocalId
    locals: Vec<TypeVar>,
}

impl Scope {
    fn new() -> Self {
        Scope { locals: Vec::new() }
    }

    fn add_local(&mut self, var: TypeVar) {
        self.locals.push(var);
    }

    fn local(&self, id: res::LocalId) -> TypeVar {
        self.locals[id.0]
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
    Global(res::GlobalId, Vec<TypeVar>),
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

    fn int_binop() -> res::Type {
        func(pair(int(), int()), int())
    }

    fn byte_comp() -> res::Type {
        func(pair(byte(), byte()), bool_())
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
                NegFloat => float_binop(),

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
            let typedef = &program.custom_types[custom.0];
            let ret = App(Custom(custom), (0..typedef.num_params).map(param).collect());
            if let Some(arg) = typedef.variants[variant.0].clone() {
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

        res::GlobalId::Custom(custom) => Cow::Borrowed(&program.vals[custom.0].scheme),
    }
}

fn instantiate_with(ctx: &mut Context, param_vars: &[TypeVar], body: &res::Type) -> TypeVar {
    match body {
        res::Type::Var(param) => param_vars[param.0],

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

fn instantiate_scheme(ctx: &mut Context, scheme: &res::TypeScheme) -> (Vec<TypeVar>, TypeVar) {
    let param_vars: Vec<_> = (0..scheme.num_params)
        .map(|_| ctx.new_var(Assign::Unknown))
        .collect();

    let root = instantiate_with(ctx, &param_vars, &scheme.body);

    (param_vars, root)
}

fn infer_pat(
    program: &res::Program,
    ctx: &mut Context,
    scope: &mut Scope,
    pat: &res::Pattern,
) -> Result<(AnnotPattern, TypeVar), Error> {
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
                    let typedef = &program.custom_types[custom.0];
                    let expected_content = typedef.variants[variant.0].clone();
                    (typedef.num_params, expected_content)
                }

                res::TypeId::Bool => (0, None),

                _ => unreachable!(),
            };

            let param_vars: Vec<_> = (0..num_params)
                .map(|_| ctx.new_var(Assign::Unknown))
                .collect();

            let content_annot = match (expected_content, content) {
                (Some(ref expected), Some(content)) => {
                    let (content_annot, content_var) = infer_pat(program, ctx, scope, content)?;
                    let expected_var = instantiate_with(ctx, &param_vars, expected);
                    ctx.unify(content_var, expected_var)?;
                    Some(Box::new(content_annot))
                }

                (None, None) => None,

                (Some(_), None) => return Err(Error::ExpectedCtorArg(*id, *variant)),

                (None, Some(_)) => return Err(Error::UnexpectedCtorArg(*id, *variant)),
            };

            let ctor_annot = AnnotPattern::Ctor(*id, param_vars.clone(), *variant, content_annot);

            let ctor_var = ctx.new_var(Assign::App(*id, param_vars));

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
    expr: &res::Expr,
) -> Result<(AnnotExpr, TypeVar), Error> {
    match expr {
        &res::Expr::Global(id) => {
            let scheme = global_scheme(program, id);
            let (param_vars, var) = instantiate_scheme(ctx, &scheme);
            Ok((AnnotExpr::Global(id, param_vars), var))
        }

        &res::Expr::Local(id) => Ok((AnnotExpr::Local(id), scope.local(id))),

        res::Expr::Tuple(items) => {
            let mut items_annot = Vec::new();
            let mut item_vars = Vec::new();
            for item in items {
                let (item_annot, item_var) = infer_expr(program, ctx, scope, item)?;
                items_annot.push(item_annot);
                item_vars.push(item_var);
            }

            let tuple_annot = AnnotExpr::Tuple(items_annot);
            let tuple_var = ctx.new_var(Assign::Tuple(item_vars));
            Ok((tuple_annot, tuple_var))
        }

        res::Expr::Lam(purity, pat, body) => scope.with_subscope(|subscope| {
            let (pat_annot, pat_var) = infer_pat(program, ctx, subscope, pat)?;
            let (body_annot, body_var) = infer_expr(program, ctx, subscope, &body)?;

            let lam_annot =
                AnnotExpr::Lam(*purity, pat_var, body_var, pat_annot, Box::new(body_annot));

            let lam_var = ctx.new_var(Assign::Func(*purity, pat_var, body_var));
            Ok((lam_annot, lam_var))
        }),

        res::Expr::App(purity, func, arg) => {
            let (func_annot, func_var) = infer_expr(program, ctx, scope, &func)?;
            let (arg_annot, arg_var) = infer_expr(program, ctx, scope, &arg)?;

            let ret_var = ctx.new_var(Assign::Unknown);
            let expected_func_var = ctx.new_var(Assign::Func(*purity, arg_var, ret_var));
            ctx.unify(expected_func_var, func_var)?;

            let app_annot = AnnotExpr::App(*purity, Box::new(func_annot), Box::new(arg_annot));
            Ok((app_annot, ret_var))
        }

        res::Expr::Match(discrim, cases) => {
            let (discrim_annot, discrim_var) = infer_expr(program, ctx, scope, discrim)?;

            let result_var = ctx.new_var(Assign::Unknown);

            let cases_annot = cases
                .iter()
                .map(|(pat, body)| {
                    scope.with_subscope(|subscope| {
                        let (pat_annot, pat_var) = infer_pat(program, ctx, subscope, pat)?;
                        let (body_annot, body_var) = infer_expr(program, ctx, subscope, &body)?;

                        ctx.unify(pat_var, discrim_var)?;
                        ctx.unify(body_var, result_var)?;

                        Ok((pat_annot, body_annot))
                    })
                })
                .collect::<Result<_, _>>()?;

            Ok((
                AnnotExpr::Match(Box::new(discrim_annot), cases_annot, result_var),
                result_var,
            ))
        }

        res::Expr::Let(lhs, rhs, body) => {
            let (rhs_annot, rhs_var) = infer_expr(program, ctx, scope, rhs)?;
            let (lhs_annot, (body_annot, body_var)) = scope.with_subscope(|subscope| {
                let (lhs_annot, lhs_var) = infer_pat(program, ctx, subscope, lhs)?;
                ctx.unify(lhs_var, rhs_var)?;
                Ok((lhs_annot, infer_expr(program, ctx, subscope, body)?))
            })?;

            let let_annot = AnnotExpr::Let(lhs_annot, Box::new(rhs_annot), Box::new(body_annot));
            Ok((let_annot, body_var))
        }

        res::Expr::ArrayLit(items) => {
            let param_var = ctx.new_var(Assign::Unknown);

            let items_annot = items
                .iter()
                .map(|item| {
                    let (item_annot, item_var) = infer_expr(program, ctx, scope, item)?;
                    ctx.unify(item_var, param_var)?;
                    Ok(item_annot)
                })
                .collect::<Result<_, _>>()?;

            let array_annot = AnnotExpr::ArrayLit(param_var, items_annot);
            let array_var = ctx.new_var(Assign::App(res::TypeId::Array, vec![param_var]));
            Ok((array_annot, array_var))
        }

        &res::Expr::ByteLit(val) => Ok((
            AnnotExpr::ByteLit(val),
            ctx.new_var(Assign::App(res::TypeId::Byte, vec![])),
        )),

        &res::Expr::IntLit(val) => Ok((
            AnnotExpr::IntLit(val),
            ctx.new_var(Assign::App(res::TypeId::Int, vec![])),
        )),

        &res::Expr::FloatLit(val) => Ok((
            AnnotExpr::FloatLit(val),
            ctx.new_var(Assign::App(res::TypeId::Float, vec![])),
        )),
    }
}

fn instantiate_rigid(ctx: &mut Context, scheme: &res::TypeScheme) -> TypeVar {
    let rigid_params: Vec<_> = (0..scheme.num_params)
        .map(|idx| ctx.new_var(Assign::Param(res::TypeParamId(idx))))
        .collect();

    instantiate_with(ctx, &rigid_params, &scheme.body)
}

fn extract_pat_solution(ctx: &Context, body: AnnotPattern) -> typed::Pattern {
    match body {
        AnnotPattern::Any(var) => typed::Pattern::Any(ctx.extract(var)),

        AnnotPattern::Var(var) => typed::Pattern::Var(ctx.extract(var)),

        AnnotPattern::Tuple(items) => typed::Pattern::Tuple(
            items
                .into_iter()
                .map(|item| extract_pat_solution(ctx, item))
                .collect(),
        ),

        AnnotPattern::Ctor(id, vars, variant, content) => typed::Pattern::Ctor(
            id,
            vars.into_iter().map(|var| ctx.extract(var)).collect(),
            variant,
            content.map(|content| Box::new(extract_pat_solution(ctx, *content))),
        ),

        AnnotPattern::ByteConst(val) => typed::Pattern::ByteConst(val),
        AnnotPattern::IntConst(val) => typed::Pattern::IntConst(val),
        AnnotPattern::FloatConst(val) => typed::Pattern::FloatConst(val),
    }
}

fn extract_solution(ctx: &Context, body: AnnotExpr) -> typed::Expr {
    match body {
        AnnotExpr::Global(id, vars) => {
            typed::Expr::Global(id, vars.iter().map(|&var| ctx.extract(var)).collect())
        }

        AnnotExpr::Local(id) => typed::Expr::Local(id),

        AnnotExpr::Tuple(items) => typed::Expr::Tuple(
            items
                .into_iter()
                .map(|item| extract_solution(ctx, item))
                .collect(),
        ),

        AnnotExpr::Lam(purity, arg_type, ret_type, pat, body) => typed::Expr::Lam(
            purity,
            ctx.extract(arg_type),
            ctx.extract(ret_type),
            extract_pat_solution(ctx, pat),
            Box::new(extract_solution(ctx, *body)),
        ),

        AnnotExpr::App(purity, func, arg) => typed::Expr::App(
            purity,
            Box::new(extract_solution(ctx, *func)),
            Box::new(extract_solution(ctx, *arg)),
        ),

        AnnotExpr::Match(discrim, cases, result_var) => typed::Expr::Match(
            Box::new(extract_solution(ctx, *discrim)),
            cases
                .into_iter()
                .map(|(pat, body)| (extract_pat_solution(ctx, pat), extract_solution(ctx, body)))
                .collect(),
            ctx.extract(result_var),
        ),

        AnnotExpr::Let(lhs, rhs, body) => typed::Expr::Let(
            extract_pat_solution(ctx, lhs),
            Box::new(extract_solution(ctx, *rhs)),
            Box::new(extract_solution(ctx, *body)),
        ),

        AnnotExpr::ArrayLit(item_var, items) => typed::Expr::ArrayLit(
            ctx.extract(item_var),
            items
                .into_iter()
                .map(|item| extract_solution(ctx, item))
                .collect(),
        ),

        AnnotExpr::ByteLit(val) => typed::Expr::ByteLit(val),

        AnnotExpr::IntLit(val) => typed::Expr::IntLit(val),

        AnnotExpr::FloatLit(val) => typed::Expr::FloatLit(val),
    }
}

fn infer_def(program: &res::Program, def: &res::ValDef) -> Result<typed::ValDef, Error> {
    let mut ctx = Context::new();
    let mut scope = Scope::new();

    let declared_type_var = instantiate_rigid(&mut ctx, &def.scheme);

    let (body_annot, body_var) = infer_expr(program, &mut ctx, &mut scope, &def.body)?;

    ctx.unify(declared_type_var, body_var)?;

    let body_typed = extract_solution(&ctx, body_annot);

    Ok(typed::ValDef {
        scheme: def.scheme.clone(),
        body: body_typed,
    })
}

pub fn type_infer(program: res::Program) -> Result<typed::Program, LocatedError> {
    let vals_inferred = program
        .vals
        .iter()
        .enumerate()
        .map(|(idx, def)| {
            infer_def(&program, def).map_err(|error| LocatedError {
                def: program.val_data[idx].val_name.0.clone(),
                error,
            })
        })
        .collect::<Result<_, _>>()?;

    Ok(typed::Program {
        custom_types: program.custom_types,
        custom_type_data: program.custom_type_data,
        vals: vals_inferred,
        val_data: program.val_data,
        main: program.main,
    })
}
