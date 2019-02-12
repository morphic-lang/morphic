use std::collections::BTreeMap;

use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;

#[derive(Clone, Debug)]
struct CaptureMap {
    locals_offset: usize,
    captures: BTreeMap<res::LocalId, lifted::CaptureId>,
}

impl CaptureMap {
    fn translate(&mut self, local: res::LocalId) -> lifted::Expr {
        if local.0 < self.locals_offset {
            let new_id_if_needed = lifted::CaptureId(self.captures.len());
            let id = self.captures.entry(local).or_insert(new_id_if_needed);
            lifted::Expr::Capture(*id)
        } else {
            lifted::Expr::Local(lifted::LocalId(local.0 - self.locals_offset))
        }
    }
}

#[derive(Clone, Debug)]
struct TypeContext<'a> {
    types: Vec<&'a mono::Type>,
}

impl<'a> TypeContext<'a> {
    fn new() -> Self {
        TypeContext { types: Vec::new() }
    }

    fn num_locals(&self) -> usize {
        self.types.len()
    }

    fn add_local(&mut self, type_: &'a mono::Type) {
        self.types.push(type_);
    }

    fn with_scope<R, F: for<'b> FnOnce(&'b mut TypeContext<'a>) -> R>(&mut self, body: F) -> R {
        let old_len = self.types.len();
        let result = body(self);
        self.types.truncate(old_len);
        result
    }
}

fn add_pattern<'a>(ctx: &mut TypeContext<'a>, pat: &'a mono::Pattern) {
    match pat {
        mono::Pattern::Any(_) => {}

        mono::Pattern::Var(type_) => ctx.add_local(type_),

        mono::Pattern::Tuple(items) => {
            for item in items {
                add_pattern(ctx, item);
            }
        }

        mono::Pattern::Ctor(_, _, content) => {
            if let Some(content) = content {
                add_pattern(ctx, content);
            }
        }

        mono::Pattern::BoolConst(_) => {}
        mono::Pattern::IntConst(_) => {}
        mono::Pattern::FloatConst(_) => {}
        mono::Pattern::TextConst(_) => {}
    }
}

fn lift_expr<'a>(
    lambdas: &mut Vec<lifted::LamDef>,
    ctx: &mut TypeContext<'a>,
    captures: &mut CaptureMap,
    expr: &'a mono::Expr,
) -> lifted::Expr {
    match expr {
        &mono::Expr::ArithOp(op) => lifted::Expr::ArithOp(op),

        mono::Expr::ArrayOp(op, type_) => lifted::Expr::ArrayOp(*op, type_.clone()),

        &mono::Expr::Ctor(id, variant) => lifted::Expr::Ctor(id, variant),

        &mono::Expr::Global(id) => lifted::Expr::Global(id),

        &mono::Expr::Local(id) => captures.translate(id),

        mono::Expr::Tuple(items) => lifted::Expr::Tuple(
            items
                .iter()
                .map(|item| lift_expr(lambdas, ctx, captures, item))
                .collect(),
        ),

        mono::Expr::Lam(purity, arg, body) => {
            let (id, captured) = lift_lam(lambdas, ctx, *purity, arg, body);
            let captures_translated = captured.iter().map(|id| captures.translate(*id)).collect();
            lifted::Expr::Lam(id, captures_translated)
        }

        mono::Expr::App(purity, func, arg) => {
            let func_lifted = lift_expr(lambdas, ctx, captures, func);
            let arg_lifted = lift_expr(lambdas, ctx, captures, arg);
            lifted::Expr::App(*purity, Box::new(func_lifted), Box::new(arg_lifted))
        }

        mono::Expr::Match(discrim, cases) => {
            let discrim_lifted = lift_expr(lambdas, ctx, captures, discrim);

            let cases_lifted = cases
                .iter()
                .map(|(pat, body)| {
                    (*ctx).with_scope(|sub_ctx| {
                        add_pattern(sub_ctx, pat);
                        (pat.clone(), lift_expr(lambdas, sub_ctx, captures, body))
                    })
                })
                .collect();

            lifted::Expr::Match(Box::new(discrim_lifted), cases_lifted)
        }

        mono::Expr::Let(lhs, rhs, body) => {
            let rhs_lifted = lift_expr(lambdas, ctx, captures, rhs);

            let body_lifted = ctx.with_scope(|sub_ctx| {
                add_pattern(sub_ctx, lhs);
                lift_expr(lambdas, sub_ctx, captures, body)
            });

            lifted::Expr::Let(lhs.clone(), Box::new(rhs_lifted), Box::new(body_lifted))
        }

        mono::Expr::ArrayLit(type_, items) => lifted::Expr::ArrayLit(
            type_.clone(),
            items
                .iter()
                .map(|item| lift_expr(lambdas, ctx, captures, item))
                .collect(),
        ),

        &mono::Expr::BoolLit(val) => lifted::Expr::BoolLit(val),

        &mono::Expr::IntLit(val) => lifted::Expr::IntLit(val),

        &mono::Expr::FloatLit(val) => lifted::Expr::FloatLit(val),

        mono::Expr::TextLit(text) => lifted::Expr::TextLit(text.clone()),
    }
}

fn lift_lam<'a>(
    lambdas: &mut Vec<lifted::LamDef>,
    ctx: &mut TypeContext<'a>,
    purity: Purity,
    arg: &'a mono::Pattern,
    body: &'a mono::Expr,
) -> (lifted::LamId, Vec<res::LocalId>) {
    let mut sub_captures = CaptureMap {
        locals_offset: ctx.num_locals(),
        captures: BTreeMap::new(),
    };

    let body_lifted = ctx.with_scope(|sub_ctx| {
        add_pattern(sub_ctx, arg);
        lift_expr(lambdas, sub_ctx, &mut sub_captures, body)
    });

    let mut captured_locals = vec![None; sub_captures.captures.len()];
    let mut capture_types = vec![None; sub_captures.captures.len()];

    for (outer_local, capture_id) in &sub_captures.captures {
        captured_locals[capture_id.0] = Some(*outer_local);
        capture_types[capture_id.0] = Some(ctx.types[outer_local.0].clone());
    }

    let lam_def = lifted::LamDef {
        purity,
        captures: capture_types
            .into_iter()
            .map(|type_| type_.unwrap())
            .collect(),
        arg: arg.clone(),
        body: body_lifted,
    };

    let id = lifted::LamId(lambdas.len());
    lambdas.push(lam_def);

    (
        id,
        captured_locals
            .into_iter()
            .map(|local| local.unwrap())
            .collect(),
    )
}

fn lift_def(lambdas: &mut Vec<lifted::LamDef>, def: mono::ValDef) -> lifted::ValDef {
    let mut dummy_captures = CaptureMap {
        locals_offset: 0,
        captures: BTreeMap::new(),
    };
    let mut ctx = TypeContext::new();

    let body_lifted = lift_expr(lambdas, &mut ctx, &mut dummy_captures, &def.body);

    debug_assert_eq!(dummy_captures.captures.len(), 0);
    debug_assert_eq!(ctx.num_locals(), 0);

    lifted::ValDef {
        type_: def.type_,
        body: body_lifted,
    }
}

pub fn lambda_lift(program: mono::Program) -> lifted::Program {
    let mut lambdas = Vec::new();

    let defs_lifted = program
        .vals
        .into_iter()
        .map(|def| lift_def(&mut lambdas, def))
        .collect();

    lifted::Program {
        custom_types: program.custom_types,
        vals: defs_lifted,
        lams: lambdas,
        main: program.main,
    }
}
