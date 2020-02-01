use std::collections::BTreeMap;

use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::id_vec::IdVec;

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
    types: IdVec<res::LocalId, &'a mono::Type>,
}

impl<'a> TypeContext<'a> {
    fn new() -> Self {
        TypeContext {
            types: IdVec::new(),
        }
    }

    fn num_locals(&self) -> usize {
        self.types.len()
    }

    fn add_local(&mut self, type_: &'a mono::Type) {
        let _ = self.types.push(type_);
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
        mono::Pattern::ByteConst(_) => {}
        mono::Pattern::IntConst(_) => {}
        mono::Pattern::FloatConst(_) => {}
    }
}

fn lift_expr<'a>(
    lambdas: &mut IdVec<lifted::LamId, lifted::LamDef>,
    lam_symbols: &mut IdVec<lifted::LamId, lifted::LamSymbols>,
    ctx: &mut TypeContext<'a>,
    captures: &mut CaptureMap,
    expr: &'a mono::Expr,
    lifted_from: mono::CustomGlobalId,
) -> lifted::Expr {
    match expr {
        &mono::Expr::ArithOp(op) => lifted::Expr::ArithOp(op),

        mono::Expr::ArrayOp(op, type_) => lifted::Expr::ArrayOp(*op, type_.clone()),

        &mono::Expr::IOOp(op) => lifted::Expr::IOOp(op),

        &mono::Expr::Ctor(id, variant) => lifted::Expr::Ctor(id, variant),

        &mono::Expr::Global(id) => lifted::Expr::Global(id),

        &mono::Expr::Local(id) => captures.translate(id),

        mono::Expr::Tuple(items) => lifted::Expr::Tuple(
            items
                .iter()
                .map(|item| lift_expr(lambdas, lam_symbols, ctx, captures, item, lifted_from))
                .collect(),
        ),

        mono::Expr::Lam(purity, arg_type, ret_type, arg, body) => {
            let (id, captured) = lift_lam(
                lambdas,
                lam_symbols,
                ctx,
                *purity,
                arg_type,
                ret_type,
                arg,
                body,
                lifted_from,
            );
            let captures_translated =
                captured.map(|_capture_id, &local_id| captures.translate(local_id));
            lifted::Expr::Lam(id, captures_translated)
        }

        mono::Expr::App(purity, func, arg) => {
            let func_lifted = lift_expr(lambdas, lam_symbols, ctx, captures, func, lifted_from);
            let arg_lifted = lift_expr(lambdas, lam_symbols, ctx, captures, arg, lifted_from);
            lifted::Expr::App(*purity, Box::new(func_lifted), Box::new(arg_lifted))
        }

        mono::Expr::Match(discrim, cases, result_type) => {
            let discrim_lifted =
                lift_expr(lambdas, lam_symbols, ctx, captures, discrim, lifted_from);

            let cases_lifted = cases
                .iter()
                .map(|(pat, body)| {
                    (*ctx).with_scope(|sub_ctx| {
                        add_pattern(sub_ctx, pat);
                        (
                            pat.clone(),
                            lift_expr(lambdas, lam_symbols, sub_ctx, captures, body, lifted_from),
                        )
                    })
                })
                .collect();

            lifted::Expr::Match(Box::new(discrim_lifted), cases_lifted, result_type.clone())
        }

        mono::Expr::Let(lhs, rhs, body) => {
            let rhs_lifted = lift_expr(lambdas, lam_symbols, ctx, captures, rhs, lifted_from);

            let body_lifted = ctx.with_scope(|sub_ctx| {
                add_pattern(sub_ctx, lhs);
                lift_expr(lambdas, lam_symbols, sub_ctx, captures, body, lifted_from)
            });

            lifted::Expr::Let(lhs.clone(), Box::new(rhs_lifted), Box::new(body_lifted))
        }

        mono::Expr::ArrayLit(type_, items) => lifted::Expr::ArrayLit(
            type_.clone(),
            items
                .iter()
                .map(|item| lift_expr(lambdas, lam_symbols, ctx, captures, item, lifted_from))
                .collect(),
        ),

        &mono::Expr::BoolLit(val) => lifted::Expr::BoolLit(val),

        &mono::Expr::ByteLit(val) => lifted::Expr::ByteLit(val),

        &mono::Expr::IntLit(val) => lifted::Expr::IntLit(val),

        &mono::Expr::FloatLit(val) => lifted::Expr::FloatLit(val),
    }
}

fn lift_lam<'a>(
    lambdas: &mut IdVec<lifted::LamId, lifted::LamDef>,
    lam_symbols: &mut IdVec<lifted::LamId, lifted::LamSymbols>,
    ctx: &mut TypeContext<'a>,
    purity: Purity,
    arg_type: &'a mono::Type,
    ret_type: &'a mono::Type,
    arg: &'a mono::Pattern,
    body: &'a mono::Expr,
    lifted_from: mono::CustomGlobalId,
) -> (lifted::LamId, IdVec<lifted::CaptureId, res::LocalId>) {
    let mut sub_captures = CaptureMap {
        locals_offset: ctx.num_locals(),
        captures: BTreeMap::new(),
    };

    let body_lifted = ctx.with_scope(|sub_ctx| {
        add_pattern(sub_ctx, arg);
        lift_expr(
            lambdas,
            lam_symbols,
            sub_ctx,
            &mut sub_captures,
            body,
            lifted_from,
        )
    });

    let mut captured_locals = IdVec::from_items(vec![None; sub_captures.captures.len()]);
    let mut capture_types = IdVec::from_items(vec![None; sub_captures.captures.len()]);

    for (outer_local, capture_id) in &sub_captures.captures {
        captured_locals[capture_id] = Some(*outer_local);
        capture_types[capture_id] = Some(ctx.types[outer_local].clone());
    }

    let lam_def = lifted::LamDef {
        purity,
        captures: capture_types.into_mapped(|_capture_id, type_| type_.unwrap()),
        arg_type: arg_type.clone(),
        ret_type: ret_type.clone(),
        arg: arg.clone(),
        body: body_lifted,
    };

    let lam_datum = lifted::LamSymbols {
        lifted_from: lifted_from,
    };

    let lam_id = lambdas.push(lam_def);
    {
        let lam_symbols_id = lam_symbols.push(lam_datum);
        debug_assert_eq!(lam_id, lam_symbols_id);
    }

    (
        lam_id,
        captured_locals.into_mapped(|_capture_id, local| local.unwrap()),
    )
}

fn lift_def(
    lambdas: &mut IdVec<lifted::LamId, lifted::LamDef>,
    lam_symbols: &mut IdVec<lifted::LamId, lifted::LamSymbols>,
    def: mono::ValDef,
    def_id: mono::CustomGlobalId,
) -> lifted::ValDef {
    let mut dummy_captures = CaptureMap {
        locals_offset: 0,
        captures: BTreeMap::new(),
    };
    let mut ctx = TypeContext::new();

    let body_lifted = lift_expr(
        lambdas,
        lam_symbols,
        &mut ctx,
        &mut dummy_captures,
        &def.body,
        def_id,
    );

    debug_assert_eq!(dummy_captures.captures.len(), 0);
    debug_assert_eq!(ctx.num_locals(), 0);

    lifted::ValDef {
        type_: def.type_,
        body: body_lifted,
    }
}

pub fn lambda_lift(program: mono::Program) -> lifted::Program {
    let mut lambdas = IdVec::new();
    let mut lam_symbols = IdVec::new();

    let defs_lifted = program
        .vals
        .into_mapped(|id, def| lift_def(&mut lambdas, &mut lam_symbols, def, id));

    lifted::Program {
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        vals: defs_lifted,
        val_symbols: program.val_symbols,
        lams: lambdas,
        lam_symbols: lam_symbols,
        main: program.main,
    }
}
