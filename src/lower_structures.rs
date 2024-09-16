use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::low_ast as low;
use crate::data::rc_specialized_ast2 as rc;
use crate::data::tail_rec_ast as tail;
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::ProgressLogger;
use crate::util::progress_logger::ProgressSession;
use id_collections::IdVec;

// we need to change branches to ifs
// we need to unwrap array literals

struct LowAstBuilder {
    offset: low::LocalId,
    exprs: Vec<(low::Type, low::Expr)>,
}

impl LowAstBuilder {
    fn new(offset: low::LocalId) -> LowAstBuilder {
        LowAstBuilder {
            offset,
            exprs: Vec::new(),
        }
    }

    fn child(&self) -> LowAstBuilder {
        LowAstBuilder::new(low::LocalId(self.offset.0 + self.exprs.len()))
    }

    fn add_expr(&mut self, type_: low::Type, expr: low::Expr) -> low::LocalId {
        debug_assert!(
            !matches!(self.exprs.last(), Some((_, low::Expr::TailCall(_, _)))),
            "The pass 'lower_strucures' tried to generate an expression immediately after \
             a tail call, which violates the invariant that a tail call must be the last \
             expression in its block."
        );

        let new_id = low::LocalId(self.offset.0 + self.exprs.len());
        self.exprs.push((type_, expr));
        new_id
    }

    fn build(self, final_local_id: low::LocalId) -> low::Expr {
        low::Expr::LetMany(self.exprs, final_local_id)
    }
}

// Used to lower constant conditions
fn build_comp(
    lhs: low::LocalId,
    rhs: low::LocalId,
    type_: first_ord::NumType,
    op: Intrinsic,
    builder: &mut LowAstBuilder,
) -> low::LocalId {
    let args = builder.add_expr(
        low::Type::Tuple(vec![low::Type::Num(type_), low::Type::Num(type_)]),
        low::Expr::Tuple(vec![lhs, rhs]),
    );

    builder.add_expr(low::Type::Bool, low::Expr::Intrinsic(op, args))
}

fn lower_condition(
    discrim: low::LocalId,
    condition: &rc::Condition,
    builder: &mut LowAstBuilder,
    match_type: &low::Type,
    typedefs: &IdVec<first_ord::CustomTypeId, low::Type>,
) -> low::LocalId {
    match condition {
        rc::Condition::Any => builder.add_expr(low::Type::Bool, low::Expr::BoolLit(true)),
        rc::Condition::Tuple(subconditions) => {
            let low::Type::Tuple(item_types) = match_type else {
                unreachable!();
            };

            let subcondition_ids = item_types
                .iter()
                .zip(subconditions.iter())
                .enumerate()
                .map(|(index, (item_type, subcondition))| {
                    let item_id =
                        builder.add_expr(item_type.clone(), low::Expr::TupleField(discrim, index));
                    lower_condition(item_id, subcondition, builder, item_type, typedefs)
                })
                .collect::<Vec<low::LocalId>>();
            let if_expr =
                subcondition_ids
                    .into_iter()
                    .rfold(low::Expr::BoolLit(true), |accum, item| {
                        low::Expr::If(item, Box::new(accum), Box::new(low::Expr::BoolLit(false)))
                    });

            builder.add_expr(low::Type::Bool, if_expr)
        }
        rc::Condition::Variant(variant_id, subcondition) => {
            let variant_id = first_ord::VariantId(variant_id.0);

            let variant_check = builder.add_expr(
                low::Type::Bool,
                low::Expr::CheckVariant(variant_id, discrim),
            );

            let mut new_builder = builder.child();
            let low::Type::Variants(variant_types) = match_type else {
                unreachable!();
            };

            let variant_type = &variant_types[variant_id];

            let sub_discrim = new_builder.add_expr(
                variant_type.clone(),
                low::Expr::UnwrapVariant(
                    variant_types.clone(),
                    first_ord::VariantId(variant_id.0),
                    discrim,
                ),
            );

            let sub_cond_id = lower_condition(
                sub_discrim,
                subcondition,
                &mut new_builder,
                variant_type,
                typedefs,
            );

            builder.add_expr(
                low::Type::Bool,
                low::Expr::If(
                    variant_check,
                    Box::new(new_builder.build(sub_cond_id)),
                    Box::new(low::Expr::BoolLit(false)),
                ),
            )
        }
        rc::Condition::Boxed(subcondition) => {
            let low::Type::Boxed(content_type) = match_type else {
                unreachable!();
            };

            let content = builder.add_expr(
                (**content_type).clone(),
                low::Expr::UnwrapBoxed(discrim, (**content_type).clone()),
            );

            lower_condition(content, subcondition, builder, content_type, typedefs)
        }
        rc::Condition::Custom(subcondition) => {
            let low::Type::Custom(custom_type_id) = match_type else {
                unreachable!();
            };

            let content_type = &typedefs[custom_type_id];
            let content = builder.add_expr(
                content_type.clone(),
                low::Expr::UnwrapCustom(*custom_type_id, discrim),
            );

            lower_condition(content, subcondition, builder, content_type, typedefs)
        }
        rc::Condition::BoolConst(val) => {
            if *val {
                discrim
            } else {
                builder.add_expr(
                    low::Type::Bool,
                    low::Expr::If(
                        discrim,
                        Box::new(low::Expr::BoolLit(false)),
                        Box::new(low::Expr::BoolLit(true)),
                    ),
                )
            }
        }
        rc::Condition::ByteConst(val) => {
            let val_id = builder.add_expr(
                low::Type::Num(first_ord::NumType::Byte),
                low::Expr::ByteLit(*val),
            );

            build_comp(
                val_id,
                discrim,
                first_ord::NumType::Byte,
                Intrinsic::EqByte,
                builder,
            )
        }
        rc::Condition::IntConst(val) => {
            let val_id = builder.add_expr(
                low::Type::Num(first_ord::NumType::Int),
                low::Expr::IntLit(*val),
            );

            build_comp(
                val_id,
                discrim,
                first_ord::NumType::Int,
                Intrinsic::EqInt,
                builder,
            )
        }

        rc::Condition::FloatConst(val) => {
            let val_id = builder.add_expr(
                low::Type::Num(first_ord::NumType::Float),
                low::Expr::FloatLit(*val),
            );

            build_comp(
                val_id,
                discrim,
                first_ord::NumType::Float,
                Intrinsic::EqFloat,
                builder,
            )
        }
    }
}

fn lower_branch(
    discrim: rc::LocalId,
    cases: &[(rc::Condition, tail::Expr)],
    result_type: &low::Type,
    context: &mut LocalContext<rc::LocalId, (rc::Type, low::LocalId)>,
    builder: &mut LowAstBuilder,
    typedefs: &IdVec<first_ord::CustomTypeId, rc::Type>,
) -> low::LocalId {
    match cases.first() {
        None => builder.add_expr(
            result_type.clone(),
            low::Expr::Unreachable(result_type.clone()),
        ),
        Some((cond, body)) => {
            let condition_id = lower_condition(
                context.local_binding(discrim).1,
                cond,
                builder,
                &context.local_binding(discrim).0,
                typedefs,
            );

            let mut then_builder = builder.child();

            let then_final_id = lower_expr(body, result_type, context, &mut then_builder, typedefs);

            let then_branch = then_builder.build(then_final_id);

            let mut else_builder = builder.child();
            let else_local_id = lower_branch(
                discrim,
                &cases[1..],
                result_type,
                // move_info,
                context,
                &mut else_builder,
                typedefs,
            );

            let else_branch = else_builder.build(else_local_id);

            builder.add_expr(
                result_type.clone(),
                low::Expr::If(condition_id, Box::new(then_branch), Box::new(else_branch)),
            )
        }
    }
}

impl rc::LocalId {
    fn lookup_in(
        &self,
        context: &LocalContext<rc::LocalId, (rc::Type, low::LocalId)>,
    ) -> low::LocalId {
        context.local_binding(*self).1
    }
}

fn lower_expr(
    expr: &tail::Expr,
    result_type: &low::Type,
    context: &mut LocalContext<rc::LocalId, (rc::Type, low::LocalId)>,
    builder: &mut LowAstBuilder,
    typedefs: &IdVec<first_ord::CustomTypeId, rc::Type>,
) -> low::LocalId {
    match expr {
        tail::Expr::LetMany(bindings, final_local_id) => context.with_scope(|subcontext| {
            for (type_, binding) in bindings {
                let low_binding_id = lower_expr(binding, &type_, subcontext, builder, typedefs);
                subcontext.add_local((type_.clone(), low_binding_id));
            }
            subcontext.local_binding(*final_local_id).1
        }),
        tail::Expr::Branch(discrim, cases, result_type) => {
            lower_branch(*discrim, cases, result_type, context, builder, typedefs)
        }
        tail::Expr::Local(local_id) => local_id.lookup_in(context),
        tail::Expr::Call(_purity, func_id, arg_id) => builder.add_expr(
            result_type.clone(),
            low::Expr::Call(low::CustomFuncId(func_id.0), arg_id.lookup_in(context)),
        ),
        tail::Expr::TailCall(tail_func_id, arg_id) => builder.add_expr(
            result_type.clone(),
            low::Expr::TailCall(*tail_func_id, arg_id.lookup_in(context)),
        ),
        tail::Expr::Tuple(elem_ids) => builder.add_expr(
            result_type.clone(),
            low::Expr::Tuple(
                elem_ids
                    .iter()
                    .map(|elem_id| elem_id.lookup_in(context))
                    .collect(),
            ),
        ),
        tail::Expr::TupleField(tuple_id, index) => {
            let tuple_elem_id = builder.add_expr(
                result_type.clone(),
                low::Expr::TupleField(tuple_id.lookup_in(context), *index),
            );
            tuple_elem_id
        }
        tail::Expr::WrapBoxed(content_id, content_type) => builder.add_expr(
            result_type.clone(),
            low::Expr::WrapBoxed(content_id.lookup_in(context), content_type.clone()),
        ),
        tail::Expr::UnwrapBoxed(boxed_id, content_type) => {
            let content_id = builder.add_expr(
                result_type.clone(),
                low::Expr::UnwrapBoxed(boxed_id.lookup_in(context), content_type.clone()),
            );
            content_id
        }
        tail::Expr::WrapVariant(variants, variant_id, content_id) => builder.add_expr(
            result_type.clone(),
            low::Expr::WrapVariant(
                variants.clone(),
                first_ord::VariantId(variant_id.0),
                content_id.lookup_in(context),
            ),
        ),
        tail::Expr::UnwrapVariant(variant_id, content_id) => {
            builder.add_expr(result_type.clone(), {
                let variant_type = &context.local_binding(*content_id).0;
                let rc::Type::Variants(variants) = variant_type else {
                    unreachable!()
                };

                low::Expr::UnwrapVariant(
                    variants.clone(),
                    first_ord::VariantId(variant_id.0),
                    content_id.lookup_in(context),
                )
            })
        }
        tail::Expr::WrapCustom(type_id, content_id) => builder.add_expr(
            low::Type::Custom(*type_id),
            low::Expr::WrapCustom(*type_id, content_id.lookup_in(context)),
        ),
        tail::Expr::UnwrapCustom(type_id, wrapped_id) => builder.add_expr(
            typedefs[type_id].clone(),
            low::Expr::UnwrapCustom(*type_id, wrapped_id.lookup_in(context)),
        ),
        tail::Expr::RcOp(op, local_id) => {
            let type_ = context.local_binding(*local_id).0.clone();
            builder.add_expr(
                low::Type::Tuple(vec![]),
                low::Expr::RcOp(op.clone(), type_, local_id.lookup_in(context)),
            )
        }
        tail::Expr::Intrinsic(intr, local_id) => builder.add_expr(
            result_type.clone(),
            low::Expr::Intrinsic(*intr, local_id.lookup_in(context)),
        ),
        tail::Expr::ArrayOp(array_op) => {
            let array_expr = match array_op {
                rc::ArrayOp::Get(scheme, array_id, index_id) => low::ArrayOp::Get(
                    scheme.clone(),
                    array_id.lookup_in(context),
                    index_id.lookup_in(context),
                ),
                rc::ArrayOp::Extract(scheme, array_id, index_id) => low::ArrayOp::Extract(
                    scheme.clone(),
                    array_id.lookup_in(context),
                    index_id.lookup_in(context),
                ),
                rc::ArrayOp::Len(scheme, array_id) => {
                    low::ArrayOp::Len(scheme.clone(), array_id.lookup_in(context))
                }
                rc::ArrayOp::Push(scheme, array_id, item_id) => low::ArrayOp::Push(
                    scheme.clone(),
                    array_id.lookup_in(context),
                    item_id.lookup_in(context),
                ),
                rc::ArrayOp::Pop(scheme, array_id) => {
                    low::ArrayOp::Pop(scheme.clone(), array_id.lookup_in(context))
                }
                rc::ArrayOp::Replace(scheme, array_id, item_id) => low::ArrayOp::Replace(
                    scheme.clone(),
                    array_id.lookup_in(context),
                    item_id.lookup_in(context),
                ),
                rc::ArrayOp::Reserve(scheme, array_id, capacity_id) => low::ArrayOp::Reserve(
                    scheme.clone(),
                    array_id.lookup_in(context),
                    capacity_id.lookup_in(context),
                ),
            };
            builder.add_expr(result_type.clone(), low::Expr::ArrayOp(array_expr))
        }
        tail::Expr::IoOp(io_type) => builder.add_expr(
            result_type.clone(),
            low::Expr::IoOp(match io_type {
                rc::IoOp::Input => low::IoOp::Input,
                rc::IoOp::Output(output_id) => low::IoOp::Output(output_id.lookup_in(context)),
            }),
        ),
        tail::Expr::Panic(ret_type, message) => builder.add_expr(
            result_type.clone(),
            low::Expr::Panic(ret_type.clone(), message.lookup_in(context)),
        ),
        tail::Expr::ArrayLit(scheme, elems) => {
            // TODO: we are inlining some knowledge here about the signatures of `Array.new`,
            // `Array.reserve`, and `Array.push`. Item types should be determined instead by the
            // signatures used for borrow inference.

            let mut result_id = builder.add_expr(
                result_type.clone(),
                low::Expr::ArrayOp(low::ArrayOp::New(scheme.clone())),
            );

            let capacity_id = builder.add_expr(
                low::Type::Num(first_ord::NumType::Int),
                low::Expr::IntLit(elems.len() as i64),
            );

            result_id = builder.add_expr(
                result_type.clone(),
                low::Expr::ArrayOp(low::ArrayOp::Reserve(
                    scheme.clone(),
                    result_id,
                    capacity_id,
                )),
            );

            for elem_id in elems {
                result_id = builder.add_expr(
                    result_type.clone(),
                    low::Expr::ArrayOp(low::ArrayOp::Push(
                        scheme.clone(),
                        result_id,
                        elem_id.lookup_in(context),
                    )),
                );
            }

            result_id
        }
        tail::Expr::BoolLit(val) => builder.add_expr(result_type.clone(), low::Expr::BoolLit(*val)),
        tail::Expr::ByteLit(val) => builder.add_expr(result_type.clone(), low::Expr::ByteLit(*val)),
        tail::Expr::IntLit(val) => builder.add_expr(result_type.clone(), low::Expr::IntLit(*val)),
        tail::Expr::FloatLit(val) => {
            builder.add_expr(result_type.clone(), low::Expr::FloatLit(*val))
        }
    }
}

fn lower_function_body(
    typedefs: &IdVec<first_ord::CustomTypeId, rc::Type>,
    arg_type: &rc::Type,
    ret_type: &rc::Type,
    body: tail::Expr,
) -> low::Expr {
    let mut builder = LowAstBuilder::new(low::LocalId(1));

    let mut context = LocalContext::new();

    context.add_local((arg_type.clone(), low::ARG_LOCAL));

    let final_local_id = lower_expr(&body, ret_type, &mut context, &mut builder, typedefs);

    builder.build(final_local_id)
}

fn lower_function(
    func: tail::FuncDef,
    typedefs: &IdVec<first_ord::CustomTypeId, rc::Type>,
) -> low::FuncDef {
    // Appease the borrow checker
    let ret_type = &func.ret_type;

    let tail_funcs = func.tail_funcs.map(|_, tail_func| low::TailFunc {
        arg_type: tail_func.arg_type.clone(),
        body: lower_function_body(typedefs, &tail_func.arg_type, ret_type, tail_func.body),
        profile_point: tail_func.profile_point,
    });

    let body = lower_function_body(typedefs, &func.arg_type, &func.ret_type, func.body);

    low::FuncDef {
        tail_funcs,
        arg_type: func.arg_type,
        ret_type: func.ret_type,
        body,
        profile_point: func.profile_point,
    }
}

pub fn lower_structures(program: tail::Program, progress: impl ProgressLogger) -> low::Program {
    let mut progress = progress.start_session(Some(program.funcs.len()));

    let lowered_funcs = program
        .funcs
        .into_values()
        .map(|func| {
            let lowered = lower_function(func, &program.custom_types.types);
            progress.update(1);
            lowered
        })
        .collect();

    progress.finish();

    low::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        funcs: IdVec::from_vec(lowered_funcs),
        schemes: program.schemes,
        profile_points: program.profile_points,
        main: low::CustomFuncId(program.main.0),
    }
}
