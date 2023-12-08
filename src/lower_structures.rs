use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::low_ast as low;
use crate::data::rc_specialized_ast as rc;
use crate::data::repr_specialized_ast as special;
use crate::data::repr_unified_ast as unif;
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
        #[cfg(debug_assertions)]
        {
            // TODO: Use 'matches' macro
            if let Some((_, low::Expr::TailCall(_, _))) = self.exprs.last() {
                panic!(
                    "The pass 'lower_strucures' tried to generate an expression immediately after \
                     a tail call, which violates the invariant that a tail call must be the last \
                     expression in its block."
                );
            }
        }

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
    condition: &special::Condition,
    builder: &mut LowAstBuilder,
    match_type: &low::Type,
    typedefs: &IdVec<special::CustomTypeId, low::Type>,
) -> low::LocalId {
    match condition {
        special::Condition::Any => builder.add_expr(low::Type::Bool, low::Expr::BoolLit(true)),
        special::Condition::Tuple(subconditions) => {
            let item_types = if let low::Type::Tuple(item_types) = match_type {
                item_types
            } else {
                unreachable![];
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
        special::Condition::Variant(variant_id, subcondition) => {
            let variant_id = first_ord::VariantId(variant_id.0);

            let variant_check = builder.add_expr(
                low::Type::Bool,
                low::Expr::CheckVariant(variant_id, discrim),
            );

            let mut new_builder = builder.child();
            let variant_types = if let low::Type::Variants(variant_types) = match_type {
                variant_types
            } else {
                unreachable![];
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
        special::Condition::Boxed(subcondition, content_type) => {
            let content = builder.add_expr(
                content_type.clone(),
                low::Expr::UnwrapBoxed(discrim, content_type.clone()),
            );

            lower_condition(content, subcondition, builder, content_type, typedefs)
        }
        special::Condition::Custom(custom_type_id, subcondition) => {
            let content_type = &typedefs[custom_type_id];

            let content = builder.add_expr(
                content_type.clone(),
                low::Expr::UnwrapCustom(*custom_type_id, discrim),
            );

            lower_condition(content, subcondition, builder, content_type, typedefs)
        }
        special::Condition::BoolConst(val) => {
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
        special::Condition::ByteConst(val) => {
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
        special::Condition::IntConst(val) => {
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

        special::Condition::FloatConst(val) => {
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
    cases: &[(special::Condition, tail::Expr)],
    result_type: &low::Type,
    context: &mut LocalContext<rc::LocalId, (special::Type, low::LocalId)>,
    builder: &mut LowAstBuilder,
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
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
        context: &LocalContext<rc::LocalId, (special::Type, low::LocalId)>,
    ) -> low::LocalId {
        context.local_binding(*self).1
    }
}

fn lower_expr(
    expr: &tail::Expr,
    result_type: &low::Type,
    context: &mut LocalContext<rc::LocalId, (special::Type, low::LocalId)>,
    builder: &mut LowAstBuilder,
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
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
                let variants = if let special::Type::Variants(variants) = variant_type {
                    variants
                } else {
                    panic![];
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
        tail::Expr::RcOp(op, container, inner_type, local_id) => {
            let container_type = match container {
                &unif::ContainerType::Array(rep) => {
                    low::Type::Array(rep, Box::new(inner_type.clone()))
                }
                &unif::ContainerType::HoleArray(rep) => {
                    low::Type::HoleArray(rep, Box::new(inner_type.clone()))
                }
                &unif::ContainerType::Boxed => low::Type::Boxed(Box::new(inner_type.clone())),
            };
            match op {
                rc::RcOp::Retain => builder.add_expr(
                    low::Type::Tuple(vec![]),
                    low::Expr::Retain(local_id.lookup_in(context), container_type),
                ),
                rc::RcOp::Release => builder.add_expr(
                    low::Type::Tuple(vec![]),
                    low::Expr::Release(local_id.lookup_in(context), container_type),
                ),
            }
        }
        tail::Expr::Intrinsic(intr, local_id) => builder.add_expr(
            result_type.clone(),
            low::Expr::Intrinsic(*intr, local_id.lookup_in(context)),
        ),
        tail::Expr::ArrayOp(rep, item_type, array_op) => {
            let array_expr = match array_op {
                unif::ArrayOp::Get(array_id, index_id) => {
                    low::ArrayOp::Get(array_id.lookup_in(context), index_id.lookup_in(context))
                }
                unif::ArrayOp::Extract(array_id, index_id) => {
                    low::ArrayOp::Extract(array_id.lookup_in(context), index_id.lookup_in(context))
                }
                unif::ArrayOp::Len(array_id) => low::ArrayOp::Len(array_id.lookup_in(context)),
                unif::ArrayOp::Push(array_id, item_id) => {
                    low::ArrayOp::Push(array_id.lookup_in(context), item_id.lookup_in(context))
                }
                unif::ArrayOp::Pop(array_id) => low::ArrayOp::Pop(array_id.lookup_in(context)),
                unif::ArrayOp::Replace(array_id, item_id) => {
                    low::ArrayOp::Replace(array_id.lookup_in(context), item_id.lookup_in(context))
                }
                unif::ArrayOp::Reserve(array_id, capacity_id) => low::ArrayOp::Reserve(
                    array_id.lookup_in(context),
                    capacity_id.lookup_in(context),
                ),
            };
            builder.add_expr(
                result_type.clone(),
                low::Expr::ArrayOp(*rep, item_type.clone(), array_expr),
            )
        }
        tail::Expr::IoOp(rep, io_type) => builder.add_expr(
            result_type.clone(),
            low::Expr::IoOp(
                *rep,
                match io_type {
                    special::IoOp::Input => low::IoOp::Input,
                    special::IoOp::Output(output_id) => {
                        low::IoOp::Output(output_id.lookup_in(context))
                    }
                },
            ),
        ),
        tail::Expr::Panic(ret_type, rep, message) => builder.add_expr(
            result_type.clone(),
            low::Expr::Panic(ret_type.clone(), *rep, message.lookup_in(context)),
        ),
        tail::Expr::ArrayLit(rep, elem_type, elems) => {
            let mut result_id = builder.add_expr(
                result_type.clone(),
                low::Expr::ArrayOp(*rep, elem_type.clone(), low::ArrayOp::New()),
            );

            let capacity_id = builder.add_expr(
                low::Type::Num(first_ord::NumType::Int),
                low::Expr::IntLit(elems.len() as i64),
            );

            result_id = builder.add_expr(
                result_type.clone(),
                low::Expr::ArrayOp(
                    *rep,
                    elem_type.clone(),
                    low::ArrayOp::Reserve(result_id, capacity_id),
                ),
            );

            for elem_id in elems {
                result_id = builder.add_expr(
                    result_type.clone(),
                    low::Expr::ArrayOp(
                        *rep,
                        elem_type.clone(),
                        low::ArrayOp::Push(result_id, elem_id.lookup_in(context)),
                    ),
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
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
    arg_type: &special::Type,
    ret_type: &special::Type,
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
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
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

    let typedefs = program.custom_types;

    let lowered_funcs = program
        .funcs
        .into_values()
        .map(|func| {
            let lowered = lower_function(func, &typedefs);
            progress.update(1);
            lowered
        })
        .collect();

    progress.finish();

    low::Program {
        mod_symbols: program.mod_symbols.clone(),
        custom_types: typedefs,
        funcs: IdVec::from_vec(lowered_funcs),
        profile_points: program.profile_points,
        main: low::CustomFuncId(program.main.0),
    }
}
