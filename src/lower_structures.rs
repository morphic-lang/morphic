use crate::data::first_order_ast as first_ord;
use crate::data::low_ast as low;
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast2::Mode;
use crate::data::rc_specialized_ast2::{self as rc, ModeScheme};
use crate::data::tail_rec_ast as tail;
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::ProgressLogger;
use crate::util::progress_logger::ProgressSession;
use id_collections::IdVec;

// In this pass we:
// - Convert array literals into a series of pushes

struct LowAstBuilder {
    offset: low::LocalId,
    exprs: Vec<(low::Type, low::Expr, Metadata)>,
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
        self.add_expr_with_metadata(type_, expr, Metadata::default())
    }

    fn add_expr_with_metadata(
        &mut self,
        type_: low::Type,
        expr: low::Expr,
        metadata: Metadata,
    ) -> low::LocalId {
        debug_assert!(
            !matches!(self.exprs.last(), Some((_, low::Expr::TailCall(_, _), _))),
            "The pass 'lower_strucures' tried to generate an expression immediately after \
             a tail call, which violates the invariant that a tail call must be the last \
             expression in its block."
        );

        let new_id = low::LocalId(self.offset.0 + self.exprs.len());
        self.exprs.push((type_, expr, metadata));
        new_id
    }

    fn build(self, final_local_id: low::LocalId) -> low::Expr {
        low::Expr::LetMany(self.exprs, final_local_id)
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
    metadata: &Metadata,
    context: &mut LocalContext<rc::LocalId, (rc::Type, low::LocalId)>,
    builder: &mut LowAstBuilder,
    typedefs: &IdVec<first_ord::CustomTypeId, rc::Type>,
) -> low::LocalId {
    let new_expr = match expr {
        tail::Expr::LetMany(bindings, final_local_id) => {
            let final_local = context.with_scope(|subcontext| {
                for (type_, binding, metadata) in bindings {
                    let low_binding_id =
                        lower_expr(binding, &type_, metadata, subcontext, builder, typedefs);
                    subcontext.add_local((type_.clone(), low_binding_id));
                }
                subcontext.local_binding(*final_local_id).1
            });

            // Note: Early return! We circumvent the usual return flow because we don't actually
            // want to create an expression directly corresponding to this 'let' block. The 'let'
            // block's bindings just get absorbed into the ambient `builder`.
            return final_local;
        }
        tail::Expr::If(discrim, then_case, else_case) => {
            let discrim_id = discrim.lookup_in(context);
            let then_case = {
                let mut then_builder = builder.child();
                let then_id = lower_expr(
                    then_case,
                    result_type,
                    &Metadata::default(),
                    context,
                    &mut then_builder,
                    typedefs,
                );
                then_builder.build(then_id)
            };
            let else_case = {
                let mut else_builder = builder.child();
                let else_id = lower_expr(
                    else_case,
                    result_type,
                    &Metadata::default(),
                    context,
                    &mut else_builder,
                    typedefs,
                );
                else_builder.build(else_id)
            };
            low::Expr::If(discrim_id, Box::new(then_case), Box::new(else_case))
        }
        tail::Expr::CheckVariant(variant_id, content_id) => {
            low::Expr::CheckVariant(*variant_id, content_id.lookup_in(context))
        }
        tail::Expr::Unreachable(type_) => low::Expr::Unreachable(type_.clone()),
        tail::Expr::Local(local_id) => low::Expr::Local(local_id.lookup_in(context)),
        tail::Expr::Call(_purity, func_id, arg_id) => {
            low::Expr::Call(low::CustomFuncId(func_id.0), arg_id.lookup_in(context))
        }
        tail::Expr::TailCall(tail_func_id, arg_id) => {
            low::Expr::TailCall(*tail_func_id, arg_id.lookup_in(context))
        }
        tail::Expr::Tuple(elem_ids) => low::Expr::Tuple(
            elem_ids
                .iter()
                .map(|elem_id| elem_id.lookup_in(context))
                .collect(),
        ),
        tail::Expr::TupleField(tuple_id, index) => {
            low::Expr::TupleField(tuple_id.lookup_in(context), *index)
        }
        tail::Expr::WrapBoxed(content_id, output_type) => {
            low::Expr::WrapBoxed(content_id.lookup_in(context), output_type.clone())
        }
        tail::Expr::UnwrapBoxed(boxed_id, input_type, output_type) => low::Expr::UnwrapBoxed(
            boxed_id.lookup_in(context),
            input_type.clone(),
            output_type.clone(),
        ),
        tail::Expr::WrapVariant(variants, variant_id, content_id) => low::Expr::WrapVariant(
            variants.clone(),
            first_ord::VariantId(variant_id.0),
            content_id.lookup_in(context),
        ),
        tail::Expr::UnwrapVariant(variant_id, content_id) => {
            let variant_type = &context.local_binding(*content_id).0;
            let rc::Type::Variants(variants) = variant_type else {
                unreachable!()
            };

            low::Expr::UnwrapVariant(
                variants.clone(),
                first_ord::VariantId(variant_id.0),
                content_id.lookup_in(context),
            )
        }
        tail::Expr::WrapCustom(type_id, content_id) => {
            low::Expr::WrapCustom(*type_id, content_id.lookup_in(context))
        }
        tail::Expr::UnwrapCustom(type_id, wrapped_id) => {
            low::Expr::UnwrapCustom(*type_id, wrapped_id.lookup_in(context))
        }
        tail::Expr::RcOp(op, local_id) => {
            let type_ = context.local_binding(*local_id).0.clone();
            low::Expr::RcOp(op.clone(), type_, local_id.lookup_in(context))
        }
        tail::Expr::Intrinsic(intr, local_id) => {
            low::Expr::Intrinsic(*intr, local_id.lookup_in(context))
        }
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
            low::Expr::ArrayOp(array_expr)
        }
        tail::Expr::IoOp(io_type) => low::Expr::IoOp(match io_type {
            rc::IoOp::Input => low::IoOp::Input,
            rc::IoOp::Output(output_id) => low::IoOp::Output(output_id.lookup_in(context)),
        }),
        tail::Expr::Panic(ret_type, message) => {
            low::Expr::Panic(ret_type.clone(), message.lookup_in(context))
        }
        tail::Expr::ArrayLit(item_scheme, elems) => {
            // TODO: we are inlining some knowledge here about the signatures of `Array.new`,
            // `Array.reserve`, and `Array.push`. Types should be determined instead by the same
            // signatures used for borrow inference.
            let scheme = ModeScheme::Array(Mode::Owned, Box::new(item_scheme.clone()));

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

            // TODO: we could clean up the output code by using the final push expression here
            low::Expr::Local(result_id)
        }
        tail::Expr::BoolLit(val) => low::Expr::BoolLit(*val),
        tail::Expr::ByteLit(val) => low::Expr::ByteLit(*val),
        tail::Expr::IntLit(val) => low::Expr::IntLit(*val),
        tail::Expr::FloatLit(val) => low::Expr::FloatLit(*val),
    };
    builder.add_expr_with_metadata(result_type.clone(), new_expr, metadata.clone())
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

    let final_local_id = lower_expr(
        &body,
        ret_type,
        &Metadata::default(),
        &mut context,
        &mut builder,
        typedefs,
    );

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
        tail_func_symbols: func.tail_func_symbols,
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
        .into_iter()
        .map(|(_func_id, func)| {
            let lowered = lower_function(func, &program.custom_types.types);
            progress.update(1);
            lowered
        })
        .collect();

    progress.finish();

    low::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs: IdVec::from_vec(lowered_funcs),
        func_symbols: IdVec::from_vec(program.func_symbols.into_vec()),
        schemes: program.schemes,
        profile_points: program.profile_points,
        main: low::CustomFuncId(program.main.0),
    }
}
