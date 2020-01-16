use crate::data::first_order_ast as first_ord;
use crate::data::low_ast as low;
use crate::util::id_vec::IdVec;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::{BasicTypeEnum, StructType};
use inkwell::values::{BasicValueEnum, FunctionValue};
use inkwell::{FloatPredicate, IntPredicate};
use lib_builtins::core::LibC;
use std::convert::TryInto;

#[derive(Clone, Debug)]
struct Globals<'a> {
    libc: LibC<'a>,
    custom_types: IdVec<low::CustomTypeId, StructType<'a>>,
    funcs: IdVec<low::CustomFuncId, FunctionValue<'a>>,
    main: FunctionValue<'a>,
    unit: BasicValueEnum<'a>,
}

fn get_llvm_type<'a>(_context: &'a Context, _ty: &low::Type) -> BasicTypeEnum<'a> {
    unimplemented!();
}

fn gen_expr<'a>(
    context: &'a Context,
    module: &Module<'a>,
    builder: &Builder<'a>,
    globals: &Globals<'a>,
    func: FunctionValue<'a>,
    expr: &low::Expr,
    locals: &mut IdVec<low::LocalId, BasicValueEnum<'a>>,
) -> BasicValueEnum<'a> {
    use low::Expr as E;
    match expr {
        E::Local(local_id) => locals[local_id],
        E::Call(func_id, local_id) => builder
            .build_call(globals.funcs[func_id], &[locals[local_id]], "result")
            .try_as_basic_value()
            .left()
            .unwrap(),
        E::If(local_id, then_expr, else_expr) => {
            let then_block = context.append_basic_block(func, "then_block");
            let else_block = context.append_basic_block(func, "else_block");
            let next_block = context.append_basic_block(func, "next_block");

            let cond = locals[local_id].into_int_value();
            builder.build_conditional_branch(cond, &then_block, &else_block);

            builder.position_at_end(&then_block);
            let result_then = gen_expr(context, module, builder, globals, func, then_expr, locals);
            builder.build_unconditional_branch(&next_block);

            builder.position_at_end(&else_block);
            let result_else = gen_expr(context, module, builder, globals, func, else_expr, locals);
            builder.build_unconditional_branch(&next_block);

            builder.position_at_end(&next_block);
            let phi = builder.build_phi(result_then.get_type(), "result");
            phi.add_incoming(&[(&result_then, &then_block), (&result_else, &else_block)]);
            phi.as_basic_value().into()
        }
        E::LetMany(bindings, local_id) => {
            let len = locals.len();
            for (_, binding_expr) in bindings {
                let binding_val = gen_expr(
                    context,
                    module,
                    builder,
                    globals,
                    func,
                    &*binding_expr,
                    locals,
                );
                let _ = locals.push(binding_val);
            }
            let body = locals[local_id];
            locals.truncate(len);
            body
        }
        E::Unreachable(type_) => {
            todo![];
        }
        E::Tuple(fields) => {
            let field_tys: Vec<_> = fields.iter().map(|id| locals[id].get_type()).collect();
            let tup_ty = context.struct_type(&field_tys[..], false);

            let mut tup = tup_ty.get_undef();
            for (elem, id) in fields.iter().enumerate() {
                tup = builder
                    .build_insert_value(tup, locals[id], elem.try_into().unwrap(), "insert")
                    .unwrap()
                    .into_struct_value();
            }

            BasicValueEnum::from(tup).into()
        }
        E::TupleField(local_id, elem) => builder
            .build_extract_value(
                locals[local_id].into_struct_value(),
                (*elem).try_into().unwrap(),
                "extract",
            )
            .unwrap()
            .into(),
        E::WrapVariant(variants, variant_id, local_id) => {
            todo![];
        }
        E::UnwrapVariant(variant_id, local_id) => {
            todo![];
        }
        E::WrapCustom(type_id, local_id) => {
            todo![];
        }
        E::UnwrapCustom(type_id, local_id) => {
            todo![];
        }
        E::CheckVariant(variant_id, local_id) => {
            todo![];
        }
        E::WrapBoxed(local_id) => {
            todo![];
        }
        E::UnwrapBoxed(local_id) => {
            todo![];
        }
        E::Retain(local_id, type_) => {
            todo![];
        }
        E::Release(local_id, type_) => {
            todo![];
        }
        E::ArithOp(op) => match op {
            low::ArithOp::Op(ty, bin_op, lhs, rhs) => match bin_op {
                first_ord::BinOp::Add => match ty {
                    first_ord::NumType::Byte => BasicValueEnum::from(builder.build_int_add(
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "byte_add",
                    ))
                    .into(),
                    first_ord::NumType::Int => BasicValueEnum::from(builder.build_int_add(
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "int_add",
                    ))
                    .into(),
                    first_ord::NumType::Float => BasicValueEnum::from(builder.build_float_add(
                        locals[lhs].into_float_value(),
                        locals[rhs].into_float_value(),
                        "float_add",
                    ))
                    .into(),
                },
                first_ord::BinOp::Sub => match ty {
                    first_ord::NumType::Byte => BasicValueEnum::from(builder.build_int_sub(
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "byte_sub",
                    ))
                    .into(),
                    first_ord::NumType::Int => BasicValueEnum::from(builder.build_int_sub(
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "int_sub",
                    ))
                    .into(),
                    first_ord::NumType::Float => BasicValueEnum::from(builder.build_float_sub(
                        locals[lhs].into_float_value(),
                        locals[rhs].into_float_value(),
                        "float_sub",
                    ))
                    .into(),
                },
                first_ord::BinOp::Mul => match ty {
                    first_ord::NumType::Byte => BasicValueEnum::from(builder.build_int_mul(
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "byte_mul",
                    ))
                    .into(),
                    first_ord::NumType::Int => BasicValueEnum::from(builder.build_int_mul(
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "int_mul",
                    ))
                    .into(),
                    first_ord::NumType::Float => BasicValueEnum::from(builder.build_float_mul(
                        locals[lhs].into_float_value(),
                        locals[rhs].into_float_value(),
                        "float_mul",
                    ))
                    .into(),
                },
                first_ord::BinOp::Div => match ty {
                    first_ord::NumType::Byte => {
                        BasicValueEnum::from(builder.build_int_unsigned_div(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "byte_div",
                        ))
                        .into()
                    }
                    first_ord::NumType::Int => BasicValueEnum::from(builder.build_int_signed_div(
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "int_div",
                    ))
                    .into(),
                    first_ord::NumType::Float => BasicValueEnum::from(builder.build_float_div(
                        locals[lhs].into_float_value(),
                        locals[rhs].into_float_value(),
                        "float_div",
                    ))
                    .into(),
                },
            },
            low::ArithOp::Cmp(ty, cmp, lhs, rhs) => match cmp {
                first_ord::Comparison::Less => match ty {
                    first_ord::NumType::Byte => BasicValueEnum::from(builder.build_int_compare(
                        IntPredicate::ULT,
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "bytes_less",
                    ))
                    .into(),
                    first_ord::NumType::Int => BasicValueEnum::from(builder.build_int_compare(
                        IntPredicate::SLT,
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "int_less",
                    ))
                    .into(),
                    first_ord::NumType::Float => BasicValueEnum::from(builder.build_float_compare(
                        FloatPredicate::OLT,
                        locals[lhs].into_float_value(),
                        locals[rhs].into_float_value(),
                        "float_less",
                    ))
                    .into(),
                },
                first_ord::Comparison::LessEqual => match ty {
                    first_ord::NumType::Byte => BasicValueEnum::from(builder.build_int_compare(
                        IntPredicate::ULE,
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "bytes_less_equal",
                    ))
                    .into(),
                    first_ord::NumType::Int => BasicValueEnum::from(builder.build_int_compare(
                        IntPredicate::SLE,
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "int_less_equal",
                    ))
                    .into(),
                    first_ord::NumType::Float => BasicValueEnum::from(builder.build_float_compare(
                        FloatPredicate::OLE,
                        locals[lhs].into_float_value(),
                        locals[rhs].into_float_value(),
                        "float_less_equal",
                    ))
                    .into(),
                },
                first_ord::Comparison::Equal => match ty {
                    first_ord::NumType::Byte => BasicValueEnum::from(builder.build_int_compare(
                        IntPredicate::EQ,
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "bytes_equal",
                    ))
                    .into(),
                    first_ord::NumType::Int => BasicValueEnum::from(builder.build_int_compare(
                        IntPredicate::EQ,
                        locals[lhs].into_int_value(),
                        locals[rhs].into_int_value(),
                        "int_equal",
                    ))
                    .into(),
                    first_ord::NumType::Float => BasicValueEnum::from(builder.build_float_compare(
                        FloatPredicate::OEQ,
                        locals[lhs].into_float_value(),
                        locals[rhs].into_float_value(),
                        "float_equal",
                    ))
                    .into(),
                },
            },
            low::ArithOp::Negate(ty, local_id) => match ty {
                first_ord::NumType::Byte => panic!(), // Bytes are unsigned. Don't negate them!
                first_ord::NumType::Int => BasicValueEnum::from(
                    builder.build_int_neg(locals[local_id].into_int_value(), "int_neg"),
                )
                .into(),
                first_ord::NumType::Float => BasicValueEnum::from(
                    builder.build_float_neg(locals[local_id].into_float_value(), "float_neg"),
                )
                .into(),
            },
        },
        E::ArrayOp(rep, item_type, array_op) => {
            todo![];
        }
        E::IoOp(rep, io_op) => {
            todo![];
        }
        E::BoolLit(val) => {
            BasicValueEnum::from(context.bool_type().const_int(*val as u64, false)).into()
        }

        E::ByteLit(val) => {
            BasicValueEnum::from(context.i8_type().const_int(*val as u64, false)).into()
        }

        E::IntLit(val) => {
            BasicValueEnum::from(context.i64_type().const_int(*val as u64, true)).into()
        }
        E::FloatLit(val) => BasicValueEnum::from(context.f64_type().const_float(*val)).into(),
    }
}
