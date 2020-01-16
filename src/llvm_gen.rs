use crate::data::first_order_ast as first_ord;
use crate::data::low_ast as low;
use crate::data::repr_constrained_ast as constrain;
use crate::util::id_vec::IdVec;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::targets::TargetData;
use inkwell::types::{BasicTypeEnum, StructType};
use inkwell::values::{BasicValueEnum, FunctionValue};
use inkwell::AddressSpace;
use inkwell::{FloatPredicate, IntPredicate};
use lib_builtins::core::LibC;
use lib_builtins::flat_array::FlatArrayBuiltin;
use lib_builtins::rc::RcBoxBuiltin;
use std::collections::BTreeMap;
use std::convert::TryInto;

const VARIANT_DISCRIM_IDX: u32 = 0;
const VARIANT_ALIGN_IDX: u32 = 1;
const VARIANT_BYTES_IDX: u32 = 2;

#[derive(Clone, Debug)]
struct Globals<'a> {
    context: &'a Context,
    module: &'a Module<'a>,
    target: &'a TargetData,
    libc: LibC<'a>,
    custom_types: IdVec<low::CustomTypeId, StructType<'a>>,
    funcs: IdVec<low::CustomFuncId, FunctionValue<'a>>,
}

struct Instances<'a> {
    flat_arrays: BTreeMap<low::Type, FlatArrayBuiltin<'a>>,
    rcs: BTreeMap<low::Type, RcBoxBuiltin<'a>>,
}

impl<'a> Instances<'a> {
    fn get_flat_array(
        &mut self,
        globals: &Globals<'a>,
        item_type: &low::Type,
    ) -> FlatArrayBuiltin<'a> {
        if let Some(existing) = self.flat_arrays.get(&item_type.clone()) {
            return *existing;
        }
        let new_builtin = FlatArrayBuiltin::declare(
            globals.context,
            globals.module,
            get_llvm_type(globals, self, item_type),
        );
        self.flat_arrays.insert(item_type.clone(), new_builtin);
        return new_builtin;
    }
    fn get_rc(&mut self, globals: &Globals<'a>, item_type: &low::Type) -> RcBoxBuiltin<'a> {
        if let Some(existing) = self.rcs.get(&item_type.clone()) {
            return *existing;
        }
        let new_builtin = RcBoxBuiltin::declare(
            globals.context,
            globals.module,
            get_llvm_type(globals, self, item_type),
        );
        self.rcs.insert(item_type.clone(), new_builtin);
        return new_builtin;
    }
}

fn get_llvm_variant_type<'a>(
    globals: &Globals<'a>,
    instances: &mut Instances<'a>,
    variants: &IdVec<low::VariantId, low::Type>,
) -> StructType<'a> {
    if variants.len() == 0 {
        return globals.context.struct_type(&[], false).into();
    }

    let discrim_type = if variants.len() <= 1 << 8 {
        globals.context.i8_type()
    } else if variants.len() <= 1 << 16 {
        globals.context.i16_type()
    } else if variants.len() <= 1 << 32 {
        globals.context.i32_type()
    } else {
        globals.context.i64_type()
    };

    let (max_alignment, max_size) = {
        let mut max_alignment = 1;
        let mut max_size = 0;
        for variant_type in &variants.items {
            let variant_type = get_llvm_type(globals, instances, &variant_type);
            let alignment = globals.target.get_abi_alignment(&variant_type);
            let size = globals.target.get_abi_size(&variant_type);
            max_alignment = max_alignment.max(alignment);
            max_size = max_size.max(size);
        }
        (max_alignment, max_size)
    };

    let alignment_array = {
        let alignment_type = match max_alignment {
            1 => globals.context.i8_type(),
            2 => globals.context.i16_type(),
            4 => globals.context.i32_type(),
            8 => globals.context.i64_type(),
            _ => panic!["Unsupported alignment {}", max_alignment],
        };
        alignment_type.array_type(0)
    };

    let bytes = globals
        .context
        .i8_type()
        .array_type(max_size.try_into().unwrap());

    let field_types = &[discrim_type.into(), alignment_array.into(), bytes.into()];
    globals.context.struct_type(field_types, false)
}

fn get_llvm_type<'a>(
    globals: &Globals<'a>,
    instances: &mut Instances<'a>,
    type_: &low::Type,
) -> BasicTypeEnum<'a> {
    match type_ {
        low::Type::Bool => globals.context.bool_type().into(),
        low::Type::Num(first_ord::NumType::Byte) => globals.context.i8_type().into(),
        low::Type::Num(first_ord::NumType::Int) => globals.context.i64_type().into(),
        low::Type::Num(first_ord::NumType::Float) => globals.context.f64_type().into(),
        low::Type::Array(constrain::RepChoice::OptimizedMut, item_type) => instances
            .get_flat_array(globals, item_type)
            .self_type
            .self_type
            .ptr_type(AddressSpace::Generic)
            .into(),
        low::Type::Array(constrain::RepChoice::FallbackImmut, _item_type) => {
            unimplemented![];
        }
        low::Type::HoleArray(constrain::RepChoice::OptimizedMut, item_type) => instances
            .get_flat_array(globals, item_type)
            .self_hole_type
            .into(),
        low::Type::HoleArray(constrain::RepChoice::FallbackImmut, _item_type) => {
            unimplemented![];
        }
        low::Type::Tuple(item_types) => {
            let mut field_types = vec![];
            for item_type in item_types.iter() {
                field_types.push(get_llvm_type(globals, instances, item_type));
            }

            globals.context.struct_type(&field_types[..], false).into()
        }
        low::Type::Variants(variants) => {
            get_llvm_variant_type(globals, instances, &variants).into()
        }
        low::Type::Boxed(type_) => instances.get_rc(globals, type_).self_type.into(),
        low::Type::Custom(type_id) => globals.custom_types[type_id].into(),
    }
}

fn gen_expr<'a>(
    builder: &Builder<'a>,
    instances: &mut Instances<'a>,
    globals: &Globals<'a>,
    func: FunctionValue<'a>,
    expr: &low::Expr,
    locals: &mut IdVec<low::LocalId, BasicValueEnum<'a>>,
) -> BasicValueEnum<'a> {
    use low::Expr as E;
    let context = globals.context;
    let module = globals.module;
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
            let result_then = gen_expr(builder, instances, globals, func, then_expr, locals);
            builder.build_unconditional_branch(&next_block);

            builder.position_at_end(&else_block);
            let result_else = gen_expr(builder, instances, globals, func, else_expr, locals);
            builder.build_unconditional_branch(&next_block);

            builder.position_at_end(&next_block);
            let phi = builder.build_phi(result_then.get_type(), "result");
            phi.add_incoming(&[(&result_then, &then_block), (&result_else, &else_block)]);
            phi.as_basic_value().into()
        }
        E::LetMany(bindings, local_id) => {
            let len = locals.len();
            for (_, binding_expr) in bindings {
                let binding_val =
                    gen_expr(builder, instances, globals, func, &*binding_expr, locals);
                let _ = locals.push(binding_val);
            }
            let body = locals[local_id];
            locals.truncate(len);
            body
        }
        E::Unreachable(type_) => {
            builder.build_unreachable();
            let unreachable_block = context.append_basic_block(func, "unreachable");
            builder.position_at_end(&unreachable_block);
            match get_llvm_type(globals, instances, type_) {
                BasicTypeEnum::ArrayType(t) => t.get_undef().into(),
                BasicTypeEnum::FloatType(t) => t.get_undef().into(),
                BasicTypeEnum::IntType(t) => t.get_undef().into(),
                BasicTypeEnum::PointerType(t) => t.get_undef().into(),
                BasicTypeEnum::StructType(t) => t.get_undef().into(),
                BasicTypeEnum::VectorType(t) => t.get_undef().into(),
            }
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
            let variant_type = get_llvm_variant_type(globals, instances, &variants);
            let byte_array_type = variant_type
                .get_field_type_at_index(VARIANT_BYTES_IDX)
                .unwrap();
            let byte_array_ptr = builder.build_alloca(byte_array_type, "byte_array_ptr");
            let casted_byte_array_ptr = builder.build_bitcast(
                byte_array_ptr,
                locals[local_id].get_type(),
                "casted_byte_array_ptr",
            );
            let byte_array = builder.build_load(byte_array_ptr, "byte_array");

            builder.build_store(casted_byte_array_ptr.into_pointer_value(), locals[local_id]);

            let discrim = variant_type
                .get_field_type_at_index(VARIANT_DISCRIM_IDX)
                .unwrap()
                .into_int_type()
                .const_int(variant_id.0.try_into().unwrap(), false);

            let mut variant_value = variant_type.get_undef();
            variant_value = builder
                .build_insert_value(variant_value, discrim, VARIANT_DISCRIM_IDX, "insert")
                .unwrap()
                .into_struct_value();
            variant_value = builder
                .build_insert_value(variant_value, byte_array, VARIANT_BYTES_IDX, "insert")
                .unwrap()
                .into_struct_value();
            variant_value.into()
        }
        E::UnwrapVariant(variants, variant_id, local_id) => {
            let variant_type = get_llvm_variant_type(globals, instances, &variants);

            let byte_array_type = variant_type
                .get_field_type_at_index(VARIANT_BYTES_IDX)
                .unwrap();
            let byte_array_ptr = builder.build_alloca(byte_array_type, "byte_array_ptr");

            let byte_array = builder
                .build_extract_value(
                    locals[local_id].into_struct_value(),
                    VARIANT_BYTES_IDX,
                    "byte_array",
                )
                .unwrap();

            builder.build_store(byte_array_ptr, byte_array);

            let content_ptr = builder.build_bitcast(
                byte_array_ptr,
                get_llvm_type(globals, instances, &variants[variant_id]),
                "content_ptr",
            );

            let content = builder.build_load(content_ptr.into_pointer_value(), "content");

            content
        }
        E::WrapCustom(type_id, local_id) => {
            let mut custom_type_val = globals.custom_types[type_id].get_undef();
            custom_type_val = builder
                .build_insert_value(custom_type_val, locals[local_id], 0, "insert")
                .unwrap()
                .into_struct_value();

            custom_type_val.into()
        }
        E::UnwrapCustom(type_id, local_id) => {
            let mut custom_type_content = builder
                .build_extract_value(locals[local_id].into_struct_value(), 0, "custom_type_val")
                .unwrap();
            custom_type_content
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
