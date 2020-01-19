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
use lib_builtins::flat_array::{FlatArrayBuiltin, FlatArrayIoBuiltin};
use lib_builtins::rc::RcBoxBuiltin;
use std::collections::BTreeMap;
use std::convert::TryInto;

const VARIANT_DISCRIM_IDX: u32 = 0;
// we use a zero sized array to enforce proper alignment on `bytes`
const VARIANT_ALIGN_IDX: u32 = 1;
const VARIANT_BYTES_IDX: u32 = 2;

#[derive(Clone, Debug)]
struct Globals<'a> {
    context: &'a Context,
    module: &'a Module<'a>,
    target: &'a TargetData,
    libc: LibC<'a>,
    custom_types: IdVec<low::CustomTypeId, CustomTypeDecls<'a>>,
    funcs: IdVec<low::CustomFuncId, FunctionValue<'a>>,
}

#[derive(Clone, Copy, Debug)]
struct CustomTypeDecls<'a> {
    ty: StructType<'a>,
    release: FunctionValue<'a>,
    retain: FunctionValue<'a>,
}

struct Instances<'a> {
    flat_arrays: BTreeMap<low::Type, FlatArrayBuiltin<'a>>,
    flat_array_io: FlatArrayIoBuiltin<'a>,
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
        low::Type::Custom(type_id) => globals.custom_types[type_id].ty.into(),
    }
}

#[derive(Clone, Copy, Debug)]
enum RcOp {
    Retain,
    Release,
}

fn gen_rc_op<'a>(
    op: RcOp,
    builder: &Builder<'a>,
    instances: &mut Instances<'a>,
    globals: &Globals<'a>,
    func: FunctionValue<'a>,
    ty: &low::Type,
    arg: BasicValueEnum<'a>,
) {
    match ty {
        low::Type::Bool => {}
        low::Type::Num(_) => {}
        low::Type::Array(constrain::RepChoice::OptimizedMut, item_type) => match op {
            RcOp::Retain => {
                let retain_func = instances
                    .get_flat_array(globals, item_type)
                    .self_type
                    .retain;
                builder.build_call(retain_func, &[arg], "retain_flat_array");
            }
            RcOp::Release => {
                let release_func = instances
                    .get_flat_array(globals, item_type)
                    .self_type
                    .release;
                builder.build_call(release_func, &[arg], "release_flat_array");
            }
        },
        low::Type::Array(constrain::RepChoice::FallbackImmut, _item_type) => {
            unimplemented![];
        }
        low::Type::HoleArray(constrain::RepChoice::OptimizedMut, item_type) => match op {
            RcOp::Retain => {
                let release_func = instances.get_flat_array(globals, item_type).retain_hole;
                builder.build_call(release_func, &[arg], "release_flat_hole_array");
            }
            RcOp::Release => {
                let release_func = instances.get_flat_array(globals, item_type).release_hole;
                builder.build_call(release_func, &[arg], "release_flat_hole_array");
            }
        },
        low::Type::HoleArray(constrain::RepChoice::FallbackImmut, _item_type) => {
            unimplemented![];
        }
        low::Type::Tuple(item_types) => {
            for i in 0..item_types.len() {
                let current_item = builder
                    .build_extract_value(
                        arg.into_struct_value(),
                        i.try_into().unwrap(),
                        "current_item",
                    )
                    .unwrap();
                gen_rc_op(
                    op,
                    builder,
                    instances,
                    globals,
                    func,
                    &item_types[i],
                    current_item,
                );
            }
        }
        low::Type::Variants(variant_types) => {
            let discrim = builder
                .build_extract_value(arg.into_struct_value(), VARIANT_DISCRIM_IDX, "discrim")
                .unwrap()
                .into_int_value();
            let undefined_block = globals.context.append_basic_block(func, "undefined");
            let mut variant_blocks = vec![];
            for _ in 0..variant_types.len() {
                variant_blocks.push(globals.context.append_basic_block(func, "variant"));
            }
            let switch_blocks = variant_blocks
                .iter()
                .enumerate()
                .map(|(i, variant_block)| {
                    (
                        globals
                            .context
                            .i64_type()
                            .const_int(i.try_into().unwrap(), false),
                        variant_block,
                    )
                })
                .collect::<Vec<_>>();

            builder.build_switch(discrim, &undefined_block, &switch_blocks[..]);

            let next_block = globals.context.append_basic_block(func, "next");

            builder.position_at_end(&undefined_block);
            builder.build_unreachable();
            for (i, variant_block) in variant_blocks.iter().enumerate() {
                builder.position_at_end(variant_block);
                let variant_id = low::VariantId(i);

                let unwrapped_variant =
                    gen_unwrap_variant(builder, instances, globals, arg, variant_types, variant_id);

                gen_rc_op(
                    op,
                    builder,
                    instances,
                    globals,
                    func,
                    &variant_types[variant_id],
                    unwrapped_variant,
                );

                builder.build_unconditional_branch(&next_block);
            }

            builder.position_at_end(&next_block);
        }
        low::Type::Boxed(inner_type) => match op {
            RcOp::Retain => {
                let retain_func = instances.get_rc(globals, inner_type).retain;
                builder.build_call(retain_func, &[arg], "retain_boxed");
            }
            RcOp::Release => {
                let release_func = instances.get_rc(globals, inner_type).release;
                builder.build_call(release_func, &[arg], "release_boxed");
            }
        },
        low::Type::Custom(type_id) => {
            let custom_type_content = builder
                .build_extract_value(arg.into_struct_value(), 0, "custom_type_val")
                .unwrap();

            match op {
                RcOp::Retain => {
                    let retain_func = globals.custom_types[type_id].retain;
                    builder.build_call(retain_func, &[custom_type_content], "retain_boxed");
                }
                RcOp::Release => {
                    let release_func = globals.custom_types[type_id].release;
                    builder.build_call(release_func, &[custom_type_content], "release_boxed");
                }
            }
        }
    }
}

fn gen_unwrap_variant<'a>(
    builder: &Builder<'a>,
    instances: &mut Instances<'a>,
    globals: &Globals<'a>,
    variant_value: BasicValueEnum<'a>,
    variants: &IdVec<low::VariantId, low::Type>,
    variant_id: low::VariantId,
) -> BasicValueEnum<'a> {
    let variant_type = get_llvm_variant_type(globals, instances, &variants);

    let byte_array_type = variant_type
        .get_field_type_at_index(VARIANT_BYTES_IDX)
        .unwrap();
    let byte_array_ptr = builder.build_alloca(byte_array_type, "byte_array_ptr");

    let byte_array = builder
        .build_extract_value(
            variant_value.into_struct_value(),
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
            phi.as_basic_value()
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
            let field_types: Vec<_> = fields.iter().map(|id| locals[id].get_type()).collect();
            let tup_type = context.struct_type(&field_types[..], false);

            let mut tup = tup_type.get_undef();
            for (elem, id) in fields.iter().enumerate() {
                tup = builder
                    .build_insert_value(tup, locals[id], elem.try_into().unwrap(), "insert")
                    .unwrap()
                    .into_struct_value();
            }

            tup.into()
        }
        E::TupleField(local_id, elem) => builder
            .build_extract_value(
                locals[local_id].into_struct_value(),
                (*elem).try_into().unwrap(),
                "extract",
            )
            .unwrap(),
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
        E::UnwrapVariant(variants, variant_id, local_id) => gen_unwrap_variant(
            builder,
            instances,
            globals,
            locals[local_id],
            variants,
            *variant_id,
        ),
        E::WrapCustom(type_id, local_id) => {
            let mut custom_type_val = globals.custom_types[type_id].ty.get_undef();
            custom_type_val = builder
                .build_insert_value(custom_type_val, locals[local_id], 0, "insert")
                .unwrap()
                .into_struct_value();

            custom_type_val.into()
        }
        E::UnwrapCustom(_type_id, local_id) => {
            let custom_type_content = builder
                .build_extract_value(locals[local_id].into_struct_value(), 0, "custom_type_val")
                .unwrap();

            custom_type_content
        }
        E::CheckVariant(variant_id, local_id) => {
            let discrim = builder
                .build_extract_value(
                    locals[local_id].into_struct_value(),
                    VARIANT_DISCRIM_IDX,
                    "discrim",
                )
                .unwrap()
                .into_int_value();

            let casted_variant_id = discrim
                .get_type()
                .const_int(variant_id.0.try_into().unwrap(), false);

            builder
                .build_int_compare(
                    IntPredicate::EQ,
                    casted_variant_id,
                    discrim,
                    "check_variant",
                )
                .into()
        }
        E::WrapBoxed(local_id, inner_type) => {
            let builtin = instances.get_rc(globals, inner_type);
            builder
                .build_call(builtin.new, &[locals[local_id]], "new_box")
                .try_as_basic_value()
                .left()
                .unwrap()
        }
        E::UnwrapBoxed(local_id, inner_type) => {
            let builtin = instances.get_rc(globals, inner_type);
            builder
                .build_call(builtin.get, &[locals[local_id]], "unbox")
                .try_as_basic_value()
                .left()
                .unwrap()
        }
        E::Retain(local_id, ty) => {
            gen_rc_op(
                RcOp::Retain,
                builder,
                instances,
                globals,
                func,
                ty,
                locals[local_id],
            );
            context.struct_type(&[], false).get_undef().into()
        }
        E::Release(local_id, ty) => {
            gen_rc_op(
                RcOp::Release,
                builder,
                instances,
                globals,
                func,
                ty,
                locals[local_id],
            );
            context.struct_type(&[], false).get_undef().into()
        }
        E::ArithOp(op) => match op {
            low::ArithOp::Op(type_, bin_op, lhs, rhs) => match bin_op {
                first_ord::BinOp::Add => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_add(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "byte_add",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_add(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_add",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_add(
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_add",
                        )
                        .into(),
                },
                first_ord::BinOp::Sub => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_sub(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "byte_sub",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_sub(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_sub",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_sub(
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_sub",
                        )
                        .into(),
                },
                first_ord::BinOp::Mul => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_mul(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "byte_mul",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_mul(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_mul",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_mul(
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_mul",
                        )
                        .into(),
                },
                first_ord::BinOp::Div => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_unsigned_div(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "byte_div",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_signed_div(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_div",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_div(
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_div",
                        )
                        .into(),
                },
            },
            low::ArithOp::Cmp(type_, cmp, lhs, rhs) => match cmp {
                first_ord::Comparison::Less => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_compare(
                            IntPredicate::ULT,
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "bytes_less",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_compare(
                            IntPredicate::SLT,
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_less",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_compare(
                            FloatPredicate::OLT,
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_less",
                        )
                        .into(),
                },
                first_ord::Comparison::LessEqual => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_compare(
                            IntPredicate::ULE,
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "bytes_less_equal",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_compare(
                            IntPredicate::SLE,
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_less_equal",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_compare(
                            FloatPredicate::OLE,
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_less_equal",
                        )
                        .into(),
                },
                first_ord::Comparison::Equal => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "bytes_equal",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_equal",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_compare(
                            FloatPredicate::OEQ,
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_equal",
                        )
                        .into(),
                },
            },
            low::ArithOp::Negate(type_, local_id) => match type_ {
                first_ord::NumType::Byte => builder
                    .build_int_neg(locals[local_id].into_int_value(), "byte_neg")
                    .into(),
                first_ord::NumType::Int => builder
                    .build_int_neg(locals[local_id].into_int_value(), "int_neg")
                    .into(),
                first_ord::NumType::Float => builder
                    .build_float_neg(locals[local_id].into_float_value(), "float_neg")
                    .into(),
            },
        },
        E::ArrayOp(rep, item_type, array_op) => match rep {
            constrain::RepChoice::OptimizedMut => {
                let builtin = instances.get_flat_array(globals, item_type);
                match array_op {
                    low::ArrayOp::New() => builder
                        .build_call(builtin.new, &[], "flat_array_new")
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Item(array_id, index_id) => builder
                        .build_call(
                            builtin.item,
                            &[locals[array_id], locals[index_id]],
                            "flat_array_item",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Len(array_id) => builder
                        .build_call(builtin.len, &[locals[array_id]], "flat_array_len")
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Push(array_id, item_id) => builder
                        .build_call(
                            builtin.len,
                            &[locals[array_id], locals[item_id]],
                            "flat_array_push",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Pop(array_id) => builder
                        .build_call(builtin.pop, &[locals[array_id]], "flat_array_pop")
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Replace(array_id, item_id) => builder
                        .build_call(
                            builtin.len,
                            &[locals[array_id], locals[item_id]],
                            "flat_array_replace",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                }
            }
            constrain::RepChoice::FallbackImmut => {
                unimplemented![];
            }
        },
        E::IoOp(rep, io_op) => match rep {
            constrain::RepChoice::OptimizedMut => {
                let builtin_io = instances.flat_array_io;
                match io_op {
                    low::IoOp::Input => builder
                        .build_call(builtin_io.input, &[], "flat_array_input")
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::IoOp::Output(array_id) => builder
                        .build_call(builtin_io.output, &[locals[array_id]], "flat_array_output")
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                }
            }
            constrain::RepChoice::FallbackImmut => {
                unimplemented![];
            }
        },
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
