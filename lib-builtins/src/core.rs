use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicTypeEnum, FloatType, IntType};
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue};
use inkwell::{AddressSpace, IntPredicate};
use itertools::Itertools;

#[derive(Clone, Copy, Debug)]
pub struct LibC<'a> {
    pub exit: FunctionValue<'a>,
    pub realloc: FunctionValue<'a>,
    pub printf: FunctionValue<'a>,
}

// TODO: these declarations are not portable
impl<'a> LibC<'a> {
    pub fn declare(context: &'a Context, module: &Module<'a>) -> Self {
        let void_type = context.void_type();
        let i64_type = context.i64_type();
        let i32_type = context.i32_type();
        let i8_ptr_type = context.i8_type().ptr_type(AddressSpace::Generic);

        let exit = module.add_function(
            "exit",
            void_type.fn_type(&[i32_type.into()], false),
            Some(Linkage::External),
        );

        let realloc = module.add_function(
            "realloc",
            i8_ptr_type.fn_type(&[i8_ptr_type.into(), i64_type.into()], false),
            Some(Linkage::External),
        );

        let printf = module.add_function(
            "printf",
            i32_type.fn_type(&[i8_ptr_type.into()], true),
            Some(Linkage::External),
        );

        Self {
            exit,
            realloc,
            printf,
        }
    }
}

pub(super) fn size_of<'a>(ty: BasicTypeEnum<'a>) -> Option<IntValue<'a>> {
    match ty {
        BasicTypeEnum::ArrayType(actual_ty) => actual_ty.size_of(),
        BasicTypeEnum::FloatType(actual_ty) => Some(actual_ty.size_of()),
        BasicTypeEnum::IntType(acutal_ty) => Some(acutal_ty.size_of()),
        BasicTypeEnum::PointerType(acutal_ty) => Some(acutal_ty.size_of()),
        BasicTypeEnum::StructType(acutal_ty) => acutal_ty.size_of(),
        BasicTypeEnum::VectorType(acutal_ty) => acutal_ty.size_of(),
    }
}

pub(super) fn if_<'a>(
    context: &'a Context,
    builder: &Builder<'a>,
    f: FunctionValue<'a>,
    cond: IntValue<'a>,
) -> BasicBlock {
    let then_block = context.append_basic_block(f, "then_block");
    let next_block = context.append_basic_block(f, "next_block");
    builder.build_conditional_branch(cond, &then_block, &next_block);
    builder.position_at_end(&then_block);
    let branch = builder.build_unconditional_branch(&next_block);
    builder.position_before(&branch);
    next_block
}

pub(super) fn for_i_less_than<'a>(
    context: &'a Context,
    builder: &Builder<'a>,
    f: FunctionValue<'a>,
    end_for: IntValue<'a>,
) -> (BasicBlock, IntValue<'a>) {
    let i64_type = context.i64_type();

    let i_ptr = builder.build_alloca(i64_type, "i_ptr");
    builder.build_store(i_ptr, i64_type.const_int(0, false));

    let for_block = context.append_basic_block(f, "for_block");
    let next_block = context.append_basic_block(f, "next_block");

    builder.position_at_end(&for_block);
    let i_cur = builder.build_load(i_ptr, "i_cur").into_int_value();
    let i_new = builder.build_int_add(i_cur, i64_type.const_int(1, false), "i_new");
    let store = builder.build_store(i_ptr, i_new);

    let done = builder.build_int_compare(IntPredicate::UGE, i_new, end_for, "done");
    builder.build_conditional_branch(done, &next_block, &for_block);

    builder.position_at(&for_block, &store);
    (next_block, i_cur)
}

pub(super) unsafe fn get_member<'a>(
    builder: &Builder<'a>,
    struct_ptr: PointerValue<'a>,
    idx: u32,
    name: &str,
) -> BasicValueEnum<'a> {
    let member_ptr_name = format!("{}_ptr", name);
    builder.build_load(
        builder.build_struct_gep(struct_ptr, idx, &member_ptr_name),
        name,
    )
}

pub(super) unsafe fn set_member<'a>(
    builder: &Builder<'a>,
    struct_ptr: PointerValue<'a>,
    idx: u32,
    val: BasicValueEnum<'a>,
    name: &str,
) {
    let member_ptr_name = format!("{}_ptr", name);
    builder.build_store(
        builder.build_struct_gep(struct_ptr, idx, &member_ptr_name),
        val,
    );
}

fn get_float_name<'a>(context: &'a Context, ty: FloatType<'a>) -> &'static str {
    if ty == context.f16_type() {
        "f16"
    } else if ty == context.f32_type() {
        "f32"
    } else if ty == context.f64_type() {
        "f64"
    } else if ty == context.f128_type() {
        "f128"
    } else {
        unreachable!();
    }
}

fn get_int_name<'a>(context: &'a Context, ty: IntType<'a>) -> &'static str {
    if ty == context.i8_type() {
        "i8"
    } else if ty == context.i16_type() {
        "i16"
    } else if ty == context.i32_type() {
        "i32"
    } else if ty == context.i64_type() {
        "i64"
    } else if ty == context.i128_type() {
        "i128"
    } else {
        unreachable!();
    }
}

pub(super) fn mangle_basic<'a>(context: &'a Context, ty: BasicTypeEnum<'a>) -> String {
    match ty {
        BasicTypeEnum::ArrayType(inner_ty) => format!(
            "A{}{}",
            inner_ty.len(),
            mangle_basic(context, inner_ty.get_element_type())
        ),
        BasicTypeEnum::FloatType(inner_ty) => get_float_name(context, inner_ty).to_owned(),
        BasicTypeEnum::IntType(inner_ty) => get_int_name(context, inner_ty).to_owned(),
        BasicTypeEnum::PointerType(inner_ty) => {
            format!("P{}", mangle_basic(context, inner_ty.into()))
        }
        BasicTypeEnum::StructType(inner_ty) => {
            if inner_ty.is_opaque() {
                format!(
                    "T{}{}",
                    inner_ty.count_fields(),
                    inner_ty
                        .get_field_types()
                        .iter()
                        .map(|x| mangle_basic(context, *x))
                        .join("")
                )
            } else {
                format!("${}", inner_ty.get_name().unwrap().to_str().unwrap())
            }
        }
        BasicTypeEnum::VectorType(inner_ty) => {
            if inner_ty.is_sized() {
                format!(
                    "V{}{}",
                    inner_ty.get_size(),
                    mangle_basic(context, inner_ty.get_element_type())
                )
            } else {
                format!("V{}", mangle_basic(context, inner_ty.get_element_type()))
            }
        }
    }
}
