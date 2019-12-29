use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::types::{BasicTypeEnum, IntType};
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue};

#[derive(Clone, Copy, Debug)]
pub struct LibC<'a> {
    pub memcpy: FunctionValue<'a>,
}

impl<'a> LibC<'a> {
    pub fn new(context: &'a Context) -> Self {
        // TODO: initialize libc
        unimplemented!();
    }
}

// there must be a better way to do this, but I couldn't find it
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
    builder: &'a Builder<'a>,
    f: FunctionValue<'a>,
    cond: IntValue<'a>,
) -> BasicBlock {
    let if_body = context.append_basic_block(f, "if_body");
    let if_tail = context.append_basic_block(f, "if_tail");
    builder.build_conditional_branch(cond, &if_body, &if_tail);
    builder.position_at_end(&if_body);
    if_tail
}

pub(super) unsafe fn get_member<'a>(
    context: &'a Context,
    builder: &'a Builder<'a>,
    struct_ptr: PointerValue<'a>,
    idx: u32,
    name: &str,
) -> BasicValueEnum<'a> {
    let member_ptr_name = [name, "ptr"].join("_");
    builder.build_load(
        builder.build_struct_gep(struct_ptr, idx, &member_ptr_name),
        name,
    )
}

pub(super) unsafe fn set_member<'a>(
    context: &'a Context,
    builder: &'a Builder<'a>,
    struct_ptr: PointerValue<'a>,
    idx: u32,
    val: BasicValueEnum<'a>,
    name: &str,
) {
    let member_ptr_name = [name, "ptr"].join("_");
    builder.build_store(
        builder.build_struct_gep(struct_ptr, idx, &member_ptr_name),
        val,
    );
}

pub(super) fn int_ptr_deref_inc<'a>(
    builder: &'a Builder<'a>,
    int_type: IntType<'a>,
    int_ptr: PointerValue<'a>,
    name: &str,
) {
    let old = builder.build_load(int_ptr, name).into_int_value();
    let tmp = builder.build_int_add(old, int_type.const_int(1, false), "tmp");
    builder.build_store(int_ptr, tmp);
}

pub(super) fn int_ptr_deref_dec<'a>(
    builder: &'a Builder<'a>,
    int_type: IntType<'a>,
    int_ptr: PointerValue<'a>,
    name: &str,
) {
    let old = builder.build_load(int_ptr, name).into_int_value();
    let tmp = builder.build_int_sub(old, int_type.const_int(1, false), "tmp");
    builder.build_store(int_ptr, tmp);
}