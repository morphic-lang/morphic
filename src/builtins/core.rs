use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue};
use inkwell::IntPredicate;

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

pub(super) fn build_if<'a>(
    context: &'a Context,
    builder: &Builder<'a>,
    func: FunctionValue<'a>,
    cond: IntValue<'a>,
    body: impl FnOnce() -> (),
) {
    let then_block = context.append_basic_block(func, "then_block");
    let next_block = context.append_basic_block(func, "next_block");
    builder.build_conditional_branch(cond, then_block, next_block);
    builder.position_at_end(then_block);

    body();

    builder.build_unconditional_branch(next_block);
    builder.position_at_end(next_block);
}

pub(super) fn build_exiting_if<'a>(
    context: &'a Context,
    builder: &Builder<'a>,
    func: FunctionValue<'a>,
    cond: IntValue<'a>,
    body: impl FnOnce() -> (),
) {
    let then_block = context.append_basic_block(func, "then_block");
    let next_block = context.append_basic_block(func, "next_block");
    builder.build_conditional_branch(cond, then_block, next_block);
    builder.position_at_end(then_block);

    body();

    builder.build_unreachable();
    builder.position_at_end(next_block);
}

pub(super) fn build_ternary<'a>(
    context: &'a Context,
    builder: &Builder<'a>,
    func: FunctionValue<'a>,
    cond: IntValue<'a>,
    then_body: impl FnOnce() -> BasicValueEnum<'a>,
    else_body: impl FnOnce() -> BasicValueEnum<'a>,
) -> BasicValueEnum<'a> {
    let then_block = context.append_basic_block(func, "then_block");
    let else_block = context.append_basic_block(func, "else_block");
    let next_block = context.append_basic_block(func, "next_block");
    builder.build_conditional_branch(cond, then_block, else_block);

    builder.position_at_end(then_block);
    let then_ret = then_body();
    builder.build_unconditional_branch(next_block);

    builder.position_at_end(else_block);
    let else_ret = else_body();
    builder.build_unconditional_branch(next_block);

    builder.position_at_end(next_block);
    let phi = builder.build_phi(then_ret.get_type(), "result");
    phi.add_incoming(&[(&then_ret, then_block), (&else_ret, else_block)]);
    phi.as_basic_value()
}

pub(super) fn build_for<'a>(
    context: &'a Context,
    builder: &Builder<'a>,
    func: FunctionValue<'a>,
    end_for: IntValue<'a>,
    body: impl for<'b> FnOnce(IntValue<'b>) -> (),
) {
    let i64_type = context.i64_type();

    let i_ptr = builder.build_alloca(i64_type, "i_ptr");
    builder.build_store(i_ptr, i64_type.const_int(0, false));

    let for_block = context.append_basic_block(func, "for_block");
    let next_block = context.append_basic_block(func, "next_block");
    builder.build_unconditional_branch(for_block);

    builder.position_at_end(for_block);
    let i_cur = builder.build_load(i_ptr, "i_cur").into_int_value();
    let i_new = builder.build_int_add(i_cur, i64_type.const_int(1, false), "i_new");
    builder.build_store(i_ptr, i_new);

    body(i_cur);

    let done = builder.build_int_compare(IntPredicate::UGE, i_new, end_for, "done");
    builder.build_conditional_branch(done, next_block, for_block);
    builder.position_at_end(next_block);
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
