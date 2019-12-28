use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::{BasicValueEnum, PointerValue};
use inkwell::AddressSpace;

unsafe fn get_member<'ctx>(
    context: &'ctx Context,
    builder: &Builder<'ctx>,
    struct_ptr: PointerValue<'ctx>,
    idx: u32,
    name: &str,
) -> BasicValueEnum<'ctx> {
    let int32_type = context.i32_type();
    let member_ptr_name = [name, "ptr"].join("_");
    let member_ptr = builder.build_in_bounds_gep(
        struct_ptr,
        &[
            int32_type.const_int(0, false),
            int32_type.const_int(idx.into(), false),
        ],
        &member_ptr_name,
    );
    builder.build_load(member_ptr, name)
}

pub fn gen_flat_array<'ctx>(
    context: &'ctx Context,
    module: &Module<'ctx>,
    item_type: BasicTypeEnum,
) {
    let builder = context.create_builder();

    let void_type = context.void_type();
    let i64_type = context.i64_type();
    let item_ptr_type = item_type.ptr_type(AddressSpace::Generic);

    // struct flat_array { data: item*, cap: i64, len: i64 }
    let flat_type = context.struct_type(
        &[item_ptr_type.into(), i64_type.into(), i64_type.into()],
        false,
    );
    let flat_ptr_type = flat_type.ptr_type(AddressSpace::Generic);

    // flat_array* -> i64
    let len_type = i64_type.fn_type(&[flat_ptr_type.into()], false);
    let len_fn = module.add_function("flat_len", len_type, Some(Linkage::External));

    let entry = context.append_basic_block(len_fn, "entry");
    builder.position_at_end(&entry);
    let ptr = len_fn.get_nth_param(0).unwrap().into_pointer_value();
    let len = unsafe { get_member(context, &builder, ptr, 2, "len") };
    builder.build_return(Some(&len));

    // flat_array* -> item -> ()
    let push_type = void_type.fn_type(&[flat_ptr_type.into(), item_type], false);

    // flat_array* -> item
    let pop_type = item_type.fn_type(&[flat_ptr_type.into()], false);

    // flat_array* -> ()
    let retain = void_type.fn_type(&[flat_ptr_type.into()], false);

    // flat_array* -> ()
    let release = void_type.fn_type(&[flat_ptr_type.into()], false);
}
