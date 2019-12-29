use crate::llvm::common::*;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::{AddressSpace, IntPredicate};

pub fn gen_flat_array<'a>(
    context: &'a Context,
    module: &'a Module<'a>,
    libc: LibC<'a>,
    item_type: BasicTypeEnum<'a>,
) {
    // must be an integer unless hopper_internal_flat_array_ensure_cap is
    // modified to use floating point multiplication
    let resize_factor = 2;

    let builder = context.create_builder();
    let void_type = context.void_type();
    let i64_type = context.i64_type();
    let item_ptr_type = item_type.ptr_type(AddressSpace::Generic);

    // *****************************************************
    // struct flat_array { data: item*, cap: u64, len: u64 }
    // *****************************************************

    let flat_type = context.struct_type(
        &[item_ptr_type.into(), i64_type.into(), i64_type.into()],
        false,
    );
    let flat_ptr_type = flat_type.ptr_type(AddressSpace::Generic);

    // for use with get_member and set_member
    let data_idx = 0;
    let cap_idx = 1;
    let len_idx = 2;

    // *************************************************
    // hopper_builtin_flat_array_len: flat_array* -> i64
    // *************************************************

    let len_type = i64_type.fn_type(&[flat_ptr_type.into()], false);
    let len_fn = module.add_function(
        "hopper_builtin_flat_array_len",
        len_type,
        Some(Linkage::External),
    );

    let entry = context.append_basic_block(len_fn, "entry");
    builder.position_at_end(&entry);
    let ptr = len_fn.get_nth_param(0).unwrap().into_pointer_value();
    let len = unsafe { get_member(context, &builder, ptr, 2, "len") };
    builder.build_return(Some(&len));

    // ********************************************************
    // hopper_internal_flat_array_ensure_cap: flat_array* -> ()
    // ********************************************************

    let ensure_cap_type = void_type.fn_type(&[flat_ptr_type.into()], false);
    let ensure_cap_fn = module.add_function(
        "hopper_internal_flat_array_ensure_cap",
        ensure_cap_type,
        Some(Linkage::Private),
    );

    let entry = context.append_basic_block(ensure_cap_fn, "entry");
    builder.position_at_end(&entry);
    let ptr = ensure_cap_fn.get_nth_param(0).unwrap().into_pointer_value();
    let len = unsafe { get_member(context, &builder, ptr, len_idx, "len") }.into_int_value();
    let cap = unsafe { get_member(context, &builder, ptr, cap_idx, "cap") }.into_int_value();

    let should_resize = builder.build_int_compare(IntPredicate::ULT, len, cap, "should_resize");
    let exit = if_(context, &builder, ensure_cap_fn, should_resize);
    let data = unsafe { get_member(context, &builder, ptr, data_idx, "data") }.into_pointer_value();
    let new_cap = builder.build_int_mul(cap, i64_type.const_int(resize_factor, false), "new_cap");

    // TODO: panic if NULL
    let new_data = builder.build_array_malloc(item_type, new_cap, "new_data");
    unsafe {
        set_member(context, &builder, ptr, cap_idx, new_cap.into(), "cap");
    }
    let count = builder.build_int_mul(len, size_of(item_type).unwrap(), "count");
    builder.build_call(
        libc.memcpy,
        &[new_data.into(), data.into(), count.into()],
        "",
    );
    builder.build_free(data);

    builder.position_at_end(&exit);
    builder.build_return(None);

    // *********************************************************
    // hopper_builtin_flat_array_push: flat_array* -> item -> ()
    // *********************************************************

    let push_type = void_type.fn_type(&[flat_ptr_type.into(), item_type], false);
    let push_fn = module.add_function(
        "hopper_builtin_flat_array_push",
        push_type,
        Some(Linkage::External),
    );

    let entry = context.append_basic_block(push_fn, "entry");
    builder.position_at_end(&entry);
    let ptr = push_fn.get_nth_param(0).unwrap().into_pointer_value();
    let item = push_fn.get_nth_param(1).unwrap();
    builder.build_call(ensure_cap_fn, &[ptr.into()], "");

    let len_ptr = unsafe { builder.build_struct_gep(ptr, 2, "len_ptr") };
    int_ptr_deref_inc(&builder, i64_type, len_ptr, "len");
    let data = unsafe { get_member(context, &builder, ptr, data_idx, "data") }.into_pointer_value();
    let dest = unsafe { builder.build_in_bounds_gep(data, &[len], "dest") };
    builder.build_store(dest, item);
    builder.build_return(None);

    // **********************************
    // hopper_builtin_flat_array* -> item
    // **********************************

    let pop_type = item_type.fn_type(&[flat_ptr_type.into()], false);

    // ********************************
    // hopper_builtin_flat_array* -> ()
    // ********************************

    let retain = void_type.fn_type(&[flat_ptr_type.into()], false);

    // ********************************
    // hopper_builtin_flat_array* -> ()
    // ********************************

    let release = void_type.fn_type(&[flat_ptr_type.into()], false);
}
