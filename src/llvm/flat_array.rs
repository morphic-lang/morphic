use crate::llvm::common::*;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::{CodeModel, InitializationConfig, RelocMode, Target};
use inkwell::types::{BasicType, BasicTypeEnum, StructType};
use inkwell::values::FunctionValue;
use inkwell::OptimizationLevel;
use inkwell::{AddressSpace, IntPredicate};
use std::path::Path;

const DATA_IDX: u32 = 0;
const CAP_IDX: u32 = 1;
const LEN_IDX: u32 = 2;
const REFCOUNT_IDX: u32 = 3;

#[derive(Clone, Copy, Debug)]
struct LibFlatArray<'a> {
    // public API
    new: FunctionValue<'a>,
    item: FunctionValue<'a>,
    len: FunctionValue<'a>,
    push: FunctionValue<'a>,
    pop: FunctionValue<'a>,
    replace: FunctionValue<'a>,
    retain: FunctionValue<'a>,
    release: FunctionValue<'a>,

    // helper functions
    ensure_cap: FunctionValue<'a>,
    ensure_in_bounds: FunctionValue<'a>,
}

impl<'a> LibFlatArray<'a> {
    fn declare(
        context: &'a Context,
        module: &Module<'a>,
        item_type: BasicTypeEnum<'a>,
        flat_type: BasicTypeEnum<'a>,
    ) -> Self {
        let void_type = context.void_type();
        let i64_type = context.i64_type();
        let flat_ptr_type = flat_type.ptr_type(AddressSpace::Generic);

        let new = module.add_function(
            "compiler_builtin_flat_array_new",
            flat_ptr_type.fn_type(&[], false),
            Some(Linkage::External),
        );

        // TODO: item signature (this is a placeholder)
        let item = module.add_function(
            "compiler_builtin_flat_array_item",
            void_type.fn_type(&[], false),
            Some(Linkage::External),
        );

        let len = module.add_function(
            "compiler_builtin_flat_array_len",
            i64_type.fn_type(&[flat_ptr_type.into()], false),
            Some(Linkage::External),
        );

        let push = module.add_function(
            "compiler_builtin_flat_array_push",
            void_type.fn_type(&[flat_ptr_type.into(), item_type], false),
            Some(Linkage::External),
        );

        let pop = module.add_function(
            "compiler_builtin_flat_array_pop",
            item_type.fn_type(&[flat_ptr_type.into()], false),
            Some(Linkage::External),
        );

        let retain = module.add_function(
            "compiler_builtin_flat_array_retain",
            void_type.fn_type(&[flat_ptr_type.into()], false),
            Some(Linkage::External),
        );

        let release = module.add_function(
            "compiler_builtin_flat_array_release",
            void_type.fn_type(&[flat_ptr_type.into()], false),
            Some(Linkage::External),
        );

        let replace = module.add_function(
            "compiler_builtin_flat_array_replace",
            flat_ptr_type.fn_type(&[flat_ptr_type.into(), item_type.into()], false),
            Some(Linkage::External),
        );

        let ensure_cap = module.add_function(
            "compiler_builtin_flat_array_ensure_cap",
            void_type.fn_type(&[flat_ptr_type.into()], false),
            Some(Linkage::External),
        );

        let ensure_in_bounds = module.add_function(
            "compiler_builtin_flat_array_ensure_in_bounds",
            void_type.fn_type(&[flat_ptr_type.into(), i64_type.into()], false),
            Some(Linkage::External),
        );

        Self {
            new,
            item,
            len,
            push,
            pop,
            replace,
            retain,
            release,

            ensure_cap,
            ensure_in_bounds,
        }
    }
}

// ********************************************************************
// struct flat_array { data: item*, cap: u64, len: u64, refcount: u64 }
// ********************************************************************
pub fn gen_flat_array<'a>(
    context: &'a Context,
    module: &Module<'a>,
    libc: LibC<'a>,
    item_type: BasicTypeEnum<'a>,
) {
    let i64_type = context.i64_type();
    let item_ptr_type = item_type.ptr_type(AddressSpace::Generic);

    let flat_type = context.opaque_struct_type("compiler_builtin_flat_array");
    flat_type.set_body(
        &[
            item_ptr_type.into(),
            i64_type.into(),
            i64_type.into(),
            i64_type.into(),
        ],
        false,
    );

    let lib_flat = LibFlatArray::declare(context, module, item_type, flat_type.into());

    gen_new(context, module, libc, lib_flat, item_type, flat_type.into());
    gen_item(context, module, libc, lib_flat, item_type, flat_type.into());
    gen_len(context, module, libc, lib_flat, item_type, flat_type.into());
    gen_push(context, module, libc, lib_flat, item_type, flat_type.into());
    gen_pop(context, module, libc, lib_flat, item_type, flat_type.into());
    gen_replace(context, module, libc, lib_flat, item_type, flat_type.into());
    gen_retain(context, module, libc, lib_flat, item_type, flat_type.into());
    gen_release(context, module, libc, lib_flat, item_type, flat_type.into());

    gen_ensure_cap(context, module, libc, lib_flat, item_type, flat_type.into());
    gen_ensure_in_bounds(context, module, libc, lib_flat, item_type, flat_type.into());
}

// ****************************************************
// compiler_builtin_flat_array_new :: () -> flat_array*
// ****************************************************
fn gen_new<'a>(
    context: &'a Context,
    module: &Module<'a>,
    libc: LibC<'a>,
    lib_flat: LibFlatArray<'a>,
    item_type: BasicTypeEnum<'a>,
    flat_type: StructType<'a>,
) {
    let builder = context.create_builder();
    let i64_type = context.i64_type();
    let i32_type = context.i32_type();

    let init_cap = i32_type.const_int(8, false);

    let entry = context.append_basic_block(lib_flat.new, "entry");
    builder.position_at_end(&entry);
    let new_data = builder.build_array_malloc(item_type, init_cap, "new_data");
    let array_ptr = builder.build_malloc(flat_type, "array_ptr");
    unsafe {
        set_member(
            context,
            &builder,
            array_ptr,
            DATA_IDX,
            new_data.into(),
            "data",
        )
    };
    unsafe {
        set_member(
            context,
            &builder,
            array_ptr,
            CAP_IDX,
            init_cap.into(),
            "cap",
        )
    };
    unsafe {
        set_member(
            context,
            &builder,
            array_ptr,
            LEN_IDX,
            i64_type.const_int(0, false).into(),
            "len",
        )
    };
    unsafe {
        set_member(
            context,
            &builder,
            array_ptr,
            REFCOUNT_IDX,
            i64_type.const_int(1, false).into(),
            "refcount",
        )
    };
    builder.build_return(Some(&array_ptr));
}

// **********************************************************************************
// compiler_builtin_flat_array_item :: flat_array* -> u64 -> (flat_array*, item_type)
// **********************************************************************************
fn gen_item<'a>(
    context: &'a Context,
    module: &Module<'a>,
    libc: LibC<'a>,
    lib_flat: LibFlatArray<'a>,
    item_type: BasicTypeEnum<'a>,
    struct_type: StructType<'a>,
) {
    // TODO
}

// *****************************************************
// compiler_builtin_flat_array_len :: flat_array* -> u64
// *****************************************************
fn gen_len<'a>(
    context: &'a Context,
    _module: &Module<'a>,
    _libc: LibC<'a>,
    lib_flat: LibFlatArray<'a>,
    _item_type: BasicTypeEnum<'a>,
    _flat_type: StructType<'a>,
) {
    let builder = context.create_builder();

    let entry = context.append_basic_block(lib_flat.len, "entry");
    builder.position_at_end(&entry);
    let ptr = lib_flat.len.get_nth_param(0).unwrap().into_pointer_value();
    let len = unsafe { get_member(context, &builder, ptr, LEN_IDX, "len") };
    builder.build_return(Some(&len));
}

// *************************************************************
// compiler_builtin_flat_array_push :: flat_array* -> item -> ()
// *************************************************************
fn gen_push<'a>(
    context: &'a Context,
    _module: &Module<'a>,
    _libc: LibC<'a>,
    lib_flat: LibFlatArray<'a>,
    _item_type: BasicTypeEnum<'a>,
    _flat_type: StructType<'a>,
) {
    let builder = context.create_builder();
    let i64_type = context.i64_type();

    let entry = context.append_basic_block(lib_flat.push, "entry");
    builder.position_at_end(&entry);
    let ptr = lib_flat.push.get_nth_param(0).unwrap().into_pointer_value();
    let item = lib_flat.push.get_nth_param(1).unwrap();

    builder.build_call(lib_flat.ensure_cap, &[ptr.into()], "");
    let len_ptr = unsafe { builder.build_struct_gep(ptr, LEN_IDX, "len_ptr") };
    let len_old = builder.build_load(len_ptr, "len_old").into_int_value();
    let data = unsafe { get_member(context, &builder, ptr, DATA_IDX, "data") }.into_pointer_value();
    let dest = unsafe { builder.build_in_bounds_gep(data, &[len_old.into()], "dest") };
    builder.build_store(dest, item);
    let len_new = builder.build_int_add(len_old, i64_type.const_int(1, false), "len_new");
    builder.build_store(len_ptr, len_new);
    builder.build_return(None);
}

// ******************************************************
// compiler_builtin_flat_array_pop :: flat_array* -> item
// ******************************************************
fn gen_pop<'a>(
    context: &'a Context,
    _module: &Module<'a>,
    _libc: LibC<'a>,
    lib_flat: LibFlatArray<'a>,
    _item_type: BasicTypeEnum<'a>,
    _flat_type: StructType<'a>,
) {
    let builder = context.create_builder();
    let i64_type = context.i64_type();

    let entry = context.append_basic_block(lib_flat.pop, "entry");
    builder.position_at_end(&entry);
    let ptr = lib_flat.pop.get_nth_param(0).unwrap().into_pointer_value();

    let len_ptr = unsafe { builder.build_struct_gep(ptr, LEN_IDX, "len_ptr") };
    let len_old = builder.build_load(len_ptr, "len_old").into_int_value();
    let len_new = builder.build_int_sub(len_old, i64_type.const_int(1, false), "len_new");
    let data = unsafe { get_member(context, &builder, ptr, DATA_IDX, "data") }.into_pointer_value();
    let src = unsafe { builder.build_in_bounds_gep(data, &[len_new], "src") };
    let item = builder.build_load(src, "item");
    builder.build_store(len_ptr, len_new);
    builder.build_return(Some(&item));
}

// ******************************************************************************
// compiler_builtin_flat_array_replace :: flat_array* -> item_type -> flat_array*
// ******************************************************************************
fn gen_replace<'a>(
    context: &'a Context,
    module: &Module<'a>,
    libc: LibC<'a>,
    lib_flat: LibFlatArray<'a>,
    item_type: BasicTypeEnum<'a>,
    flat_type: StructType<'a>,
) {
    // TODO
    // let builder = context.create_builder();

    // let entry = context.append_basic_block(lib_flat.replace, "entry");
    // builder.position_at_end(&entry);
    // let ptr = lib_flat
    //     .replace
    //     .get_nth_param(0)
    //     .unwrap()
    //     .into_pointer_value();
    // let item = lib_flat.replace.get_nth_param(1).unwrap();
}

// *******************************************************
// compiler_builtin_flat_array_retain :: flat_array* -> ()
// *******************************************************
fn gen_retain<'a>(
    context: &'a Context,
    module: &Module<'a>,
    libc: LibC<'a>,
    lib_flat: LibFlatArray<'a>,
    item_type: BasicTypeEnum<'a>,
    flat_type: StructType<'a>,
) {
    let builder = context.create_builder();
    let i64_type = context.i64_type();

    let entry = context.append_basic_block(lib_flat.retain, "entry");
    builder.position_at_end(&entry);
    let ptr = lib_flat
        .retain
        .get_nth_param(0)
        .unwrap()
        .into_pointer_value();

    let refcount_ptr = unsafe { builder.build_struct_gep(ptr, REFCOUNT_IDX, "refcount_ptr") };
    let refcount = builder
        .build_load(refcount_ptr, "refcount")
        .into_int_value();
    let tmp = builder.build_int_add(refcount, i64_type.const_int(1, false), "tmp");
    builder.build_store(refcount_ptr, tmp);
    builder.build_return(None);
}

// *******************************************************
// compiler_builtin_flat_array_retain :: flat_array* -> ()
// *******************************************************
fn gen_release<'a>(
    context: &'a Context,
    module: &Module<'a>,
    libc: LibC<'a>,
    lib_flat: LibFlatArray<'a>,
    item_type: BasicTypeEnum<'a>,
    flat_type: StructType<'a>,
) {
    let builder = context.create_builder();
    let i64_type = context.i64_type();

    let entry = context.append_basic_block(lib_flat.release, "entry");
    builder.position_at_end(&entry);
    let ptr = lib_flat
        .release
        .get_nth_param(0)
        .unwrap()
        .into_pointer_value();

    let refcount_ptr = unsafe { builder.build_struct_gep(ptr, REFCOUNT_IDX, "refcount_ptr") };
    let refcount = builder
        .build_load(refcount_ptr, "refcount")
        .into_int_value();
    let tmp = builder.build_int_sub(refcount, i64_type.const_int(1, false), "tmp");
    builder.build_store(refcount_ptr, tmp);

    let should_drop = builder.build_int_compare(
        IntPredicate::EQ,
        tmp,
        i64_type.const_int(0, false),
        "should_drop",
    );
    let exit = if_(context, &builder, lib_flat.release, should_drop);
    // TODO: drop

    builder.position_at_end(&exit);
    builder.build_return(None);
}

// ************************************************************
// compiler_internal_flat_array_ensure_cap :: flat_array* -> ()
// ************************************************************
fn gen_ensure_cap<'a>(
    context: &'a Context,
    _module: &Module<'a>,
    libc: LibC<'a>,
    lib_flat: LibFlatArray<'a>,
    item_type: BasicTypeEnum<'a>,
    _flat_type: StructType<'a>,
) {
    // if this isn't an integer we need to start using floating point multiplication
    let resize_factor = 2;

    let builder = context.create_builder();
    let i64_type = context.i64_type();
    let i32_type = context.i32_type();

    let entry = context.append_basic_block(lib_flat.ensure_cap, "entry");
    builder.position_at_end(&entry);
    let ptr = lib_flat
        .ensure_cap
        .get_nth_param(0)
        .unwrap()
        .into_pointer_value();

    let len = unsafe { get_member(context, &builder, ptr, LEN_IDX, "len") }.into_int_value();
    let cap = unsafe { get_member(context, &builder, ptr, CAP_IDX, "cap") }.into_int_value();
    let should_resize = builder.build_int_compare(IntPredicate::UGE, len, cap, "should_resize");

    // let exit = if_(context, &builder, lib_flat.ensure_cap, should_resize);
    // let data = unsafe { get_member(context, &builder, ptr, DATA_IDX, "data") }.into_pointer_value();
    // let new_cap = builder.build_int_mul(cap, i64_type.const_int(resize_factor, false), "new_cap");
    // let new_data = builder.build_array_malloc(item_type, new_cap, "new_data");
    // // let is_not_null = builder.build_is_not_null(new_data, "is_not_null");
    // // let is_null = builder.build_not(is_not_null, "is_null");

    // // let success = if_(context, &builder, lib_flat.ensure_cap, is_null);
    // // builder.build_call(libc.exit, &[i32_type.const_int(1, false).into()], "");

    // // builder.position_at_end(&success);
    // unsafe { set_member(context, &builder, ptr, CAP_IDX, new_cap.into(), "cap") };
    // let count = builder.build_int_mul(len, size_of(item_type).unwrap(), "count");
    // builder.build_call(
    //     libc.memcpy,
    //     &[new_data.into(), data.into(), count.into()],
    //     "",
    // );
    // builder.build_free(data);

    // builder.position_at_end(&exit);
    builder.build_return(None);
}

// ***************************************************************
// compiler_builtin_flat_array_in_bounds: flat_array* -> u64 -> ()
// ***************************************************************
fn gen_ensure_in_bounds<'a>(
    context: &'a Context,
    module: &Module<'a>,
    libc: LibC<'a>,
    lib_flat: LibFlatArray<'a>,
    item_type: BasicTypeEnum<'a>,
    flat_type: StructType<'a>,
) {
    let builder = context.create_builder();
    let i32_type = context.i32_type();

    let entry = context.append_basic_block(lib_flat.ensure_in_bounds, "entry");
    builder.position_at_end(&entry);
    let ptr = lib_flat
        .ensure_in_bounds
        .get_nth_param(0)
        .unwrap()
        .into_pointer_value();
    let idx = lib_flat
        .ensure_in_bounds
        .get_nth_param(1)
        .unwrap()
        .into_int_value();

    let len = unsafe { get_member(context, &builder, ptr, LEN_IDX, "len") }.into_int_value();
    let out_of_bounds = builder.build_int_compare(IntPredicate::UGE, idx, len, "out_of_bounds");
    let exit = if_(context, &builder, lib_flat.ensure_in_bounds, out_of_bounds);
    builder.build_call(libc.exit, &[i32_type.const_int(1, false).into()], "");

    builder.position_at_end(&exit);
    builder.build_return(None);
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn well_formed() {
        Target::initialize_all(&InitializationConfig::default());
        let target = Target::from_triple("x86_64-pc-linux-gnu").unwrap();
        let target_machine = target
            .create_target_machine(
                "x86_64-pc-linux-gnu",
                "x86-64",
                "",
                OptimizationLevel::None,
                RelocMode::Default,
                CodeModel::Default,
            )
            .unwrap();

        let context = Context::create();
        let module = context.create_module("test");
        let item_type = context.i32_type();
        let libc = LibC::declare(&context, &module);
        gen_flat_array(&context, &module, libc, item_type.into());

        module
            .print_to_file(Path::new("test_flat_array.ll.out"))
            .unwrap();
        module.verify().unwrap();
    }
}
