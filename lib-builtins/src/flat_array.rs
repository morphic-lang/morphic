use crate::core::*;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicType, BasicTypeEnum, StructType};
use inkwell::values::{FunctionValue, InstructionOpcode};
use inkwell::{AddressSpace, IntPredicate};

const DATA_IDX: u32 = 0; // has type T*
const CAP_IDX: u32 = 1; // has type u64
const LEN_IDX: u32 = 2; // has type u64

#[derive(Clone, Copy, Debug)]
pub struct FlatArrayBuiltin<'a> {
    // related types
    inner_type: BasicTypeEnum<'a>,
    self_type: StructType<'a>,

    // public API
    new: FunctionValue<'a>,
    item: FunctionValue<'a>,
    len: FunctionValue<'a>,
    push: FunctionValue<'a>,
    pop: FunctionValue<'a>,
    replace: FunctionValue<'a>,
    drop: FunctionValue<'a>,

    // helper functions
    ensure_cap: FunctionValue<'a>,
    bounds_check: FunctionValue<'a>,
}

impl<'a> FlatArrayBuiltin<'a> {
    pub fn declare(
        context: &'a Context,
        module: &Module<'a>,
        inner_type: BasicTypeEnum<'a>,
    ) -> Self {
        let void_type = context.void_type();
        let i64_type = context.i64_type();

        let inner_mangled = mangle_basic(context, inner_type);

        let self_type =
            context.opaque_struct_type(&format!("compiler_builtin_flat_array_{}", inner_mangled));
        let self_ptr_type = self_type.ptr_type(AddressSpace::Generic);

        let new = module.add_function(
            &format!("compiler_builtin_flat_array_{}_new", inner_mangled),
            self_type.fn_type(&[], false),
            Some(Linkage::External),
        );

        // TODO: signature (this is a placeholder)
        let item = module.add_function(
            &format!("compiler_builtin_flat_array_{}_item", inner_mangled),
            void_type.fn_type(&[], false),
            Some(Linkage::External),
        );

        let len = module.add_function(
            &format!("compiler_builtin_flat_array_{}_len", inner_mangled),
            i64_type.fn_type(&[self_ptr_type.into()], false),
            Some(Linkage::External),
        );

        let push = module.add_function(
            &format!("compiler_builtin_flat_array_{}_push", inner_mangled),
            void_type.fn_type(&[self_ptr_type.into(), inner_type.into()], false),
            Some(Linkage::External),
        );

        let pop = module.add_function(
            &format!("compiler_builtin_flat_array_{}_pop", inner_mangled),
            inner_type.fn_type(&[self_ptr_type.into()], false),
            Some(Linkage::External),
        );

        let replace = module.add_function(
            &format!("compiler_builtin_flat_array_{}_replace", inner_mangled),
            self_type.fn_type(&[self_ptr_type.into(), inner_type.into()], false),
            Some(Linkage::External),
        );

        let drop = module.add_function(
            &format!("compiler_builtin_flat_array_{}_drop", inner_mangled),
            void_type.fn_type(&[self_ptr_type.into()], false),
            Some(Linkage::External),
        );

        let ensure_cap = module.add_function(
            &format!("compiler_builtin_flat_array_{}_ensure_cap", inner_mangled),
            void_type.fn_type(&[self_ptr_type.into(), i64_type.into()], false),
            Some(Linkage::External),
        );

        let bounds_check = module.add_function(
            &format!("compiler_builtin_flat_array_{}_bounds_check", inner_mangled),
            void_type.fn_type(&[self_ptr_type.into(), i64_type.into()], false),
            Some(Linkage::External),
        );

        Self {
            inner_type,
            self_type,
            new,
            item,
            len,
            push,
            pop,
            replace,
            drop,
            ensure_cap,
            bounds_check,
        }
    }

    pub fn define(&self, context: &'a Context, libc: &LibC<'a>, _inner_drop: FunctionValue<'a>) {
        let i64_type = context.i64_type();
        let inner_ptr_type = self.inner_type.ptr_type(AddressSpace::Generic);
        self.self_type.set_body(
            &[inner_ptr_type.into(), i64_type.into(), i64_type.into()],
            false,
        );
        self.define_new(context);
        // TODO: define_item
        self.define_len(context);
        self.define_push(context);
        self.define_pop(context);
        // TODO: define_replace
        // TODO: define_drop
        self.define_ensure_cap(context, libc);
        self.define_bounds_check(context, libc);
    }

    fn define_new(&self, context: &'a Context) {
        let i32_type = context.i32_type();
        let i64_type = context.i64_type();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.new, "entry");

        builder.position_at_end(&entry);

        let init_cap = 8;
        // for some reason, LLVM's built in malloc takes an i32 instead of a size_t (i.e. a u64)
        let data =
            builder.build_array_malloc(self.inner_type, i32_type.const_int(init_cap, true), "data");

        let mut new = self.self_type.get_undef();
        new = builder
            .build_insert_value(new, data, DATA_IDX, "tmp0")
            .unwrap()
            .into_struct_value();
        new = builder
            .build_insert_value(new, i64_type.const_int(init_cap, false), CAP_IDX, "tmp1")
            .unwrap()
            .into_struct_value();
        new = builder
            .build_insert_value(new, i64_type.const_int(0, false), LEN_IDX, "tmp2")
            .unwrap()
            .into_struct_value();
        builder.build_return(Some(&new));
    }

    fn define_len(&self, context: &'a Context) {
        let ptr = self.len.get_nth_param(0).unwrap().into_pointer_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.len, "entry");

        builder.position_at_end(&entry);
        let len = unsafe { get_member(&builder, ptr, LEN_IDX, "len") };
        builder.build_return(Some(&len));
    }

    fn define_push(&self, context: &'a Context) {
        let i64_type = context.i64_type();
        let ptr = self.push.get_nth_param(0).unwrap().into_pointer_value();
        let item = self.push.get_nth_param(1).unwrap();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.push, "entry");

        builder.position_at_end(&entry);

        let len_ptr = unsafe { builder.build_struct_gep(ptr, LEN_IDX, "len_ptr") };
        let len = builder.build_load(len_ptr, "len").into_int_value();
        let len_new = builder.build_int_add(len, i64_type.const_int(1, false), "len_new");

        builder.build_call(self.ensure_cap, &[ptr.into(), len_new.into()], "");
        builder.build_store(len_ptr, len_new);

        let data = unsafe { get_member(&builder, ptr, DATA_IDX, "data") }.into_pointer_value();
        let item_dest = unsafe { builder.build_in_bounds_gep(data, &[len.into()], "item_dest") };
        builder.build_store(item_dest, item);

        builder.build_return(None);
    }

    fn define_pop(&self, context: &'a Context) {
        let i64_type = context.i64_type();
        let ptr = self.pop.get_nth_param(0).unwrap().into_pointer_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.pop, "entry");

        builder.position_at_end(&entry);
        let len_ptr = unsafe { builder.build_struct_gep(ptr, LEN_IDX, "len_ptr") };
        let len = builder.build_load(len_ptr, "len").into_int_value();

        let len_new = builder.build_int_sub(len, i64_type.const_int(1, false), "len_new");
        builder.build_store(len_ptr, len_new);

        let data = unsafe { get_member(&builder, ptr, DATA_IDX, "data") }.into_pointer_value();
        let item_src = unsafe { builder.build_in_bounds_gep(data, &[len_new], "item_src") };
        let item = builder.build_load(item_src, "item");

        builder.build_return(Some(&item));
    }

    fn define_ensure_cap(&self, context: &'a Context, libc: &LibC<'a>) {
        let i32_type = context.i32_type();
        let i64_type = context.i64_type();
        let i8_ptr_type = context.i8_type().ptr_type(AddressSpace::Generic);
        let inner_ptr_type = self.inner_type.ptr_type(AddressSpace::Generic);
        let ptr = self
            .ensure_cap
            .get_nth_param(0)
            .unwrap()
            .into_pointer_value();
        let min_cap = self.ensure_cap.get_nth_param(1).unwrap().into_int_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.ensure_cap, "entry");
        let resize_block = context.append_basic_block(self.ensure_cap, "resize_block");
        let panic_block = context.append_basic_block(self.ensure_cap, "panic_block");
        let success_block = context.append_basic_block(self.ensure_cap, "success_block");
        let exit_block = context.append_basic_block(self.ensure_cap, "exit_block");

        builder.position_at_end(&entry);

        // if this isn't an integer we need to start using floating point multiplication
        let resize_factor = 2;

        let cap_ptr = unsafe { builder.build_struct_gep(ptr, CAP_IDX, "cap_ptr") };
        let cap = builder.build_load(cap_ptr, "cap").into_int_value();
        let should_resize =
            builder.build_int_compare(IntPredicate::ULT, cap, min_cap, "should_resize");
        builder.build_conditional_branch(should_resize, &resize_block, &exit_block);

        builder.position_at_end(&resize_block);
        let cap_new =
            builder.build_int_mul(cap, i64_type.const_int(resize_factor, false), "cap_new");

        let data_ptr = unsafe { builder.build_struct_gep(ptr, DATA_IDX, "data_ptr") };
        let data = builder.build_load(data_ptr, "data");
        let data_i8 = builder.build_cast(InstructionOpcode::BitCast, data, i8_ptr_type, "data_i8");
        let data_new_i8 = builder
            .build_call(
                libc.realloc,
                &[data_i8.into(), cap_new.into()],
                "data_new_i8",
            )
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value();

        let is_null = builder.build_is_null(data_new_i8, "is_null");
        builder.build_conditional_branch(is_null, &panic_block, &success_block);

        builder.position_at_end(&panic_block);
        builder.build_call(libc.exit, &[i32_type.const_int(1, true).into()], "");
        builder.build_unconditional_branch(&exit_block); // unreachable

        builder.position_at_end(&success_block);
        let data_new = builder.build_cast(
            InstructionOpcode::BitCast,
            data_new_i8,
            inner_ptr_type,
            "data_new",
        );
        builder.build_store(data_ptr, data_new);
        builder.build_store(cap_ptr, cap_new);
        builder.build_unconditional_branch(&exit_block);

        builder.position_at_end(&exit_block);
        builder.build_return(None);
    }

    fn define_bounds_check(&self, context: &'a Context, libc: &LibC<'a>) {
        let i32_type = context.i32_type();
        let ptr = self
            .bounds_check
            .get_nth_param(0)
            .unwrap()
            .into_pointer_value();
        let idx = self.bounds_check.get_nth_param(1).unwrap().into_int_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.bounds_check, "entry");

        builder.position_at_end(&entry);
        let len = unsafe { get_member(&builder, ptr, LEN_IDX, "len") }.into_int_value();
        let out_of_bounds = builder.build_int_compare(IntPredicate::UGE, idx, len, "out_of_bounds");
        let then_block = if_(context, &builder, self.bounds_check, out_of_bounds);
        builder.build_call(libc.exit, &[i32_type.const_int(1, false).into()], "");

        builder.position_at_end(&then_block);
        builder.build_return(None);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use inkwell::values::BasicValue;
    use std::path::Path;

    #[test]
    fn well_formed() {
        let context = Context::create();
        let module = context.create_module("test");
        let inner_type = context.i32_type();
        let inner_ptr_type = inner_type.ptr_type(AddressSpace::Generic);

        let libc = LibC::declare(&context, &module);

        // TODO: deduplicate dummy (also in rc.rs)

        // declare dummy
        let void_type = context.void_type();
        let dummy = module.add_function(
            "dummy",
            void_type.fn_type(&[inner_ptr_type.into()], false),
            Some(Linkage::External),
        );

        // define dummy
        let builder = context.create_builder();
        let entry = context.append_basic_block(dummy, "entry");
        builder.position_at_end(&entry);
        let hello_global = builder.build_global_string_ptr("Hello, world!", "hello");
        let hello_value = (&hello_global as &dyn BasicValue).as_basic_value_enum();
        builder.build_call(libc.printf, &[hello_value], "");
        builder.build_return(None);

        let flat_array = FlatArrayBuiltin::declare(&context, &module, inner_type.into());
        flat_array.define(&context, &libc, dummy);

        module
            .print_to_file(Path::new("test_flat_array.ll.out"))
            .unwrap();
        module.verify().unwrap();
    }
}