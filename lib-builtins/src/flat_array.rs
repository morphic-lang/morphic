use crate::core::*;
use crate::rc::RcBoxBuiltin;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicType, BasicTypeEnum, StructType};
use inkwell::values::{FunctionValue, InstructionOpcode};
use inkwell::{AddressSpace, IntPredicate};

// TODO: make sure retains/releases are correct

const DATA_IDX: u32 = 0; // has type T*
const CAP_IDX: u32 = 1; // has type u64
const LEN_IDX: u32 = 2; // has type u64

const HOLE_IDX_IDX: u32 = 0; // has type u64
const HOLE_PTR_IDX: u32 = 1; // has type FlatArray<T>*

const ITEM_RET_ITEM_IDX: u32 = 0; // has type T
const ITEM_RET_HOLE_IDX: u32 = 1; // has type HoleArray<T>

const POP_RET_PTR_IDX: u32 = 0; // has type FlatArray<T>*
const POP_RET_ITEM_IDX: u32 = 1; // has type T

#[derive(Clone, Copy, Debug)]
pub struct FlatArrayBuiltin<'a> {
    // related types
    pub inner_type: BasicTypeEnum<'a>,
    pub self_type: RcBoxBuiltin<'a>,
    pub self_hole_type: StructType<'a>,
    pub item_ret_type: StructType<'a>,
    pub pop_ret_type: StructType<'a>,

    // public API
    pub new: FunctionValue<'a>,
    pub item: FunctionValue<'a>,
    pub len: FunctionValue<'a>,
    pub push: FunctionValue<'a>,
    pub pop: FunctionValue<'a>,
    pub replace: FunctionValue<'a>,
    pub retain_hole: FunctionValue<'a>,
    pub release_hole: FunctionValue<'a>,
    // only exists to be passed to RcBoxBuiltin
    drop: FunctionValue<'a>,

    // helper functions
    pub ensure_cap: FunctionValue<'a>,
    pub bounds_check: FunctionValue<'a>,
}

#[derive(Clone, Copy, Debug)]
pub struct FlatArrayIoBuiltin<'a> {
    pub byte_array_type: FlatArrayBuiltin<'a>,
    pub input: FunctionValue<'a>,
    pub output: FunctionValue<'a>,
}

impl<'a> FlatArrayBuiltin<'a> {
    pub fn declare(
        context: &'a Context,
        module: &Module<'a>,
        inner_type: BasicTypeEnum<'a>,
    ) -> Self {
        let void_type = context.void_type();
        let i64_type = context.i64_type();

        let unwrapped_array_type = context.opaque_struct_type("builtin_flat_array");
        let unwrapped_array_ptr_type = unwrapped_array_type.ptr_type(AddressSpace::Generic);

        let rc_box = RcBoxBuiltin::declare(context, module, unwrapped_array_type.into());
        let self_type = rc_box.self_type;
        let self_ptr_type = self_type.ptr_type(AddressSpace::Generic);

        let self_hole_type = context.struct_type(&[i64_type.into(), self_ptr_type.into()], false);
        let item_ret_type = context.struct_type(&[inner_type.into(), self_hole_type.into()], false);
        let pop_ret_type = context.struct_type(&[self_ptr_type.into(), inner_type.into()], false);

        let new = module.add_function(
            "builtin_flat_array_new",
            self_ptr_type.fn_type(&[], false),
            Some(Linkage::Private),
        );

        let item = module.add_function(
            "builtin_flat_array_item",
            item_ret_type.fn_type(&[self_ptr_type.into(), i64_type.into()], false),
            Some(Linkage::Private),
        );

        let len = module.add_function(
            "builtin_flat_array_len",
            i64_type.fn_type(&[self_ptr_type.into()], false),
            Some(Linkage::Private),
        );

        let push = module.add_function(
            "builtin_flat_array_push",
            self_ptr_type.fn_type(&[self_ptr_type.into(), inner_type.into()], false),
            Some(Linkage::Private),
        );

        let pop = module.add_function(
            "builtin_flat_array_pop",
            pop_ret_type.fn_type(&[self_ptr_type.into()], false),
            Some(Linkage::Private),
        );

        let replace = module.add_function(
            "builtin_flat_array_replace",
            self_ptr_type.fn_type(&[self_hole_type.into(), inner_type.into()], false),
            Some(Linkage::Private),
        );

        let retain_hole = module.add_function(
            "builtin_flat_array_retain_hole",
            void_type.fn_type(&[self_hole_type.into()], false),
            Some(Linkage::Private),
        );

        let release_hole = module.add_function(
            "builtin_flat_array_release_hole",
            void_type.fn_type(&[self_hole_type.into()], false),
            Some(Linkage::Private),
        );

        // opearates on a raw FlatArray (not an RcBoxFlatArray)
        let drop = module.add_function(
            "builtin_flat_array_drop",
            void_type.fn_type(&[unwrapped_array_ptr_type.into()], false),
            Some(Linkage::Private),
        );

        let ensure_cap = module.add_function(
            "builtin_flat_array_ensure_cap",
            void_type.fn_type(&[self_ptr_type.into(), i64_type.into()], false),
            Some(Linkage::Private),
        );

        let bounds_check = module.add_function(
            "builtin_flat_array_bounds_check",
            void_type.fn_type(&[self_ptr_type.into(), i64_type.into()], false),
            Some(Linkage::Private),
        );

        Self {
            inner_type,
            self_type: rc_box,
            self_hole_type,
            item_ret_type,
            pop_ret_type,
            new,
            item,
            len,
            push,
            pop,
            replace,
            retain_hole,
            release_hole,
            drop,
            ensure_cap,
            bounds_check,
        }
    }

    pub fn define(
        &self,
        context: &'a Context,
        libc: &LibC<'a>,
        inner_retain: Option<FunctionValue<'a>>,
        inner_drop: Option<FunctionValue<'a>>,
    ) {
        let i64_type = context.i64_type();

        let inner_ptr_type = self.inner_type.ptr_type(AddressSpace::Generic);
        self.self_type.inner_type.into_struct_type().set_body(
            &[inner_ptr_type.into(), i64_type.into(), i64_type.into()],
            false,
        );
        self.self_type.define(context, libc, Some(self.drop));

        self.define_new(context);
        self.define_item(context, inner_retain);
        self.define_len(context);
        self.define_push(context);
        self.define_pop(context);
        self.define_replace(context, inner_drop);
        self.define_retain_hole(context);
        self.define_release_hole(context);
        self.define_drop(context, libc, inner_drop);
        self.define_ensure_cap(context, libc);
        self.define_bounds_check(context, libc);
    }

    fn define_new(&self, context: &'a Context) {
        let i64_type = context.i64_type();
        let inner_ptr_type = self.inner_type.ptr_type(AddressSpace::Generic);

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.new, "entry");

        builder.position_at_end(&entry);

        let mut new_inner = self.self_type.inner_type.into_struct_type().get_undef();
        new_inner = builder
            .build_insert_value(
                new_inner,
                inner_ptr_type.const_null(),
                DATA_IDX,
                "new_inner",
            )
            .unwrap()
            .into_struct_value();
        new_inner = builder
            .build_insert_value(
                new_inner,
                i64_type.const_int(0, false),
                CAP_IDX,
                "new_inner",
            )
            .unwrap()
            .into_struct_value();
        new_inner = builder
            .build_insert_value(
                new_inner,
                i64_type.const_int(0, false),
                LEN_IDX,
                "new_inner",
            )
            .unwrap()
            .into_struct_value();

        let new = builder
            .build_call(self.self_type.new, &[new_inner.into()], "new_inner")
            .try_as_basic_value()
            .left()
            .unwrap();
        builder.build_return(Some(&new));
    }

    fn define_item(&self, context: &'a Context, inner_retain: Option<FunctionValue<'a>>) {
        let rc_ptr = self.item.get_nth_param(0).unwrap().into_pointer_value();
        let idx = self.item.get_nth_param(1).unwrap().into_int_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.item, "entry");

        builder.position_at_end(&entry);
        let ptr = builder
            .build_call(self.self_type.get, &[rc_ptr.into()], "ptr")
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value();
        let data = unsafe { get_member(&builder, ptr, DATA_IDX, "data") }.into_pointer_value();
        let item_src = unsafe { builder.build_in_bounds_gep(data, &[idx], "item_src") };

        builder.build_call(self.self_type.retain, &[rc_ptr.into()], "");
        if let Some(actual_retain) = inner_retain {
            builder.build_call(actual_retain, &[item_src.into()], "");
        }

        let item = builder.build_load(item_src, "item");

        let mut hole = self.self_hole_type.get_undef();
        hole = builder
            .build_insert_value(hole, idx, HOLE_IDX_IDX, "idx")
            .unwrap()
            .into_struct_value();
        hole = builder
            .build_insert_value(hole, rc_ptr, HOLE_PTR_IDX, "ptr")
            .unwrap()
            .into_struct_value();

        let mut ret = self.item_ret_type.get_undef();
        ret = builder
            .build_insert_value(ret, hole, ITEM_RET_HOLE_IDX, "hole")
            .unwrap()
            .into_struct_value();
        ret = builder
            .build_insert_value(ret, item, ITEM_RET_ITEM_IDX, "item")
            .unwrap()
            .into_struct_value();

        builder.build_return(Some(&ret));
    }

    fn define_len(&self, context: &'a Context) {
        let rc_ptr = self.len.get_nth_param(0).unwrap().into_pointer_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.len, "entry");

        builder.position_at_end(&entry);
        let ptr = builder
            .build_call(self.self_type.get, &[rc_ptr.into()], "ptr")
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value();
        let len = unsafe { get_member(&builder, ptr, LEN_IDX, "len") };
        builder.build_return(Some(&len));
    }

    fn define_push(&self, context: &'a Context) {
        let i64_type = context.i64_type();
        let rc_ptr = self.push.get_nth_param(0).unwrap();
        let item = self.push.get_nth_param(1).unwrap();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.push, "entry");

        builder.position_at_end(&entry);
        let ptr = builder
            .build_call(self.self_type.get, &[rc_ptr], "ptr")
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value();

        let len_ptr = unsafe { builder.build_struct_gep(ptr, LEN_IDX, "len_ptr") };
        let len = builder.build_load(len_ptr, "len").into_int_value();
        let len_new = builder.build_int_add(len, i64_type.const_int(1, false), "len_new");

        builder.build_call(self.ensure_cap, &[rc_ptr, len_new.into()], "");
        builder.build_store(len_ptr, len_new);

        let data = unsafe { get_member(&builder, ptr, DATA_IDX, "data") }.into_pointer_value();
        let item_dest = unsafe { builder.build_in_bounds_gep(data, &[len.into()], "item_dest") };
        builder.build_store(item_dest, item);

        builder.build_return(Some(&rc_ptr));
    }

    fn define_pop(&self, context: &'a Context) {
        let i64_type = context.i64_type();
        let rc_ptr = self.pop.get_nth_param(0).unwrap();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.pop, "entry");

        builder.position_at_end(&entry);
        let ptr = builder
            .build_call(self.self_type.get, &[rc_ptr], "ptr")
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value();
        let len_ptr = unsafe { builder.build_struct_gep(ptr, LEN_IDX, "len_ptr") };
        let len = builder.build_load(len_ptr, "len").into_int_value();

        let len_new = builder.build_int_sub(len, i64_type.const_int(1, false), "len_new");
        builder.build_store(len_ptr, len_new);

        let data = unsafe { get_member(&builder, ptr, DATA_IDX, "data") }.into_pointer_value();
        let item_src = unsafe { builder.build_in_bounds_gep(data, &[len_new], "item_src") };
        let item = builder.build_load(item_src, "item");

        let mut ret = self.pop_ret_type.get_undef();
        ret = builder
            .build_insert_value(ret, rc_ptr, POP_RET_PTR_IDX, "rc_ptr")
            .unwrap()
            .into_struct_value();
        ret = builder
            .build_insert_value(ret, item, POP_RET_ITEM_IDX, "item")
            .unwrap()
            .into_struct_value();

        builder.build_return(Some(&ret));
    }

    fn define_replace(&self, context: &'a Context, inner_drop: Option<FunctionValue<'a>>) {
        let hole = self.replace.get_nth_param(0).unwrap().into_struct_value();
        let item = self.replace.get_nth_param(1).unwrap();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.replace, "entry");

        builder.position_at_end(&entry);
        let idx = builder
            .build_extract_value(hole, HOLE_IDX_IDX, "idx")
            .unwrap()
            .into_int_value();
        let rc_ptr = builder
            .build_extract_value(hole, HOLE_PTR_IDX, "rc_ptr")
            .unwrap();
        let array_ptr = builder
            .build_call(self.self_type.get, &[rc_ptr], "array_ptr")
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value();
        let data =
            unsafe { get_member(&builder, array_ptr, DATA_IDX, "data") }.into_pointer_value();
        let item_dest = unsafe { builder.build_in_bounds_gep(data, &[idx], "item_dest") };
        builder.build_store(item_dest, item);

        if let Some(actual_drop) = inner_drop {
            builder.build_call(actual_drop, &[item_dest.into()], "");
        }

        builder.build_return(Some(&rc_ptr));
    }

    fn define_retain_hole(&self, context: &'a Context) {
        let hole = self.retain_hole.get_nth_param(0).unwrap();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.retain_hole, "entry");

        builder.position_at_end(&entry);
        let rc_ptr = builder
            .build_extract_value(hole.into_struct_value(), HOLE_PTR_IDX, "rc_ptr")
            .unwrap();

        builder.build_call(self.self_type.retain, &[rc_ptr], "retain_hole");

        builder.build_return(None);
    }

    fn define_release_hole(&self, context: &'a Context) {
        let hole = self.release_hole.get_nth_param(0).unwrap();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.release_hole, "entry");

        builder.position_at_end(&entry);
        let rc_ptr = builder
            .build_extract_value(hole.into_struct_value(), HOLE_PTR_IDX, "rc_ptr")
            .unwrap();

        builder.build_call(self.self_type.release, &[rc_ptr], "release_hole");

        builder.build_return(None);
    }

    fn define_drop(
        &self,
        context: &'a Context,
        libc: &LibC<'a>,
        inner_drop: Option<FunctionValue<'a>>,
    ) {
        let i8_type = context.i8_type();
        let i8_ptr_type = i8_type.ptr_type(AddressSpace::Generic);
        let ptr = self.drop.get_nth_param(0).unwrap().into_pointer_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.drop, "entry");

        builder.position_at_end(&entry);
        let data = unsafe { get_member(&builder, ptr, DATA_IDX, "data") }.into_pointer_value();

        if let Some(actual_drop) = inner_drop {
            let len = unsafe { get_member(&builder, ptr, LEN_IDX, "len") }.into_int_value();
            build_for(context, &builder, self.drop, len, |i| {
                let item_src = unsafe { builder.build_in_bounds_gep(data, &[i], "item_src") };
                builder.build_call(actual_drop, &[item_src.into()], "");
            });
        }

        let i8_data = builder.build_bitcast(data, i8_ptr_type, "i8_data");
        builder.build_call(libc.free, &[i8_data.into()], "");
        builder.build_return(None);
    }

    // TODO: handle unit
    fn define_ensure_cap(&self, context: &'a Context, libc: &LibC<'a>) {
        let i32_type = context.i32_type();
        let i64_type = context.i64_type();
        let i8_ptr_type = context.i8_type().ptr_type(AddressSpace::Generic);
        let inner_ptr_type = self.inner_type.ptr_type(AddressSpace::Generic);
        let ptr = self.ensure_cap.get_nth_param(0).unwrap();
        let min_cap = self.ensure_cap.get_nth_param(1).unwrap().into_int_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.ensure_cap, "entry");
        let resize_block = context.append_basic_block(self.ensure_cap, "resize_block");
        let panic_block = context.append_basic_block(self.ensure_cap, "panic_block");
        let success_block = context.append_basic_block(self.ensure_cap, "success_block");
        let exit_block = context.append_basic_block(self.ensure_cap, "exit_block");

        builder.position_at_end(&entry);
        let ptr = builder
            .build_call(self.self_type.get, &[ptr], "")
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value();

        // if this isn't an integer we need to start using floating point multiplication
        let resize_factor = 2;

        let cap_ptr = unsafe { builder.build_struct_gep(ptr, CAP_IDX, "cap_ptr") };
        let cap = builder.build_load(cap_ptr, "cap").into_int_value();
        let should_resize =
            builder.build_int_compare(IntPredicate::ULT, cap, min_cap, "should_resize");
        builder.build_conditional_branch(should_resize, &resize_block, &exit_block);

        builder.position_at_end(&resize_block);

        let candidate_cap = builder.build_int_mul(
            cap,
            i64_type.const_int(resize_factor, false),
            "candidate_cap",
        );

        let use_candidate_cap = builder.build_int_compare(
            IntPredicate::UGE,
            candidate_cap,
            min_cap,
            "use_candidate_cap",
        );

        let cap_new = build_ternary(
            context,
            &builder,
            self.ensure_cap,
            use_candidate_cap,
            || candidate_cap.into(),
            || min_cap.into(),
        )
        .into_int_value();

        let allocation_size = builder.build_int_mul(
            cap_new,
            size_of(self.inner_type).unwrap(),
            "allocation_size",
        );

        let data_ptr = unsafe { builder.build_struct_gep(ptr, DATA_IDX, "data_ptr") };
        let data = builder.build_load(data_ptr, "data");
        let data_i8 = builder.build_cast(InstructionOpcode::BitCast, data, i8_ptr_type, "data_i8");
        let data_new_i8 = builder
            .build_call(
                libc.realloc,
                &[data_i8.into(), allocation_size.into()],
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
        builder.build_unreachable();

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
        let ptr = self.bounds_check.get_nth_param(0).unwrap();
        let idx = self.bounds_check.get_nth_param(1).unwrap().into_int_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.bounds_check, "entry");

        builder.position_at_end(&entry);
        let ptr = builder
            .build_call(self.self_type.get, &[ptr], "ptr")
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value();
        let len = unsafe { get_member(&builder, ptr, LEN_IDX, "len") }.into_int_value();
        let out_of_bounds = builder.build_int_compare(IntPredicate::UGE, idx, len, "out_of_bounds");
        build_if(context, &builder, self.bounds_check, out_of_bounds, || {
            builder.build_call(libc.exit, &[i32_type.const_int(1, false).into()], "");
        });

        builder.build_return(None);
    }
}

impl<'a> FlatArrayIoBuiltin<'a> {
    pub fn define(&self, context: &'a Context, libc: &LibC<'a>) {
        self.define_input(context, libc);
        self.define_output(context, libc);
    }

    pub fn declare(
        context: &'a Context,
        module: &Module<'a>,
        byte_array_type: FlatArrayBuiltin<'a>,
    ) -> Self {
        let void_type = context.void_type();

        let self_ptr_type = byte_array_type
            .self_type
            .self_type
            .ptr_type(AddressSpace::Generic);

        let input = module.add_function(
            "builtin_flat_array_input",
            self_ptr_type.fn_type(&[], false),
            Some(Linkage::Private),
        );

        let output = module.add_function(
            "builtin_flat_array_output",
            void_type.fn_type(&[self_ptr_type.into()], false),
            Some(Linkage::Private),
        );

        Self {
            byte_array_type,
            input,
            output,
        }
    }

    fn define_input(&self, context: &'a Context, libc: &LibC<'a>) {
        let builder = context.create_builder();
        let entry_block = context.append_basic_block(self.input, "entry");
        let loop_block = context.append_basic_block(self.input, "loop");
        let append_block = context.append_basic_block(self.input, "append");
        let exit_block = context.append_basic_block(self.input, "exit");

        builder.position_at_end(&entry_block);

        let stdout_value = builder.build_load(libc.stdout.as_pointer_value(), "stdout_value");
        builder.build_call(libc.fflush, &[stdout_value], "fflush");

        let array = builder
            .build_call(self.byte_array_type.new, &[], "input_array")
            .try_as_basic_value()
            .left()
            .unwrap();

        builder.build_unconditional_branch(&loop_block);

        builder.position_at_end(&loop_block);

        let getchar_result = builder
            .build_call(libc.getchar, &[], "char")
            .try_as_basic_value()
            .left()
            .unwrap();
        let eof_value = context.i32_type().const_int(0xff_ff_ff_ff, false);
        let new_line = context.i32_type().const_int('\n' as u64, false);
        builder.build_switch(
            getchar_result.into_int_value(),
            &append_block,
            &[(eof_value, &exit_block), (new_line, &exit_block)],
        );

        builder.position_at_end(&append_block);
        let input_byte = builder.build_int_truncate(
            getchar_result.into_int_value(),
            context.i8_type(),
            "input_byte",
        );
        builder.build_call(
            self.byte_array_type.push,
            &[array, input_byte.into()],
            "push_call",
        );
        builder.build_unconditional_branch(&loop_block);

        builder.position_at_end(&exit_block);
        builder.build_return(Some(&array));
    }

    fn define_output(&self, context: &'a Context, libc: &LibC<'a>) {
        let i64_type = context.i64_type();
        let rc_ptr = self.output.get_nth_param(0).unwrap();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.output, "entry");

        builder.position_at_end(&entry);
        let ptr = builder
            .build_call(self.byte_array_type.self_type.get, &[rc_ptr], "ptr")
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value();
        let len_ptr = unsafe { builder.build_struct_gep(ptr, LEN_IDX, "len_ptr") };
        let len = builder.build_load(len_ptr, "len");

        let data = unsafe { get_member(&builder, ptr, DATA_IDX, "data") };

        let stdout_value = builder.build_load(libc.stdout.as_pointer_value(), "stdout_value");

        // TODO: check bytes_written for errors
        let _bytes_written = builder.build_call(
            libc.fwrite,
            &[data, i64_type.const_int(1, false).into(), len, stdout_value],
            "bytes_written",
        );

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
        better_panic::install();

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
            Some(Linkage::Private),
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
        flat_array.define(&context, &libc, None, Some(dummy));

        module
            .print_to_file(Path::new("test_flat_array.out.ll"))
            .unwrap();
        module.verify().unwrap();
    }

    #[test]
    fn well_formed_io() {
        better_panic::install();

        let context = Context::create();
        let module = context.create_module("test");
        let inner_type = context.i8_type();

        let libc = LibC::declare(&context, &module);
        libc.define(&context);

        let flat_array = FlatArrayBuiltin::declare(&context, &module, inner_type.into());
        flat_array.define(&context, &libc, None, None);

        let flat_array_io = FlatArrayIoBuiltin::declare(&context, &module, flat_array);
        flat_array_io.define(&context, &libc);

        module
            .print_to_file(Path::new("test_flat_array_io.out.ll"))
            .unwrap();
        module.verify().unwrap();
    }
}
