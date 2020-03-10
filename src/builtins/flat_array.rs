use crate::builtins::core::*;
use crate::builtins::fountain_pen::scope;
use crate::builtins::rc::RcBoxBuiltin;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicType, BasicTypeEnum, StructType};
use inkwell::values::FunctionValue;
use inkwell::AddressSpace;

// TODO: make sure retains/releases are correct

const F_DATA: u32 = 0; // has type T*
const F_CAP: u32 = 1; // has type u64
const F_LEN: u32 = 2; // has type u64

const HOLE_F_IDX: u32 = 0; // has type u64
const HOLE_F_PTR: u32 = 1; // has type FlatArray<T>*

#[derive(Clone, Copy, Debug)]
pub struct FlatArrayBuiltin<'a> {
    // related types
    pub inner_type: BasicTypeEnum<'a>,
    pub rc_builtin: RcBoxBuiltin<'a>,
    pub rc_type: StructType<'a>,
    pub array_type: StructType<'a>,
    pub hole_array_type: StructType<'a>,

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

        let array_type = context.opaque_struct_type("builtin_flat_array");
        let array_ptr_type = array_type.ptr_type(AddressSpace::Generic);

        let rc_builtin = RcBoxBuiltin::declare(context, module, array_type.into());
        let rc_type = rc_builtin.rc_type;
        let rc_ptr_type = rc_type.ptr_type(AddressSpace::Generic);

        let hole_array_type = context.struct_type(&[i64_type.into(), rc_ptr_type.into()], false);
        let item_ret_type =
            context.struct_type(&[inner_type.into(), hole_array_type.into()], false);
        let pop_ret_type = context.struct_type(&[rc_ptr_type.into(), inner_type.into()], false);

        let new = module.add_function(
            "builtin_flat_array_new",
            rc_ptr_type.fn_type(&[], false),
            Some(Linkage::Internal),
        );

        let item = module.add_function(
            "builtin_flat_array_item",
            item_ret_type.fn_type(&[rc_ptr_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        let len = module.add_function(
            "builtin_flat_array_len",
            i64_type.fn_type(&[rc_ptr_type.into()], false),
            Some(Linkage::Internal),
        );

        let push = module.add_function(
            "builtin_flat_array_push",
            rc_ptr_type.fn_type(&[rc_ptr_type.into(), inner_type.into()], false),
            Some(Linkage::Internal),
        );

        let pop = module.add_function(
            "builtin_flat_array_pop",
            pop_ret_type.fn_type(&[rc_ptr_type.into()], false),
            Some(Linkage::Internal),
        );

        let replace = module.add_function(
            "builtin_flat_array_replace",
            rc_ptr_type.fn_type(&[hole_array_type.into(), inner_type.into()], false),
            Some(Linkage::Internal),
        );

        let retain_hole = module.add_function(
            "builtin_flat_array_retain_hole",
            void_type.fn_type(&[hole_array_type.into()], false),
            Some(Linkage::Internal),
        );

        let release_hole = module.add_function(
            "builtin_flat_array_release_hole",
            void_type.fn_type(&[hole_array_type.into()], false),
            Some(Linkage::Internal),
        );

        // opearates on a raw FlatArray (not an RcBoxFlatArray)
        let drop = module.add_function(
            "builtin_flat_array_drop",
            void_type.fn_type(&[array_ptr_type.into()], false),
            Some(Linkage::Internal),
        );

        let ensure_cap = module.add_function(
            "builtin_flat_array_ensure_cap",
            void_type.fn_type(&[rc_ptr_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        let bounds_check = module.add_function(
            "builtin_flat_array_bounds_check",
            void_type.fn_type(&[rc_ptr_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        Self {
            rc_builtin,
            inner_type,
            rc_type,
            array_type,
            hole_array_type,
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
        self.array_type.set_body(
            &[inner_ptr_type.into(), i64_type.into(), i64_type.into()],
            false,
        );
        self.rc_builtin.define(context, libc, Some(self.drop));

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
        let s = scope(self.new, context);
        let me = s.make_struct(
            self.array_type,
            &[
                (F_DATA, s.null(self.inner_type)),
                (F_CAP, s.i64(0)),
                (F_LEN, s.i64(0)),
            ],
        );
        s.ret(s.call(self.rc_builtin.new, &[me]));
    }

    fn define_item(&self, context: &'a Context, inner_retain: Option<FunctionValue<'a>>) {
        let s = scope(self.item, context);
        let rc = s.arg(0);
        let idx = s.arg(1);
        let me = s.call(self.rc_builtin.get, &[rc]);

        s.call_void(self.bounds_check, &[rc, idx]);
        let data = s.arrow(me, F_DATA);

        s.call_void(self.rc_builtin.retain, &[rc]);
        if let Some(actual_retain) = inner_retain {
            s.call_void(actual_retain, &[s.buf_addr(data, idx)]);
        }

        s.ret(s.make_tup(&[
            s.buf_get(data, idx),
            s.make_struct(self.hole_array_type, &[(HOLE_F_IDX, idx), (HOLE_F_PTR, rc)]),
        ]));
    }

    fn define_len(&self, context: &'a Context) {
        let s = scope(self.len, context);
        s.ret(s.arrow(s.call(self.rc_builtin.get, &[s.arg(0)]), F_LEN))
    }

    fn define_push(&self, context: &'a Context) {
        let s = scope(self.push, context);

        let rc = s.arg(0);
        let me = s.call(self.rc_builtin.get, &[rc]);
        let old_len = s.arrow(me, F_LEN);
        let new_len = s.add(old_len, s.i64(1));

        s.call_void(self.ensure_cap, &[rc, new_len]);
        s.arrow_set(me, F_LEN, new_len);
        s.buf_set(s.arrow(me, F_DATA), old_len, s.arg(1));

        s.ret(rc);
    }

    fn define_pop(&self, context: &'a Context) {
        let s = scope(self.pop, context);
        let rc = s.arg(0);
        let me = s.call(self.rc_builtin.get, &[rc]);

        s.call_void(self.bounds_check, &[rc, s.i64(0)]);
        let len = s.arrow(me, F_LEN);
        let new_len = s.sub(len, s.i64(1));

        let item = s.buf_get(s.arrow(me, F_DATA), new_len);
        s.ret(s.make_tup(&[rc, item]))
    }

    fn define_replace(&self, context: &'a Context, inner_drop: Option<FunctionValue<'a>>) {
        let s = scope(self.replace, context);

        let hole = s.arg(0);
        let item = s.arg(1);
        let idx = s.field(hole, HOLE_F_IDX);
        let rc = s.field(hole, HOLE_F_PTR);
        let me = s.call(self.rc_builtin.get, &[rc]);

        if let Some(actual_drop) = inner_drop {
            s.call_void(actual_drop, &[s.buf_addr(s.arrow(me, F_DATA), idx)]);
        }

        s.buf_set(s.arrow(me, F_DATA), idx, item);

        s.ret(rc);
    }

    fn define_retain_hole(&self, context: &'a Context) {
        let s = scope(self.retain_hole, context);
        let hole = s.arg(0);

        s.call_void(self.rc_builtin.retain, &[s.field(hole, HOLE_F_PTR)]);
        s.ret_void();
    }

    fn define_release_hole(&self, context: &'a Context) {
        let s = scope(self.release_hole, context);
        let hole = s.arg(0);

        s.call_void(self.rc_builtin.release, &[s.field(hole, HOLE_F_PTR)]);
        s.ret_void();
    }

    fn define_drop(
        &self,
        context: &'a Context,
        libc: &LibC<'a>,
        inner_drop: Option<FunctionValue<'a>>,
    ) {
        let s = scope(self.drop, context);
        let me = s.arg(0);
        let data = s.arrow(me, F_DATA);

        if let Some(actual_drop) = inner_drop {
            s.for_(s.arrow(me, F_LEN), |s, i| {
                s.call_void(actual_drop, &[s.buf_addr(data, i)]);
            });
        }

        s.call_void(libc.free, &[s.ptr_cast(s.i8_t(), data)]);
        s.ret_void();
    }

    // TODO: handle unit
    fn define_ensure_cap(&self, context: &'a Context, libc: &LibC<'a>) {
        let s = scope(self.ensure_cap, context);
        let me = s.call(self.rc_builtin.get, &[s.arg(0)]);

        let min_cap = s.arg(1);
        let curr_cap = s.arrow(me, F_CAP);
        let should_resize = s.ult(curr_cap, min_cap);

        s.if_(should_resize, |s| {
            let candidate_cap = s.mul(curr_cap, s.i64(2));
            let use_candidate_cap = s.uge(candidate_cap, min_cap);
            let new_cap = s.ternary(use_candidate_cap, candidate_cap, min_cap);

            let alloc_size = s.mul(s.size(self.inner_type), new_cap);
            let new_data = s.ptr_cast(
                self.inner_type,
                s.call(
                    libc.realloc,
                    &[s.ptr_cast(s.i8_t(), s.arrow(me, F_DATA)), alloc_size],
                ),
            );

            s.if_(s.is_null(new_data), |s| {
                s.panic(
                    "ensure_capacity: failed to allocate %zu bytes\n",
                    &[alloc_size],
                    libc,
                );
            });
            s.arrow_set(me, F_DATA, new_data);
            s.arrow_set(me, F_CAP, new_cap);
        });

        s.ret_void();
    }

    fn define_bounds_check(&self, context: &'a Context, libc: &LibC<'a>) {
        let s = scope(self.bounds_check, context);
        let me = s.call(self.rc_builtin.get, &[s.arg(0)]);
        let idx = s.arg(1);

        let len = s.arrow(me, F_LEN);
        let out_of_bounds = s.uge(idx, len);

        s.if_(out_of_bounds, |s| {
            let error_str =
                "index out of bounds: attempt to access item %lld of array with length %llu\n";
            s.panic(error_str, &[idx, len], libc);
        });

        s.ret_void();
    }
}

impl<'a> FlatArrayIoBuiltin<'a> {
    pub fn declare(
        context: &'a Context,
        module: &Module<'a>,
        byte_array_type: FlatArrayBuiltin<'a>,
    ) -> Self {
        let void_type = context.void_type();

        let rc_ptr_type = byte_array_type.rc_type.ptr_type(AddressSpace::Generic);

        let input = module.add_function(
            "builtin_flat_array_input",
            rc_ptr_type.fn_type(&[], false),
            Some(Linkage::Internal),
        );

        let output = module.add_function(
            "builtin_flat_array_output",
            void_type.fn_type(&[rc_ptr_type.into()], false),
            Some(Linkage::Internal),
        );

        Self {
            byte_array_type,
            input,
            output,
        }
    }

    pub fn define(&self, context: &'a Context, libc: &LibC<'a>) {
        self.define_input(context, libc);
        self.define_output(context, libc);
    }

    fn define_input(&self, context: &'a Context, libc: &LibC<'a>) {
        let s = scope(self.input, context);

        s.call(libc.fflush, &[s.ptr_get(libc.stdout)]);
        let array = s.call(self.byte_array_type.new, &[]);

        let getchar_result = s.alloca(s.i32_t());
        s.while_(
            |s| {
                let getchar_result_value = s.call(libc.getchar, &[]);
                s.ptr_set(getchar_result, getchar_result_value);
                s.not(s.or(
                    s.eq(getchar_result_value, s.i32(-1i32 as u32)), // EOF
                    s.eq(getchar_result_value, s.i32('\n' as u32)),
                ))
            },
            |s| {
                let input_bytes = s.truncate(s.i8_t(), s.ptr_get(getchar_result));
                s.call(self.byte_array_type.push, &[array, input_bytes]);
            },
        );

        s.ret(array);
    }

    fn define_output(&self, context: &'a Context, libc: &LibC<'a>) {
        let s = scope(self.output, context);
        let me = s.call(self.byte_array_type.rc_builtin.get, &[s.arg(0)]);

        let stdout_value = s.ptr_get(libc.stdout);

        // TODO: check bytes_written for errors
        let _bytes_written = s.call(
            libc.fwrite,
            &[
                s.arrow(me, F_DATA),
                s.i64(1),
                s.arrow(me, F_LEN),
                stdout_value,
            ],
        );
        s.ret_void();
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
            Some(Linkage::Internal),
        );

        // define dummy
        let builder = context.create_builder();
        let entry = context.append_basic_block(dummy, "entry");
        builder.position_at_end(entry);
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
