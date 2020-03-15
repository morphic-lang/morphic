use crate::builtins::core::*;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::FunctionValue;
use inkwell::{AddressSpace, IntPredicate};

const REFCOUNT_IDX: u32 = 0; // has type u32
const INNER_IDX: u32 = 1; // has type T

#[derive(Clone, Copy, Debug)]
pub struct RcBoxBuiltin<'a> {
    // related types
    pub inner_type: BasicTypeEnum<'a>,
    pub rc_type: BasicTypeEnum<'a>,

    // public API
    pub new: FunctionValue<'a>,
    pub get: FunctionValue<'a>,
    pub retain: FunctionValue<'a>,
    pub release: FunctionValue<'a>,
}

impl<'a> RcBoxBuiltin<'a> {
    pub fn declare(
        context: &'a Context,
        module: &Module<'a>,
        inner_type: BasicTypeEnum<'a>,
    ) -> Self {
        let void_type = context.void_type();
        let inner_ptr_type = inner_type.ptr_type(AddressSpace::Generic);

        let rc_type = context.opaque_struct_type("builtin_rc");
        let rc_ptr_type = rc_type.ptr_type(AddressSpace::Generic);

        let new = module.add_function(
            "builtin_rc_new",
            rc_ptr_type.fn_type(&[inner_type.into()], false),
            Some(Linkage::Internal),
        );

        let get = module.add_function(
            "builtin_rc_get",
            inner_ptr_type.fn_type(&[rc_ptr_type.into()], false),
            Some(Linkage::Internal),
        );

        let retain = module.add_function(
            "builtin_rc_retain",
            void_type.fn_type(&[rc_ptr_type.into()], false),
            Some(Linkage::Internal),
        );

        let release = module.add_function(
            "builtin_rc_release",
            void_type.fn_type(&[rc_ptr_type.into()], false),
            Some(Linkage::Internal),
        );

        Self {
            inner_type,
            rc_type: rc_type.into(),
            new,
            get,
            retain,
            release,
        }
    }

    pub fn define(
        &self,
        context: &'a Context,
        libc: &LibC<'a>,
        inner_drop: Option<FunctionValue<'a>>,
    ) {
        let i32_type = context.i32_type();
        self.rc_type
            .into_struct_type()
            .set_body(&[i32_type.into(), self.inner_type.into()], false);
        self.define_new(context, libc);
        self.define_get(context);
        self.define_retain(context);
        self.define_release(context, libc, inner_drop);
    }

    fn define_new(&self, context: &'a Context, libc: &LibC<'a>) {
        let i32_type = context.i32_type();
        let inner = self.new.get_nth_param(0).unwrap();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.new, "entry");

        builder.position_at_end(entry);

        let i8_new_ptr = builder
            .build_call(
                libc.malloc,
                &[self.rc_type.into_struct_type().size_of().unwrap().into()],
                "i8_new_ptr",
            )
            .try_as_basic_value()
            .left()
            .unwrap();

        let new_ptr = builder
            .build_bitcast(
                i8_new_ptr,
                self.rc_type.ptr_type(AddressSpace::Generic),
                "new_ptr",
            )
            .into_pointer_value();

        unsafe {
            set_member(
                &builder,
                new_ptr,
                REFCOUNT_IDX,
                i32_type.const_int(1, false).into(),
                "refcount",
            );

            set_member(&builder, new_ptr, INNER_IDX, inner, "inner");
        }

        builder.build_return(Some(&new_ptr));
    }

    fn define_get(&self, context: &'a Context) {
        let ptr = self.get.get_nth_param(0).unwrap().into_pointer_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.get, "entry");

        builder.position_at_end(entry);
        let inner = unsafe { builder.build_struct_gep(ptr, INNER_IDX, "inner") };
        builder.build_return(Some(&inner));
    }

    fn define_retain(&self, context: &'a Context) {
        let i32_type = context.i32_type();
        let ptr = self.retain.get_nth_param(0).unwrap().into_pointer_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.retain, "entry");

        builder.position_at_end(entry);
        let refcount_ptr = unsafe { builder.build_struct_gep(ptr, REFCOUNT_IDX, "refcount_ptr") };
        let refcount = builder
            .build_load(refcount_ptr, "refcount")
            .into_int_value();
        let tmp = builder.build_int_add(refcount, i32_type.const_int(1, false), "tmp");
        builder.build_store(refcount_ptr, tmp);
        builder.build_return(None);
    }

    fn define_release(
        &self,
        context: &'a Context,
        libc: &LibC<'a>,
        inner_drop: Option<FunctionValue<'a>>,
    ) {
        let i8_type = context.i8_type();
        let i32_type = context.i32_type();
        let i8_ptr_type = i8_type.ptr_type(AddressSpace::Generic);
        let ptr = self.release.get_nth_param(0).unwrap().into_pointer_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.release, "entry");

        builder.position_at_end(entry);
        let refcount_ptr = unsafe { builder.build_struct_gep(ptr, REFCOUNT_IDX, "refcount_ptr") };
        let refcount = builder
            .build_load(refcount_ptr, "refcount")
            .into_int_value();
        let tmp = builder.build_int_sub(refcount, i32_type.const_int(1, false), "tmp");
        builder.build_store(refcount_ptr, tmp);

        let should_drop = builder.build_int_compare(
            IntPredicate::EQ,
            tmp,
            i32_type.const_int(0, false),
            "should_drop",
        );
        build_if(context, &builder, self.release, should_drop, || {
            if let Some(actual_drop) = inner_drop {
                let inner_ptr = unsafe { builder.build_struct_gep(ptr, INNER_IDX, "inner_ptr") };
                builder.build_call(actual_drop, &[inner_ptr.into()], "");
            }
            let i8_ptr = builder.build_bitcast(ptr, i8_ptr_type, "i8_ptr");
            builder.build_call(libc.free, &[i8_ptr.into()], "");
        });

        builder.build_return(None);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::builtins::test_utils::verify;
    use inkwell::values::BasicValue;

    #[test]
    fn well_formed() {
        let context = Context::create();
        let module = context.create_module("test");
        let inner_type = context.i32_type();
        let inner_ptr_type = inner_type.ptr_type(AddressSpace::Generic);

        let libc = LibC::declare(&context, &module);

        // TODO: deduplicate dummy (also in flat_array.rs)

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

        let rc = RcBoxBuiltin::declare(&context, &module, inner_type.into());
        rc.define(&context, &libc, Some(dummy));

        verify("test_rc.out.ll", &module);
    }
}
