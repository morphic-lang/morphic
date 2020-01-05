use crate::llvm::common::*;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicTypeEnum, StructType};
use inkwell::values::FunctionValue;
use inkwell::{AddressSpace, IntPredicate};

const REFCOUNT_IDX: u32 = 0; // has type u32
const INNER_IDX: u32 = 1; // has type T

#[derive(Clone, Copy, Debug)]
pub struct RcBuiltin<'a> {
    // related types
    inner_type: BasicTypeEnum<'a>,
    self_type: StructType<'a>,

    // public API
    new: FunctionValue<'a>,
    retain: FunctionValue<'a>,
    release: FunctionValue<'a>,
}

impl<'a> RcBuiltin<'a> {
    pub fn declare(
        context: &'a Context,
        module: &Module<'a>,
        inner_type: BasicTypeEnum<'a>,
    ) -> Self {
        let i32_type = context.i32_type();
        let void_type = context.void_type();

        let inner_mangled = mangle_basic(context, inner_type);

        let self_type =
            context.opaque_struct_type(&format!("compiler_builtin_rc_{}", inner_mangled));
        self_type.set_body(&[i32_type.into(), inner_type.into()], false);
        let self_ptr_type = self_type.ptr_type(AddressSpace::Generic);

        let new = module.add_function(
            &format!("compiler_builtin_rc_{}_new", inner_mangled),
            self_type.fn_type(&[inner_type.into()], false),
            Some(Linkage::External),
        );

        let retain = module.add_function(
            &format!("compiler_builtin_rc_{}_retain", inner_mangled),
            void_type.fn_type(&[self_ptr_type.into()], false),
            Some(Linkage::External),
        );

        let release = module.add_function(
            &format!("compiler_builtin_rc_{}_release", inner_mangled),
            void_type.fn_type(&[self_ptr_type.into()], false),
            Some(Linkage::External),
        );

        Self {
            inner_type,
            self_type,
            new,
            retain,
            release,
        }
    }

    pub fn define(&self, context: &'a Context, inner_drop: FunctionValue<'a>) {
        self.define_new(context);
        self.define_retain(context);
        self.define_release(context, inner_drop);
    }

    fn define_new(&self, context: &'a Context) {
        let i32_type = context.i32_type();
        let value = self.new.get_nth_param(0).unwrap();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.new, "entry");

        builder.position_at_end(&entry);
        let mut new = self.self_type.get_undef();
        new = builder
            .build_insert_value(new, i32_type.const_int(1, false), REFCOUNT_IDX, "refcount")
            .unwrap()
            .into_struct_value();
        new = builder
            .build_insert_value(new, value, INNER_IDX, "inner")
            .unwrap()
            .into_struct_value();
        builder.build_return(Some(&new));
    }

    fn define_retain(&self, context: &'a Context) {
        let i32_type = context.i32_type();
        let ptr = self.retain.get_nth_param(0).unwrap().into_pointer_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.retain, "entry");

        builder.position_at_end(&entry);
        let refcount_ptr = unsafe { builder.build_struct_gep(ptr, REFCOUNT_IDX, "refcount_ptr") };
        let refcount = builder
            .build_load(refcount_ptr, "refcount")
            .into_int_value();
        let tmp = builder.build_int_add(refcount, i32_type.const_int(1, false), "tmp");
        builder.build_store(refcount_ptr, tmp);
        builder.build_return(None);
    }

    fn define_release(&self, context: &'a Context, inner_drop: FunctionValue<'a>) {
        let i32_type = context.i32_type();
        let ptr = self.release.get_nth_param(0).unwrap().into_pointer_value();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.release, "entry");

        builder.position_at_end(&entry);
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
        let next_block = if_(context, &builder, self.release, should_drop);
        let inner_ptr = unsafe { builder.build_struct_gep(ptr, INNER_IDX, "inner_ptr") };
        builder.build_call(inner_drop, &[inner_ptr.into()], "");

        builder.position_at_end(&next_block);
        builder.build_return(None);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::path::Path;

    #[test]
    fn well_formed() {
        let context = Context::create();
        let module = context.create_module("test");
        let inner_type = context.i32_type();
        let inner_ptr_type = inner_type.ptr_type(AddressSpace::Generic);

        let libc = LibC::declare(&context, &module);

        let void_type = context.void_type();
        let dummy = module.add_function(
            "dummy",
            void_type.fn_type(&[inner_ptr_type.into()], false),
            Some(Linkage::External),
        );
        let builder = context.create_builder();
        let entry = context.append_basic_block(dummy, "entry");
        builder.position_at_end(&entry);

        let hello_global = builder.build_global_string_ptr("Hello, world!", "hello");
        let hello_value = (&hello_global as &dyn BasicValue).as_basic_value_enum();
        builder.build_call(libc.printf, &[hello_value], "");
        builder.build_return(None);

        let rc = RcBuiltin::declare(&context, &module, inner_type.into());
        rc.define(&context, dummy);

        module.print_to_file(Path::new("test_rc.ll.out")).unwrap();
        module.verify().unwrap();
    }
}
