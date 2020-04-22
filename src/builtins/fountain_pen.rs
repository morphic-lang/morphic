use crate::builtins::libc::LibC;
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue};
use inkwell::{AddressSpace, IntPredicate};
use std::convert::TryInto;

pub struct Scope<'a> {
    context: &'a Context,
    builder: Builder<'a>,
    func: FunctionValue<'a>,
}

pub fn scope<'a>(func: FunctionValue<'a>, context: &'a Context) -> Scope<'a> {
    assert![func.count_basic_blocks() == 0];
    let entry_block = context.append_basic_block(func, "entry");
    Scope::new(context, func, entry_block)
}

impl<'a> Scope<'a> {
    fn new(context: &'a Context, func: FunctionValue<'a>, block: BasicBlock<'a>) -> Scope<'a> {
        let builder = context.create_builder();
        builder.position_at_end(block);

        Scope {
            context: &context,
            builder,
            func,
        }
    }

    pub fn str(&self, s: &str) -> BasicValueEnum<'a> {
        self.builder
            .build_global_string_ptr(s, "global_str")
            .as_basic_value_enum()
    }

    pub fn arg(&self, idx: u32) -> BasicValueEnum<'a> {
        self.func.get_nth_param(idx).unwrap()
    }

    pub fn call(
        &self,
        called: FunctionValue<'a>,
        args: &[BasicValueEnum<'a>],
    ) -> BasicValueEnum<'a> {
        self.builder
            .build_call(called, args, "call")
            .try_as_basic_value()
            .left()
            .expect("Cannot use 'call' to call a function without a return value")
    }

    pub fn call_void(&self, called: FunctionValue<'a>, args: &[BasicValueEnum<'a>]) {
        self.builder
            .build_call(called, args, "call")
            .try_as_basic_value()
            .right()
            .expect("Cannot use 'call_void' to call a function with a return value");
    }

    pub fn gep(&self, struct_ptr: BasicValueEnum<'a>, idx: u32) -> BasicValueEnum<'a> {
        let struct_type = struct_ptr
            .get_type()
            .into_pointer_type()
            .get_element_type()
            .into_struct_type();

        // This assert checks that the subsequent GEP is safe
        assert!(
            struct_type.get_field_type_at_index(idx).is_some(),
            "Struct type has no field at index {}",
            idx
        );

        unsafe {
            self.builder
                .build_struct_gep(struct_ptr.into_pointer_value(), idx, "gep")
                .into()
        }
    }

    pub fn arrow(&self, struct_ptr: BasicValueEnum<'a>, idx: u32) -> BasicValueEnum<'a> {
        self.builder
            .build_load(self.gep(struct_ptr, idx).into_pointer_value(), "arrow")
    }

    pub fn field(&self, struct_val: BasicValueEnum<'a>, idx: u32) -> BasicValueEnum<'a> {
        self.builder
            .build_extract_value(struct_val.into_struct_value(), idx, "field")
            .unwrap()
    }

    pub fn arrow_set(
        &self,
        struct_ptr: BasicValueEnum<'a>,
        idx: u32,
        new_data: BasicValueEnum<'a>,
    ) {
        let struct_type = struct_ptr
            .get_type()
            .into_pointer_type()
            .get_element_type()
            .into_struct_type();

        // This assert checks that the subsequent GEP is safe
        assert!(
            struct_type.get_field_type_at_index(idx).is_some(),
            "Struct type has no field at index {}",
            idx
        );

        self.builder.build_store(
            unsafe {
                self.builder
                    .build_struct_gep(struct_ptr.into_pointer_value(), idx, "gep")
            },
            new_data,
        );
    }

    pub fn if_(&self, cond: BasicValueEnum<'a>, body: impl FnOnce(&Scope<'a>) -> ()) {
        let cond_int = cond.into_int_value();
        let then_block = self.context.append_basic_block(self.func, "then_block");
        let next_block = self.context.append_basic_block(self.func, "next_block");

        self.builder
            .build_conditional_branch(cond_int, then_block, next_block);
        let new_scope = Scope::new(self.context, self.func, then_block);

        body(&new_scope);

        let final_child_block = new_scope.builder.get_insert_block().unwrap();

        if final_child_block.get_terminator().is_none() {
            new_scope.builder.build_unconditional_branch(next_block);
        }

        self.builder.position_at_end(next_block);
    }

    pub fn if_else(
        &self,
        cond: BasicValueEnum<'a>,
        if_body: impl FnOnce(&Scope<'a>) -> (),
        else_body: impl FnOnce(&Scope<'a>),
    ) {
        let cond_int = cond.into_int_value();
        let then_block = self.context.append_basic_block(self.func, "then_block");
        let else_block = self.context.append_basic_block(self.func, "else_block");
        let next_block = self.context.append_basic_block(self.func, "next_block");

        self.builder
            .build_conditional_branch(cond_int, then_block, else_block);
        let then_scope = Scope::new(self.context, self.func, then_block);

        if_body(&then_scope);

        let final_then_block = then_scope.builder.get_insert_block().unwrap();

        if final_then_block.get_terminator().is_none() {
            then_scope.builder.build_unconditional_branch(next_block);
        }

        let else_scope = Scope::new(self.context, self.func, else_block);

        else_body(&else_scope);

        let final_else_block = else_scope.builder.get_insert_block().unwrap();

        if final_else_block.get_terminator().is_none() {
            else_scope.builder.build_unconditional_branch(next_block);
        }

        self.builder.position_at_end(next_block);
    }

    pub fn if_expr(
        &self,
        cond: BasicValueEnum<'a>,
        then_body: impl FnOnce(&Scope<'a>) -> BasicValueEnum<'a>,
        else_body: impl FnOnce(&Scope<'a>) -> BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        let cond_int = cond.into_int_value();
        let then_block = self.context.append_basic_block(self.func, "then_block");
        let else_block = self.context.append_basic_block(self.func, "else_block");
        let next_block = self.context.append_basic_block(self.func, "next_block");

        self.builder
            .build_conditional_branch(cond_int, then_block, else_block);

        let then_scope = Scope::new(self.context, self.func, then_block);
        let then_value = then_body(&then_scope);
        let final_then_block = then_scope.builder.get_insert_block().unwrap();
        then_scope.builder.build_unconditional_branch(next_block);

        let else_scope = Scope::new(self.context, self.func, else_block);
        let else_value = else_body(&else_scope);
        let final_else_block = else_scope.builder.get_insert_block().unwrap();
        else_scope.builder.build_unconditional_branch(next_block);

        assert![then_value.get_type() == else_value.get_type()];

        self.builder.position_at_end(next_block);

        let phi = self.builder.build_phi(then_value.get_type(), "result");
        phi.add_incoming(&[
            (&then_value, final_then_block),
            (&else_value, final_else_block),
        ]);

        phi.as_basic_value()
    }

    pub fn and_lazy(
        &self,
        left: BasicValueEnum<'a>,
        right: impl FnOnce(&Scope<'a>) -> BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        self.if_expr(left, right, |s| s.i1(false))
    }

    pub fn ternary(
        &self,
        cond: BasicValueEnum<'a>,
        then_value: BasicValueEnum<'a>,
        else_value: BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        let cond_int = cond.into_int_value();
        self.builder
            .build_select(cond_int, then_value, else_value, "ternary")
    }

    pub fn ptr_cast(
        &self,
        result_type: BasicTypeEnum<'a>,
        ptr: BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        let ptr_type = match result_type {
            BasicTypeEnum::ArrayType(t) => t.ptr_type(AddressSpace::Generic),
            BasicTypeEnum::FloatType(t) => t.ptr_type(AddressSpace::Generic),
            BasicTypeEnum::IntType(t) => t.ptr_type(AddressSpace::Generic),
            BasicTypeEnum::PointerType(t) => t.ptr_type(AddressSpace::Generic),
            BasicTypeEnum::StructType(t) => t.ptr_type(AddressSpace::Generic),
            BasicTypeEnum::VectorType(t) => t.ptr_type(AddressSpace::Generic),
        };
        self.builder.build_bitcast(ptr, ptr_type, "ptr_cast")
    }

    pub fn make_struct(
        &self,
        ty: BasicTypeEnum<'a>,
        fields: &[(u32, BasicValueEnum<'a>)],
    ) -> BasicValueEnum<'a> {
        let mut new_inner = self.undef(ty);

        for (idx, value) in fields {
            new_inner = self
                .builder
                .build_insert_value(new_inner.into_struct_value(), *value, *idx, "insert_value")
                .unwrap()
                .into_struct_value()
                .into();
        }

        new_inner.into()
    }

    pub fn make_tup(&self, fields: &[BasicValueEnum<'a>]) -> BasicValueEnum<'a> {
        let field_types: Vec<_> = fields.iter().map(|field| field.get_type()).collect();
        let tup_type = self.context.struct_type(&field_types[..], false);

        let mut tup = tup_type.get_undef();
        for (elem, value) in fields.iter().enumerate() {
            tup = self
                .builder
                .build_insert_value(tup, *value, elem.try_into().unwrap(), "insert")
                .unwrap()
                .into_struct_value();
        }

        tup.into()
    }

    pub fn buf_addr(&self, arr: BasicValueEnum<'a>, idx: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        unsafe {
            self.builder
                .build_in_bounds_gep(
                    arr.into_pointer_value().into(),
                    &[idx.into_int_value()],
                    "arr_addr",
                )
                .into()
        }
    }

    pub fn buf_set(
        &self,
        arr: BasicValueEnum<'a>,
        idx: BasicValueEnum<'a>,
        val: BasicValueEnum<'a>,
    ) {
        let addr = self.buf_addr(arr, idx).into_pointer_value();

        self.builder.build_store(addr, val);
    }

    pub fn buf_get(&self, arr: BasicValueEnum<'a>, idx: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        let addr = self.buf_addr(arr, idx).into_pointer_value();

        self.builder.build_load(addr, "get")
    }

    pub fn arr_addr(&self, arr: BasicValueEnum<'a>, idx: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        let target_type = arr
            .get_type()
            .into_pointer_type()
            .get_element_type()
            .into_array_type()
            .get_element_type();

        self.buf_addr(self.ptr_cast(target_type, arr), idx)
    }

    pub fn arr_set(
        &self,
        arr: BasicValueEnum<'a>,
        idx: BasicValueEnum<'a>,
        val: BasicValueEnum<'a>,
    ) {
        let addr = self.arr_addr(arr, idx).into_pointer_value();

        self.builder.build_store(addr, val);
    }

    pub fn arr_get(&self, arr: BasicValueEnum<'a>, idx: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        let addr = self.arr_addr(arr, idx).into_pointer_value();

        self.builder.build_load(addr, "get")
    }

    pub fn null(&self, ty: BasicTypeEnum<'a>) -> BasicValueEnum<'a> {
        let ptr_type = match ty {
            BasicTypeEnum::ArrayType(t) => t.ptr_type(AddressSpace::Generic),
            BasicTypeEnum::FloatType(t) => t.ptr_type(AddressSpace::Generic),
            BasicTypeEnum::IntType(t) => t.ptr_type(AddressSpace::Generic),
            BasicTypeEnum::PointerType(t) => t.ptr_type(AddressSpace::Generic),
            BasicTypeEnum::StructType(t) => t.ptr_type(AddressSpace::Generic),
            BasicTypeEnum::VectorType(t) => t.ptr_type(AddressSpace::Generic),
        };

        ptr_type.const_null().into()
    }

    pub fn for_(
        &self,
        bound: BasicValueEnum<'a>,
        body: impl FnOnce(&Scope<'a>, BasicValueEnum<'a>),
    ) {
        let i_ptr = self.alloca(self.i64_t());
        self.ptr_set(i_ptr, self.i64(0));
        self.while_(
            |s| s.ult(s.ptr_get(i_ptr), bound),
            |s| {
                body(s, s.ptr_get(i_ptr));
                s.ptr_set(i_ptr, s.add(s.ptr_get(i_ptr), s.i64(1)));
            },
        );
    }

    pub fn ptr_set(&self, ptr: BasicValueEnum<'a>, val: BasicValueEnum<'a>) {
        self.builder.build_store(ptr.into_pointer_value(), val);
    }

    pub fn ptr_get(&self, ptr: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder.build_load(ptr.into_pointer_value(), "get")
    }

    pub fn panic(&self, panic_string: &str, panic_args: &[BasicValueEnum<'a>], libc: &LibC<'a>) {
        let i32_type = self.context.i32_type();

        let panic_global = self
            .builder
            .build_global_string_ptr(panic_string, "panic_str");

        let mut print_error_args = vec![panic_global.as_pointer_value().into()];
        print_error_args.extend_from_slice(panic_args);

        self.builder
            .build_call(libc.print_error, &print_error_args, "print_error_output");

        self.builder
            .build_call(libc.exit, &[i32_type.const_int(1, true).into()], "");

        self.builder.build_unreachable();
    }

    pub fn print(&self, message: &str, message_args: &[BasicValueEnum<'a>], libc: &LibC<'a>) {
        let message_global = self.builder.build_global_string_ptr(message, "print_str");

        let mut print_args = vec![message_global.as_pointer_value().into()];
        print_args.extend_from_slice(message_args);

        self.builder
            .build_call(libc.print, &print_args, "print_output");
    }

    pub fn debug(&self, message: &str, message_args: &[BasicValueEnum<'a>], libc: &LibC<'a>) {
        let message_global = self.builder.build_global_string_ptr(message, "debug_str");

        let mut print_error_args = vec![message_global.as_pointer_value().into()];
        print_error_args.extend_from_slice(message_args);

        self.builder
            .build_call(libc.print_error, &print_error_args, "print_error__output");
    }

    pub fn malloc(
        &self,
        num: BasicValueEnum<'a>,
        ty: BasicTypeEnum<'a>,
        libc: &LibC<'a>,
    ) -> BasicValueEnum<'a> {
        let ptr = self.call(libc.malloc, &[self.mul(num, self.size(ty))]);
        self.if_(self.is_null(ptr), |s| {
            s.panic("malloc failed", &[], libc);
        });
        return ptr;
    }

    pub fn calloc(
        &self,
        num: BasicValueEnum<'a>,
        ty: BasicTypeEnum<'a>,
        libc: &LibC<'a>,
    ) -> BasicValueEnum<'a> {
        let ptr = self.call(libc.calloc, &[num.into_int_value().into(), self.size(ty)]);
        self.if_(self.is_null(ptr), |s| {
            s.panic("calloc failed", &[], libc);
        });

        return self.ptr_cast(ty, ptr);
    }

    pub fn free(&self, ptr: BasicValueEnum<'a>, libc: &LibC<'a>) {
        self.call_void(libc.free, &[self.ptr_cast(self.i8_t(), ptr)]);
    }

    pub fn is_null(&self, ptr: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_is_null(ptr.into_pointer_value(), "is_null")
            .into()
    }

    pub fn ult(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_compare(
                IntPredicate::ULT,
                arg1.into_int_value(),
                arg2.into_int_value(),
                "ult",
            )
            .into()
    }

    pub fn ugt(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_compare(
                IntPredicate::UGT,
                arg1.into_int_value(),
                arg2.into_int_value(),
                "ugt",
            )
            .into()
    }

    pub fn ule(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_compare(
                IntPredicate::ULE,
                arg1.into_int_value(),
                arg2.into_int_value(),
                "ule",
            )
            .into()
    }

    pub fn uge(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_compare(
                IntPredicate::UGE,
                arg1.into_int_value(),
                arg2.into_int_value(),
                "uge",
            )
            .into()
    }

    pub fn eq(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_compare(
                IntPredicate::EQ,
                arg1.into_int_value(),
                arg2.into_int_value(),
                "eq",
            )
            .into()
    }

    pub fn ne(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_compare(
                IntPredicate::NE,
                arg1.into_int_value(),
                arg2.into_int_value(),
                "neq",
            )
            .into()
    }

    pub fn mul(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_mul(arg1.into_int_value(), arg2.into_int_value(), "mul")
            .into()
    }

    pub fn udiv(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_unsigned_div(arg1.into_int_value(), arg2.into_int_value(), "udiv")
            .into()
    }

    pub fn urem(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_unsigned_rem(arg1.into_int_value(), arg2.into_int_value(), "urem")
            .into()
    }

    pub fn add(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_add(arg1.into_int_value(), arg2.into_int_value(), "add")
            .into()
    }

    pub fn sub(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_sub(arg1.into_int_value(), arg2.into_int_value(), "sub")
            .into()
    }

    pub fn and(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_and(arg1.into_int_value(), arg2.into_int_value(), "and")
            .into()
    }

    pub fn or(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_or(arg1.into_int_value(), arg2.into_int_value(), "and")
            .into()
    }

    pub fn not(&self, arg: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder.build_not(arg.into_int_value(), "not").into()
    }

    pub fn sll(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_left_shift(arg1.into_int_value(), arg2.into_int_value(), "sll")
            .into()
    }

    pub fn srl(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_right_shift(arg1.into_int_value(), arg2.into_int_value(), false, "srl")
            .into()
    }

    pub fn truncate(
        &self,
        result_type: BasicTypeEnum<'a>,
        value: BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        self.builder
            .build_int_truncate(
                value.into_int_value(),
                result_type.into_int_type(),
                "truncate",
            )
            .into()
    }

    pub fn i8_t(&self) -> BasicTypeEnum<'a> {
        self.context.i8_type().into()
    }

    pub fn i32_t(&self) -> BasicTypeEnum<'a> {
        self.context.i32_type().into()
    }

    pub fn i64_t(&self) -> BasicTypeEnum<'a> {
        self.context.i64_type().into()
    }

    pub fn i1(&self, val: bool) -> BasicValueEnum<'a> {
        self.context.bool_type().const_int(val as u64, false).into()
    }

    pub fn i8(&self, val: u8) -> BasicValueEnum<'a> {
        self.context.i8_type().const_int(val as u64, false).into()
    }

    pub fn i32(&self, val: u32) -> BasicValueEnum<'a> {
        self.context.i32_type().const_int(val as u64, false).into()
    }

    pub fn i64(&self, val: u64) -> BasicValueEnum<'a> {
        self.context.i64_type().const_int(val as u64, false).into()
    }

    pub fn ret_void(&self) {
        self.builder.build_return(None);
    }

    pub fn ret(&self, ret_val: BasicValueEnum<'a>) {
        self.builder.build_return(Some(&ret_val));
    }

    pub fn size(&self, ty: BasicTypeEnum<'a>) -> BasicValueEnum<'a> {
        match ty {
            BasicTypeEnum::ArrayType(t) => t.size_of().unwrap(),
            BasicTypeEnum::FloatType(t) => t.size_of(),
            BasicTypeEnum::IntType(t) => t.size_of(),
            BasicTypeEnum::PointerType(t) => t.size_of(),
            BasicTypeEnum::StructType(t) => t.size_of().unwrap(),
            BasicTypeEnum::VectorType(t) => t.size_of().unwrap(),
        }
        .into()
    }

    pub fn undef(&self, ty: BasicTypeEnum<'a>) -> BasicValueEnum<'a> {
        match ty {
            BasicTypeEnum::ArrayType(t) => t.get_undef().into(),
            BasicTypeEnum::FloatType(t) => t.get_undef().into(),
            BasicTypeEnum::IntType(t) => t.get_undef().into(),
            BasicTypeEnum::PointerType(t) => t.get_undef().into(),
            BasicTypeEnum::StructType(t) => t.get_undef().into(),
            BasicTypeEnum::VectorType(t) => t.get_undef().into(),
        }
    }

    // TODO: Should we consolidate this with similar code in 'llvm_gen.rs'?
    pub fn alloca(&self, ty: BasicTypeEnum<'a>) -> BasicValueEnum<'a> {
        let entry = self.func.get_first_basic_block().unwrap();

        let entry_builder = self.context.create_builder();

        if let Some(entry_inst) = entry.get_first_instruction() {
            entry_builder.position_before(&entry_inst);
        } else {
            entry_builder.position_at_end(entry);
        }

        entry_builder.build_alloca(ty, "alloca").into()
    }

    pub fn while_(
        &self,
        cond: impl FnOnce(&Scope<'a>) -> BasicValueEnum<'a>,
        body: impl FnOnce(&Scope<'a>),
    ) {
        let cond_block = self.context.append_basic_block(self.func, "cond_block");
        let loop_block = self.context.append_basic_block(self.func, "loop_block");
        let next_block = self.context.append_basic_block(self.func, "next_block");

        self.builder.build_unconditional_branch(cond_block);

        let cond_scope = Scope::new(self.context, self.func, cond_block);
        let cond_val = cond(&cond_scope);
        cond_scope.builder.build_conditional_branch(
            cond_val.into_int_value(),
            loop_block,
            next_block,
        );

        let loop_scope = Scope::new(self.context, self.func, loop_block);
        body(&loop_scope);
        loop_scope.builder.build_unconditional_branch(cond_block);

        self.builder.position_at_end(next_block);
    }
}
