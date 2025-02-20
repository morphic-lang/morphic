use std::convert::TryInto;

use crate::llvm_gen::tal::Tal;
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::targets::TargetData;
use inkwell::types::{BasicTypeEnum, IntType};
use inkwell::values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue};
use inkwell::{AddressSpace, IntPredicate};

pub fn usize_t<'a>(context: &'a Context, target: &TargetData) -> IntType<'a> {
    let bits_per_byte = 8;
    let ptr_size = target.get_pointer_byte_size(Some(AddressSpace::default())) * bits_per_byte;
    return context.custom_width_int_type(ptr_size);
}

pub struct Scope<'a, 'b> {
    context: &'a Context,
    target: &'b TargetData,
    builder: Builder<'a>,
    func: FunctionValue<'a>,
}

pub fn scope<'a, 'b>(
    func: FunctionValue<'a>,
    context: &'a Context,
    target: &'b TargetData,
) -> Scope<'a, 'b> {
    assert![func.count_basic_blocks() == 0];
    let entry_block = context.append_basic_block(func, "entry");
    Scope::new(context, target, func, entry_block)
}

impl<'a, 'b> Scope<'a, 'b> {
    fn new(
        context: &'a Context,
        target: &'b TargetData,
        func: FunctionValue<'a>,
        block: BasicBlock<'a>,
    ) -> Scope<'a, 'b> {
        let builder = context.create_builder();
        builder.position_at_end(block);

        Scope {
            context,
            target,
            builder,
            func,
        }
    }

    pub fn builder(&self) -> &Builder<'a> {
        &self.builder
    }

    pub fn func(&self) -> FunctionValue<'a> {
        self.func
    }

    pub fn context(&self) -> &'a Context {
        self.context
    }

    pub fn str(&self, s: &str) -> BasicValueEnum<'a> {
        self.builder
            .build_global_string_ptr(s, "global_str")
            .unwrap()
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
            .build_call(
                called,
                &args
                    .iter()
                    .map(|x| Into::<BasicMetadataValueEnum>::into(*x))
                    .collect::<Vec<_>>(),
                "call",
            )
            .unwrap()
            .try_as_basic_value()
            .left()
            .expect("Cannot use 'call' to call a function without a return value")
    }

    pub fn call_void(&self, called: FunctionValue<'a>, args: &[BasicValueEnum<'a>]) {
        self.builder
            .build_call(
                called,
                &args
                    .iter()
                    .map(|x| Into::<BasicMetadataValueEnum>::into(*x))
                    .collect::<Vec<_>>(),
                "call",
            )
            .unwrap()
            .try_as_basic_value()
            .right()
            .expect("Cannot use 'call_void' to call a function with a return value");
    }

    pub fn gep(
        &self,
        struct_ty: BasicTypeEnum<'a>,
        struct_ptr: BasicValueEnum<'a>,
        idx: u32,
    ) -> BasicValueEnum<'a> {
        self.builder
            .build_struct_gep(struct_ty, struct_ptr.into_pointer_value(), idx, "gep")
            .unwrap()
            .into()
    }

    pub fn arrow(
        &self,
        struct_ty: BasicTypeEnum<'a>,
        field_ty: BasicTypeEnum<'a>,
        struct_ptr: BasicValueEnum<'a>,
        idx: u32,
    ) -> BasicValueEnum<'a> {
        self.builder
            .build_load(
                field_ty,
                self.gep(struct_ty, struct_ptr, idx).into_pointer_value(),
                "arrow",
            )
            .unwrap()
    }

    pub fn field(&self, struct_val: BasicValueEnum<'a>, idx: u32) -> BasicValueEnum<'a> {
        self.builder
            .build_extract_value(struct_val.into_struct_value(), idx, "field")
            .unwrap()
    }

    pub fn arrow_set(
        &self,
        struct_ty: BasicTypeEnum<'a>,
        struct_ptr: BasicValueEnum<'a>,
        idx: u32,
        new_data: BasicValueEnum<'a>,
    ) {
        self.builder
            .build_store(
                self.builder
                    .build_struct_gep(struct_ty, struct_ptr.into_pointer_value(), idx, "gep")
                    .unwrap(),
                new_data,
            )
            .unwrap();
    }

    pub fn if_(&self, cond: BasicValueEnum<'a>, body: impl FnOnce(&Scope<'a, 'b>) -> ()) {
        let cond_int = cond.into_int_value();
        let then_block = self.context.append_basic_block(self.func, "then_block");
        let next_block = self.context.append_basic_block(self.func, "next_block");

        self.builder
            .build_conditional_branch(cond_int, then_block, next_block)
            .unwrap();
        let new_scope = Scope::new(self.context, self.target, self.func, then_block);

        body(&new_scope);

        let final_child_block = new_scope.builder.get_insert_block().unwrap();

        if final_child_block.get_terminator().is_none() {
            new_scope
                .builder
                .build_unconditional_branch(next_block)
                .unwrap();
        }

        self.builder.position_at_end(next_block);
    }

    pub fn if_else(
        &self,
        cond: BasicValueEnum<'a>,
        if_body: impl FnOnce(&Scope<'a, 'b>) -> (),
        else_body: impl FnOnce(&Scope<'a, 'b>),
    ) {
        let cond_int = cond.into_int_value();
        let then_block = self.context.append_basic_block(self.func, "then_block");
        let else_block = self.context.append_basic_block(self.func, "else_block");
        let next_block = self.context.append_basic_block(self.func, "next_block");

        self.builder
            .build_conditional_branch(cond_int, then_block, else_block)
            .unwrap();
        let then_scope = Scope::new(self.context, self.target, self.func, then_block);

        if_body(&then_scope);

        let final_then_block = then_scope.builder.get_insert_block().unwrap();

        if final_then_block.get_terminator().is_none() {
            then_scope
                .builder
                .build_unconditional_branch(next_block)
                .unwrap();
        }

        let else_scope = Scope::new(self.context, self.target, self.func, else_block);

        else_body(&else_scope);

        let final_else_block = else_scope.builder.get_insert_block().unwrap();

        if final_else_block.get_terminator().is_none() {
            else_scope
                .builder
                .build_unconditional_branch(next_block)
                .unwrap();
        }

        self.builder.position_at_end(next_block);
    }

    pub fn if_expr(
        &self,
        cond: BasicValueEnum<'a>,
        then_body: impl FnOnce(&Scope<'a, 'b>) -> BasicValueEnum<'a>,
        else_body: impl FnOnce(&Scope<'a, 'b>) -> BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        let cond_int = cond.into_int_value();
        let then_block = self.context.append_basic_block(self.func, "then_block");
        let else_block = self.context.append_basic_block(self.func, "else_block");
        let next_block = self.context.append_basic_block(self.func, "next_block");

        self.builder
            .build_conditional_branch(cond_int, then_block, else_block)
            .unwrap();

        let then_scope = Scope::new(self.context, self.target, self.func, then_block);
        let then_value = then_body(&then_scope);
        let final_then_block = then_scope.builder.get_insert_block().unwrap();
        then_scope
            .builder
            .build_unconditional_branch(next_block)
            .unwrap();

        let else_scope = Scope::new(self.context, self.target, self.func, else_block);
        let else_value = else_body(&else_scope);
        let final_else_block = else_scope.builder.get_insert_block().unwrap();
        else_scope
            .builder
            .build_unconditional_branch(next_block)
            .unwrap();

        assert![then_value.get_type() == else_value.get_type()];

        self.builder.position_at_end(next_block);

        let phi = self
            .builder
            .build_phi(then_value.get_type(), "result")
            .unwrap();
        phi.add_incoming(&[
            (&then_value, final_then_block),
            (&else_value, final_else_block),
        ]);

        phi.as_basic_value()
    }

    pub fn and_lazy(
        &self,
        left: BasicValueEnum<'a>,
        right: impl FnOnce(&Scope<'a, 'b>) -> BasicValueEnum<'a>,
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
            .unwrap()
    }

    pub fn ptr_cast(
        &self,
        result_type: BasicTypeEnum<'a>,
        ptr: BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        let ptr_type = match result_type {
            BasicTypeEnum::ArrayType(t) => t.ptr_type(AddressSpace::default()),
            BasicTypeEnum::FloatType(t) => t.ptr_type(AddressSpace::default()),
            BasicTypeEnum::IntType(t) => t.ptr_type(AddressSpace::default()),
            BasicTypeEnum::PointerType(t) => t.ptr_type(AddressSpace::default()),
            BasicTypeEnum::StructType(t) => t.ptr_type(AddressSpace::default()),
            BasicTypeEnum::VectorType(t) => t.ptr_type(AddressSpace::default()),
        };
        self.builder
            .build_bitcast(ptr, ptr_type, "ptr_cast")
            .unwrap()
    }

    pub fn int_cast(
        &self,
        result_type: BasicTypeEnum<'a>,
        int: BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        self.builder
            .build_int_cast(
                int.into_int_value(),
                result_type.into_int_type(),
                "int_cast",
            )
            .unwrap()
            .into()
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

    pub fn buf_addr(
        &self,
        pointee_ty: BasicTypeEnum<'a>,
        arr: BasicValueEnum<'a>,
        idx: BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        unsafe {
            self.builder
                .build_in_bounds_gep(
                    pointee_ty,
                    arr.into_pointer_value().into(),
                    &[idx.into_int_value()],
                    "arr_addr",
                )
                .unwrap()
                .into()
        }
    }

    /// 'buf_addr' out of bounds (OOB) -- i.e., without the "in-bounds" requirement.
    pub fn buf_addr_oob(
        &self,
        pointee_ty: BasicTypeEnum<'a>,
        arr: BasicValueEnum<'a>,
        idx: BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        unsafe {
            self.builder
                .build_gep(
                    pointee_ty,
                    arr.into_pointer_value().into(),
                    &[idx.into_int_value()],
                    "arr_addr",
                )
                .unwrap()
                .into()
        }
    }

    pub fn buf_set(
        &self,
        pointee_ty: BasicTypeEnum<'a>,
        arr: BasicValueEnum<'a>,
        idx: BasicValueEnum<'a>,
        val: BasicValueEnum<'a>,
    ) {
        let addr = self.buf_addr(pointee_ty, arr, idx).into_pointer_value();

        self.builder.build_store(addr, val).unwrap();
    }

    pub fn buf_get(
        &self,
        pointee_ty: BasicTypeEnum<'a>,
        arr: BasicValueEnum<'a>,
        idx: BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        let addr = self.buf_addr(pointee_ty, arr, idx).into_pointer_value();

        self.builder.build_load(pointee_ty, addr, "get").unwrap()
    }

    pub fn arr_addr(
        &self,
        pointee_ty: BasicTypeEnum<'a>,
        arr: BasicValueEnum<'a>,
        idx: BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        self.buf_addr(pointee_ty, self.ptr_cast(pointee_ty, arr), idx)
    }

    pub fn arr_set(
        &self,
        pointee_ty: BasicTypeEnum<'a>,
        arr: BasicValueEnum<'a>,
        idx: BasicValueEnum<'a>,
        val: BasicValueEnum<'a>,
    ) {
        let addr = self.arr_addr(pointee_ty, arr, idx).into_pointer_value();

        self.builder.build_store(addr, val).unwrap();
    }

    pub fn arr_get(
        &self,
        pointee_ty: BasicTypeEnum<'a>,
        arr: BasicValueEnum<'a>,
        idx: BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        let addr = self.arr_addr(pointee_ty, arr, idx).into_pointer_value();

        self.builder.build_load(pointee_ty, addr, "get").unwrap()
    }

    pub fn null(&self, ty: BasicTypeEnum<'a>) -> BasicValueEnum<'a> {
        let ptr_type = match ty {
            BasicTypeEnum::ArrayType(t) => t.ptr_type(AddressSpace::default()),
            BasicTypeEnum::FloatType(t) => t.ptr_type(AddressSpace::default()),
            BasicTypeEnum::IntType(t) => t.ptr_type(AddressSpace::default()),
            BasicTypeEnum::PointerType(t) => t.ptr_type(AddressSpace::default()),
            BasicTypeEnum::StructType(t) => t.ptr_type(AddressSpace::default()),
            BasicTypeEnum::VectorType(t) => t.ptr_type(AddressSpace::default()),
        };

        ptr_type.const_null().into()
    }

    pub fn for_(
        &self,
        bound: BasicValueEnum<'a>,
        body: impl FnOnce(&Scope<'a, 'b>, BasicValueEnum<'a>),
    ) {
        let i_ptr = self.alloca(self.i64_t());
        self.ptr_set(i_ptr, self.i64(0));
        self.while_(
            |s| s.ult(s.ptr_get(self.i64_t(), i_ptr), bound),
            |s| {
                body(s, s.ptr_get(self.i64_t(), i_ptr));
                s.ptr_set(i_ptr, s.add(s.ptr_get(self.i64_t(), i_ptr), s.i64(1)));
            },
        );
    }

    pub fn ptr_set(&self, ptr: BasicValueEnum<'a>, val: BasicValueEnum<'a>) {
        self.builder
            .build_store(ptr.into_pointer_value(), val)
            .unwrap();
    }

    pub fn ptr_get(
        &self,
        pointee_ty: BasicTypeEnum<'a>,
        ptr: BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        self.builder
            .build_load(pointee_ty, ptr.into_pointer_value(), "get")
            .unwrap()
    }

    pub fn panic(&self, panic_string: &str, panic_args: &[BasicValueEnum<'a>], tal: &Tal<'a>) {
        let i32_type = self.context.i32_type();

        let panic_global = self
            .builder
            .build_global_string_ptr(panic_string, "panic_str")
            .unwrap();

        let mut print_error_args = vec![panic_global.as_pointer_value().into()];
        print_error_args.extend_from_slice(
            &panic_args
                .iter()
                .map(|x| Into::<BasicMetadataValueEnum>::into(*x))
                .collect::<Vec<_>>(),
        );

        self.builder
            .build_call(tal.print_error, &print_error_args, "print_error_output")
            .unwrap();

        self.builder
            .build_call(tal.exit, &[i32_type.const_int(1, true).into()], "")
            .unwrap();

        self.builder.build_unreachable().unwrap();
    }

    pub fn print(&self, message: &str, message_args: &[BasicValueEnum<'a>], tal: &Tal<'a>) {
        let message_global = self
            .builder
            .build_global_string_ptr(message, "print_str")
            .unwrap();

        let mut print_args = vec![message_global.as_pointer_value().into()];
        print_args.extend_from_slice(
            &message_args
                .iter()
                .map(|x| Into::<BasicMetadataValueEnum>::into(*x))
                .collect::<Vec<_>>(),
        );

        self.builder
            .build_call(tal.print, &print_args, "print_output")
            .unwrap();
    }

    pub fn debug(&self, message: &str, message_args: &[BasicValueEnum<'a>], tal: &Tal<'a>) {
        let message_global = self
            .builder
            .build_global_string_ptr(message, "debug_str")
            .unwrap();

        let mut print_error_args = vec![message_global.as_pointer_value().into()];
        print_error_args.extend_from_slice(
            &message_args
                .iter()
                .map(|x| Into::<BasicMetadataValueEnum>::into(*x))
                .collect::<Vec<_>>(),
        );

        self.builder
            .build_call(tal.print_error, &print_error_args, "print_error__output")
            .unwrap();
    }

    pub fn malloc(
        &self,
        num: BasicValueEnum<'a>,
        ty: BasicTypeEnum<'a>,
        tal: &Tal<'a>,
    ) -> BasicValueEnum<'a> {
        let size = self.size(ty);

        let alloc_size_umul_result = self.call(
            tal.umul_with_overflow_i64,
            &[num, self.int_cast(self.usize_t(), size)],
        );

        let is_overflow = self.field(alloc_size_umul_result, 1);
        self.if_(is_overflow, |s| {
            s.panic(
                "malloc: requested size overflows 64-bit integer type",
                &[],
                tal,
            );
        });

        // TODO: Check for truncation overflow on 32-bit platforms
        let ptr = self.call(tal.malloc, &[self.field(alloc_size_umul_result, 0)]);
        self.if_(self.is_null(ptr), |s| {
            s.panic("malloc failed", &[], tal);
        });

        return self.ptr_cast(ty, ptr);
    }

    pub fn calloc(
        &self,
        num: BasicValueEnum<'a>,
        ty: BasicTypeEnum<'a>,
        tal: &Tal<'a>,
    ) -> BasicValueEnum<'a> {
        let ptr = self.call(
            tal.calloc,
            &[
                num.into_int_value().into(),
                self.int_cast(self.usize_t(), self.size(ty)),
            ],
        );
        self.if_(self.is_null(ptr), |s| {
            s.panic("calloc failed", &[], tal);
        });

        return self.ptr_cast(ty, ptr);
    }

    pub fn free(&self, ptr: BasicValueEnum<'a>, tal: &Tal<'a>) {
        self.call_void(tal.free, &[self.ptr_cast(self.i8_t(), ptr)]);
    }

    pub fn is_null(&self, ptr: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_is_null(ptr.into_pointer_value(), "is_null")
            .unwrap()
            .into()
    }

    pub fn slt(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_compare(
                IntPredicate::SLT,
                arg1.into_int_value(),
                arg2.into_int_value(),
                "slt",
            )
            .unwrap()
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
            .unwrap()
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
            .unwrap()
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
            .unwrap()
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
            .unwrap()
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
            .unwrap()
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
            .unwrap()
            .into()
    }

    pub fn mul(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_mul(arg1.into_int_value(), arg2.into_int_value(), "mul")
            .unwrap()
            .into()
    }

    pub fn udiv(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_unsigned_div(arg1.into_int_value(), arg2.into_int_value(), "udiv")
            .unwrap()
            .into()
    }

    pub fn urem(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_unsigned_rem(arg1.into_int_value(), arg2.into_int_value(), "urem")
            .unwrap()
            .into()
    }

    pub fn add(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_add(arg1.into_int_value(), arg2.into_int_value(), "add")
            .unwrap()
            .into()
    }

    pub fn sub(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_int_sub(arg1.into_int_value(), arg2.into_int_value(), "sub")
            .unwrap()
            .into()
    }

    pub fn and(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_and(arg1.into_int_value(), arg2.into_int_value(), "and")
            .unwrap()
            .into()
    }

    pub fn or(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_or(arg1.into_int_value(), arg2.into_int_value(), "and")
            .unwrap()
            .into()
    }

    pub fn not(&self, arg: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_not(arg.into_int_value(), "not")
            .unwrap()
            .into()
    }

    pub fn sll(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_left_shift(arg1.into_int_value(), arg2.into_int_value(), "sll")
            .unwrap()
            .into()
    }

    pub fn srl(&self, arg1: BasicValueEnum<'a>, arg2: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        self.builder
            .build_right_shift(arg1.into_int_value(), arg2.into_int_value(), false, "srl")
            .unwrap()
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
            .unwrap()
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

    pub fn usize_t(&self) -> BasicTypeEnum<'a> {
        usize_t(self.context, self.target).into()
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

    pub fn usize(&self, val: u64) -> BasicValueEnum<'a> {
        usize_t(self.context, self.target)
            .const_int(val as u64, false)
            .into()
    }

    pub fn ret_void(&self) {
        self.builder.build_return(None).unwrap();
    }

    pub fn ret(&self, ret_val: BasicValueEnum<'a>) {
        self.builder.build_return(Some(&ret_val)).unwrap();
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

        entry_builder.build_alloca(ty, "alloca").unwrap().into()
    }

    pub fn while_(
        &self,
        cond: impl FnOnce(&Scope<'a, 'b>) -> BasicValueEnum<'a>,
        body: impl FnOnce(&Scope<'a, 'b>),
    ) {
        let cond_block = self.context.append_basic_block(self.func, "cond_block");
        let loop_block = self.context.append_basic_block(self.func, "loop_block");
        let next_block = self.context.append_basic_block(self.func, "next_block");

        self.builder.build_unconditional_branch(cond_block).unwrap();

        let cond_scope = Scope::new(self.context, self.target, self.func, cond_block);
        let cond_val = cond(&cond_scope);
        cond_scope
            .builder
            .build_conditional_branch(cond_val.into_int_value(), loop_block, next_block)
            .unwrap();

        let loop_scope = Scope::new(self.context, self.target, self.func, loop_block);
        body(&loop_scope);
        loop_scope
            .builder
            .build_unconditional_branch(cond_block)
            .unwrap();

        self.builder.position_at_end(next_block);
    }
}
