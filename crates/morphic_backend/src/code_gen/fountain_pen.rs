pub trait ProfileRc: Clone {
    type FunctionValue: Copy;

    /// () -> ()
    fn record_retain(&self) -> Self::FunctionValue;

    /// () -> ()
    fn record_release(&self) -> Self::FunctionValue;

    /// () -> ()
    fn record_rc1(&self) -> Self::FunctionValue;

    /// () -> i64
    fn get_retain_count(&self) -> Self::FunctionValue;

    /// () -> i64
    fn get_release_count(&self) -> Self::FunctionValue;

    /// () -> i64
    fn get_rc1_count(&self) -> Self::FunctionValue;
}

pub trait Tal: Clone {
    type FunctionValue: Copy;
    type ProfileRc: ProfileRc<FunctionValue = Self::FunctionValue>;

    /// (i8*, i8*, usize) -> i8*
    fn memcpy(&self) -> Self::FunctionValue;

    /// (i32) -> !
    fn exit(&self) -> Self::FunctionValue;

    /// () -> i32
    fn getchar(&self) -> Self::FunctionValue;

    /// (usize) -> i8*
    fn malloc(&self) -> Self::FunctionValue;

    /// arg1: number of elements to allocate
    /// arg2: size of each element
    ///
    /// (usize, usize) -> i8*
    fn calloc(&self) -> Self::FunctionValue;

    /// (i8*, usize) -> i8*
    fn realloc(&self) -> Self::FunctionValue;

    /// (i8*) -> ()
    fn free(&self) -> Self::FunctionValue;

    // Modified versions of libc functions for wasm portability.

    /// (i8*, ...) -> ()
    fn print(&self) -> Self::FunctionValue;

    /// (i8*, ...) -> ()
    fn print_error(&self) -> Self::FunctionValue;

    /// arg1: array to be written to stdout
    /// arg2: size of each object to be written
    /// arg3: number of objects
    ///
    /// (i8*, usize, usize) -> ()
    fn write(&self) -> Self::FunctionValue;

    /// arg1: array to be written to stderr
    /// arg2: size of each object to be written
    /// arg3: number of objects
    ///
    /// (i8*, usize, usize) -> ()
    fn write_error(&self) -> Self::FunctionValue;

    /// () -> i32
    fn flush(&self) -> Self::FunctionValue;

    // Profiling primitives

    /// () -> u64
    fn prof_clock_res_nanos(&self) -> Self::FunctionValue;

    /// () -> u64
    fn prof_clock_nanos(&self) -> Self::FunctionValue;

    /// () -> ()
    fn prof_report_init(&self) -> Self::FunctionValue;

    /// (i8*) -> ()
    fn prof_report_write_string(&self) -> Self::FunctionValue;

    /// (u64) -> ()
    fn prof_report_write_u64(&self) -> Self::FunctionValue;

    /// () -> ()
    fn prof_report_done(&self) -> Self::FunctionValue;

    fn prof_rc(&self) -> Option<&Self::ProfileRc>;

    // LLVM Intrinsics

    /// Allows provision of an expected (most probable) value, which can be used by optimizers.
    ///
    /// arg1: value
    /// arg2: expected value
    ///
    /// (i1, i1) -> i1
    fn expect_i1(&self) -> Self::FunctionValue;

    /// Performs an unsigned multiplication of the two arguments, and indicates whether an overflow
    /// occurred during the unsigned multiplication.
    ///
    /// (i64, i64) -> (i64, i1)
    fn umul_with_overflow_i64(&self) -> Self::FunctionValue;

    /// (i64) -> i64
    fn ctpop_i64(&self) -> Self::FunctionValue;

    /// arg1: value to count zeros of
    /// arg2: bool indicating whether the output is poison if the value is 0
    ///
    /// (i64, i1) -> i64
    fn ctlz_i64(&self) -> Self::FunctionValue;

    /// arg1: value to count zeros of
    /// arg2: bool indicating whether the output is poison if the value is 0
    ///
    /// (i64, i1) -> i64
    fn cttz_i64(&self) -> Self::FunctionValue;
}

pub trait Context: Clone {
    type Scope: Scope<
        Context = Self,
        TailTarget = Self::TailTarget,
        VariantsType = Self::VariantsType,
        Type = Self::Type,
        GlobalValue = Self::GlobalValue,
        FunctionValue = Self::FunctionValue,
        Value = Self::Value,
    >;

    type TailTarget: Copy;
    type VariantsType: Clone;
    type Type: Copy;
    type GlobalValue: Copy;
    type FunctionValue: Copy;
    type Value: Copy;

    type ProfileRc: ProfileRc<FunctionValue = Self::FunctionValue>;
    type Tal: Tal<FunctionValue = Self::FunctionValue, ProfileRc = Self::ProfileRc>;

    fn is_gc_on(&self) -> bool;

    fn tal(&self) -> &Self::Tal;

    fn declare_main_func(&self) -> Self::FunctionValue;

    fn declare_func(
        &self,
        name: &str,
        arg_tys: &[Self::Type],
        ret_ty: Option<Self::Type>,
    ) -> Self::FunctionValue;

    fn declare_tail_func(
        &self,
        name: &str,
        arg_tys: &[Self::Type],
        ret_ty: Option<Self::Type>,
        tail_arg_tys: &[Self::Type],
    ) -> (Self::FunctionValue, Vec<Self::TailTarget>);

    fn declare_global(
        &self,
        name: &str,
        ty: Self::Type,
        init: Option<Self::Value>,
    ) -> Self::GlobalValue;

    fn scope(&self, func: Self::FunctionValue) -> Self::Scope;

    fn tail_scope(&self, func: Self::TailTarget) -> Self::Scope;

    fn global_value_as_pointer(&self, global_value: Self::GlobalValue) -> Self::Value;

    fn variants_type_as_type(&self, variants_type: &Self::VariantsType) -> Self::Type;

    fn get_type(&self, val: Self::Value) -> Self::Type;

    // TODO: should we just have this instead of also having `size`? (The latter is implemented in
    // LLVM as a GEP, but is, therefore, target independent.)
    fn get_abi_size(&self, ty: Self::Type) -> u64;

    fn is_iso_to_unit(&self, ty: Self::Type) -> bool;

    fn i1_t(&self) -> Self::Type;

    fn i8_t(&self) -> Self::Type;

    fn i32_t(&self) -> Self::Type;

    fn i64_t(&self) -> Self::Type;

    fn usize_t(&self) -> Self::Type;

    fn f32_t(&self) -> Self::Type;

    fn f64_t(&self) -> Self::Type;

    fn ptr_t(&self) -> Self::Type;

    fn array_t(&self, item_ty: Self::Type, len: u32) -> Self::Type;

    fn struct_t(&self, fields: &[Self::Type]) -> Self::Type;

    fn variants_t(&self, variants: &[Self::Type]) -> Self::VariantsType;

    fn undef(&self, ty: Self::Type) -> Self::Value;

    fn i1(&self, val: bool) -> Self::Value;

    fn i8(&self, val: u8) -> Self::Value;

    fn i32(&self, val: u32) -> Self::Value;

    fn i64(&self, val: u64) -> Self::Value;

    fn usize(&self, val: u64) -> Self::Value;

    fn f32(&self, val: f32) -> Self::Value;

    fn f64(&self, val: f64) -> Self::Value;

    /// Returns an (untyped) null pointer.
    fn null(&self) -> Self::Value;
}

pub trait Scope {
    type Context: Context<
        Scope = Self,
        TailTarget = Self::TailTarget,
        VariantsType = Self::VariantsType,
        Type = Self::Type,
        GlobalValue = Self::GlobalValue,
        FunctionValue = Self::FunctionValue,
        Value = Self::Value,
    >;

    type TailTarget: Copy;
    type VariantsType: Clone;
    type Type: Copy;
    type GlobalValue: Copy;
    type FunctionValue: Copy;
    type Value: Copy;

    fn context(&self) -> &Self::Context;

    fn func(&self) -> Self::FunctionValue;

    fn is_gc_on(&self) -> bool {
        self.context().is_gc_on()
    }

    fn global_value_as_pointer(&self, global_value: Self::GlobalValue) -> Self::Value {
        self.context().global_value_as_pointer(global_value)
    }

    fn variants_type_as_type(&self, variants_type: &Self::VariantsType) -> Self::Type {
        self.context().variants_type_as_type(variants_type)
    }

    fn get_type(&self, val: Self::Value) -> Self::Type {
        self.context().get_type(val)
    }

    fn get_abi_size(&self, ty: Self::Type) -> u64 {
        self.context().get_abi_size(ty)
    }

    fn is_iso_to_unit(&self, ty: Self::Type) -> bool {
        self.context().is_iso_to_unit(ty)
    }

    fn i1_t(&self) -> Self::Type {
        self.context().i1_t()
    }

    fn i8_t(&self) -> Self::Type {
        self.context().i8_t()
    }

    fn i32_t(&self) -> Self::Type {
        self.context().i32_t()
    }

    fn i64_t(&self) -> Self::Type {
        self.context().i64_t()
    }

    fn usize_t(&self) -> Self::Type {
        self.context().usize_t()
    }

    fn f32_t(&self) -> Self::Type {
        self.context().f32_t()
    }

    fn f64_t(&self) -> Self::Type {
        self.context().f64_t()
    }

    fn ptr_t(&self) -> Self::Type {
        self.context().ptr_t()
    }

    fn array_t(&self, item_ty: Self::Type, len: u32) -> Self::Type {
        self.context().array_t(item_ty, len)
    }

    fn struct_t(&self, fields: &[Self::Type]) -> Self::Type {
        self.context().struct_t(fields)
    }

    fn variants_t(&self, variants: &[Self::Type]) -> Self::VariantsType {
        self.context().variants_t(variants)
    }

    fn undef(&self, ty: Self::Type) -> Self::Value {
        self.context().undef(ty)
    }

    fn i1(&self, val: bool) -> Self::Value {
        self.context().i1(val)
    }

    fn i8(&self, val: u8) -> Self::Value {
        self.context().i8(val)
    }

    fn i32(&self, val: u32) -> Self::Value {
        self.context().i32(val)
    }

    fn i64(&self, val: u64) -> Self::Value {
        self.context().i64(val)
    }

    fn usize(&self, val: u64) -> Self::Value {
        self.context().usize(val)
    }

    fn f32(&self, val: f32) -> Self::Value {
        self.context().f32(val)
    }

    fn f64(&self, val: f64) -> Self::Value {
        self.context().f64(val)
    }

    fn null(&self) -> Self::Value {
        self.context().null()
    }

    fn str(&self, s: &str) -> Self::Value;

    fn arg(&self, idx: u32) -> Self::Value;

    fn tail_arg(&self) -> Self::Value;

    fn call(&self, called: Self::FunctionValue, args: &[Self::Value]) -> Self::Value;

    fn call_void(&self, called: Self::FunctionValue, args: &[Self::Value]);

    fn tail_call(&self, called: Self::TailTarget, arg: Self::Value) -> Self::Value;

    fn gep(&self, struct_ty: Self::Type, struct_ptr: Self::Value, idx: u32) -> Self::Value;

    fn arrow(
        &self,
        struct_ty: Self::Type,
        field_ty: Self::Type,
        struct_ptr: Self::Value,
        idx: u32,
    ) -> Self::Value;

    fn field(&self, struct_val: Self::Value, idx: u32) -> Self::Value;

    fn arrow_set(
        &self,
        struct_ty: Self::Type,
        struct_ptr: Self::Value,
        idx: u32,
        new_data: Self::Value,
    );

    fn if_(&self, cond: Self::Value, body: impl FnOnce(&Self));

    // We have `body` take a `bool` instead of having separate 'then' and 'else' closures because a
    // typical caller would need to share mutable state between these closures.
    fn if_else(&self, cond: Self::Value, body: impl FnMut(&Self, bool));

    fn if_expr(
        &self,
        cond: Self::Value,
        body: impl FnMut(&Self, bool) -> Self::Value,
    ) -> Self::Value;

    fn if_else2(
        &self,
        cond: Self::Value,
        mut then_body: impl FnMut(&Self),
        mut else_body: impl FnMut(&Self),
    ) {
        self.if_else(
            cond,
            |s, cond| if cond { then_body(s) } else { else_body(s) },
        );
    }

    fn if_expr2(
        &self,
        cond: Self::Value,
        mut then_body: impl FnMut(&Self) -> Self::Value,
        mut else_body: impl FnMut(&Self) -> Self::Value,
    ) -> Self::Value {
        self.if_expr(
            cond,
            |s, cond| if cond { then_body(s) } else { else_body(s) },
        )
    }

    fn and_lazy(&self, left: Self::Value, right: impl FnMut(&Self) -> Self::Value) -> Self::Value {
        self.if_expr2(left, right, |s| s.i1(false))
    }

    fn ternary(
        &self,
        cond: Self::Value,
        then_value: Self::Value,
        else_value: Self::Value,
    ) -> Self::Value;

    fn int_cast(&self, result_type: Self::Type, int: Self::Value) -> Self::Value;

    fn make_struct(&self, ty: Self::Type, fields: &[(u32, Self::Value)]) -> Self::Value;

    fn make_tup(&self, fields: &[Self::Value]) -> Self::Value;

    fn buf_addr(&self, pointee_ty: Self::Type, arr: Self::Value, idx: Self::Value) -> Self::Value;

    /// 'buf_addr' out of bounds (OOB) -- i.e., without the "in-bounds" requirement.
    fn buf_addr_oob(
        &self,
        pointee_ty: Self::Type,
        arr: Self::Value,
        idx: Self::Value,
    ) -> Self::Value;

    fn buf_set(&self, pointee_ty: Self::Type, arr: Self::Value, idx: Self::Value, val: Self::Value);

    fn buf_get(&self, pointee_ty: Self::Type, arr: Self::Value, idx: Self::Value) -> Self::Value;

    fn arr_addr(&self, pointee_ty: Self::Type, arr: Self::Value, idx: Self::Value) -> Self::Value;

    fn arr_set(&self, pointee_ty: Self::Type, arr: Self::Value, idx: Self::Value, val: Self::Value);

    fn arr_get(&self, pointee_ty: Self::Type, arr: Self::Value, idx: Self::Value) -> Self::Value;

    fn for_(&self, bound: Self::Value, body: impl FnOnce(&Self, Self::Value));

    fn ptr_set(&self, ptr: Self::Value, val: Self::Value);

    fn ptr_get(&self, pointee_ty: Self::Type, ptr: Self::Value) -> Self::Value;

    fn global_set(&self, ptr: Self::GlobalValue, val: Self::Value);

    fn global_get(&self, pointee_ty: Self::Type, ptr: Self::GlobalValue) -> Self::Value;

    fn panic(&self, panic_string: &str, panic_args: &[Self::Value]);

    fn print(&self, message: &str, message_args: &[Self::Value]);

    fn debug(&self, message: &str, message_args: &[Self::Value]);

    fn malloc(&self, num: Self::Value, ty: Self::Type) -> Self::Value;

    fn calloc(&self, num: Self::Value, ty: Self::Type) -> Self::Value;

    fn free(&self, ptr: Self::Value);

    fn is_null(&self, ptr: Self::Value) -> Self::Value;

    fn variants_new_discrim(&self, ty: Self::Type, idx: u32) -> Self::Value;

    fn variants_get_discrim(&self, val: Self::Value) -> Self::Value;

    fn variants_new(&self, ty: &Self::VariantsType, val: Self::Value, idx: u32) -> Self::Value;

    fn variants_get(&self, ty: &Self::VariantsType, val: Self::Value, idx: u32) -> Self::Value;

    fn variants_switch(
        &self,
        ty: &Self::VariantsType,
        val: Self::Value,
        cases: impl FnMut(&Self, u32, Self::Value),
    );

    fn ret_void(&self);

    fn ret(&self, ret_val: Self::Value);

    fn size(&self, ty: Self::Type) -> Self::Value;

    fn unreachable(&self);

    fn alloca(&self, ty: Self::Type) -> Self::Value;

    fn while_(&self, cond: impl FnOnce(&Self) -> Self::Value, body: impl FnOnce(&Self));

    // Integer operations

    fn eq(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn ne(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;

    fn slt(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn sle(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn sgt(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn sge(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;

    fn ult(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn ule(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn ugt(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn uge(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;

    fn sdiv(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn srem(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn udiv(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn urem(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;

    fn neg(&self, arg: Self::Value) -> Self::Value;
    fn add(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn sub(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn mul(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;

    // Floating point operations

    fn oeq(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn one(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;

    fn olt(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn ole(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn ogt(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn oge(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;

    fn fneg(&self, arg: Self::Value) -> Self::Value;
    fn fadd(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn fsub(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn fmul(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn fdiv(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;

    // Bitwise operations

    fn sll(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn srl(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;

    fn and(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn or(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;
    fn not(&self, arg: Self::Value) -> Self::Value;
    fn xor(&self, arg1: Self::Value, arg2: Self::Value) -> Self::Value;

    fn z_extend(&self, result_type: Self::Type, value: Self::Value) -> Self::Value;
    fn s_extend(&self, result_type: Self::Type, value: Self::Value) -> Self::Value;
    fn truncate(&self, result_type: Self::Type, value: Self::Value) -> Self::Value;

    fn ctpop(&self, arg: Self::Value) -> Self::Value;
    fn ctlz(&self, arg: Self::Value) -> Self::Value;
    fn cttz(&self, arg: Self::Value) -> Self::Value;
}
