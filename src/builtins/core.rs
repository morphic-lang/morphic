use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue};
use inkwell::{AddressSpace, IntPredicate};

#[derive(Clone, Copy, Debug)]
pub struct LibC<'a> {
    pub stderr: BasicValueEnum<'a>,
    pub stdout: BasicValueEnum<'a>,

    // initializes stderr and stdout
    pub initialize: FunctionValue<'a>,

    pub calloc: FunctionValue<'a>,
    pub exit: FunctionValue<'a>,
    pub fdopen: FunctionValue<'a>,
    pub fflush: FunctionValue<'a>,
    pub fprintf: FunctionValue<'a>,
    pub free: FunctionValue<'a>,
    pub fwrite: FunctionValue<'a>,
    pub getchar: FunctionValue<'a>,
    pub malloc: FunctionValue<'a>,
    pub printf: FunctionValue<'a>,
    pub realloc: FunctionValue<'a>,
}

// TODO: these declarations are not portable
impl<'a> LibC<'a> {
    pub fn declare(context: &'a Context, module: &Module<'a>) -> Self {
        let void_type = context.void_type();
        let i64_type = context.i64_type();
        let i32_type = context.i32_type();
        let i8_ptr_type = context.i8_type().ptr_type(AddressSpace::Generic);
        let file_ptr_type = context
            .opaque_struct_type("FILE")
            .ptr_type(AddressSpace::Generic);

        let stderr = module.add_global(file_ptr_type, None, "builtin_stderr");
        stderr.set_linkage(Linkage::Internal);
        stderr.set_initializer(&file_ptr_type.const_null());

        let stdout = module.add_global(file_ptr_type, None, "builtin_stdout");
        stdout.set_linkage(Linkage::Internal);
        stdout.set_initializer(&file_ptr_type.const_null());

        let initialize = module.add_function(
            "builtin_init_libc",
            void_type.fn_type(&[], false),
            Some(Linkage::External),
        );

        let calloc = module.add_function(
            "calloc",
            i8_ptr_type.fn_type(&[i64_type.into(), i64_type.into()], false),
            Some(Linkage::External),
        );

        let exit = module.add_function(
            "exit",
            void_type.fn_type(&[i32_type.into()], false),
            Some(Linkage::External),
        );

        let fdopen = module.add_function(
            "fdopen",
            file_ptr_type.fn_type(&[i32_type.into(), i8_ptr_type.into()], false),
            Some(Linkage::External),
        );

        let fflush = module.add_function(
            "fflush",
            i32_type.fn_type(&[file_ptr_type.into()], false),
            Some(Linkage::External),
        );

        let fprintf = module.add_function(
            "fprintf",
            i32_type.fn_type(&[file_ptr_type.into(), i8_ptr_type.into()], true),
            Some(Linkage::External),
        );

        let free = module.add_function(
            "free",
            void_type.fn_type(&[i8_ptr_type.into()], false),
            Some(Linkage::External),
        );

        let fwrite = module.add_function(
            "fwrite",
            i64_type.fn_type(
                &[
                    i8_ptr_type.into(),
                    i64_type.into(),
                    i64_type.into(),
                    file_ptr_type.into(),
                ],
                false,
            ),
            Some(Linkage::External),
        );

        let getchar = module.add_function(
            "getchar",
            i32_type.fn_type(&[], false),
            Some(Linkage::External),
        );

        let malloc = module.add_function(
            "malloc",
            i8_ptr_type.fn_type(&[i64_type.into()], false),
            Some(Linkage::External),
        );

        let printf = module.add_function(
            "printf",
            i32_type.fn_type(&[i8_ptr_type.into()], true),
            Some(Linkage::External),
        );

        let realloc = module.add_function(
            "realloc",
            i8_ptr_type.fn_type(&[i8_ptr_type.into(), i64_type.into()], false),
            Some(Linkage::External),
        );

        Self {
            stderr: stderr.as_basic_value_enum(),
            stdout: stdout.as_basic_value_enum(),

            initialize,

            calloc,
            exit,
            fdopen,
            fflush,
            fprintf,
            free,
            fwrite,
            getchar,
            malloc,
            printf,
            realloc,
        }
    }

    pub fn define(&self, context: &'a Context) {
        let i32_type = context.i32_type();

        let builder = context.create_builder();
        let entry = context.append_basic_block(self.initialize, "entry");
        let success_block = context.append_basic_block(self.initialize, "success");
        let panic_block = context.append_basic_block(self.initialize, "panic");

        builder.position_at_end(entry);

        let stdout_fd_no = 1;
        let stderr_fd_no = 2;

        let file_descriptors = [(stdout_fd_no, self.stdout), (stderr_fd_no, self.stderr)];

        let fdopen_mode = builder
            .build_global_string_ptr("w", "fdopen_mode")
            .as_pointer_value();

        for (fd_no, dest_global) in &file_descriptors {
            let file_ptr = builder
                .build_call(
                    self.fdopen,
                    &[i32_type.const_int(*fd_no, false).into(), fdopen_mode.into()],
                    "file_ptr",
                )
                .try_as_basic_value()
                .left()
                .unwrap();

            let is_null = builder.build_is_null(file_ptr.into_pointer_value(), "is_null");

            let next_block = context.append_basic_block(self.initialize, "next_fd");
            builder.build_conditional_branch(is_null, panic_block, next_block);

            builder.position_at_end(success_block);
            let global_ptr = dest_global.into_pointer_value();

            builder.build_store(global_ptr, file_ptr);
            builder.position_at_end(next_block);
        }

        builder.build_unconditional_branch(success_block);
        builder.position_at_end(success_block);
        builder.build_return(None);

        builder.position_at_end(panic_block);

        // don't try to print on panic; we failed to open stderr/stdout,
        // so chances of being able to report an error sucessfully are dubious
        builder.build_call(self.exit, &[i32_type.const_int(1, true).into()], "");
        builder.build_unreachable();
    }

    pub fn gen_panic(
        &self,
        builder: &Builder<'a>,
        context: &'a Context,
        panic_string: &str,
        panic_args: &[BasicValueEnum<'a>],
    ) {
        let i32_type = context.i32_type();

        let panic_global = builder.build_global_string_ptr(panic_string, "panic_str");

        let stderr_value = builder.build_load(self.stderr.into_pointer_value(), "stderr_value");

        let mut fprintf_args = vec![stderr_value, panic_global.as_pointer_value().into()];
        fprintf_args.extend_from_slice(panic_args);

        builder.build_call(self.fprintf, &fprintf_args, "fprintf_output");

        builder.build_call(self.exit, &[i32_type.const_int(1, true).into()], "");
    }
}

pub(super) fn size_of<'a>(ty: BasicTypeEnum<'a>) -> Option<IntValue<'a>> {
    match ty {
        BasicTypeEnum::ArrayType(actual_ty) => actual_ty.size_of(),
        BasicTypeEnum::FloatType(actual_ty) => Some(actual_ty.size_of()),
        BasicTypeEnum::IntType(acutal_ty) => Some(acutal_ty.size_of()),
        BasicTypeEnum::PointerType(acutal_ty) => Some(acutal_ty.size_of()),
        BasicTypeEnum::StructType(acutal_ty) => acutal_ty.size_of(),
        BasicTypeEnum::VectorType(acutal_ty) => acutal_ty.size_of(),
    }
}

pub(super) fn build_if<'a>(
    context: &'a Context,
    builder: &Builder<'a>,
    func: FunctionValue<'a>,
    cond: IntValue<'a>,
    body: impl FnOnce() -> (),
) {
    let then_block = context.append_basic_block(func, "then_block");
    let next_block = context.append_basic_block(func, "next_block");
    builder.build_conditional_branch(cond, then_block, next_block);
    builder.position_at_end(then_block);

    body();

    builder.build_unconditional_branch(next_block);
    builder.position_at_end(next_block);
}

pub(super) fn build_exiting_if<'a>(
    context: &'a Context,
    builder: &Builder<'a>,
    func: FunctionValue<'a>,
    cond: IntValue<'a>,
    body: impl FnOnce() -> (),
) {
    let then_block = context.append_basic_block(func, "then_block");
    let next_block = context.append_basic_block(func, "next_block");
    builder.build_conditional_branch(cond, then_block, next_block);
    builder.position_at_end(then_block);

    body();

    builder.build_unreachable();
    builder.position_at_end(next_block);
}

pub(super) fn build_ternary<'a>(
    context: &'a Context,
    builder: &Builder<'a>,
    func: FunctionValue<'a>,
    cond: IntValue<'a>,
    then_body: impl FnOnce() -> BasicValueEnum<'a>,
    else_body: impl FnOnce() -> BasicValueEnum<'a>,
) -> BasicValueEnum<'a> {
    let then_block = context.append_basic_block(func, "then_block");
    let else_block = context.append_basic_block(func, "else_block");
    let next_block = context.append_basic_block(func, "next_block");
    builder.build_conditional_branch(cond, then_block, else_block);

    builder.position_at_end(then_block);
    let then_ret = then_body();
    builder.build_unconditional_branch(next_block);

    builder.position_at_end(else_block);
    let else_ret = else_body();
    builder.build_unconditional_branch(next_block);

    builder.position_at_end(next_block);
    let phi = builder.build_phi(then_ret.get_type(), "result");
    phi.add_incoming(&[(&then_ret, then_block), (&else_ret, else_block)]);
    phi.as_basic_value()
}

pub(super) fn build_for<'a>(
    context: &'a Context,
    builder: &Builder<'a>,
    func: FunctionValue<'a>,
    end_for: IntValue<'a>,
    body: impl for<'b> FnOnce(IntValue<'b>) -> (),
) {
    let i64_type = context.i64_type();

    let i_ptr = builder.build_alloca(i64_type, "i_ptr");
    builder.build_store(i_ptr, i64_type.const_int(0, false));

    let for_block = context.append_basic_block(func, "for_block");
    let next_block = context.append_basic_block(func, "next_block");
    builder.build_unconditional_branch(for_block);

    builder.position_at_end(for_block);
    let i_cur = builder.build_load(i_ptr, "i_cur").into_int_value();
    let i_new = builder.build_int_add(i_cur, i64_type.const_int(1, false), "i_new");
    builder.build_store(i_ptr, i_new);

    body(i_cur);

    let done = builder.build_int_compare(IntPredicate::UGE, i_new, end_for, "done");
    builder.build_conditional_branch(done, next_block, for_block);
    builder.position_at_end(next_block);
}

pub(super) unsafe fn get_member<'a>(
    builder: &Builder<'a>,
    struct_ptr: PointerValue<'a>,
    idx: u32,
    name: &str,
) -> BasicValueEnum<'a> {
    let member_ptr_name = format!("{}_ptr", name);
    builder.build_load(
        builder.build_struct_gep(struct_ptr, idx, &member_ptr_name),
        name,
    )
}

pub(super) unsafe fn set_member<'a>(
    builder: &Builder<'a>,
    struct_ptr: PointerValue<'a>,
    idx: u32,
    val: BasicValueEnum<'a>,
    name: &str,
) {
    let member_ptr_name = format!("{}_ptr", name);
    builder.build_store(
        builder.build_struct_gep(struct_ptr, idx, &member_ptr_name),
        val,
    );
}
