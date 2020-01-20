use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicTypeEnum, FloatType, IntType};
use inkwell::values::{BasicValueEnum, FunctionValue, GlobalValue, IntValue, PointerValue};
use inkwell::{AddressSpace, IntPredicate};
use itertools::Itertools;

#[derive(Clone, Copy, Debug)]
pub struct LibC<'a> {
    pub stdout: GlobalValue<'a>,

    pub initialize: FunctionValue<'a>,

    pub exit: FunctionValue<'a>,
    pub fdopen: FunctionValue<'a>,
    pub fflush: FunctionValue<'a>,
    pub fwrite: FunctionValue<'a>,
    pub getchar: FunctionValue<'a>,
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

        let stdout = module.add_global(file_ptr_type, None, "builtin_stdout");
        stdout.set_linkage(Linkage::Private);
        stdout.set_initializer(&file_ptr_type.const_null());

        let initialize = module.add_function(
            "builtin_init_libc",
            void_type.fn_type(&[], false),
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
            stdout,
            initialize,
            exit,
            fdopen,
            fflush,
            fwrite,
            getchar,
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

        builder.position_at_end(&entry);
        let stdout_fd_no = 1;
        let stdout_fd = context.i32_type().const_int(stdout_fd_no, false);

        let stdout_mode = builder
            .build_global_string_ptr("w", "stdout_mode")
            .as_pointer_value();

        let file_ptr = builder
            .build_call(
                self.fdopen,
                &[stdout_fd.into(), stdout_mode.into()],
                "file_ptr",
            )
            .try_as_basic_value()
            .left()
            .unwrap();

        let is_null = builder.build_is_null(file_ptr.into_pointer_value(), "is_null");
        builder.build_conditional_branch(is_null, &panic_block, &success_block);

        builder.position_at_end(&success_block);
        let stdout_ptr = self.stdout.as_pointer_value();

        builder.build_store(stdout_ptr, file_ptr);

        builder.build_return(None);

        builder.position_at_end(&panic_block);
        builder.build_call(self.exit, &[i32_type.const_int(1, true).into()], "");
        builder.build_unreachable();
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
    builder.build_conditional_branch(cond, &then_block, &next_block);
    builder.position_at_end(&then_block);

    body();

    builder.build_unconditional_branch(&next_block);
    builder.position_at_end(&next_block);
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
    builder.build_conditional_branch(cond, &then_block, &else_block);

    builder.position_at_end(&then_block);
    let then_ret = then_body();
    builder.build_unconditional_branch(&next_block);

    builder.position_at_end(&else_block);
    let else_ret = else_body();
    builder.build_unconditional_branch(&next_block);

    builder.position_at_end(&next_block);
    let phi = builder.build_phi(then_ret.get_type(), "result");
    phi.add_incoming(&[(&then_ret, &then_block), (&else_ret, &else_block)]);
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
    builder.build_unconditional_branch(&for_block);

    builder.position_at_end(&for_block);
    let i_cur = builder.build_load(i_ptr, "i_cur").into_int_value();
    let i_new = builder.build_int_add(i_cur, i64_type.const_int(1, false), "i_new");
    builder.build_store(i_ptr, i_new);

    body(i_cur);

    let done = builder.build_int_compare(IntPredicate::UGE, i_new, end_for, "done");
    builder.build_conditional_branch(done, &next_block, &for_block);
    builder.position_at_end(&next_block);
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

fn get_float_name<'a>(context: &'a Context, ty: FloatType<'a>) -> &'static str {
    if ty == context.f16_type() {
        "f16"
    } else if ty == context.f32_type() {
        "f32"
    } else if ty == context.f64_type() {
        "f64"
    } else if ty == context.f128_type() {
        "f128"
    } else {
        unreachable!();
    }
}

fn get_int_name<'a>(context: &'a Context, ty: IntType<'a>) -> &'static str {
    if ty == context.i8_type() {
        "i8"
    } else if ty == context.i16_type() {
        "i16"
    } else if ty == context.i32_type() {
        "i32"
    } else if ty == context.i64_type() {
        "i64"
    } else if ty == context.i128_type() {
        "i128"
    } else {
        unreachable!();
    }
}

pub(super) fn mangle_basic<'a>(context: &'a Context, ty: BasicTypeEnum<'a>) -> String {
    match ty {
        BasicTypeEnum::ArrayType(inner_ty) => format!(
            "A{}{}",
            inner_ty.len(),
            mangle_basic(context, inner_ty.get_element_type())
        ),
        BasicTypeEnum::FloatType(inner_ty) => get_float_name(context, inner_ty).to_owned(),
        BasicTypeEnum::IntType(inner_ty) => get_int_name(context, inner_ty).to_owned(),
        BasicTypeEnum::PointerType(inner_ty) => {
            format!("P{}", mangle_basic(context, inner_ty.into()))
        }
        BasicTypeEnum::StructType(inner_ty) => {
            if !inner_ty.is_opaque() {
                format!(
                    "T{}{}",
                    inner_ty.count_fields(),
                    inner_ty
                        .get_field_types()
                        .iter()
                        .map(|x| mangle_basic(context, *x))
                        .join("")
                )
            } else {
                format!("${}", inner_ty.get_name().unwrap().to_str().unwrap())
            }
        }
        BasicTypeEnum::VectorType(inner_ty) => {
            if inner_ty.is_sized() {
                format!(
                    "V{}{}",
                    inner_ty.get_size(),
                    mangle_basic(context, inner_ty.get_element_type())
                )
            } else {
                format!("V{}", mangle_basic(context, inner_ty.get_element_type()))
            }
        }
    }
}
