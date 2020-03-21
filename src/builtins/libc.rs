use crate::builtins::fountain_pen::scope;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue};
use inkwell::AddressSpace;

#[derive(Clone, Copy, Debug)]
pub struct LibC<'a> {
    pub stderr: BasicValueEnum<'a>,
    pub stdout: BasicValueEnum<'a>,

    // initialize/cleanup stderr and stdout
    pub initialize: FunctionValue<'a>,
    pub cleanup: FunctionValue<'a>,

    pub calloc: FunctionValue<'a>,
    pub exit: FunctionValue<'a>,
    pub fclose: FunctionValue<'a>,
    pub fdopen: FunctionValue<'a>,
    pub fflush: FunctionValue<'a>,
    pub fprintf: FunctionValue<'a>,
    pub free: FunctionValue<'a>,
    pub fwrite: FunctionValue<'a>,
    pub getchar: FunctionValue<'a>,
    pub malloc: FunctionValue<'a>,
    pub memcpy: FunctionValue<'a>,
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

        let cleanup = module.add_function(
            "builtin_cleanup_libc",
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

        let fclose = module.add_function(
            "fclose",
            i32_type.fn_type(&[file_ptr_type.into()], false),
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

        let memcpy = module.add_function(
            "memcpy",
            i8_ptr_type.fn_type(
                &[i8_ptr_type.into(), i8_ptr_type.into(), i64_type.into()],
                false,
            ),
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
            cleanup,

            calloc,
            exit,
            fclose,
            fdopen,
            fflush,
            fprintf,
            free,
            fwrite,
            getchar,
            malloc,
            memcpy,
            printf,
            realloc,
        }
    }

    pub fn define(&self, context: &'a Context) {
        // define init
        {
            let stdout_fd_no = 1;
            let stderr_fd_no = 2;

            let s = scope(self.initialize, context);

            let fdopen_mode = s.str("w");

            // don't try to print on panic; we failed to open stderr/stdout, so chances of being
            // able to report an error sucessfully are dubious
            let stdout_ptr = s.call(self.fdopen, &[s.i32(stdout_fd_no), fdopen_mode]);
            s.if_(s.is_null(stdout_ptr), |s| {
                s.call_void(self.exit, &[s.i32(1)]);
            });
            let stderr_ptr = s.call(self.fdopen, &[s.i32(stderr_fd_no), fdopen_mode]);
            s.if_(s.is_null(stderr_ptr), |s| {
                s.call_void(self.exit, &[s.i32(1)]);
            });

            s.ptr_set(self.stdout, stdout_ptr);
            s.ptr_set(self.stderr, stderr_ptr);
            s.ret_void();
        }

        // define cleanup
        {
            let s = scope(self.cleanup, context);
            let _ = s.call(self.fclose, &[s.ptr_get(self.stdout)]);
            let _ = s.call(self.fclose, &[s.ptr_get(self.stderr)]);
            s.ret_void();
        }
    }
}
