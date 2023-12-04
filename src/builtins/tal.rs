use crate::builtins::fountain_pen;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::TargetData;
use inkwell::values::FunctionValue;
use inkwell::AddressSpace;

pub mod native {
    pub const TAL_O: &'static [u8] = include_bytes!(concat!(env!("OUT_DIR"), "/native/tal.o"));
}

pub mod wasm {
    pub const MALLOC_O: &'static [u8] = include_bytes!(concat!(env!("OUT_DIR"), "/wasm/malloc.o"));

    pub const TAL_O: &'static [u8] = include_bytes!(concat!(env!("OUT_DIR"), "/wasm/tal.o"));

    pub const INDEX_HTML: &'static [u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tal/wasm/dist/index.html"
    ));
    pub const WASM_LOADER_JS: &'static [u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tal/wasm/dist/wasm_loader.js"
    ));
}

#[derive(Clone, Copy, Debug)]
pub struct ProfileRc<'a> {
    pub record_retain: FunctionValue<'a>,
    pub record_release: FunctionValue<'a>,
    pub get_retain_count: FunctionValue<'a>,
    pub get_release_count: FunctionValue<'a>,
}

#[derive(Clone, Copy, Debug)]
pub struct Tal<'a> {
    pub memcpy: FunctionValue<'a>,
    pub exit: FunctionValue<'a>,
    pub getchar: FunctionValue<'a>,

    pub malloc: FunctionValue<'a>,
    pub calloc: FunctionValue<'a>,
    pub realloc: FunctionValue<'a>,
    pub free: FunctionValue<'a>,

    // Modified versions of libc functions for wasm portability.
    pub print: FunctionValue<'a>,
    pub print_error: FunctionValue<'a>,
    pub write: FunctionValue<'a>,
    pub write_error: FunctionValue<'a>,
    pub flush: FunctionValue<'a>,

    // Profiling primitives
    pub prof_clock_res_nanos: FunctionValue<'a>,
    pub prof_clock_nanos: FunctionValue<'a>,
    pub prof_report_init: FunctionValue<'a>,
    pub prof_report_write_string: FunctionValue<'a>,
    pub prof_report_write_u64: FunctionValue<'a>,
    pub prof_report_done: FunctionValue<'a>,
    pub prof_rc: Option<ProfileRc<'a>>,

    // LLVM Intrinsics
    pub expect_i1: FunctionValue<'a>,
    pub umul_with_overflow_i64: FunctionValue<'a>,
}

impl<'a> Tal<'a> {
    pub fn declare(
        context: &'a Context,
        module: &Module<'a>,
        target: &TargetData,
        profile_record_rc: bool,
    ) -> Self {
        let usize_t = fountain_pen::usize_t(context, target);
        let void_t = context.void_type();
        let i8_t = context.i8_type();
        let i8_ptr_t = i8_t.ptr_type(AddressSpace::default());
        let i32_t = context.i32_type();
        let i64_t = context.i64_type();

        let memcpy = module.add_function(
            "memcpy",
            i8_ptr_t.fn_type(&[i8_ptr_t.into(), i8_ptr_t.into(), usize_t.into()], false),
            Some(Linkage::External),
        );
        let exit = module.add_function(
            "exit",
            void_t.fn_type(&[i32_t.into()], false),
            Some(Linkage::External),
        );
        let getchar = module.add_function(
            "getchar",
            i32_t.fn_type(&[], false),
            Some(Linkage::External),
        );

        let malloc = module.add_function(
            "malloc",
            i8_ptr_t.fn_type(&[usize_t.into()], false),
            Some(Linkage::External),
        );
        let calloc = module.add_function(
            "calloc",
            i8_ptr_t.fn_type(&[usize_t.into(), usize_t.into()], false),
            Some(Linkage::External),
        );
        let realloc = module.add_function(
            "realloc",
            i8_ptr_t.fn_type(&[i8_ptr_t.into(), usize_t.into()], false),
            Some(Linkage::External),
        );
        let free = module.add_function(
            "free",
            void_t.fn_type(&[i8_ptr_t.into()], false),
            Some(Linkage::External),
        );

        let print = module.add_function(
            "print",
            void_t.fn_type(&[i8_ptr_t.into()], true),
            Some(Linkage::External),
        );
        let print_error = module.add_function(
            "print_error",
            void_t.fn_type(&[i8_ptr_t.into()], true),
            Some(Linkage::External),
        );
        let write = module.add_function(
            "write",
            void_t.fn_type(&[i8_ptr_t.into(), usize_t.into(), usize_t.into()], false),
            Some(Linkage::External),
        );
        let write_error = module.add_function(
            "write_error",
            void_t.fn_type(&[i8_ptr_t.into(), usize_t.into(), usize_t.into()], false),
            Some(Linkage::External),
        );
        let flush =
            module.add_function("flush", i32_t.fn_type(&[], false), Some(Linkage::External));

        // Profiling primitives:

        let prof_clock_res_nanos = module.add_function(
            "prof_clock_res_nanos",
            i64_t.fn_type(&[], false),
            Some(Linkage::External),
        );
        let prof_clock_nanos = module.add_function(
            "prof_clock_nanos",
            i64_t.fn_type(&[], false),
            Some(Linkage::External),
        );
        let prof_report_init = module.add_function(
            "prof_report_init",
            void_t.fn_type(&[], false),
            Some(Linkage::External),
        );
        let prof_report_write_string = module.add_function(
            "prof_report_write_string",
            void_t.fn_type(&[i8_ptr_t.into()], false),
            Some(Linkage::External),
        );
        let prof_report_write_u64 = module.add_function(
            "prof_report_write_u64",
            void_t.fn_type(&[i64_t.into()], false),
            Some(Linkage::External),
        );
        let prof_report_done = module.add_function(
            "prof_report_done",
            void_t.fn_type(&[], false),
            Some(Linkage::External),
        );

        // LLVM Intrinsics:

        let expect_i1 = module.add_function(
            "llvm.expect.i1",
            context.bool_type().fn_type(
                &[context.bool_type().into(), context.bool_type().into()],
                false,
            ),
            Some(Linkage::External),
        );
        let umul_with_overflow_i64 = module.add_function(
            "llvm.umul.with.overflow.i64",
            context
                .struct_type(&[i64_t.into(), context.bool_type().into()], false)
                .fn_type(&[i64_t.into(), i64_t.into()], false),
            Some(Linkage::External),
        );

        let prof_rc = if profile_record_rc {
            let record_retain = module.add_function(
                "prof_rc_record_retain",
                void_t.fn_type(&[], false),
                Some(Linkage::External),
            );
            let record_release = module.add_function(
                "prof_rc_record_release",
                void_t.fn_type(&[], false),
                Some(Linkage::External),
            );
            let get_retain_count = module.add_function(
                "prof_rc_get_retain_count",
                i64_t.fn_type(&[], false),
                Some(Linkage::External),
            );
            let get_release_count = module.add_function(
                "prof_rc_get_release_count",
                i64_t.fn_type(&[], false),
                Some(Linkage::External),
            );
            Some(ProfileRc {
                record_retain,
                record_release,
                get_retain_count,
                get_release_count,
            })
        } else {
            None
        };

        Self {
            memcpy,
            exit,
            getchar,

            malloc,
            calloc,
            realloc,
            free,

            print,
            print_error,
            write,
            write_error,
            flush,

            prof_clock_res_nanos,
            prof_clock_nanos,
            prof_report_init,
            prof_report_write_string,
            prof_report_write_u64,
            prof_report_done,
            prof_rc,

            expect_i1,
            umul_with_overflow_i64,
        }
    }
}
