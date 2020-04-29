use crate::builtins::fountain_pen;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::TargetData;
use inkwell::values::FunctionValue;
use inkwell::AddressSpace;

pub mod native {
    pub const SHIM_O: &'static [u8] = include_bytes!(concat!(env!("OUT_DIR"), "/shim.o"));
}

pub mod wasm {
    pub const LIBC_O: &'static [u8] = include_bytes!(concat!(env!("OUT_DIR"), "/libc.o"));
    pub const MALLOC_O: &'static [u8] = include_bytes!(concat!(env!("OUT_DIR"), "/malloc.o"));

    pub const INDEX_HTML: &'static [u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/libc/wasm/dist/index.html"
    ));
    pub const WASM_LOADER_JS: &'static [u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/libc/wasm/dist/wasm_loader.js"
    ));
}

#[derive(Clone, Copy, Debug)]
pub struct LibC<'a> {
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
    pub flush: FunctionValue<'a>,
}

impl<'a> LibC<'a> {
    pub fn declare(context: &'a Context, module: &Module<'a>, target: &TargetData) -> Self {
        let usize_t = fountain_pen::usize_t(context, target);
        let void_t = context.void_type();
        let i8_t = context.i8_type();
        let i8_ptr_t = i8_t.ptr_type(AddressSpace::Generic);
        let i32_t = context.i32_type();

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
        let flush =
            module.add_function("flush", i32_t.fn_type(&[], false), Some(Linkage::External));

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
            flush,
        }
    }
}
