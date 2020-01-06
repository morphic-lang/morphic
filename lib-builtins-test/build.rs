use inkwell::context::Context;
use inkwell::module::Linkage;
use inkwell::values::BasicValue;
use inkwell::AddressSpace;
use lib_builtins::{core::LibC, flat_array::FlatArrayBuiltin, rc::RcBuiltin};
use std::{env, process::Command};

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let ir_file = format!("{}/builtins.ll", out_dir);
    let obj_file = format!("{}/builtins.o", out_dir);
    let ar_file = format!("{}/libbuiltins.a", out_dir);

    // TODO: specify module target triple

    let context = Context::create();
    let module = context.create_module("test");
    let inner_type = context.i32_type();
    let inner_ptr_type = inner_type.ptr_type(AddressSpace::Generic);

    let libc = LibC::declare(&context, &module);

    // TODO: deduplicate dummy (also in lib-builtins)

    // declare dummy
    let void_type = context.void_type();
    let dummy = module.add_function(
        "dummy",
        void_type.fn_type(&[inner_ptr_type.into()], false),
        Some(Linkage::External),
    );

    // define dummy
    let builder = context.create_builder();
    let entry = context.append_basic_block(dummy, "entry");
    builder.position_at_end(&entry);
    let hello_global = builder.build_global_string_ptr("I am LLVM IR code!\n", "hello");
    let hello_value = (&hello_global as &dyn BasicValue).as_basic_value_enum();
    builder.build_call(libc.printf, &[hello_value], "");
    builder.build_return(None);

    let flat_array = FlatArrayBuiltin::declare(&context, &module, inner_type.into());
    flat_array.define(&context, &libc, dummy);

    let rc = RcBuiltin::declare(&context, &module, inner_type.into());
    rc.define(&context, dummy);

    module.verify().unwrap();
    module.print_to_file(&ir_file).unwrap();

    Command::new("clang")
        .args(&["-c", &ir_file, "-o", &obj_file])
        .status()
        .unwrap();

    Command::new("ar")
        .args(&["rsc", &ar_file, &obj_file])
        .status()
        .unwrap();

    println!("cargo:rustc-link-search=native={}", out_dir);
    println!("cargo:rustc-link-lib=static=builtins");
}
