use find_clang::find_clang;
use std::process::Command;
use std::{env, fs};
use walkdir::WalkDir;

fn compile_libc() {
    let cwd = env::current_dir().unwrap();
    let out_dir = env::var("OUT_DIR").unwrap();
    let clang = find_clang(10).unwrap();

    let shim_c = fs::canonicalize("./libc/native/shim.c").unwrap();
    let libc_c = fs::canonicalize("./libc/wasm/src/libc.c").unwrap();
    let malloc_c = fs::canonicalize("./libc/wasm/src/malloc.c").unwrap();

    // Change the CWD so that clang outputs artifacts to the right location.
    env::set_current_dir(out_dir).unwrap();

    let status = Command::new(&clang.path)
        .arg("-c")
        .arg(shim_c)
        .status()
        .unwrap();
    assert!(status.success());

    let status = Command::new(&clang.path)
        .arg("--target=wasm32")
        .arg("-nostdlib")
        .arg("-c")
        .arg(libc_c)
        .arg(malloc_c)
        .status()
        .unwrap();
    assert!(status.success());

    // Make sure to reset the CWD since lalrpop depends on it being the root.
    env::set_current_dir(cwd).unwrap();
}

fn main() {
    compile_libc();
    lalrpop::process_root().unwrap();

    println!("cargo:rerun-if-changed=build.rs");
    for entry in WalkDir::new("libc") {
        let entry = entry.unwrap();
        println!("cargo:rerun-if-changed={}", entry.path().display());
    }
}
