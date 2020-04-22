use find_clang::find_clang;
use std::process::Command;
use std::{env, fs};

fn wasm_libc_path(filename: &str) -> String {
    fs::canonicalize(format!("./wasm_libc/libc/{}", filename))
        .unwrap()
        .to_str()
        .unwrap()
        .to_owned()
}

fn compile_wasm_libc() {
    let cwd = env::current_dir().unwrap();
    let out_dir = env::var("OUT_DIR").unwrap();
    let clang = find_clang(10).unwrap();

    let libc_c = wasm_libc_path("libc.c");
    let malloc_c = wasm_libc_path("malloc.c");

    // Change the cwd so that clang outputs artifacts to the right location.
    env::set_current_dir(out_dir).unwrap();

    let status = Command::new(clang.path)
        .args(&["--target=wasm32", "-nostdlib", "-c", &libc_c, &malloc_c])
        .status()
        .unwrap();
    assert!(status.success());

    // Make sure to reset cwd since lalrpop depends on it.
    env::set_current_dir(cwd).unwrap();
}

fn main() {
    compile_wasm_libc();
    lalrpop::process_root().unwrap();
}
