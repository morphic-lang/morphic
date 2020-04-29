use find_clang::find_clang;
use std::path::Path;
use std::process::Command;
use std::{env, fs};
use walkdir::WalkDir;

fn compile_tal() {
    let cwd = env::current_dir().unwrap();
    let clang = find_clang(10).unwrap();

    let wasm_out_dir = env::var("OUT_DIR").unwrap() + "/wasm";
    let native_out_dir = env::var("OUT_DIR").unwrap() + "/native";

    if !Path::new(&wasm_out_dir).exists() {
        fs::create_dir(&wasm_out_dir).unwrap();
    }
    if !Path::new(&native_out_dir).exists() {
        fs::create_dir(&native_out_dir).unwrap();
    }

    let native_tal_c = fs::canonicalize("./tal/native/tal.c").unwrap();
    let wasm_tal_c = fs::canonicalize("./tal/wasm/src/tal.c").unwrap();
    let wasm_malloc_c = fs::canonicalize("./tal/wasm/src/malloc.c").unwrap();

    // Change the CWD so that clang outputs artifacts to the right location.
    env::set_current_dir(native_out_dir).unwrap();
    let status = Command::new(&clang.path)
        .arg("-c")
        .arg(native_tal_c)
        .status()
        .unwrap();
    assert!(status.success());

    // Change the CWD so that clang outputs artifacts to the right location.
    env::set_current_dir(wasm_out_dir).unwrap();
    let status = Command::new(&clang.path)
        .arg("-O3")
        .arg("-ffunction-sections")
        .arg("-fdata-sections")
        .arg("-fPIC")
        .arg("-Wl,--gc-sections")
        // WASM only options:
        .arg("--target=wasm32")
        .arg("-nostdlib")
        .arg("-Wl,--allow-undefined")
        /////////////////////
        .arg("-c")
        .arg(wasm_tal_c)
        .arg(wasm_malloc_c)
        .status()
        .unwrap();
    assert!(status.success());

    // Make sure to reset the CWD, since lalrpop depends on it being the root.
    env::set_current_dir(cwd).unwrap();
}

fn main() {
    compile_tal();
    lalrpop::process_root().unwrap();

    println!("cargo:rerun-if-changed=build.rs");
    for entry in WalkDir::new("tal") {
        let entry = entry.unwrap();
        println!("cargo:rerun-if-changed={}", entry.path().display());
    }
}
