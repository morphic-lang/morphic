use find_clang::find_default_clang;
use std::path::Path;
use std::process::Command;
use std::{env, fs};
use walkdir::WalkDir;

fn compile_tal() -> anyhow::Result<()> {
    let cwd = env::current_dir()?;
    let clang = find_default_clang().map_err(|err| anyhow::anyhow!("{err}"))?;

    let wasm_out_dir = env::var("OUT_DIR")? + "/wasm";
    let native_out_dir = env::var("OUT_DIR")? + "/native";

    if !Path::new(&wasm_out_dir).exists() {
        fs::create_dir(&wasm_out_dir)?;
    }
    if !Path::new(&native_out_dir).exists() {
        fs::create_dir(&native_out_dir)?;
    }

    let native_tal_c = fs::canonicalize("./tal/native/tal.c")?;
    let wasm_tal_c = fs::canonicalize("./tal/wasm/src/tal.c")?;
    let wasm_malloc_c = fs::canonicalize("./tal/wasm/src/malloc.c")?;

    // Change the CWD so that clang outputs artifacts to the right location.
    env::set_current_dir(native_out_dir)?;
    let status = Command::new(&clang.path)
        .arg("-c")
        .arg(native_tal_c)
        .status()?;
    assert!(status.success());

    // Change the CWD so that clang outputs artifacts to the right location.
    env::set_current_dir(wasm_out_dir)?;
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
        .status()?;
    assert!(status.success());

    // Make sure to reset the CWD, since lalrpop depends on it being the root.
    env::set_current_dir(cwd)?;

    Ok(())
}

fn main() -> anyhow::Result<()> {
    compile_tal()?;

    lalrpop::Configuration::new()
        .emit_rerun_directives(true)
        .process_current_dir()
        .map_err(|err| anyhow::anyhow!("{err}"))?;

    println!("cargo:rerun-if-changed=build.rs");
    for entry in WalkDir::new("tal") {
        let entry = entry?;
        println!("cargo:rerun-if-changed={}", entry.path().display());
    }

    Ok(())
}
