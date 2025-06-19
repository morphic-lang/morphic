use find_clang::find_default_clang;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};
use walkdir::WalkDir;

struct Paths {
    out_dir: PathBuf,
    manifest_dir: PathBuf,
}

impl Paths {
    fn new() -> anyhow::Result<Self> {
        return Ok(Self {
            out_dir: PathBuf::from(env::var("OUT_DIR")?),
            manifest_dir: PathBuf::from(env::var("CARGO_MANIFEST_DIR")?),
        });
    }
}

fn compile_tal(paths: &Paths) -> anyhow::Result<()> {
    let cwd = env::current_dir()?;
    let clang = find_default_clang().map_err(|err| anyhow::anyhow!("{err}"))?;

    let wasm_out_dir = paths.out_dir.join("wasm");
    let native_out_dir = paths.out_dir.join("native");

    if !Path::new(&wasm_out_dir).exists() {
        fs::create_dir(&wasm_out_dir)?;
    }
    if !Path::new(&native_out_dir).exists() {
        fs::create_dir(&native_out_dir)?;
    }

    let native_tal_c = paths.manifest_dir.join("tal/native/tal.c");
    let wasm_tal_c = paths.manifest_dir.join("tal/wasm/src/tal.c");
    let wasm_malloc_c = paths.manifest_dir.join("tal/wasm/src/malloc.c");

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
    let paths = Paths::new()?;
    compile_tal(&paths)?;

    lalrpop::Configuration::new()
        .emit_rerun_directives(true)
        .process_current_dir()
        .map_err(|err| anyhow::anyhow!("{err}"))?;

    println!("cargo:rerun-if-changed=build.rs");
    for entry in WalkDir::new(paths.manifest_dir.join("tal")) {
        let entry = entry?;
        println!("cargo:rerun-if-changed={}", entry.path().display());
    }

    Ok(())
}
