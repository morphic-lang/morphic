use find_tool::finders::{self, ClangKind};
use find_tool::Tool;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};
use walkdir::WalkDir;

struct Paths {
    out_dir: PathBuf,
    manifest_dir: PathBuf,
    root_dir: PathBuf,
    clang: Tool,
    clangxx: Tool,
    cmake: Tool,
    ctest: Tool,
}

fn map_err<T>(result: Result<T, String>) -> anyhow::Result<T> {
    result.map_err(|err| anyhow::anyhow!("{err}"))
}

impl Paths {
    fn new() -> anyhow::Result<Self> {
        let out_dir = PathBuf::from(env::var("OUT_DIR")?);
        let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR")?);
        let root_dir = manifest_dir.parent().unwrap().parent().unwrap().to_owned();

        let clang = map_err(finders::find_default_clang(ClangKind::C))?;
        let clangxx = map_err(finders::find_default_clang(ClangKind::CXX))?;

        // Minimum version required by bdwgc.
        let version = finders::KitwareVersion::new(3, 10, 0);
        let cmake = map_err(finders::find_cmake(version))?;
        let ctest = map_err(finders::find_ctest(version))?;

        return Ok(Self {
            out_dir,
            manifest_dir,
            root_dir,
            clang,
            clangxx,
            cmake,
            ctest,
        });
    }
}

fn compile_tal(paths: &Paths) -> anyhow::Result<()> {
    let cwd = env::current_dir()?;

    let wasm_out_dir = paths.out_dir.join("wasm");
    let native_out_dir = paths.out_dir.join("native");
    let gc_out_dir = native_out_dir.join("gc");

    if !Path::new(&wasm_out_dir).exists() {
        fs::create_dir(&wasm_out_dir)?;
    }
    if !Path::new(&native_out_dir).exists() {
        fs::create_dir(&native_out_dir)?;
    }
    if !Path::new(&gc_out_dir).exists() {
        fs::create_dir(&gc_out_dir)?;
    }

    let native_tal_c = paths.manifest_dir.join("tal/native/tal.c");
    let wasm_tal_c = paths.manifest_dir.join("tal/wasm/src/tal.c");
    let wasm_malloc_c = paths.manifest_dir.join("tal/wasm/src/malloc.c");

    // Change the CWD so that clang outputs artifacts to the right location.
    env::set_current_dir(native_out_dir)?;
    let status = Command::new(paths.clang.path())
        .arg("-c")
        .arg(native_tal_c)
        .arg("-I")
        .arg(paths.root_dir.join("vendor/bdwgc/include"))
        .status()?;
    assert!(status.success());

    // Change the CWD so that cmake outputs artifacts to the right location.
    env::set_current_dir(gc_out_dir)?;
    let clang_str = paths.clang.path().to_str().unwrap();
    let clangxx_str = paths.clangxx.path().to_str().unwrap();
    let status = Command::new(paths.cmake.path())
        .arg(format!("-DCMAKE_C_COMPILER={}", clang_str))
        .arg(format!("-DCMAKE_CXX_COMPILER={}", clangxx_str))
        .arg("-DCMAKE_BUILD_TYPE=Debug")
        .arg("-DBUILD_SHARED_LIBS=OFF")
        .arg("-Dbuild_tests=ON")
        .arg("-Denable_threads=OFF")
        .arg("-Denable_gc_assertions=ON")
        .arg("-Denable_valgrind_tracking=ON")
        .arg(paths.root_dir.join("vendor/bdwgc"))
        .status()?;
    assert!(status.success());
    let status = Command::new(paths.cmake.path())
        .arg("--build")
        .arg(".")
        .status()?;
    assert!(status.success());
    let status = Command::new(paths.ctest.path()).status()?;
    assert!(status.success());

    // Change the CWD so that clang outputs artifacts to the right location.
    env::set_current_dir(wasm_out_dir)?;
    let status = Command::new(paths.clang.path())
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

    // Make sure to reset the CWD
    env::set_current_dir(cwd)?;
    Ok(())
}

fn main() -> anyhow::Result<()> {
    let paths = Paths::new()?;
    compile_tal(&paths)?;

    println!("cargo:rerun-if-changed=build.rs");
    for entry in WalkDir::new(paths.manifest_dir.join("tal")) {
        let entry = entry?;
        println!("cargo:rerun-if-changed={}", entry.path().display());
    }

    Ok(())
}
