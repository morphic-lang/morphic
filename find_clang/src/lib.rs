use anyhow::{anyhow, Context, Result};
use std::process::Command as Cmd;

pub const DEFAULT_CLANG_VERSION: u32 = 14;

pub struct Clang {
    pub path: String,
}

fn trim_newline(s: &mut String) {
    if s.ends_with('\n') {
        s.pop();
        if s.ends_with('\r') {
            s.pop();
        }
    }
}

fn get_cmd_out(cmd: &mut Cmd) -> Result<String> {
    let out = cmd
        .output()
        .context(format!("failed to run command {:#?}.", cmd))?;
    if out.status.success() {
        let mut s = String::from_utf8(out.stdout)?;
        trim_newline(&mut s);
        Ok(s)
    } else {
        Err(anyhow!(
            "command {:#?} exited unsuccessfully with status {}.",
            cmd,
            out.status
        ))
    }
}

fn check_clang(clang: &str, version: u32) -> Result<Clang> {
    // this might be overkill, but it is probably the most reliable way to check the clang version,
    // since the output of 'clang --version' might differ from platform to platform
    let macros = get_cmd_out(Cmd::new(clang).args(&["-dM", "-E", "-"]))?;
    let clang_major_prefix = "#define __clang_major__ ";
    for line in macros.lines() {
        if line.starts_with(clang_major_prefix) && line.len() > clang_major_prefix.len() {
            let detected_version =
                std::str::from_utf8(&line.as_bytes()[clang_major_prefix.len()..])?
                    .parse::<u32>()?;
            if detected_version == version {
                return Ok(Clang {
                    path: clang.to_owned(),
                });
            } else {
                return Err(anyhow!(format!(
                    "{} is version {}, but version {} is required.",
                    clang, detected_version, version
                )));
            }
        }
    }
    return Err(anyhow!(format!(
        "cannot determine __clang_major__ for {}.",
        clang
    )));
}

pub fn find_clang(version: u32) -> Result<Clang> {
    let clang_suffix = format!("clang-{}", version);
    let clang = "clang";
    let mut llvm_config_suffix = Cmd::new(format!("llvm-config-{}", version));
    let mut llvm_config = Cmd::new("llvm-config");
    llvm_config_suffix.arg("--bindir");
    llvm_config.arg("--bindir");

    std::env::var("MORPHIC_CLANG_PATH")
        .map_err(|err| err.into())
        .and_then(|path| check_clang(&path, version))
        .or_else(|_| check_clang(&clang_suffix, version))
        .or_else(|_| check_clang(&clang, version))
        .or_else(|_| {
            get_cmd_out(&mut llvm_config_suffix).and_then(|bindir| {
                check_clang(&format!("{}/{}", bindir, clang_suffix), version)
                    .or_else(|_| check_clang(&format!("{}/{}", bindir, clang), version))
            })
        })
        .or_else(|_| {
            get_cmd_out(&mut llvm_config).and_then(|bindir| {
                check_clang(&format!("{}/{}", bindir, clang_suffix), version)
                    .or_else(|_| check_clang(&format!("{}/{}", bindir, clang), version))
            })
        })
}

pub fn find_default_clang() -> Result<Clang> {
    find_clang(DEFAULT_CLANG_VERSION)
}
