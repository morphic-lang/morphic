use crate::{get_cmd_out, EnvVarKind, Strategy, StrategyProvider, Tool, ToolFinder, Validator};
use std::path::Path;
use std::process::Command as Cmd;

fn check_clang(clang: &Path, expected: u32) -> Result<(), String> {
    // This might be overkill, but it is probably the most reliable way to check the clang version.
    // The output of 'clang --version' differs from platform to platform.
    let macros = get_cmd_out(Cmd::new(clang).args(&["-dM", "-E", "-"]))?;
    let prefix = "#define __clang_major__ ";
    for line in macros.lines() {
        if line.starts_with(prefix) && line.len() > prefix.len() {
            let found = std::str::from_utf8(&line.as_bytes()[prefix.len()..])
                .map_err(|err| format!("Cannot parse __clang_major__: {err}"))?
                .parse::<u32>()
                .map_err(|err| format!("Cannot parse __clang_major__: {err}"))?;
            if found == expected {
                return Ok(());
            } else {
                return Err(format!(
                    "'{}' is version {}, but verision {} is required",
                    clang.display(),
                    found,
                    expected,
                ));
            }
        }
    }
    Err(format!(
        "'{}' does not define __clang_major__",
        clang.display()
    ))
}

pub fn find_clang(version: u32) -> Result<Tool, String> {
    ToolFinder::new("clang")
        .with_strategy(Strategy::EnvVar(
            "MORPHIC_CLANG_PATH".into(),
            EnvVarKind::Hard,
        ))
        .with_strategy(Strategy::Which(format!("clang-{version}").into()))
        .with_strategy(Strategy::Which("clang".into()))
        .with_strategy(Strategy::Tool(
            ToolFinder::new("llvm-config")
                .with_strategy(Strategy::Which(format!("llvm-config-{version}").into()))
                .with_strategy(Strategy::Which("llvm-config".into())),
            StrategyProvider::new(move |tool| {
                get_cmd_out(&mut Cmd::new(tool.path()).arg("--bindir")).map(|bindir| {
                    Strategy::TryEach(vec![
                        Strategy::Which(format!("{}/clang-{version}", bindir).into()),
                        Strategy::Which(format!("{}/clang", bindir).into()),
                    ])
                })
            }),
        ))
        .with_validator(Validator::new("check clang version", move |tool| {
            check_clang(tool.path(), version)
        }))
        .find_tool()
}

pub fn find_default_clang() -> Result<Tool, String> {
    find_clang(16)
}
