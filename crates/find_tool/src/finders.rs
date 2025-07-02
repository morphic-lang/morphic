use crate::{get_cmd_out, EnvVarKind, Strategy, StrategyProvider, Tool, ToolFinder, Validator};
use std::fmt;
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

#[derive(Debug, Clone, Copy)]
pub enum ClangKind {
    C,
    CXX,
}

impl ClangKind {
    fn to_str(&self) -> &'static str {
        match self {
            ClangKind::C => "clang",
            ClangKind::CXX => "clang++",
        }
    }
}

pub fn find_clang(version: u32, kind: ClangKind) -> Result<Tool, String> {
    let name = kind.to_str();
    ToolFinder::new(name)
        .with_strategy(Strategy::EnvVar(
            "MORPHIC_CLANG_PATH".into(),
            EnvVarKind::Hard,
        ))
        .with_strategy(Strategy::Which(format!("{name}-{version}").into()))
        .with_strategy(Strategy::Which(name.into()))
        .with_strategy(Strategy::Tool(
            ToolFinder::new("llvm-config")
                .with_strategy(Strategy::Which(format!("llvm-config-{version}").into()))
                .with_strategy(Strategy::Which("llvm-config".into())),
            StrategyProvider::new(move |tool| {
                get_cmd_out(&mut Cmd::new(tool.path()).arg("--bindir")).map(|bindir| {
                    Strategy::TryEach(vec![
                        Strategy::Which(format!("{bindir}/{name}-{version}").into()),
                        Strategy::Which(format!("{bindir}/{name}").into()),
                    ])
                })
            }),
        ))
        .with_validator(Validator::new("check clang version", move |tool| {
            check_clang(tool.path(), version)
        }))
        .find_tool()
}

pub fn find_default_clang(kind: ClangKind) -> Result<Tool, String> {
    find_clang(16, kind)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KitwareVersion {
    major: u32,
    minor: u32,
    patch: u32,
    extra: Option<String>,
}

impl PartialOrd for KitwareVersion {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KitwareVersion {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.major
            .cmp(&other.major)
            .then(self.minor.cmp(&other.minor))
            .then(self.patch.cmp(&other.patch))
    }
}

impl fmt::Display for KitwareVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(extra) = &self.extra {
            write!(f, "{}.{}.{}-{}", self.major, self.minor, self.patch, extra)
        } else {
            write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
        }
    }
}

impl KitwareVersion {
    pub fn new(major: u32, minor: u32, patch: u32) -> Self {
        Self {
            major,
            minor,
            patch,
            extra: None,
        }
    }
}

fn check_kitware(name: &str, exe: &Path, min_version: &KitwareVersion) -> Result<(), String> {
    // Example 'cmake --version' output:
    // ```
    // cmake version 3.10.0
    //
    // CMake suite maintained and supported by Kitware (kitware.com/cmake).
    // ```
    let output = get_cmd_out(&mut Cmd::new(exe).arg("--version"))?;
    let first_line = output.lines().next().ok_or("No output from --version")?;

    let version_str = first_line
        .strip_prefix(&format!("{name} version "))
        .ok_or("Unexpected --version output format")?;

    let (version_str, extra) = if let Some((v, p)) = version_str.split_once('-') {
        (v, Some(p.to_string()))
    } else {
        (version_str, None)
    };

    let parts: Vec<_> = version_str
        .split('.')
        .map(|s| s.parse::<u32>())
        .collect::<Result<_, _>>()
        .map_err(|_| "Could not parse version number")?;

    if parts.len() != 3 {
        return Err("Unexpected version format".into());
    }

    let version = KitwareVersion {
        major: parts[0],
        minor: parts[1],
        patch: parts[2],
        extra,
    };

    if &version < min_version {
        return Err(format!(
            "Version {version} is less than minimum required {min_version}"
        ));
    }

    Ok(())
}

pub fn find_cmake(min_version: KitwareVersion) -> Result<Tool, String> {
    ToolFinder::new("cmake")
        .with_strategy(Strategy::EnvVar(
            "MORPHIC_CMAKE_PATH".into(),
            EnvVarKind::Hard,
        ))
        .with_strategy(Strategy::Which("cmake".into()))
        .with_validator(Validator::new("check cmake version", move |tool| {
            check_kitware("cmake", tool.path(), &min_version)
        }))
        .find_tool()
}

pub fn find_ctest(min_version: KitwareVersion) -> Result<Tool, String> {
    ToolFinder::new("ctest")
        .with_strategy(Strategy::EnvVar(
            "MORPHIC_CTEST_PATH".into(),
            EnvVarKind::Hard,
        ))
        .with_strategy(Strategy::Which("ctest".into()))
        .with_validator(Validator::new("check ctest version", move |tool| {
            check_kitware("ctest", tool.path(), &min_version)
        }))
        .find_tool()
}
