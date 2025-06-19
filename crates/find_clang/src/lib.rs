use std::iter;
use std::process::Command as Cmd;

pub const DEFAULT_CLANG_VERSION: u32 = 16;

#[derive(Debug, Clone)]
pub struct Clang {
    pub path: String,
}

impl Clang {
    fn new(path: &str) -> Clang {
        Clang {
            path: path.to_owned(),
        }
    }
}

fn display_cmd(cmd: &Cmd) -> String {
    iter::once(cmd.get_program())
        .chain(cmd.get_args().into_iter())
        .map(|s| s.to_string_lossy())
        .collect::<Vec<_>>()
        .join(" ")
}

fn get_cmd_out(cmd: &mut Cmd) -> Result<String, String> {
    let out = cmd
        .output()
        .map_err(|err| format!("Cannot execute '{}': {}", display_cmd(cmd), err))?;
    if out.status.success() {
        Ok(String::from_utf8(out.stdout)
            .map_err(|err| format!("Cannot parse output from '{}': {}", display_cmd(cmd), err))?
            .trim()
            .to_owned())
    } else {
        Err(format!(
            "Command failed '{}': {}",
            display_cmd(cmd),
            out.status
        ))
    }
}

fn check_clang(clang: &str, expected: u32) -> Result<(), String> {
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
                    "'{clang}' is version {found}, but verision {expected} is required",
                ));
            }
        }
    }
    Err(format!("'{clang}' does not define __clang_major__"))
}

macro_rules! check {
    ($log:ident, $clang:ident, $expected:ident) => {
        $log.push(format!("Trying '{}'", $clang));
        if let Err(err) = check_clang($clang, $expected) {
            $log.push(err);
        } else {
            return Ok(Clang::new($clang));
        }
    };
}

pub fn find_clang(version: u32) -> Result<Clang, String> {
    let clang_full = format!("clang-{}", version);
    let clang = "clang";
    let mut config_full = Cmd::new(format!("llvm-config-{}", version));
    let mut config_full = config_full.arg("--bindir");
    let mut config = Cmd::new("llvm-config");
    let mut config = config.arg("--bindir");

    let mut log = Vec::new();

    log.push("Checking environment for MORPHIC_CLANG_PATH".to_owned());
    match std::env::var("MORPHIC_CLANG_PATH") {
        Ok(clang) => {
            let clang = &clang;
            log.push(format!("SUCCESS: MORPHIC_CLANG_PATH={clang}"));
            check!(log, clang, version);
        }
        Err(err) => {
            log.push(format!("Got: {err}"));
        }
    }

    for clang in [&clang_full, clang] {
        check!(log, clang, version);
    }

    for config in [&mut config_full, &mut config] {
        log.push(format!("Trying '{}'", display_cmd(config)));
        match get_cmd_out(config) {
            Ok(bindir) => {
                log.push(format!("SUCCESS: bindir={bindir}"));
                for clang in [&clang_full, clang] {
                    let clang = &format!("{}/{}", bindir, clang);
                    check!(log, clang, version);
                }
            }
            Err(err) => {
                log.push(err);
            }
        }
    }

    let mut err = String::new();
    err.push_str("Cannot find a valid clang compiler. Log:\n");
    for line in log {
        err.push_str(&format!("    - {}\n", line));
    }
    err.push_str("No further fallbacks available.");
    Err(err)
}

pub fn find_default_clang() -> Result<Clang, String> {
    find_clang(DEFAULT_CLANG_VERSION)
}
