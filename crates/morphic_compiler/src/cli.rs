use clap::builder::{styling, PossibleValuesParser};
use clap::{Arg, ArgAction, Command};
use inkwell::OptimizationLevel;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use crate::progress_ui::ProgressMode;
use crate::pseudoprocess::{Stdio, ValgrindConfig};

#[derive(Clone, Debug)]
pub struct ArtifactDir {
    pub dir_path: PathBuf,
    pub filename_prefix: PathBuf,
}

#[derive(Clone, Debug)]
pub enum RunMode {
    Compile { valgrind: Option<ValgrindConfig> },
    Interpret,
}

#[derive(Clone, Copy, Debug)]
pub enum PurityMode {
    Checked,
    Unchecked,
}

#[derive(Clone, Debug)]
pub struct RunConfig {
    pub src_path: PathBuf,
    pub mode: RunMode,
    pub rc_strat: RcStrategy,
    pub purity_mode: PurityMode,

    // This controls the stdio capture behavior of the *user* program.  Logging and error messages
    // from the compiler itself are unaffected.
    //
    // When invoking the compiler from the command line this should always take the value 'Inherit'.
    // The 'Piped' variant exists only for use within the internal testing framework.
    pub stdio: Stdio,
}

#[derive(Clone, Copy, Debug)]
pub enum LlvmConfig {
    Native,
    Wasm,
}

#[derive(Clone, Copy, Debug)]
pub enum MlConfig {
    Sml,
    Ocaml,
}

#[derive(Clone, Copy, Debug)]
pub enum TargetConfig {
    Llvm(LlvmConfig),
    Ml(MlConfig),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SymbolName(pub String);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SpecializationMode {
    Specialize,
    Single,
}

impl Default for SpecializationMode {
    fn default() -> Self {
        SpecializationMode::Specialize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RcStrategy {
    Default,
    Perceus, // Linear type inference. Everything is inferred as owned.
}

impl Default for RcStrategy {
    fn default() -> Self {
        RcStrategy::Default
    }
}

const RC_STRATS: &[&str] = &["default", "perceus"];
const DEFAULT_RC_STRATS: &str = "default";

fn parse_rc_strat(s: &str) -> RcStrategy {
    match s {
        "default" => RcStrategy::Default,
        "perceus" => RcStrategy::Perceus,
        _ => unreachable!(),
    }
}

#[derive(Clone, Debug)]
pub struct PassOptions {
    pub defunc_mode: SpecializationMode,
    pub rc_strat: RcStrategy,
}

impl Default for PassOptions {
    fn default() -> Self {
        Self {
            defunc_mode: SpecializationMode::default(),
            rc_strat: RcStrategy::default(),
        }
    }
}

#[derive(Debug)]
pub struct BuildConfig {
    pub src_path: PathBuf,
    pub purity_mode: PurityMode,

    pub profile_syms: Vec<SymbolName>,
    pub profile_record_rc: bool,

    pub target: TargetConfig,
    pub llvm_opt_level: OptimizationLevel,

    pub output_path: PathBuf,
    pub artifact_dir: Option<ArtifactDir>,
    pub progress: ProgressMode,

    pub pass_options: PassOptions,
}

#[derive(Debug)]
pub enum Config {
    RunConfig(RunConfig),
    BuildConfig(BuildConfig),
}

pub fn default_llvm_opt_level() -> OptimizationLevel {
    OptimizationLevel::Aggressive
}

impl Config {
    pub fn from_args() -> Self {
        let styles = styling::Styles::styled()
            .header(styling::AnsiColor::Green.on_default() | styling::Effects::BOLD)
            .usage(styling::AnsiColor::Green.on_default() | styling::Effects::BOLD)
            .literal(styling::AnsiColor::Cyan.on_default() | styling::Effects::BOLD)
            .placeholder(styling::AnsiColor::Cyan.on_default());

        let matches = Command::new(std::env!("CARGO_PKG_NAME"))
            .version(std::env!("CARGO_PKG_VERSION"))
            .about(std::env!("CARGO_PKG_DESCRIPTION"))
            .styles(styles)
            .next_line_help(true)
            .subcommand_required(true)
            .arg_required_else_help(true)
            .subcommand(
                Command::new("run")
                    .about("Compiles and runs a program from source")
                    .arg(
                        Arg::new("src-path")
                            .help("Specify the source file for compilation.")
                            .required(true)
                            .index(1),
                    )
                    .arg(
                        Arg::new("no-check-purity")
                            .long("no-check-purity")
                            .action(ArgAction::SetTrue)
                            .help("Do not enforce purity."),
                    )
                    .arg(
                        Arg::new("valgrind")
                            .long("valgrind")
                            .conflicts_with("interpret")
                            .action(ArgAction::SetTrue)
                            .help("Run the compiler output program inside of valgrind."),
                    )
                    .arg(
                        Arg::new("valgrind-ignore-leaks")
                            .long("valgrind-ignore-leaks")
                            .requires("valgrind")
                            .action(ArgAction::SetTrue)
                            .help("Ignore memory leaks when running under valgrind."),
                    )
                    .arg(
                        Arg::new("interpret")
                            .long("interpret")
                            .action(ArgAction::SetTrue)
                            .help(
                                "Run the program using the reference interpreter instead of \
                                generating LLVM and running a fully compiled executable.",
                            ),
                    )
                    .arg(Arg::new("rc-strat")
                        .long("rc-strat")
                        .value_parser(PossibleValuesParser::new(RC_STRATS))
                        .default_value(DEFAULT_RC_STRATS)
                        .help("Same as '--rc-strat' for 'morphic build'."),
                    )
            )
            .subcommand(
                Command::new("build")
                    .about("Builds a program from source")
                    .arg(
                        Arg::new("src-path")
                            .help("Specify the source file for compilation.")
                            .required(true)
                            .index(1),
                    )
                    .arg(
                        Arg::new("no-check-purity")
                            .long("no-check-purity")
                            .action(ArgAction::SetTrue)
                            .help("Do not enforce purity."),
                    )
                    .arg(
                        Arg::new("emit-artifacts")
                            .long("emit-artifacts")
                            .short('a')
                            .action(ArgAction::SetTrue)
                            .help(
                                "Emit compilation artifacts including the generated LLVM IR and \
                                object file. Artifacts will be placed in a directory whose name is \
                                derived from the generated executable's name.",
                            ),
                    )
                    .arg(
                        Arg::new("llvm-opt-level")
                            .long("llvm-opt-level")
                            .help("Set the optimization level used by the LLVM backend.")
                            .value_parser(0..=3)
                            .default_value((default_llvm_opt_level() as i64).to_string()),
                    )
                    .arg(
                        Arg::new("wasm")
                            .long("wasm")
                            .action(ArgAction::SetTrue)
                            .help("Compile to wasm instead of a native binary."),
                    )
                    .arg(
                        Arg::new("sml")
                            .long("sml")
                            .action(ArgAction::SetTrue)
                            .help("Compile to SML instead of a native binary."),
                    )
                    .arg(
                        Arg::new("ocaml")
                            .long("ocaml")
                            .action(ArgAction::SetTrue)
                            .help("Compile to OCaml instead of a native binary."),
                    )
                    .arg(
                        Arg::new("output-path")
                            .short('o')
                            .long("output-path")
                            .help("Place the output executable at this path.")
                    )
                    .arg(
                        // If you ever change the CLI syntax for profiling, you need to grep for
                        // "--profile" elsewhere in the project and adjust things as necessary,
                        // because several error message strings in other modules mention the
                        // argument syntax.
                        Arg::new("profile")
                            .long("profile")
                            .help(
                                "Instrument a function to measure performance statistics. To use \
                                this instrumentation, run the compiled program with the \
                                environment variable MORPHIC_PROFILE_PATH set. When the program \
                                exits, it will write a JSON file to this path containing \
                                performance data for every '--profile'd function.",
                            )
                            .action(ArgAction::Append)
                            .number_of_values(1),
                    )
                    .arg(
                        Arg::new("profile-record-rc")
                        .long("profile-record-rc")
                        .action(ArgAction::SetTrue)
                        .help(
                            "Record number of reference count increments and decrements for each \
                             '--profile'd function."
                        )
                    )
                    .arg(
                        Arg::new("defunc-mode")
                            .long("defunc-mode")
                            .help("Set whether or not to specialize during defunctionalization")
                            .value_parser(PossibleValuesParser::new(&["specialize", "single"]))
                            .default_value("specialize"),
                    )
                    .arg(
                        Arg::new("rc-strat")
                        .long("rc-strat")
                        .help(
                            "Set whether or not to elide reference counting operations. This is \
                            mostly useful for working around compiler bugs."
                        )
                        .value_parser(PossibleValuesParser::new(RC_STRATS))
                        .default_value(DEFAULT_RC_STRATS),
                    )
                    .arg(
                        Arg::new("progress")
                            .long("progress")
                            .action(ArgAction::SetTrue)
                            .help("Set whether or not to show progress"),
                    ),
            )
            .get_matches();

        if let Some(matches) = matches.subcommand_matches("run") {
            let src_path = matches
                .get_one::<String>("src-path")
                .unwrap()
                .to_owned()
                .into();

            let purity_mode = if matches.get_flag("no-check-purity") {
                PurityMode::Unchecked
            } else {
                PurityMode::Checked
            };

            let mode = if matches.get_flag("interpret") {
                RunMode::Interpret
            } else {
                RunMode::Compile {
                    valgrind: if matches.get_flag("valgrind") {
                        Some(ValgrindConfig {
                            leak_check: !matches.get_flag("valgrind-ignore-leaks"),
                        })
                    } else {
                        None
                    },
                }
            };

            let rc_strat = parse_rc_strat(matches.get_one::<String>("rc-strat").unwrap());

            let run_config = RunConfig {
                src_path,
                purity_mode,
                mode,
                rc_strat: rc_strat,
                stdio: Stdio::Inherit,
            };
            return Self::RunConfig(run_config);
        }

        if let Some(matches) = matches.subcommand_matches("build") {
            let src_path: PathBuf = matches
                .get_one::<String>("src-path")
                .unwrap()
                .to_owned()
                .into();

            let purity_mode = if matches.get_flag("no-check-purity") {
                PurityMode::Unchecked
            } else {
                PurityMode::Checked
            };

            let target = if matches.get_flag("wasm") {
                TargetConfig::Llvm(LlvmConfig::Wasm)
            } else if matches.get_flag("sml") {
                TargetConfig::Ml(MlConfig::Sml)
            } else if matches.get_flag("ocaml") {
                TargetConfig::Ml(MlConfig::Ocaml)
            } else {
                TargetConfig::Llvm(LlvmConfig::Native)
            };

            let llvm_opt_level = match matches.get_one::<i64>("llvm-opt-level").unwrap() {
                0 => OptimizationLevel::None,
                1 => OptimizationLevel::Less,
                2 => OptimizationLevel::Default,
                3 => OptimizationLevel::Aggressive,
                _ => unreachable!(),
            };

            let output_path = matches
                .get_one::<OsString>("output-path")
                .map(|s| s.to_owned().into())
                .unwrap_or(
                    std::env::current_dir()
                        .unwrap()
                        .join(src_path.file_name().unwrap())
                        .with_extension(""),
                );

            let artifact_dir = if matches.get_flag("emit-artifacts") {
                let mut artifact_dir = output_path.clone().into_os_string();
                artifact_dir.push("-artifacts");
                std::fs::create_dir_all(&artifact_dir).unwrap();
                Some(ArtifactDir {
                    dir_path: artifact_dir.into(),
                    filename_prefix: output_path.file_name().unwrap().into(),
                })
            } else {
                None
            };

            let profile_syms = match matches.get_many::<String>("profile") {
                Some(values) => values.map(|val| SymbolName(val.to_owned())).collect(),
                None => Vec::new(),
            };

            let profile_record_rc = matches.get_flag("profile-record-rc");

            let defunc_mode = match matches.get_one::<String>("defunc-mode").unwrap().as_str() {
                "specialize" => SpecializationMode::Specialize,
                "single" => SpecializationMode::Single,
                _ => unreachable!(),
            };

            let rc_strat = parse_rc_strat(matches.get_one::<String>("rc-strat").unwrap());

            let progress = if matches.get_flag("progress") {
                ProgressMode::Visible
            } else {
                ProgressMode::Hidden
            };

            let build_config = BuildConfig {
                src_path,
                purity_mode,
                profile_syms,
                profile_record_rc,
                target,
                llvm_opt_level,
                output_path: output_path.into(),
                artifact_dir,
                progress,
                pass_options: PassOptions {
                    defunc_mode,
                    rc_strat: rc_strat,
                },
            };
            return Self::BuildConfig(build_config);
        }

        // Clap will exit our program gracefully if no subcommand is provided.
        // Therefore, one of the above if statements will always trigger.
        unreachable!();
    }

    pub fn src_path(&self) -> &Path {
        match self {
            Self::RunConfig(config) => &config.src_path,
            Self::BuildConfig(config) => &config.src_path,
        }
    }

    pub fn artifact_dir(&self) -> Option<&ArtifactDir> {
        match self {
            Self::RunConfig(_) => None,
            Self::BuildConfig(build_config) => build_config.artifact_dir.as_ref(),
        }
    }

    pub fn profile_syms(&self) -> &[SymbolName] {
        match self {
            Self::RunConfig(_) => &[],
            Self::BuildConfig(build_config) => &build_config.profile_syms,
        }
    }
}

impl ArtifactDir {
    pub fn artifact_path(&self, extension: &(impl AsRef<OsStr> + ?Sized)) -> PathBuf {
        self.dir_path
            .join(self.filename_prefix.with_extension(extension))
    }
}
