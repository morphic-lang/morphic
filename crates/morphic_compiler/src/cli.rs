use clap::builder::{styling, PossibleValuesParser};
use clap::{Arg, ArgAction, ArgMatches, Command};
use inkwell::OptimizationLevel;
use morphic_backend::BuildConfig;
use morphic_common::config::{
    default_llvm_opt_level, ArrayKind, ArtifactDir, GcKind, LlvmConfig, MlConfig, PassOptions,
    PurityMode, RcStrategy, SpecializationMode, SymbolName, TargetConfig,
};
use morphic_common::progress_ui::ProgressMode;
use morphic_common::pseudoprocess::{Stdio, ValgrindConfig};
use std::ffi::OsString;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug)]
pub enum RunMode {
    Compile { valgrind: Option<ValgrindConfig> },
    Interpret,
}

#[derive(Clone, Debug)]
pub struct RunConfig {
    pub src_path: PathBuf,
    pub mode: RunMode,
    pub pass_options: PassOptions,
    pub purity_mode: PurityMode,

    // This controls the stdio capture behavior of the *user* program.  Logging and error messages
    // from the compiler itself are unaffected.
    //
    // When invoking the compiler from the command line this should always take the value 'Inherit'.
    // The 'Piped' variant exists only for use within the internal testing framework.
    pub stdio: Stdio,
}

#[derive(Debug)]
pub enum Config {
    RunConfig(RunConfig),
    BuildConfig(BuildConfig),
}

const DEFUNC_MODE_STRS: &[&str] = &["specialize", "single"];

fn parse_defunc_mode(s: &str) -> SpecializationMode {
    match s {
        "specialize" => SpecializationMode::Specialize,
        "single" => SpecializationMode::Single,
        _ => unreachable!(),
    }
}

fn defunc_mode_to_str(mode: SpecializationMode) -> &'static str {
    match mode {
        SpecializationMode::Specialize => "specialize",
        SpecializationMode::Single => "single",
    }
}

const RC_STRAT_STRS: &[&str] = &["default", "perceus"];

fn parse_rc_strat(s: &str) -> RcStrategy {
    match s {
        "default" => RcStrategy::Default,
        "perceus" => RcStrategy::Perceus,
        _ => unreachable!(),
    }
}

fn rc_strat_to_str(strat: RcStrategy) -> &'static str {
    match strat {
        RcStrategy::Default => "default",
        RcStrategy::Perceus => "perceus",
    }
}

const GC_KIND_STRS: &[&str] = &["none", "bdw"];

fn parse_gc_kind(s: &str) -> GcKind {
    match s {
        "none" => GcKind::None,
        "bdw" => GcKind::Bdw,
        _ => unreachable!(),
    }
}

fn gc_kind_to_str(kind: GcKind) -> &'static str {
    match kind {
        GcKind::None => "none",
        GcKind::Bdw => "bdw",
    }
}

const ARRAY_KIND_STRS: &[&str] = &["cow", "persistent"];

fn parse_array_kind(s: &str) -> ArrayKind {
    match s {
        "cow" => ArrayKind::Cow,
        "persistent" => ArrayKind::Persistent,
        _ => unreachable!(),
    }
}

fn array_kind_to_str(kind: ArrayKind) -> &'static str {
    match kind {
        ArrayKind::Cow => "cow",
        ArrayKind::Persistent => "persistent",
    }
}

trait RegisterCommonArgs {
    fn register_common_args(self) -> Self;
}

impl RegisterCommonArgs for Command {
    fn register_common_args(self) -> Self {
        self.arg(
            Arg::new("no-check-purity")
                .long("no-check-purity")
                .action(ArgAction::SetTrue)
                .help("Do not enforce purity."),
        )
        .arg(
            Arg::new("llvm-opt-level")
                .long("llvm-opt-level")
                .help("Set the optimization level used by the LLVM backend.")
                .value_parser(0..=3)
                .default_value((default_llvm_opt_level() as i64).to_string()),
        )
        .arg(
            Arg::new("defunc-mode")
                .long("defunc-mode")
                .help("Set whether or not to specialize during defunctionalization")
                .value_parser(PossibleValuesParser::new(DEFUNC_MODE_STRS))
                .default_value(defunc_mode_to_str(SpecializationMode::default())),
        )
        .arg(
            Arg::new("rc-strat")
                .long("rc-strat")
                .help(
                    "Set whether or not to elide reference counting operations. This is \
                    mostly useful for working around compiler bugs.",
                )
                .value_parser(PossibleValuesParser::new(RC_STRAT_STRS))
                .default_value(rc_strat_to_str(RcStrategy::default())),
        )
        .arg(
            Arg::new("gc-kind")
                .long("gc-kind")
                .help(
                    "Set the garbage collector to use. This exists for experimental purposes. \
                    The best choice is 'none' which does *not* leak memory but rather employs \
                    reference counting with static, borrow-based reference count elision. \
                    'bwd' is the Boehm-Demers-Weiser coservative collector.",
                )
                .value_parser(PossibleValuesParser::new(GC_KIND_STRS))
                .default_value(gc_kind_to_str(GcKind::default())),
        )
        .arg(
            Arg::new("array-kind")
                .long("array-kind")
                .help(
                    "Set the kind of array to use. 'cow' is a copy-on-write array that takes \
                    advantage of the RC-1 optimization when reference counting is turned on. \
                    'persistent' is a Clojure-style persistent array that always has O(log n) \
                    updates, but with a *large* constant factor.",
                )
                .value_parser(PossibleValuesParser::new(ARRAY_KIND_STRS))
                .default_value(array_kind_to_str(ArrayKind::default())),
        )
        .arg(
            Arg::new("progress")
                .long("progress")
                .action(ArgAction::SetTrue)
                .help("Set whether or not to show progress"),
        )
    }
}

struct CommonArgs {
    purity_mode: PurityMode,
    llvm_opt_level: OptimizationLevel,
    defunc_mode: SpecializationMode,
    rc_strat: RcStrategy,
    gc_kind: GcKind,
    array_kind: ArrayKind,
    progress: ProgressMode,
}

fn parse_common_args(matches: &ArgMatches) -> CommonArgs {
    let purity_mode = if matches.get_flag("no-check-purity") {
        PurityMode::Unchecked
    } else {
        PurityMode::Checked
    };

    let llvm_opt_level = match matches.get_one::<i64>("llvm-opt-level").unwrap() {
        0 => OptimizationLevel::None,
        1 => OptimizationLevel::Less,
        2 => OptimizationLevel::Default,
        3 => OptimizationLevel::Aggressive,
        _ => unreachable!(),
    };

    let defunc_mode = parse_defunc_mode(matches.get_one::<String>("defunc-mode").unwrap());
    let rc_strat = parse_rc_strat(matches.get_one::<String>("rc-strat").unwrap());
    let gc_kind = parse_gc_kind(matches.get_one::<String>("gc-kind").unwrap());
    let array_kind = parse_array_kind(matches.get_one::<String>("array-kind").unwrap());

    let progress = if matches.get_flag("progress") {
        ProgressMode::Visible
    } else {
        ProgressMode::Hidden
    };

    CommonArgs {
        purity_mode,
        llvm_opt_level,
        defunc_mode,
        rc_strat,
        gc_kind,
        array_kind,
        progress,
    }
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
                    .register_common_args()
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
                        Arg::new("output-path")
                            .short('o')
                            .long("output-path")
                            .help("Place the output executable at this path.")
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
                    .register_common_args()
            )
            .get_matches();

        if let Some(matches) = matches.subcommand_matches("run") {
            let src_path = matches
                .get_one::<String>("src-path")
                .unwrap()
                .to_owned()
                .into();

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

            let CommonArgs {
                purity_mode,
                llvm_opt_level,
                defunc_mode,
                rc_strat,
                gc_kind,
                array_kind,
                progress,
            } = parse_common_args(matches);

            let run_config = RunConfig {
                src_path,
                purity_mode,
                mode,
                pass_options: PassOptions {
                    defunc_mode,
                    rc_strat,
                    array_kind,
                    gc_kind,
                },
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

            let target = if matches.get_flag("wasm") {
                TargetConfig::Llvm(LlvmConfig::Wasm)
            } else if matches.get_flag("sml") {
                TargetConfig::Ml(MlConfig::Sml)
            } else if matches.get_flag("ocaml") {
                TargetConfig::Ml(MlConfig::Ocaml)
            } else {
                TargetConfig::Llvm(LlvmConfig::Native)
            };

            let profile_syms = match matches.get_many::<String>("profile") {
                Some(values) => values.map(|val| SymbolName(val.to_owned())).collect(),
                None => Vec::new(),
            };

            let profile_record_rc = matches.get_flag("profile-record-rc");

            let CommonArgs {
                purity_mode,
                llvm_opt_level,
                defunc_mode,
                rc_strat,
                gc_kind,
                array_kind,
                progress,
            } = parse_common_args(matches);

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
                    rc_strat,
                    array_kind,
                    gc_kind,
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
