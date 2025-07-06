use clap::builder::{styling, EnumValueParser};
use clap::{Arg, ArgAction, ArgMatches, Command};
use inkwell::OptimizationLevel;
use morphic_common::config::{self as cfg, ValueEnumExt};
use morphic_common::progress_ui::ProgressMode;
use morphic_common::pseudoprocess::{Stdio, ValgrindConfig};
use std::ffi::OsString;
use std::path::{Path, PathBuf};

const LLVM_BACKEND_OPTS: &[&str] = &[
    "rc-strat",
    "gc-kind",
    "array-kind",
    "llvm-opt-level",
    "wasm",
];

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
            Arg::new("defunc-mode")
                .long("defunc-mode")
                .help("Set whether or not to specialize during defunctionalization.")
                .value_parser(EnumValueParser::<cfg::DefuncMode>::new())
                .default_value(cfg::DefuncMode::default_as_str()),
        )
        .arg(
            Arg::new("rc-strat")
                .long("rc-strat")
                .help("Set the reference count elision algorithm to use.")
                .value_parser(EnumValueParser::<cfg::RcStrategy>::new())
                .default_value(cfg::RcStrategy::default_as_str()),
        )
        .arg(
            Arg::new("gc-kind")
                .long("gc-kind")
                .help(
                    "Set the garbage collector to use. The best choice is 'rc', which performs \
                    reference counting subject to '--rc-strat'. 'bwd' is the Boehm-Demers-Weiser \
                    conservative collector.",
                )
                .value_parser(EnumValueParser::<cfg::GcKind>::new())
                .default_value(cfg::GcKind::default_as_str()),
        )
        .arg(
            Arg::new("array-kind")
                .long("array-kind")
                .help(
                    "Set the kind of array to use. 'cow' is a copy-on-write array that takes \
                    advantage of the RC-1 optimization when reference counting is turned on. \
                    'persistent' is a Clojure-style persistent array that always has O(log n) \
                    updates, but with a large constant factor.",
                )
                .value_parser(EnumValueParser::<cfg::ArrayKind>::new())
                .default_value(cfg::ArrayKind::default_as_str()),
        )
        .arg(
            Arg::new("llvm-opt-level")
                .long("llvm-opt-level")
                .help("Set the optimization level used by the LLVM backend.")
                .value_parser(0..=3)
                .default_value((cfg::default_llvm_opt_level() as i64).to_string()),
        )
        .arg(
            Arg::new("progress")
                .long("progress")
                .action(ArgAction::SetTrue)
                .help("Set whether or not to show progress."),
        )
    }
}

struct CommonArgs {
    purity_mode: cfg::PurityMode,
    llvm_opt_level: OptimizationLevel,
    defunc_mode: cfg::DefuncMode,
    rc_strat: cfg::RcStrategy,
    gc_kind: cfg::GcKind,
    array_kind: cfg::ArrayKind,
    progress: ProgressMode,
}

fn parse_common_args(matches: &ArgMatches) -> CommonArgs {
    let purity_mode = if matches.get_flag("no-check-purity") {
        cfg::PurityMode::Unchecked
    } else {
        cfg::PurityMode::Checked
    };

    let llvm_opt_level = match matches.get_one::<i64>("llvm-opt-level").unwrap() {
        0 => OptimizationLevel::None,
        1 => OptimizationLevel::Less,
        2 => OptimizationLevel::Default,
        3 => OptimizationLevel::Aggressive,
        _ => unreachable!(),
    };

    let defunc_mode = *matches.get_one::<cfg::DefuncMode>("defunc-mode").unwrap();
    let rc_strat = *matches.get_one::<cfg::RcStrategy>("rc-strat").unwrap();
    let gc_kind = *matches.get_one::<cfg::GcKind>("gc-kind").unwrap();
    let array_kind = *matches.get_one::<cfg::ArrayKind>("array-kind").unwrap();

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

#[derive(Debug)]
pub enum Config {
    RunConfig(cfg::RunConfig),
    BuildConfig(cfg::BuildConfig),
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
                    .about("Compile and run a program from source")
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
                    .about("Build a program from source (provides more extensive options than 'run')")
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
                            .conflicts_with_all(LLVM_BACKEND_OPTS)
                            .action(ArgAction::SetTrue)
                            .help("Compile to SML instead of a native binary."),
                    )
                    .arg(
                        Arg::new("ocaml")
                            .long("ocaml")
                            .conflicts_with_all(LLVM_BACKEND_OPTS)
                            .conflicts_with("sml")
                            .action(ArgAction::SetTrue)
                            .help("Compile to OCaml instead of a native binary."),
                    )
                    .arg(
                        Arg::new("ml-stage")
                            .long("ml-stage")
                            .conflicts_with_all(LLVM_BACKEND_OPTS)
                            .help(
                                "The Morphic compilation stage at which to emit SML/OCaml code \
                                if compiling with '--sml' or '--ocaml'."
                            )
                            .value_parser(EnumValueParser::<cfg::CompilationStage>::new())
                            .default_value(cfg::CompilationStage::default_as_str()),
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

            let run_mode = if matches.get_flag("interpret") {
                cfg::RunMode::Interpret
            } else {
                cfg::RunMode::Compile {
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

            let llvm_config = cfg::LlvmConfig {
                rc_strat,
                gc_kind,
                array_kind,
                opt_level: llvm_opt_level,
                target: cfg::TargetConfig::Native,
            };

            let run_config = cfg::RunConfig {
                src_path,
                progress,
                purity_mode,
                defunc_mode,
                llvm_config,
                run_mode,
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
                Some(cfg::ArtifactDir {
                    dir_path: artifact_dir.into(),
                    filename_prefix: output_path.file_name().unwrap().into(),
                })
            } else {
                None
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

            let profile_syms = match matches.get_many::<String>("profile") {
                Some(values) => values.map(|val| cfg::SymbolName(val.to_owned())).collect(),
                None => Vec::new(),
            };

            let profile_mode = if matches.get_flag("profile-record-rc") {
                cfg::ProfileMode::RecordRc
            } else {
                cfg::ProfileMode::NoRecordRc
            };

            if matches.get_flag("sml") {
                let stage = *matches
                    .get_one::<cfg::CompilationStage>("ml-stage")
                    .unwrap();

                let build_config = cfg::BuildConfig {
                    src_path,
                    progress,
                    purity_mode,
                    defunc_mode,
                    backend_opts: cfg::BackendOptions::Ml(cfg::MlConfig {
                        variant: cfg::MlVariant::Sml,
                        stage,
                    }),
                    profile_syms,
                    profile_mode,
                    output_path,
                    artifact_dir,
                };

                return Self::BuildConfig(build_config);
            } else if matches.get_flag("ocaml") {
                let stage = *matches
                    .get_one::<cfg::CompilationStage>("ml-stage")
                    .unwrap();

                let build_config = cfg::BuildConfig {
                    src_path,
                    progress,
                    purity_mode,
                    defunc_mode,
                    backend_opts: cfg::BackendOptions::Ml(cfg::MlConfig {
                        variant: cfg::MlVariant::OCaml,
                        stage,
                    }),
                    profile_syms,
                    profile_mode,
                    output_path,
                    artifact_dir,
                };

                return Self::BuildConfig(build_config);
            } else {
                let target = if matches.get_flag("wasm") {
                    cfg::TargetConfig::Wasm
                } else {
                    cfg::TargetConfig::Native
                };

                let backend_opts = cfg::BackendOptions::Llvm(cfg::LlvmConfig {
                    rc_strat,
                    gc_kind,
                    array_kind,
                    opt_level: llvm_opt_level,
                    target,
                });

                let build_config = cfg::BuildConfig {
                    src_path,
                    progress,
                    purity_mode,
                    defunc_mode,
                    backend_opts,
                    profile_syms,
                    profile_mode,
                    output_path,
                    artifact_dir,
                };

                return Self::BuildConfig(build_config);
            }
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

    pub fn artifact_dir(&self) -> Option<&cfg::ArtifactDir> {
        match self {
            Self::RunConfig(_) => None,
            Self::BuildConfig(build_config) => build_config.artifact_dir.as_ref(),
        }
    }

    pub fn profile_syms(&self) -> &[cfg::SymbolName] {
        match self {
            Self::RunConfig(_) => &[],
            Self::BuildConfig(build_config) => &build_config.profile_syms,
        }
    }
}
