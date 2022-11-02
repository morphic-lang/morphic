use clap::{App, AppSettings, Arg, SubCommand};
use inkwell::OptimizationLevel;
use std::ffi::OsStr;
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

#[derive(Clone, Debug)]
pub struct RunConfig {
    pub src_path: PathBuf,
    pub mode: RunMode,

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

#[derive(Debug)]
pub struct BuildConfig {
    pub src_path: PathBuf,
    pub profile_syms: Vec<SymbolName>,

    pub target: TargetConfig,
    pub llvm_opt_level: OptimizationLevel,

    pub output_path: PathBuf,
    pub artifact_dir: Option<ArtifactDir>,
    pub progress: ProgressMode,

    pub defunc_mode: SpecializationMode,
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
        // We need to create this string at the top of this function because clap's cli builder
        // can't take ownership of strings.
        let default_opt_level_string = (default_llvm_opt_level() as u32).to_string();

        let matches = App::new(clap::crate_name!())
            .version(clap::crate_version!())
            .about(clap::crate_description!())
            .setting(AppSettings::SubcommandRequiredElseHelp)
            .setting(AppSettings::ColoredHelp)
            .subcommand(
                SubCommand::with_name("run")
                    .about("Compiles and runs a program from source")
                    .setting(AppSettings::ColoredHelp)
                    .setting(AppSettings::NextLineHelp)
                    .arg(
                        Arg::with_name("src-path")
                            .help("Specify the source file for compilation.")
                            .required(true)
                            .index(1),
                    )
                    .arg(
                        Arg::with_name("valgrind")
                            .long("valgrind")
                            .conflicts_with("interpret")
                            .help("Run the compiler output program inside of valgrind."),
                    )
                    .arg(
                        Arg::with_name("valgrind-ignore-leaks")
                            .long("valgrind-ignore-leaks")
                            .requires("valgrind")
                            .help("Ignore memory leaks when running under valgrind."),
                    )
                    .arg(Arg::with_name("interpret").long("interpret").help(
                        "Run the program using the reference interpreter instead of generating \
                         LLVM and running a fully compiled executable.",
                    )),
            )
            .subcommand(
                SubCommand::with_name("build")
                    .about("Builds a program from source")
                    .setting(AppSettings::ColoredHelp)
                    .setting(AppSettings::NextLineHelp)
                    .arg(
                        Arg::with_name("src-path")
                            .help("Specify the source file for compilation.")
                            .required(true)
                            .index(1),
                    )
                    .arg(
                        Arg::with_name("emit-artifacts")
                            .long("emit-artifacts")
                            .short("a")
                            .help(
                                "Emit compilation artifacts including the generated LLVM IR and \
                                object file. Artifacts will be placed in a directory whose name is \
                                derived from the generated executable's name.",
                            ),
                    )
                    .arg(
                        Arg::with_name("llvm-opt-level")
                            .long("llvm-opt-level")
                            .help("Set the optimization level used by the LLVM backend.")
                            .takes_value(true)
                            .possible_values(&["0", "1", "2", "3"])
                            .default_value(&default_opt_level_string),
                    )
                    .arg(
                        Arg::with_name("wasm")
                            .long("wasm")
                            .help("Compile to wasm instead of a native binary."),
                    )
                    .arg(
                        Arg::with_name("sml")
                            .long("sml")
                            .help("Compile to SML instead of a native binary."),
                    )
                    .arg(
                        Arg::with_name("ocaml")
                            .long("ocaml")
                            .help("Compile to OCaml instead of a native binary."),
                    )
                    .arg(
                        Arg::with_name("output-path")
                            .short("o")
                            .long("output-path")
                            .help("Place the output executable at this path.")
                            .takes_value(true),
                    )
                    .arg(
                        // If you ever change the CLI syntax for profiling, you need to grep for
                        // "--profile" elsewhere in the project and adjust things as necessary,
                        // because several error message strings in other modules mention the
                        // argument syntax.
                        Arg::with_name("profile")
                            .long("profile")
                            .help(
                                "Instrument a function to measure performance statistics. To use \
                                this instrumentation, run the compiled program with the \
                                environment variable MORPHIC_PROFILE_PATH set. When the program \
                                exits, it will write a JSON file to this path containing \
                                performance data for every '--profile'd function.",
                            )
                            .multiple(true)
                            .number_of_values(1),
                    )
                    .arg(
                        Arg::with_name("defunc-mode")
                            .long("defunc-mode")
                            .help("Set whether or not to specialize during defunctionalization")
                            .possible_values(&["specialize", "single"])
                            .default_value("specialize"),
                    )
                    .arg(
                        Arg::with_name("progress")
                            .long("progress")
                            .help("Set whether or not to show progress"),
                    ),
            )
            .get_matches();

        if let Some(matches) = matches.subcommand_matches("run") {
            let src_path = matches.value_of_os("src-path").unwrap().to_owned().into();

            let mode = if matches.is_present("interpret") {
                RunMode::Interpret
            } else {
                RunMode::Compile {
                    valgrind: if matches.is_present("valgrind") {
                        Some(ValgrindConfig {
                            leak_check: !matches.is_present("valgrind-ignore-leaks"),
                        })
                    } else {
                        None
                    },
                }
            };

            let run_config = RunConfig {
                src_path,
                mode,
                stdio: Stdio::Inherit,
            };
            return Self::RunConfig(run_config);
        }

        if let Some(matches) = matches.subcommand_matches("build") {
            let src_path: PathBuf = matches.value_of_os("src-path").unwrap().to_owned().into();

            let target = if matches.is_present("wasm") {
                TargetConfig::Llvm(LlvmConfig::Wasm)
            } else if matches.is_present("sml") {
                TargetConfig::Ml(MlConfig::Sml)
            } else if matches.is_present("ocaml") {
                TargetConfig::Ml(MlConfig::Ocaml)
            } else {
                TargetConfig::Llvm(LlvmConfig::Native)
            };

            let llvm_opt_level = match matches.value_of("llvm-opt-level").unwrap() {
                "0" => OptimizationLevel::None,
                "1" => OptimizationLevel::Less,
                "2" => OptimizationLevel::Default,
                "3" => OptimizationLevel::Aggressive,
                _ => unreachable!(),
            };

            let output_path = matches
                .value_of_os("output-path")
                .map(|s| s.to_owned().into())
                .unwrap_or(
                    std::env::current_dir()
                        .unwrap()
                        .join(src_path.file_name().unwrap())
                        .with_extension(""),
                );

            let artifact_dir = if matches.is_present("emit-artifacts") {
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

            let profile_syms = match matches.values_of("profile") {
                Some(values) => values.map(|val| SymbolName(val.to_owned())).collect(),
                None => Vec::new(),
            };

            let defunc_mode = match matches.value_of("defunc-mode").unwrap() {
                "specialize" => SpecializationMode::Specialize,
                "single" => SpecializationMode::Single,
                _ => unreachable!(),
            };

            let progress = if matches.is_present("progress") {
                ProgressMode::Visible
            } else {
                ProgressMode::Hidden
            };

            let build_config = BuildConfig {
                src_path,
                profile_syms,
                target,
                llvm_opt_level,
                output_path: output_path.into(),
                artifact_dir,
                defunc_mode,
                progress,
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
