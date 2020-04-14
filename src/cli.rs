use clap::{App, AppSettings, Arg, SubCommand};
use inkwell::targets::{TargetMachine, TargetTriple};
use inkwell::OptimizationLevel;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};

use crate::pseudoprocess::Stdio;

#[derive(Clone, Debug)]
pub struct ArtifactDir {
    pub dir_path: PathBuf,
    pub filename_prefix: PathBuf,
}

#[derive(Clone, Copy, Debug)]
pub enum RunMode {
    Compile { use_valgrind: bool },
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

#[derive(Debug)]
pub struct TargetConfig {
    pub target: TargetTriple,
    pub target_cpu: String,
    pub target_features: String,
}

#[derive(Debug)]
pub struct BuildConfig {
    pub src_path: PathBuf,
    pub target: TargetConfig,
    pub llvm_opt_level: OptimizationLevel,

    pub output_path: PathBuf,
    pub artifact_dir: Option<ArtifactDir>,
}

#[derive(Debug)]
pub enum Config {
    RunConfig(RunConfig),
    BuildConfig(BuildConfig),
}

pub fn native_target_config() -> TargetConfig {
    TargetConfig {
        target: TargetMachine::get_default_triple(),
        target_cpu: TargetMachine::get_host_cpu_name().to_string(),
        target_features: TargetMachine::get_host_cpu_features().to_string(),
    }
}

pub fn default_llvm_opt_level() -> OptimizationLevel {
    // TODO: Set this to 'Aggressive' once we fix the undefined behavior revealed by compiling with
    // full optimizations.
    OptimizationLevel::None
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
                        Arg::with_name("output-path")
                            .short("o")
                            .long("output-path")
                            .help("Place the output executable at this path.")
                            .takes_value(true),
                    ),
            )
            .get_matches();

        if let Some(matches) = matches.subcommand_matches("run") {
            let src_path = matches.value_of_os("src-path").unwrap().to_owned().into();

            let mode = if matches.is_present("interpret") {
                RunMode::Interpret
            } else {
                RunMode::Compile {
                    use_valgrind: matches.is_present("valgrind"),
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
                // TargetConfig {
                //     target: TargetTriple::create("wasm32-unknown-unknown-wasm"),
                //     target_cpu: "".to_owned(),
                //     target_features: "".to_owned(),
                // }
                unimplemented!("wasm support is an illusion")
            } else {
                native_target_config()
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

            let build_config = BuildConfig {
                src_path,
                target,
                llvm_opt_level,
                output_path: output_path.into(),
                artifact_dir,
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
}

impl ArtifactDir {
    pub fn artifact_path(&self, extension: &(impl AsRef<OsStr> + ?Sized)) -> PathBuf {
        self.dir_path
            .join(self.filename_prefix.with_extension(extension))
    }
}
