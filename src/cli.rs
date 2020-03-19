use clap::{App, AppSettings, Arg, SubCommand};
use inkwell::targets::{TargetMachine, TargetTriple};
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

    pub output_path: PathBuf,
    pub artifact_dir: Option<ArtifactDir>,
}

#[derive(Debug)]
pub enum Config {
    RunConfig(RunConfig),
    BuildConfig(BuildConfig),
}

pub fn default_target_config() -> TargetConfig {
    TargetConfig {
        target: TargetMachine::get_default_triple(),
        target_cpu: TargetMachine::get_host_cpu_name().to_string(),
        target_features: TargetMachine::get_host_cpu_features().to_string(),
    }
}

impl Config {
    pub fn from_args() -> Self {
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
                        Arg::with_name("target")
                            .long("target")
                            .help(
                                "Specify the architecture to compile for as a target triple. The \
                                 target should have the format '<arch><sub>-<vendor>-<sys>-<abi>'. \
                                 If 'unknown' is specified for a component for the target, default \
                                 values will be selected. If a 'target' is specified, a \
                                 'target-cpu' and 'target-features' should also be specified for \
                                 performant generated code, since, in this case, they cannot be \
                                 determined automatically",
                            )
                            .takes_value(true),
                    )
                    .arg(
                        Arg::with_name("target-cpu")
                            .long("target-cpu")
                            .help("Specify a cpu for the target.")
                            .takes_value(true),
                    )
                    .arg(
                        Arg::with_name("target-features")
                            .long("target-features")
                            .help(
                                "Specify a list of features for the target. The list should have \
                                 the format '(+|-)<feature>,...', where '+' specifies that a \
                                 feature should be enabled and '-' specifies that a feature should \
                                 be disabled.",
                            )
                            .takes_value(true),
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

            let specified_output_path = matches
                .value_of_os("output-path")
                .map(|s| s.to_owned().into());

            let specified_target = matches.value_of("target").map(TargetTriple::create);
            let specified_target_cpu = matches.value_of("target-cpu").map(|s| s.to_owned());
            let specified_target_features =
                matches.value_of("target-features").map(|s| s.to_owned());

            let target = if let Some(target) = specified_target {
                TargetConfig {
                    target,
                    target_cpu: specified_target_cpu.unwrap_or("".to_owned()),
                    target_features: specified_target_features.unwrap_or("".to_owned()),
                }
            } else {
                let mut target = default_target_config();
                if let Some(cpu) = specified_target_cpu {
                    target.target_cpu = cpu;
                }
                if let Some(features) = specified_target_features {
                    target.target_features = features;
                }
                target
            };

            let output_path = specified_output_path.unwrap_or(
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
