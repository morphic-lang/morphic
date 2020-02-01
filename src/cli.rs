use clap::{App, AppSettings, Arg, SubCommand};
use failure::Fail;
use inkwell::targets::TargetMachine;
use std::path::PathBuf;

#[derive(Clone, Debug, Fail)]
#[fail(display = "Invalid compiler options: {}", _0)]
pub struct Error(String);

#[derive(Clone, Debug)]
pub struct BuildConfig {
    pub output_path: PathBuf,
    pub artifact_dir: Option<PathBuf>,
}

#[derive(Clone, Debug)]
pub enum SubCommandConfig {
    RunConfig(),
    BuildConfig(BuildConfig),
}

#[derive(Clone, Debug)]
pub struct Config {
    pub src_path: PathBuf,
    pub target: String,
    pub target_cpu: String,
    pub target_features: String,
    pub sub_command_config: SubCommandConfig,
}

impl Config {
    pub fn from_args() -> Result<Self, Error> {
        let matches = App::new(clap::crate_name!())
            .version(clap::crate_version!())
            .about(clap::crate_description!())
            .setting(AppSettings::SubcommandRequiredElseHelp)
            .subcommand(
                SubCommand::with_name("run")
                    .about("Compiles and runs a program from source")
                    .arg(
                        Arg::with_name("src-path")
                            .help("Specify the source file for compilation.")
                            .required(true)
                            .index(1),
                    ),
            )
            .subcommand(
                SubCommand::with_name("build")
                    .about("Builds a program from source")
                    .arg(
                        Arg::with_name("src-path")
                            .help("Specify the source file for compilation.")
                            .required(true)
                            .index(1),
                    )
                    .arg(
                        Arg::with_name("emit-artifacts")
                            .long("emit-artifacts")
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

            return Ok(Self {
                src_path,
                target: TargetMachine::get_default_triple().to_string(),
                target_cpu: TargetMachine::get_host_cpu_name().to_string(),
                target_features: TargetMachine::get_host_cpu_features().to_string(),
                sub_command_config: SubCommandConfig::RunConfig(),
            });
        }

        if let Some(matches) = matches.subcommand_matches("build") {
            let src_path: PathBuf = matches.value_of_os("src-path").unwrap().to_owned().into();

            let specified_output_path = matches
                .value_of_os("output-path")
                .map(|s| s.to_owned().into());
            let specified_target = matches.value_of("target").map(|s| s.to_owned());
            let specified_target_cpu = matches.value_of("target-cpu").map(|s| s.to_owned());
            let specified_target_features =
                matches.value_of("target-features").map(|s| s.to_owned());

            let (target, target_cpu, target_features) = if let Some(target) = specified_target {
                (
                    target,
                    specified_target_cpu.unwrap_or("".to_owned()),
                    specified_target_features.unwrap_or("".to_owned()),
                )
            } else {
                (
                    TargetMachine::get_default_triple().to_string(),
                    specified_target_cpu.unwrap_or(TargetMachine::get_host_cpu_name().to_string()),
                    specified_target_features
                        .unwrap_or(TargetMachine::get_host_cpu_features().to_string()),
                )
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
                Some(artifact_dir.into())
            } else {
                None
            };
            let build_config = BuildConfig {
                output_path: output_path.into(),
                artifact_dir,
            };

            return Ok(Self {
                src_path,
                target,
                target_cpu,
                target_features,
                sub_command_config: SubCommandConfig::BuildConfig(build_config),
            });
        }

        // Clap will exit our program gracefully if no subcommand is provided.
        // Therefore, one of the above if statements will always trigger.
        unreachable!();
    }
}
