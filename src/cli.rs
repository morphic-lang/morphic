use clap::{App, Arg};
use failure::Fail;
use inkwell::targets::TargetMachine;
use std::path::PathBuf;

#[derive(Clone, Debug, Fail)]
#[fail(display = "Could not generate compiler configuration")]
pub struct Error;

#[derive(Clone, Debug)]
pub struct Config {
    pub src_path: PathBuf,
    pub target: String,
    pub target_cpu: String,
    pub target_features: String,
}

impl Config {
    pub fn from_args() -> Result<Self, Error> {
        let src_path_help = "Specify the source file for compilation.";

        let target_help = "Specify the architecture to compile for (as a 'target triple'). The \
                           target should have the format '<arch><sub>-<vendor>-<sys>-<abi>'. If \
                           'unknown' is specified for a component for the target, default values \
                           will be selected. If a 'target' is specified, a 'target-cpu' and \
                           'target-features' should likely also be specified for performant \
                           generated code";

        let target_cpu_help = "Specify the cpu to compile for.";

        let target_features_help = "Specify a list of features for the target. The list should \
                                    have the format '(+|-)<feature>,...', where '+' specifies \
                                    that a feature should be enabled and '-' specifies that a \
                                    feature should be disabled.";

        let matches = App::new("opt-proto")
            .arg(
                Arg::with_name("src_path")
                    .help(src_path_help)
                    .required(true)
                    .index(1),
            )
            .arg(
                Arg::with_name("target")
                    .long("target")
                    .help(target_help)
                    .takes_value(true),
            )
            .arg(
                Arg::with_name("target-cpu")
                    .long("target-cpu")
                    .help(target_cpu_help)
                    .takes_value(true),
            )
            .arg(
                Arg::with_name("target-features")
                    .long("target-features")
                    .help(target_features_help)
                    .takes_value(true),
            )
            .get_matches();

        let src_path = matches.value_of_os("src_path").unwrap().to_owned().into();

        let target = matches
            .value_of("target")
            .unwrap_or(TargetMachine::get_default_triple().to_str().unwrap())
            .to_owned();

        let target_cpu = matches
            .value_of("target-cpu")
            .map(|s| s.to_owned())
            .unwrap_or(if matches.value_of("target").is_some() {
                "".to_owned()
            } else {
                TargetMachine::get_host_cpu_name().to_string()
            });

        let target_features = matches
            .value_of("target-features")
            .map(|s| s.to_owned())
            .unwrap_or(if matches.value_of("target").is_some() {
                "".to_owned()
            } else {
                TargetMachine::get_host_cpu_features().to_string()
            });

        Ok(Self {
            src_path,
            target,
            target_cpu,
            target_features,
        })
    }
}
