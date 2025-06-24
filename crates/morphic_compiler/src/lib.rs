#![allow(dead_code)]

#[cfg(test)]
mod test;

pub mod cli;

use morphic_backend::{compile_to_low_ast, interpreter, code_gen, BuildConfig};
use morphic_common::config as cfg;
use morphic_common::report_error::Reportable;
use morphic_common::{file_cache, progress_ui, pseudoprocess};
use morphic_frontend::compile_to_first_order_ast;
use std::io;

#[derive(Debug)]
enum ErrorKind {
    ArtifactDirMissing,
    WaitChildFailed(io::Error),
    ChildFailed { exit_status: Option<i32> },
    FrontendError(morphic_frontend::error::Error),
    BackendError(morphic_backend::error::Error),
}

// This type is separate from 'ErrorKind' because enums cannot have private variants, and we don't
// want to expose the internal compiler error types appearing in the variants of 'ErrorKind'.
#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
}

impl From<ErrorKind> for Error {
    fn from(kind: ErrorKind) -> Self {
        Error { kind }
    }
}

impl Reportable for Error {
    fn report(&self, dest: &mut impl io::Write, files: &file_cache::FileCache) -> io::Result<()> {
        use ErrorKind::*;
        match &self.kind {
            ArtifactDirMissing => {
                writeln!(dest, "Compilation to ML requires an artifact directory")
            }
            WaitChildFailed(err) => writeln!(dest, "Could not execute compiled program: {}", err),
            ChildFailed {
                exit_status: Some(_),
            } => {
                // When the child program fails with an exit code, it presumably displays its own
                // error message.
                Ok(())
            }
            ChildFailed { exit_status: None } => writeln!(
                dest,
                "Program terminated due to signal.  This probably indicates a SIGTERM or segfault."
            ),
            FrontendError(err) => err.report(dest, files),
            BackendError(err) => err.report(dest, files),
        }
    }

    fn exit_status(&self) -> i32 {
        match &self.kind {
            &ErrorKind::ChildFailed {
                exit_status: Some(status),
            } => status,
            _ => 1,
        }
    }
}

pub fn handle_config(config: cli::Config, files: &mut file_cache::FileCache) -> Result<(), Error> {
    match config {
        cli::Config::RunConfig(run_config) => {
            let child = run(run_config, files)?;
            let exit_status = child.wait().map_err(ErrorKind::WaitChildFailed)?;
            match exit_status {
                pseudoprocess::ExitStatus::Success => Ok(()),
                pseudoprocess::ExitStatus::Failure(exit_status) => {
                    Err(ErrorKind::ChildFailed { exit_status }.into())
                }
            }
        }

        cli::Config::BuildConfig(build_config) => build(build_config, files),
    }
}

pub fn run(
    config: cli::RunConfig,
    files: &mut file_cache::FileCache,
) -> Result<pseudoprocess::Child, Error> {
    let pass_options = cfg::PassOptions {
        defunc_mode: cfg::SpecializationMode::Specialize,
        rc_strat: config.rc_strat,
    };

    let first_order = compile_to_first_order_ast(
        &config.src_path,
        config.purity_mode,
        &[],
        false,
        None,
        files,
        progress_ui::ProgressMode::Hidden,
        &pass_options,
    )
    .map_err(ErrorKind::FrontendError)?;
    let lowered = compile_to_low_ast(
        first_order,
        None,
        progress_ui::ProgressMode::Hidden,
        &pass_options,
    )
    .map_err(ErrorKind::BackendError)?;

    match config.mode {
        cli::RunMode::Compile { valgrind } => {
            Ok(code_gen::run(config.stdio, lowered, valgrind).map_err(ErrorKind::BackendError)?)
        }
        cli::RunMode::Interpret => Ok(interpreter::interpret(config.stdio, lowered)),
    }
}

pub fn build(config: BuildConfig, files: &mut file_cache::FileCache) -> Result<(), Error> {
    match config.target {
        cfg::TargetConfig::Llvm(_) => {
            let first_order = compile_to_first_order_ast(
                &config.src_path,
                config.purity_mode,
                &config.profile_syms,
                config.profile_record_rc,
                config.artifact_dir.as_ref(),
                files,
                config.progress,
                &config.pass_options,
            )
            .map_err(ErrorKind::FrontendError)?;
            let lowered = compile_to_low_ast(
                first_order,
                config.artifact_dir.as_ref(),
                config.progress,
                &config.pass_options,
            )
            .map_err(ErrorKind::BackendError)?;
            Ok(code_gen::build(lowered, &config).map_err(ErrorKind::BackendError)?)
        }
        cfg::TargetConfig::Ml(_) => match config.artifact_dir {
            None => Err(Error {
                kind: ErrorKind::ArtifactDirMissing,
            }),
            Some(_) => {
                compile_to_first_order_ast(
                    &config.src_path,
                    config.purity_mode,
                    &config.profile_syms,
                    config.profile_record_rc,
                    config.artifact_dir.as_ref(),
                    files,
                    config.progress,
                    &config.pass_options,
                )
                .map_err(ErrorKind::FrontendError)?;
                Ok(())
            }
        },
    }
}
