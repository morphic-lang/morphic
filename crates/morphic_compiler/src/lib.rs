#![allow(dead_code)]

#[cfg(test)]
mod test;

pub mod cli;

use morphic_backend::{code_gen, interpreter};
use morphic_common::config as cfg;
use morphic_common::report_error::Reportable;
use morphic_common::{file_cache, pseudoprocess};
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
    config: cfg::RunConfig,
    files: &mut file_cache::FileCache,
) -> Result<pseudoprocess::Child, Error> {
    let first_order = morphic_frontend::compile_to_first_order_ast(
        &config.src_path,
        &[],
        cfg::ProfileMode::NoRecordRc,
        None,
        files,
        config.progress,
        config.purity_mode,
        config.defunc_mode,
    )
    .map_err(ErrorKind::FrontendError)?;
    let lowered = morphic_backend::compile_to_low_ast(
        first_order,
        None,
        config.progress,
        &config.llvm_config,
    )
    .map_err(ErrorKind::BackendError)?;

    match config.run_mode {
        cfg::RunMode::Compile { valgrind } => {
            Ok(
                code_gen::run(config.stdio, lowered, &config.llvm_config, valgrind)
                    .map_err(ErrorKind::BackendError)?,
            )
        }
        cfg::RunMode::Interpret => Ok(interpreter::interpret(config.stdio, lowered)),
    }
}

pub fn build(config: cfg::BuildConfig, files: &mut file_cache::FileCache) -> Result<(), Error> {
    match config.backend_opts {
        cfg::BackendOptions::Llvm(llvm_config) => {
            let first_order = morphic_frontend::compile_to_first_order_ast(
                &config.src_path,
                &config.profile_syms,
                config.profile_mode,
                config.artifact_dir.as_ref(),
                files,
                config.progress,
                config.purity_mode,
                config.defunc_mode,
            )
            .map_err(ErrorKind::FrontendError)?;

            let lowered = morphic_backend::compile_to_low_ast(
                first_order,
                config.artifact_dir.as_ref(),
                config.progress,
                &llvm_config,
            )
            .map_err(ErrorKind::BackendError)?;

            code_gen::build(
                lowered,
                config.artifact_dir.as_ref(),
                &config.output_path,
                config.progress,
                &llvm_config,
            )
            .map_err(ErrorKind::BackendError)?;

            Ok(())
        }
        cfg::BackendOptions::Ml(ml_config) => match ml_config.stage {
            cfg::CompilationStage::Typed => {
                let typed = morphic_frontend::compile_to_typed_ast(
                    &config.src_path,
                    &config.profile_syms,
                    config.profile_mode,
                    config.artifact_dir.as_ref(),
                    files,
                    config.progress,
                    config.purity_mode,
                )
                .map_err(ErrorKind::FrontendError)?;

                morphic_frontend::compile_typed_to_ml(
                    typed,
                    ml_config.variant,
                    config.artifact_dir.as_ref(),
                    &config.output_path,
                    config.progress,
                )
                .map_err(ErrorKind::FrontendError)?;

                Ok(())
            }
            cfg::CompilationStage::Mono => {
                let mono = morphic_frontend::compile_to_mono_ast(
                    &config.src_path,
                    &config.profile_syms,
                    config.profile_mode,
                    config.artifact_dir.as_ref(),
                    files,
                    config.progress,
                    config.purity_mode,
                )
                .map_err(ErrorKind::FrontendError)?;

                morphic_frontend::compile_mono_to_ml(
                    mono,
                    ml_config.variant,
                    config.artifact_dir.as_ref(),
                    &config.output_path,
                    config.progress,
                )
                .map_err(ErrorKind::FrontendError)?;

                Ok(())
            }
            cfg::CompilationStage::FirstOrder => {
                let first_order = morphic_frontend::compile_to_first_order_ast(
                    &config.src_path,
                    &config.profile_syms,
                    config.profile_mode,
                    config.artifact_dir.as_ref(),
                    files,
                    config.progress,
                    config.purity_mode,
                    config.defunc_mode,
                )
                .map_err(ErrorKind::FrontendError)?;

                morphic_frontend::compile_first_order_to_ml(
                    first_order,
                    ml_config.variant,
                    config.artifact_dir.as_ref(),
                    &config.output_path,
                    config.progress,
                )
                .map_err(ErrorKind::FrontendError)?;

                Ok(())
            }
        },
    }
}
