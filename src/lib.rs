#![allow(dead_code)]

pub mod cli;
pub mod file_cache;
pub mod progress_ui;
pub mod pseudoprocess;

#[macro_use]
mod util;

mod data;
mod intrinsic_config;
mod pretty_print;

mod lex;

lalrpop_mod!(parse);

mod parse_error;
mod report_error;

mod resolve;

mod check_purity;

mod report_type;
mod type_infer;

mod check_exhaustive;
mod report_pattern;

mod check_main;

mod monomorphize;

mod shield_functions;

mod lambda_lift;

mod annot_closures;

mod closure_specialize;

mod lower_closures;

mod remove_unit;

mod typecheck_first_order;

mod split_custom_types;

mod flatten;

mod guard_types;

mod annot_modes2;

mod annot_obligations;

mod annot_rcs;

mod rc_specialize2;

mod tail_call_elim;

mod lower_structures;

mod interpreter;

mod llvm_gen;

#[cfg(test)]
mod test;

use cli::PassOptions;
use lalrpop_util::lalrpop_mod;
use std::fs;
use std::io;
use std::path::Path;

#[derive(Debug)]
enum ErrorKind {
    ArtifactDirMissing,
    ResolveFailed(resolve::Error),
    PurityCheckFailed(check_purity::Error),
    TypeInferFailed(type_infer::Error),
    CheckExhaustiveFailed(check_exhaustive::Error),
    CheckMainFailed(check_main::Error),
    CreateArtifactsFailed(io::Error),
    WriteIrFailed(io::Error),
    LlvmGenFailed(llvm_gen::Error),
    WaitChildFailed(io::Error),
    ChildFailed { exit_status: Option<i32> },
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

impl Error {
    pub fn report(
        &self,
        dest: &mut impl io::Write,
        files: &file_cache::FileCache,
    ) -> io::Result<()> {
        use ErrorKind::*;
        match &self.kind {
            ArtifactDirMissing => {
                writeln!(dest, "Compilation to ML requires an artifact directory")
            }
            ResolveFailed(err) => err.report(dest, files),
            PurityCheckFailed(err) => err.report(dest, files),
            TypeInferFailed(err) => err.report(dest, files),
            CheckExhaustiveFailed(err) => err.report(dest, files),
            CheckMainFailed(err) => writeln!(dest, "{}", err),
            CreateArtifactsFailed(err) => {
                writeln!(dest, "Could not create artifacts directory: {}", err)
            }
            WriteIrFailed(err) => writeln!(
                dest,
                "Could not write intermediate representation artifacts: {}",
                err
            ),
            LlvmGenFailed(err) => writeln!(dest, "{}", err),
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
        }
    }

    pub fn exit_status(&self) -> i32 {
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
    let pass_options = PassOptions {
        defunc_mode: cli::SpecializationMode::Specialize,
        rc_mode: config.rc_mode,
        mutation_mode: config.mutation_mode,
    };

    let lowered = compile_to_low_ast(
        &config.src_path,
        config.purity_mode,
        &[],
        false,
        None,
        files,
        progress_ui::ProgressMode::Hidden,
        &pass_options,
    )?;

    match config.mode {
        cli::RunMode::Compile { valgrind } => {
            Ok(llvm_gen::run(config.stdio, lowered, valgrind).map_err(ErrorKind::LlvmGenFailed)?)
        }
        cli::RunMode::Interpret => Ok(interpreter::interpret(config.stdio, lowered)),
    }
}

pub fn build(config: cli::BuildConfig, files: &mut file_cache::FileCache) -> Result<(), Error> {
    match config.target {
        cli::TargetConfig::Llvm(_) => {
            let lowered = compile_to_low_ast(
                &config.src_path,
                config.purity_mode,
                &config.profile_syms,
                config.profile_record_rc,
                config.artifact_dir.as_ref(),
                files,
                config.progress,
                &config.pass_options,
            )?;
            Ok(llvm_gen::build(lowered, &config).map_err(ErrorKind::LlvmGenFailed)?)
        }
        cli::TargetConfig::Ml(_) => match config.artifact_dir {
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
                )?;
                Ok(())
            }
        },
    }
}

fn compile_to_first_order_ast(
    src_path: &Path,
    purity_mode: cli::PurityMode,
    profile_syms: &[cli::SymbolName],
    profile_record_rc: bool,
    artifact_dir: Option<&cli::ArtifactDir>,
    files: &mut file_cache::FileCache,
    progress: progress_ui::ProgressMode,
    pass_options: &cli::PassOptions,
) -> Result<data::first_order_ast::Program, Error> {
    let resolved = resolve::resolve_program(files, src_path, profile_syms, profile_record_rc)
        .map_err(ErrorKind::ResolveFailed)?;
    // Check obvious errors and infer types
    if matches!(purity_mode, cli::PurityMode::Checked) {
        check_purity::check_purity(&resolved).map_err(ErrorKind::PurityCheckFailed)?;
    }
    let typed = type_infer::type_infer(resolved).map_err(ErrorKind::TypeInferFailed)?;
    check_exhaustive::check_exhaustive(&typed).map_err(ErrorKind::CheckExhaustiveFailed)?;
    check_main::check_main(&typed).map_err(ErrorKind::CheckMainFailed)?;

    // Ensure clean artifacts directory, if applicable
    if let Some(artifact_dir) = artifact_dir {
        fs::remove_dir_all(&artifact_dir.dir_path).map_err(ErrorKind::CreateArtifactsFailed)?;
        fs::create_dir(&artifact_dir.dir_path).map_err(ErrorKind::CreateArtifactsFailed)?;
    }

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("typed.sml"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::typed::write_sml_program(&mut out_file, &typed)
            .map_err(ErrorKind::WriteIrFailed)?;
    }

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("typed.ml"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::typed::write_ocaml_program(&mut out_file, &typed)
            .map_err(ErrorKind::WriteIrFailed)?;
    }

    let mono = monomorphize::monomorphize(typed);

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("mono.sml"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::mono::write_sml_program(&mut out_file, &mono)
            .map_err(ErrorKind::WriteIrFailed)?;
    }

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("mono.ml"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::mono::write_ocaml_program(&mut out_file, &mono)
            .map_err(ErrorKind::WriteIrFailed)?;
    }

    // let shielded = shield_functions::shield_functions(mono);

    let lifted = lambda_lift::lambda_lift(mono);

    let annot = annot_closures::annot_closures(
        lifted,
        pass_options.defunc_mode,
        progress_ui::bar(progress, "annot_closures"),
    );

    let special = closure_specialize::closure_specialize(
        annot,
        progress_ui::bar(progress, "closure_specialize"),
    );
    closure_specialize::check_patterns(&special);

    let first_order =
        lower_closures::lower_closures(special, progress_ui::bar(progress, "lower_closures"));

    typecheck_first_order::typecheck(&first_order);

    // // Temporarily disabled due to infinite recursion on `samples/recursive_array.mor`
    // TODO: Fix infinite recursion
    // let first_order = remove_unit::remove_unit(&first_order);

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("first_order.sml"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::first_order::write_sml_program(&mut out_file, &first_order)
            .map_err(ErrorKind::WriteIrFailed)?;

        let mut out_file = fs::File::create(artifact_dir.artifact_path("first_order.ml"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::first_order::write_ocaml_program(&mut out_file, &first_order)
            .map_err(ErrorKind::WriteIrFailed)?;

        let mut out_file = fs::File::create(artifact_dir.artifact_path("first_order.mor"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::first_order::write_morphic_program(&mut out_file, &first_order)
            .map_err(ErrorKind::WriteIrFailed)?;
    }

    typecheck_first_order::typecheck(&first_order);

    Ok(first_order)
}

fn compile_to_low_ast(
    src_path: &Path,
    purity_mode: cli::PurityMode,
    profile_syms: &[cli::SymbolName],
    profile_record_rc: bool,
    artifact_dir: Option<&cli::ArtifactDir>,
    files: &mut file_cache::FileCache,
    progress: progress_ui::ProgressMode,
    pass_options: &cli::PassOptions,
) -> Result<data::low_ast::Program, Error> {
    let first_order = compile_to_first_order_ast(
        src_path,
        purity_mode,
        profile_syms,
        profile_record_rc,
        artifact_dir,
        files,
        progress,
        pass_options,
    )?;

    let split = split_custom_types::split_custom_types(
        &first_order,
        progress_ui::bar(progress, "split_custom_types"),
    );

    let flat = flatten::flatten(split, progress_ui::bar(progress, "flatten"));

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("flat"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::flat::write_program(&mut out_file, &flat)
            .map_err(ErrorKind::WriteIrFailed)?;
    }

    let guarded = guard_types::guard_types(flat);

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("guarded"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::guarded::write_program(&mut out_file, &guarded)
            .map_err(ErrorKind::WriteIrFailed)?;
    }

    let interner = crate::data::mode_annot_ast2::Interner::empty();
    let mode_annot = annot_modes2::annot_modes(
        annot_modes2::Strategy::Default,
        &interner,
        guarded,
        progress_ui::bar(progress, "annot_modes"),
    );

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("mode_annot"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::mode_annot::write_program(&mut out_file, &mode_annot)
            .map_err(ErrorKind::WriteIrFailed)?;
    }

    let obligation_annot = annot_obligations::annot_obligations(
        &interner,
        mode_annot,
        progress_ui::bar(progress, "annot_obligations"),
    );

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("ob_annot"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::obligation_annot::write_program(&mut out_file, &obligation_annot)
            .map_err(ErrorKind::WriteIrFailed)?;
    }

    let rc_annot = annot_rcs::annot_rcs(
        &interner,
        obligation_annot,
        progress_ui::bar(progress, "annot_rcs"),
    );

    let rc_specialized = rc_specialize2::rc_specialize(
        rc_annot,
        rc_specialize2::Strategy::Default,
        progress_ui::bar(progress, "rc_specialize"),
    );

    let tail_rec = tail_call_elim::tail_call_elim(
        rc_specialized.clone(),
        progress_ui::bar(progress, "tail_call_elim"),
    );

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("tail_rec"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::tail::write_program(&mut out_file, &tail_rec)
            .map_err(ErrorKind::WriteIrFailed)?;
    }

    let lowered = lower_structures::lower_structures(
        tail_rec,
        progress_ui::bar(progress, "lower_structures"),
    );

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("low-ir"))
            .map_err(ErrorKind::WriteIrFailed)?;

        pretty_print::low::write_program(&mut out_file, &lowered)
            .map_err(ErrorKind::WriteIrFailed)?;
    }

    Ok(lowered)
}
