#![allow(dead_code)]

mod annot_closures;
mod check_exhaustive;
mod check_main;
mod check_purity;
mod closure_specialize;
mod lambda_lift;
mod lex;
mod lower_closures;
mod monomorphize;
mod parse_error;
mod remove_unit;
mod report_pattern;
mod report_type;
mod resolve;
mod shield_functions;
mod type_infer;
mod typecheck_first_order;

pub mod error;

use lalrpop_util::lalrpop_mod;
use morphic_common::util::progress_logger::{ProgressLogger, ProgressSession};
lalrpop_mod!(parse);

use crate::error::Error;
use find_tool::finders;
use morphic_common::{config as cfg, data, file_cache, pretty_print, progress_ui};
use std::path::Path;
use std::{fs, io, process};

pub fn compile_to_typed_ast(
    src_path: &Path,
    profile_syms: &[cfg::SymbolName],
    profile_mode: cfg::ProfileMode,
    artifact_dir: Option<&cfg::ArtifactDir>,
    files: &mut file_cache::FileCache,
    _progress: progress_ui::ProgressMode,
    purity_mode: cfg::PurityMode,
) -> Result<data::typed_ast::Program, Error> {
    // Ensure clean artifacts directory, if applicable
    if let Some(artifact_dir) = artifact_dir {
        fs::remove_dir_all(&artifact_dir.dir_path).map_err(Error::CreateArtifactsFailed)?;
        fs::create_dir(&artifact_dir.dir_path).map_err(Error::CreateArtifactsFailed)?;
    }

    let resolved = resolve::resolve_program(files, src_path, profile_syms, profile_mode)
        .map_err(Error::ResolveFailed)?;

    // Check obvious errors and infer types
    if purity_mode == cfg::PurityMode::Checked {
        check_purity::check_purity(&resolved).map_err(Error::PurityCheckFailed)?;
    }
    let typed = type_infer::type_infer(resolved).map_err(Error::TypeInferFailed)?;
    check_exhaustive::check_exhaustive(&typed).map_err(Error::CheckExhaustiveFailed)?;
    check_main::check_main(&typed).map_err(Error::CheckMainFailed)?;

    Ok(typed)
}

pub fn compile_to_mono_ast(
    src_path: &Path,
    profile_syms: &[cfg::SymbolName],
    profile_mode: cfg::ProfileMode,
    artifact_dir: Option<&cfg::ArtifactDir>,
    files: &mut file_cache::FileCache,
    progress: progress_ui::ProgressMode,
    purity_mode: cfg::PurityMode,
) -> Result<data::mono_ast::Program, Error> {
    let typed = compile_to_typed_ast(
        src_path,
        profile_syms,
        profile_mode,
        artifact_dir,
        files,
        progress,
        purity_mode,
    )?;

    Ok(monomorphize::monomorphize(typed))
}

pub fn compile_to_first_order_ast(
    src_path: &Path,
    profile_syms: &[cfg::SymbolName],
    profile_mode: cfg::ProfileMode,
    artifact_dir: Option<&cfg::ArtifactDir>,
    files: &mut file_cache::FileCache,
    progress: progress_ui::ProgressMode,
    purity_mode: cfg::PurityMode,
    defunc_mode: cfg::DefuncMode,
) -> Result<data::first_order_ast::Program, Error> {
    let mono = compile_to_mono_ast(
        src_path,
        profile_syms,
        profile_mode,
        artifact_dir,
        files,
        progress,
        purity_mode,
    )?;

    let shielded = shield_functions::shield_functions(mono);

    let lifted = lambda_lift::lambda_lift(shielded);

    let annot = annot_closures::annot_closures(
        lifted,
        defunc_mode,
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
        let mut out_file = fs::File::create(artifact_dir.artifact_path("first_order.mor"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print::first_order::write_morphic_program(&mut out_file, &first_order)
            .map_err(Error::WriteIrFailed)?;
    }

    typecheck_first_order::typecheck(&first_order);

    Ok(first_order)
}

fn run_mlton(
    output_path: &Path,
    input_path: &Path,
    progress: progress_ui::ProgressMode,
) -> Result<(), Error> {
    let mlton = finders::find_mlton().map_err(Error::FindMltonFailed)?;

    let progress_bar = progress_ui::bar(progress, "mlton").start_session(None);
    let mlton_output = process::Command::new(mlton.path())
        .arg("-default-type")
        .arg("int64")
        .arg("-output")
        .arg(output_path)
        .arg(input_path)
        .output()
        .map_err(Error::RunMltonFailed)?;
    progress_bar.finish();

    if mlton_output.status.success() {
        Ok(())
    } else {
        let err = String::from_utf8_lossy(&mlton_output.stderr);
        Err(Error::RunMltonFailed(io::Error::other(err)))
    }
}

fn run_ocamlopt(
    output_path: &Path,
    input_path: &Path,
    progress: progress_ui::ProgressMode,
) -> Result<(), Error> {
    let ocamlopt = finders::find_ocamlopt().map_err(Error::FindOCamloptFailed)?;

    let progress_bar = progress_ui::bar(progress, "ocamlopt").start_session(None);
    let ocaml_output = process::Command::new(ocamlopt.path())
        .arg("unix.cmxa")
        .arg("-O3")
        .arg(input_path)
        .arg("-o")
        .arg(output_path)
        .output()
        .map_err(Error::RunOCamloptFailed)?;
    progress_bar.finish();

    if ocaml_output.status.success() {
        Ok(())
    } else {
        let err = String::from_utf8_lossy(&ocaml_output.stderr);
        Err(Error::RunOCamloptFailed(io::Error::other(err)))
    }
}

fn run_ml_compiler(
    variant: cfg::MlVariant,
    output_path: &Path,
    input_path: &Path,
    progress: progress_ui::ProgressMode,
) -> Result<(), Error> {
    match variant {
        cfg::MlVariant::Sml => run_mlton(output_path, input_path, progress),
        cfg::MlVariant::OCaml => run_ocamlopt(output_path, input_path, progress),
    }
}

pub fn compile_typed_to_ml(
    typed: data::typed_ast::Program,
    variant: cfg::MlVariant,
    artifact_dir: Option<&cfg::ArtifactDir>,
    output_path: &Path,
    progress: progress_ui::ProgressMode,
) -> Result<(), Error> {
    let ext = format!("typed.{}", variant.extension());
    let mut file = cfg::OutFile::create(artifact_dir, &ext).map_err(Error::WriteIrFailed)?;
    pretty_print::typed::write_ml_program(file.file_mut(), &typed, variant)
        .map_err(Error::WriteIrFailed)?;
    run_ml_compiler(variant, output_path, file.path(), progress)
}

pub fn compile_mono_to_ml(
    mono: data::mono_ast::Program,
    variant: cfg::MlVariant,
    artifact_dir: Option<&cfg::ArtifactDir>,
    output_path: &Path,
    progress: progress_ui::ProgressMode,
) -> Result<(), Error> {
    let ext = format!("mono.{}", variant.extension());
    let mut file = cfg::OutFile::create(artifact_dir, &ext).map_err(Error::WriteIrFailed)?;
    pretty_print::mono::write_ml_program(file.file_mut(), &mono, variant)
        .map_err(Error::WriteIrFailed)?;
    run_ml_compiler(variant, output_path, file.path(), progress)
}

pub fn compile_first_order_to_ml(
    first_order: data::first_order_ast::Program,
    variant: cfg::MlVariant,
    artifact_dir: Option<&cfg::ArtifactDir>,
    output_path: &Path,
    progress: progress_ui::ProgressMode,
) -> Result<(), Error> {
    let ext = format!("first_order.{}", variant.extension());
    let mut file = cfg::OutFile::create(artifact_dir, &ext).map_err(Error::WriteIrFailed)?;
    pretty_print::first_order::write_ml_program(file.file_mut(), &first_order, variant)
        .map_err(Error::WriteIrFailed)?;
    run_ml_compiler(variant, output_path, file.path(), progress)
}
