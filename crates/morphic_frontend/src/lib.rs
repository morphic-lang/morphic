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
lalrpop_mod!(parse);

use crate::error::Error;
use morphic_common::{config as cfg, data, file_cache, pretty_print, progress_ui};
use std::fs;
use std::path::Path;

pub fn compile_to_first_order_ast(
    src_path: &Path,
    purity_mode: cfg::PurityMode,
    profile_syms: &[cfg::SymbolName],
    profile_record_rc: bool,
    artifact_dir: Option<&cfg::ArtifactDir>,
    files: &mut file_cache::FileCache,
    progress: progress_ui::ProgressMode,
    pass_options: &cfg::PassOptions,
) -> Result<data::first_order_ast::Program, Error> {
    let resolved = resolve::resolve_program(files, src_path, profile_syms, profile_record_rc)
        .map_err(Error::ResolveFailed)?;
    // Check obvious errors and infer types
    if matches!(purity_mode, cfg::PurityMode::Checked) {
        check_purity::check_purity(&resolved).map_err(Error::PurityCheckFailed)?;
    }
    let typed = type_infer::type_infer(resolved).map_err(Error::TypeInferFailed)?;
    check_exhaustive::check_exhaustive(&typed).map_err(Error::CheckExhaustiveFailed)?;
    check_main::check_main(&typed).map_err(Error::CheckMainFailed)?;

    // Ensure clean artifacts directory, if applicable
    if let Some(artifact_dir) = artifact_dir {
        fs::remove_dir_all(&artifact_dir.dir_path).map_err(Error::CreateArtifactsFailed)?;
        fs::create_dir(&artifact_dir.dir_path).map_err(Error::CreateArtifactsFailed)?;
    }

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("typed.sml"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print::typed::write_sml_program(&mut out_file, &typed)
            .map_err(Error::WriteIrFailed)?;
    }

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("typed.ml"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print::typed::write_ocaml_program(&mut out_file, &typed)
            .map_err(Error::WriteIrFailed)?;
    }

    let mono = monomorphize::monomorphize(typed);

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("mono.sml"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print::mono::write_sml_program(&mut out_file, &mono)
            .map_err(Error::WriteIrFailed)?;
    }

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("mono.ml"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print::mono::write_ocaml_program(&mut out_file, &mono)
            .map_err(Error::WriteIrFailed)?;
    }

    let shielded = shield_functions::shield_functions(mono);

    let lifted = lambda_lift::lambda_lift(shielded);

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
            .map_err(Error::WriteIrFailed)?;

        pretty_print::first_order::write_sml_program(&mut out_file, &first_order)
            .map_err(Error::WriteIrFailed)?;

        let mut out_file = fs::File::create(artifact_dir.artifact_path("first_order.ml"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print::first_order::write_ocaml_program(&mut out_file, &first_order)
            .map_err(Error::WriteIrFailed)?;

        let mut out_file = fs::File::create(artifact_dir.artifact_path("first_order.mor"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print::first_order::write_morphic_program(&mut out_file, &first_order)
            .map_err(Error::WriteIrFailed)?;
    }

    typecheck_first_order::typecheck(&first_order);

    Ok(first_order)
}
