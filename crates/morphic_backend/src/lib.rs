#![allow(dead_code)]

mod annot_modes;
mod annot_obligations;
mod annot_rcs;
mod flatten;
mod guard_types;
mod lower_structures;
mod rc_specialize;
mod split_custom_types;
mod tail_call_elim;
mod type_check_borrows;
mod typecheck_guarded;

pub mod code_gen;
pub mod error;
pub mod interpreter;

use crate::error::Error;
use morphic_common::{config as cfg, data, pretty_print, progress_ui};
use std::fs;
use std::path::PathBuf;

#[derive(Debug)]
pub struct BuildConfig {
    pub src_path: PathBuf,
    pub purity_mode: cfg::PurityMode,

    pub profile_syms: Vec<cfg::SymbolName>,
    pub profile_record_rc: bool,

    pub target: cfg::TargetConfig,
    pub llvm_opt_level: inkwell::OptimizationLevel,

    pub output_path: PathBuf,
    pub artifact_dir: Option<cfg::ArtifactDir>,
    pub progress: progress_ui::ProgressMode,

    pub pass_options: cfg::PassOptions,
}

pub fn compile_to_low_ast(
    first_order: data::first_order_ast::Program,
    artifact_dir: Option<&cfg::ArtifactDir>,
    progress: progress_ui::ProgressMode,
    pass_options: &cfg::PassOptions,
) -> Result<data::low_ast::Program, Error> {
    let split = split_custom_types::split_custom_types(
        &first_order,
        progress_ui::bar(progress, "split_custom_types"),
    );

    let flat = flatten::flatten(split, progress_ui::bar(progress, "flatten"));

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file =
            fs::File::create(artifact_dir.artifact_path("flat")).map_err(Error::WriteIrFailed)?;

        pretty_print::flat::write_program(&mut out_file, &flat).map_err(Error::WriteIrFailed)?;
    }

    let guarded = guard_types::guard_types(flat);

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("guarded"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print::guarded::write_program(&mut out_file, &guarded)
            .map_err(Error::WriteIrFailed)?;
    }

    let interner = crate::data::mode_annot_ast::Interner::empty();
    let mode_annot = annot_modes::annot_modes(
        pass_options.rc_strat,
        &interner,
        guarded,
        progress_ui::bar(progress, "annot_modes"),
    );

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("mode_annot"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print::mode_annot::write_program(&mut out_file, &mode_annot)
            .map_err(Error::WriteIrFailed)?;
    }

    let obligation_annot = annot_obligations::annot_obligations(
        &interner,
        mode_annot,
        progress_ui::bar(progress, "annot_obligations"),
    );

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("ob_annot"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print::obligation_annot::write_program(&mut out_file, &obligation_annot)
            .map_err(Error::WriteIrFailed)?;
    }

    let rc_annot = annot_rcs::annot_rcs(
        &interner,
        obligation_annot,
        progress_ui::bar(progress, "annot_rcs"),
    );

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("rc_annot"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print::rc_annot::write_program(&mut out_file, &rc_annot)
            .map_err(Error::WriteIrFailed)?;
    }

    // type_check_borrows::type_check(&interner, &rc_annot);

    let rc_specialized =
        rc_specialize::rc_specialize(rc_annot, progress_ui::bar(progress, "rc_specialize"));

    let tail_rec = tail_call_elim::tail_call_elim(
        rc_specialized.clone(),
        progress_ui::bar(progress, "tail_call_elim"),
    );

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("tail_rec"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print::tail::write_program(&mut out_file, &tail_rec)
            .map_err(Error::WriteIrFailed)?;
    }

    let lowered = lower_structures::lower_structures(
        tail_rec,
        progress_ui::bar(progress, "lower_structures"),
    );

    if let Some(artifact_dir) = artifact_dir {
        let mut out_file =
            fs::File::create(artifact_dir.artifact_path("low-ir")).map_err(Error::WriteIrFailed)?;

        pretty_print::low::write_program(&mut out_file, &lowered).map_err(Error::WriteIrFailed)?;
    }

    Ok(lowered)
}
