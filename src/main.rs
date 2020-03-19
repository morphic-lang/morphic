#![allow(dead_code)]

#[macro_use]
mod util;

mod builtins;

mod data;
mod pretty_print_lifted;
mod pretty_print_low;
mod pretty_print_special;

mod lex;

lalrpop_mod!(pub parse);

mod file_cache;
mod parse_error;
mod report_error;

mod resolve;

mod check_purity;

mod type_infer;

mod check_exhaustive;

mod check_main;

mod monomorphize;

mod shield_functions;

mod lambda_lift;

mod annot_closures;

mod closure_specialize;

mod lower_closures;

mod typecheck_first_order;

mod split_custom_types;

mod flatten;

// Abstract interpretation utilities
mod field_path;
mod fixed_point;
mod mutation_status;

mod annot_aliases;

mod annot_mutation;

mod unify_reprs;

mod constrain_reprs;

mod specialize_reprs;

mod lower_structures;

mod interpreter;

mod llvm_gen;

mod cli;

mod pseudoprocess;

#[cfg(test)]
mod test;

use lalrpop_util::lalrpop_mod;
use std::fs;
use std::io;

#[derive(Debug)]
enum Error {
    ResolveFailed(resolve::Error),
    PurityCheckFailed(check_purity::Error),
    TypeInferFailed(type_infer::LocatedError),
    CheckExhaustiveFailed(check_exhaustive::Error),
    CheckMainFailed(check_main::Error),
    CreateArtifactsFailed(io::Error),
    WriteIrFailed(io::Error),
}

impl Error {
    pub fn report(
        &self,
        dest: &mut impl io::Write,
        files: &file_cache::FileCache,
    ) -> io::Result<()> {
        use Error::*;
        match self {
            ResolveFailed(err) => err.report(dest, files),
            PurityCheckFailed(err) => err.report(dest, files),
            TypeInferFailed(err) => writeln!(dest, "{}", err),
            CheckExhaustiveFailed(err) => writeln!(dest, "{}", err),
            CheckMainFailed(err) => writeln!(dest, "{}", err),
            CreateArtifactsFailed(err) => {
                writeln!(dest, "Could not create artifacts directory: {}", err)
            }
            WriteIrFailed(err) => writeln!(
                dest,
                "Could not write intermediate representation artifacts: {}",
                err
            ),
        }
    }
}

fn main() {
    better_panic::install();

    let config = cli::Config::from_args();
    let mut files = file_cache::FileCache::new();
    let result = run(config, &mut files);
    match result {
        Ok(Some(spawned_child)) => wait_child(spawned_child),
        Ok(None) => {}
        Err(err) => {
            let _ = err.report(&mut io::stderr().lock(), &files);
            std::process::exit(1);
        }
    }
}

fn run(
    config: cli::Config,
    files: &mut file_cache::FileCache,
) -> Result<Option<pseudoprocess::Child>, Error> {
    let resolved =
        resolve::resolve_program(files, config.src_path()).map_err(Error::ResolveFailed)?;

    // Check obvious errors and infer types
    check_purity::check_purity(&resolved).map_err(Error::PurityCheckFailed)?;
    let typed = type_infer::type_infer(resolved).map_err(Error::TypeInferFailed)?;
    check_exhaustive::check_exhaustive(&typed).map_err(Error::CheckExhaustiveFailed)?;
    check_main::check_main(&typed).map_err(Error::CheckMainFailed)?;

    // Ensure clean artifacts directory, if applicable
    if let Some(artifact_dir) = config.artifact_dir() {
        fs::remove_dir_all(&artifact_dir.dir_path).map_err(Error::CreateArtifactsFailed)?;
        fs::create_dir(&artifact_dir.dir_path).map_err(Error::CreateArtifactsFailed)?;
    }

    let mono = monomorphize::monomorphize(typed);

    let shielded = shield_functions::shield_functions(mono);

    let lifted = lambda_lift::lambda_lift(shielded);

    let annot = annot_closures::annot_closures(lifted);

    let special = closure_specialize::closure_specialize(annot);
    closure_specialize::check_patterns(&special);

    let first_order = lower_closures::lower_closures(special);

    typecheck_first_order::typecheck(&first_order);

    let split = split_custom_types::split_custom_types(&first_order);

    let flat = flatten::flatten(split);

    let alias_annot = annot_aliases::annot_aliases(flat);

    let mut_annot = annot_mutation::annot_mutation(alias_annot);

    let repr_unified = unify_reprs::unify_reprs(mut_annot);

    let repr_constrained = constrain_reprs::constrain_reprs(repr_unified);

    let repr_specialized = specialize_reprs::specialize_reprs(repr_constrained);

    if let Some(artifact_dir) = config.artifact_dir() {
        let mut out_file = fs::File::create(artifact_dir.artifact_path("repr-spec-ir"))
            .map_err(Error::WriteIrFailed)?;

        pretty_print_special::write_program(&mut out_file, &repr_specialized)
            .map_err(Error::WriteIrFailed)?;
    }

    let lowered = lower_structures::lower_structures(repr_specialized);

    if let Some(artifact_dir) = config.artifact_dir() {
        let mut out_file =
            fs::File::create(artifact_dir.artifact_path("low-ir")).map_err(Error::WriteIrFailed)?;

        pretty_print_low::write_program(&mut out_file, &lowered).map_err(Error::WriteIrFailed)?;
    }

    let child = match config {
        cli::Config::RunConfig(cli::RunConfig { mode, stdio, .. }) => match mode {
            cli::RunMode::Compile => Some(llvm_gen::run(stdio, lowered)),
            cli::RunMode::Interpret => Some(interpreter::interpret(stdio, lowered)),
        },

        cli::Config::BuildConfig(build_config) => {
            llvm_gen::build(lowered, &build_config);
            None
        }
    };

    Ok(child)
}

fn wait_child(child: pseudoprocess::Child) {
    let exit_status = child.wait();
    match exit_status {
        Ok(pseudoprocess::ExitStatus::Success) => {}
        Ok(pseudoprocess::ExitStatus::Failure(Some(code))) => std::process::exit(code),
        Ok(pseudoprocess::ExitStatus::Failure(None)) => {
            eprintln!(
                "Program terminated due to signal.  This probably indicates a SIGTERM or \
                 segfault."
            );
            std::process::exit(1)
        }
        Err(err) => {
            eprintln!("Could not execute compiled program: {}", err);
            std::process::exit(1);
        }
    }
}
