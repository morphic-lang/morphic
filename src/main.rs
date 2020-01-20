#![allow(dead_code)]

#[macro_use]
mod util;

mod data;
mod pretty_print_lifted;
mod pretty_print_low;
mod pretty_print_special;

mod lex;

lalrpop_mod!(pub parse);

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

#[cfg(test)]
mod test;

use failure::Fail;
use lalrpop_util::lalrpop_mod;
use std::env::args_os;
use std::io;
use std::path::PathBuf;
use std::process::exit;

#[derive(Debug, Fail)]
enum Error {
    #[fail(display = "{}", _0)]
    ResolveFailed(#[cause] resolve::Error),

    #[fail(display = "{}", _0)]
    PurityCheckFailed(#[cause] check_purity::Error),

    #[fail(display = "{}", _0)]
    TypeInferFailed(#[cause] type_infer::LocatedError),

    #[fail(display = "{}", _0)]
    CheckExhaustiveFailed(#[cause] check_exhaustive::Error),

    #[fail(display = "{}", _0)]
    CheckMainFailed(#[cause] check_main::Error),
}

#[derive(Clone, Debug)]
struct Config {
    src_path: PathBuf,
}

fn parse_args() -> Option<Config> {
    let mut args = args_os();
    args.next()?; // Consume program name

    let src_path = args.next().unwrap_or("samples/mutate.txt".into()).into();

    if args.next().is_some() {
        return None;
    }

    Some(Config { src_path })
}

fn usage() -> String {
    "Usage: opt-proto <src.txt>".to_owned()
}

fn main() {
    better_panic::install();

    // let matches = clap::App::new(clap::crate_name!())
    //     .version(clap::crate_version!())
    //     .author(clap::crate_authors!())
    //     .about(clap::crate_description!())
    //     .arg(
    //         clap::Arg::with_name("src_file")
    //             .help("Specify the source file to compile.")
    //             .required(true)
    //             .index(1),
    //     )
    //     .arg(
    //         clap::Arg::with_name("target")
    //             .long("Specify the architecture to compile for.
    //                    The target has the general format <arch><sub>-<vendor>-<sys>-<abi>.
    //                    If \"unknown\" is specified for one of these components, the defaults will be used.")
    //             .help("")
    //     )
    //     .get_matches();

    if let Some(config) = parse_args() {
        let result = run(&mut io::stdin().lock(), &mut io::stdout().lock(), config);
        if let Err(err) = result {
            eprintln!("{}", err);
            eprintln!("{:?}", err);
            exit(1);
        }
    } else {
        println!("{}", usage());
    }
}

fn run<R: io::BufRead, W: io::Write>(
    stdin: &mut R,
    stdout: &mut W,
    config: Config,
) -> Result<(), Error> {
    let resolved = resolve::resolve_program(&config.src_path).map_err(Error::ResolveFailed)?;

    // Check obvious errors and infer types
    check_purity::check_purity(&resolved).map_err(Error::PurityCheckFailed)?;
    let typed = type_infer::type_infer(resolved).map_err(Error::TypeInferFailed)?;
    check_exhaustive::check_exhaustive(&typed).map_err(Error::CheckExhaustiveFailed)?;
    check_main::check_main(&typed).map_err(Error::CheckMainFailed)?;

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

    // println!("Representation-specialized program:");
    // pretty_print_special::write_program(&mut io::stdout(), &repr_specialized)
    //     .expect("printing program failed");
    // println!("(end representation-specialized program)");

    let lowered = lower_structures::lower_structures(repr_specialized);

    println!("Lowered program:");
    pretty_print_low::write_program(&mut io::stdout(), &lowered).expect("printing program failed");
    println!("(end lowered program)");

    llvm_gen::llvm_gen(lowered, "a.out".as_ref());

    // println!("==============================================================");
    // println!("============== Running program ===============================");
    // println!("==============================================================");

    // interpreter::interpret(stdin, stdout, &lowered);

    Ok(())
}
