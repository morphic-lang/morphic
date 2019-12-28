#![allow(dead_code)]

#[macro_use]
mod util;

mod data;
mod pretty_print;

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

mod field_path;
mod fixed_point;

mod annot_aliases_alt;

mod annot_mutation;

mod unify_reprs;

mod constrain_reprs;

mod annot_aliases;

mod annot_reprs;

mod lower_reprs;

mod interpreter;

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
    // println!("Lambda-lifted AST:\n{:#?}", lifted);

    let annot = annot_closures::annot_closures(lifted);
    println!("Built closure-annotated AST");

    let special = closure_specialize::closure_specialize(annot);
    closure_specialize::check_patterns(&special);
    println!("Built closure-specialized AST");
    println!("Statistics:");
    println!("  # custom types: {}", special.custom_types.len());
    println!("  # opaque reps: {}", special.opaque_reps.len());
    println!("  # globals: {}", special.vals.len());
    println!("  # lambdas: {}", special.lams.len());

    let first_order = lower_closures::lower_closures(special);
    println!("Built first-order AST");
    println!("Statistics:");
    println!("  # custom types: {}", first_order.custom_types.len());
    println!("  # functions {}", first_order.funcs.len());
    println!("First order AST:");
    let fo = format!("{:#?}", first_order);
    let mut fo_better = String::new();
    let mut prev_comma = false;
    for line in fo.lines() {
        if prev_comma {
            fo_better.push_str("\n");
            fo_better.push_str(&line);
        } else if !line.contains(":") && !line.contains("}") {
            fo_better.push_str(line.trim());
        } else {
            if !fo_better.is_empty() {
                fo_better.push_str("\n");
            }
            fo_better.push_str(line);
        }
        prev_comma = line.ends_with(",");
    }
    println!("{}", fo_better);

    typecheck_first_order::typecheck(&first_order);

    let split = split_custom_types::split_custom_types(&first_order);

    let flat = flatten::flatten(split);

    println!("Flat program: {:#?}", flat);
    println!("(end flat program)");

    let alias_annot = annot_aliases_alt::annot_aliases(flat);

    println!("Alias-annotated program: {:#?}", alias_annot);
    println!("(end alias-annotated program)");

    let mut_annot = annot_mutation::annot_mutation(alias_annot);

    println!("Mutation-annotated program: {:#?}", mut_annot);
    println!("(end mutation-annotated program)");

    let repr_unified = unify_reprs::unify_reprs(mut_annot);

    println!("Representation-unified program: {:#?}", repr_unified);
    println!("(end repr-unified program)");

    let unique_infos = annot_aliases::annot_aliases(&first_order);

    let data_structure_annotated = annot_reprs::annot_reprs(&first_order, unique_infos);

    let specialized = lower_reprs::lower_reprs(data_structure_annotated);

    println!("==============================================================");
    println!("============== Running program ===============================");
    println!("==============================================================");

    interpreter::interpret(stdin, stdout, &specialized);

    Ok(())
}
