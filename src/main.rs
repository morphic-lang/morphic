#![allow(dead_code)]

mod annot_aliases;
mod annot_closures;
mod annot_reprs;
mod check_exhaustive;
mod check_main;
mod check_purity;
mod closure_specialize;
mod data;
mod graph;
mod lambda_lift;
mod lex;
mod lower_closures;
mod monomorphize;
mod pretty_print;
mod resolve;
mod shield_functions;
mod type_infer;
mod util;

use failure::Fail;
use lalrpop_util::lalrpop_mod;
use std::env::args_os;
use std::fs;
use std::io;
use std::path::PathBuf;
use std::process::exit;

lalrpop_mod!(pub parse);

#[derive(Debug, Fail)]
enum Error {
    #[fail(display = "Could not read source file: {}", _0)]
    ReadFailed(#[cause] io::Error),

    #[fail(display = "Could not parse source file: {}", _0)]
    ParseFailed(#[cause] lalrpop_util::ParseError<usize, lex::Token, lex::Error>),

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

    let src_path = args.next()?.into();

    if args.next().is_some() {
        return None;
    }

    Some(Config { src_path })
}

fn usage() -> String {
    "Usage: opt-proto <src.txt>".to_owned()
}

fn main() {
    if let Some(config) = parse_args() {
        let result = run(config);
        if let Err(err) = result {
            eprintln!("{}", err);
            eprintln!("{:?}", err);
            exit(1);
        }
    } else {
        println!("{}", usage());
    }
}

fn run(config: Config) -> Result<(), Error> {
    let src = fs::read_to_string(&config.src_path).map_err(Error::ReadFailed)?;

    let raw = parse::ProgramParser::new()
        .parse(lex::Lexer::new(&src))
        .map_err(Error::ParseFailed)?;

    let resolved = resolve::resolve(raw).map_err(Error::ResolveFailed)?;

    check_purity::check_purity(&resolved).map_err(Error::PurityCheckFailed)?;

    let typed = type_infer::type_infer(resolved).map_err(Error::TypeInferFailed)?;

    check_exhaustive::check_exhaustive(&typed).map_err(Error::CheckExhaustiveFailed)?;

    check_main::check_main(&typed).map_err(Error::CheckMainFailed)?;

    let mono = monomorphize::monomorphize(typed);

    let shielded = shield_functions::shield_functions(mono);

    let lifted = lambda_lift::lambda_lift(shielded);

    println!("Lambda-lifted AST:\n{:#?}", lifted);

    let annot = annot_closures::annot_closures(lifted);

    println!("Built closure-annotated AST");

    let special = closure_specialize::closure_specialize(annot);

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

    let unique_infos = annot_aliases::annot_aliases(&first_order);

    let _data_structure_annotated = annot_reprs::annot_reprs(&first_order, &unique_infos);

    Ok(())
}
