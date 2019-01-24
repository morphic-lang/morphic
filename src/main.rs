#![allow(dead_code)]

mod check_exhaustive;
mod check_main;
mod check_purity;
mod data;
mod lex;
mod monomorphize;
mod resolve;
mod type_infer;

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

    println!("Raw AST:\n{:#?}", raw);

    let resolved = resolve::resolve(raw).map_err(Error::ResolveFailed)?;

    println!("Resolved AST:\n{:#?}", resolved);

    check_purity::check_purity(&resolved).map_err(Error::PurityCheckFailed)?;

    let typed = type_infer::type_infer(resolved).map_err(Error::TypeInferFailed)?;

    println!("Typed AST:\n{:#?}", typed);

    check_exhaustive::check_exhaustive(&typed).map_err(Error::CheckExhaustiveFailed)?;

    check_main::check_main(&typed).map_err(Error::CheckMainFailed)?;

    let mono = monomorphize::monomorphize(typed);

    println!("Monomorphic AST:\n{:#?}", mono);

    Ok(())
}
