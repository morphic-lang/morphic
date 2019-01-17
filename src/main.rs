#![allow(dead_code)]

mod data;
mod lex;
mod resolve;

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

    println!("Resolved ADT:\n{:#?}", resolved);

    Ok(())
}
