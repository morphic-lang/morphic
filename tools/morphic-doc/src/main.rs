use anyhow::{anyhow, Result};
use clap::{App, Arg};
use glob::glob;
use morphic::{data::raw_ast as syntax, lex, parse};
use std::{fs, path::Path};

fn parse_mod_docs(name: &str, src: &str) -> Result<()> {
    let mod_ = parse::ProgramParser::new().parse(lex::Lexer::new(src))?;
    let mod_doc = mod_.0.map(|doc| doc.0);
    Ok(())
}

fn main() -> Result<()> {
    let authors = clap::crate_authors!().replace(":", ", ");
    let matches = App::new("morphic-doc")
        .version(clap::crate_version!())
        .author(&authors[..])
        .about("Create HTML documentation from Morphic source files")
        .arg(Arg::with_name("dir").required(true))
        .get_matches();

    let dir = matches.value_of("dir").unwrap();
    if !Path::new(dir).is_dir() {
        return Err(anyhow!("\"{}\" is not a directory", dir));
    }

    for entry in glob(&format!("{}/**/*.mor", dir))? {
        let path = entry?;
        let name =
            path.file_name().unwrap().to_str().ok_or_else(|| {
                anyhow!("Module name \"{}\" is not valid Unicode", path.display())
            })?;
        parse_mod_docs(name, &fs::read_to_string(&path)?)?;
    }

    Ok(())
}
