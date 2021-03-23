mod parse;
mod util;

use crate::parse::{parse_mod_docs, Mod};
use anyhow::{anyhow, Result};
use clap::{App, Arg};
use glob::glob;
use std::{fs, path::Path};

#[derive(Debug, Clone)]
pub struct Package {
    mods: Vec<Mod>,
}

fn main() -> Result<()> {
    let authors = clap::crate_authors!().replace(":", ", ");
    let matches = App::new("morphic-doc")
        .version(clap::crate_version!())
        .author(&authors[..])
        .about("Create HTML documentation from Morphic source files")
        .arg(
            Arg::with_name("input")
                .help("Input file or directory")
                .required(true),
        )
        .get_matches();

    let input = matches.value_of("input").unwrap();
    let input_path = Path::new(input);

    let mods = if input_path.is_file() {
        if !input_path.extension().map(|x| x == "mor").unwrap_or(false) {
            return Err(anyhow!(
                "\"{}\" does not appear to be a Morphic source file (extension is not \".mor\")",
                input
            ));
        }
        vec![parse_mod_docs(
            input.to_owned(),
            &fs::read_to_string(&input_path)?,
        )?]
    } else if input_path.is_dir() {
        glob(&format!("{}/**/*.mor", input))?
            .map(|entry| {
                let path = entry?;
                let name = path.file_name().unwrap().to_str().ok_or_else(|| {
                    anyhow!("Module name \"{}\" is not valid Unicode", path.display())
                })?;
                parse_mod_docs(name.to_owned(), &fs::read_to_string(&path)?)
            })
            .collect::<Result<Vec<_>, _>>()?
    } else {
        return Err(anyhow!("\"{}\" is neither a file nor a directory", input));
    };

    let pkg = Package { mods };
    println!("{:#?}", pkg);

    Ok(())
}
