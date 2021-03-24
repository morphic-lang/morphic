use crate::parse::Mod;
use anyhow::{anyhow, Context, Result};
use handlebars::{handlebars_helper, Handlebars};
use lazy_static::lazy_static;
use regex::Regex;
use serde::Serialize;
use std::{
    fs::{self, File},
    path::Path,
};

// TODO: much of this file duplicates functionality from the "morphic-lang/morphic-lang.org"
// repository

const LAYOUT: &str = "layout";
const INPUT_DIR: &str = "tools/morphic-doc/src";

#[derive(Debug, Clone, Serialize)]
struct GlobalContext {
    title: String,
    description: String,
    style: String,
}

fn compile_scss(name: &str, dir: &str) -> Result<String> {
    let scss_file = format!("{}/styles/{}.scss", INPUT_DIR, name);
    let css_file = format!("{}/styles/{}.css", dir, name);
    let css = sass_rs::compile_file(&scss_file, sass_rs::Options::default())
        .map_err(|err| anyhow!(err))?;
    fs::write(&css_file, &css)
        .with_context(|| format!("Cannot write CSS file \"{}\"", &css_file))?;
    Ok(format!("/styles/{}.css", name))
}

fn render_template(
    page: &str,
    handlebars: &mut Handlebars,
    ctx: &GlobalContext,
    mod_: &Mod,
    dir: &str,
) -> Result<()> {
    #[derive(Serialize)]
    struct Context<'a> {
        #[serde(flatten)]
        ctx: &'a GlobalContext,

        #[serde(flatten)]
        mod_: &'a Mod,
    }

    let name = format!("{}/{}.html", dir, page);
    let f = File::create(&name).with_context(|| format!("Cannot create file \"{}\"", &name))?;

    handlebars
        .render_to_write(LAYOUT, &Context { ctx, mod_ }, f)
        .with_context(|| format!("Cannot render {} to \"{}\"", LAYOUT, &name))?;
    Ok(())
}

// TODO: we lose information about whether a module name is a file name or an inline name when we
// parse the documentation. Producing more precise types during parsing would allow us to avoid
// depending on regex to normalize module names.
fn normalize_mod_name(name: &str) -> String {
    lazy_static! {
        static ref RE: Regex = Regex::new("[A-Z][a-z]*").unwrap();
    }
    if RE.is_match(name) {
        name.to_owned()
    } else {
        let mut name = Path::new(name)
            .file_name()
            .unwrap()
            .to_str()
            .unwrap()
            .strip_suffix(".mor")
            .unwrap()
            .to_owned();
        name.get_mut(0..1).unwrap().make_ascii_uppercase();
        assert!(RE.is_match(&name));
        name
    }
}

fn render_mod(
    mod_: &Mod,
    handlebars: &mut Handlebars,
    ctx: &GlobalContext,
    dir: &str,
) -> Result<()> {
    let name = normalize_mod_name(&mod_.self_.name);

    if mod_.children.len() == 0 {
        render_template(&name, handlebars, &ctx, mod_, dir)?;
    } else {
        let new_dir = format!("{}/{}", dir, name);
        fs::create_dir_all(&new_dir)?;
        render_template(&name, handlebars, &ctx, mod_, &new_dir)?;

        for child in &mod_.children {
            render_mod(child, handlebars, ctx, &new_dir)?;
        }
    };

    Ok(())
}

handlebars_helper!(nonempty: |a: array| a.len() > 0);
handlebars_helper!(normalize_mod_name_: |s: str| normalize_mod_name(s));

#[derive(Debug, Clone)]
pub struct Package {
    pub mods: Vec<Mod>,
}

pub fn render_pkg(pkg: &Package, title: &str, description: &str, dir: &str) -> Result<()> {
    // create output root directories
    let pages_dir = format!("{}/pkg", dir);
    fs::create_dir_all(&pages_dir)?;
    fs::create_dir_all(format!("{}/styles", dir))?;
    fs::create_dir_all(format!("{}/static", dir))?;

    // copy static resources
    fs::copy(
        format!("{}/static/morphic-logo.png", INPUT_DIR),
        format!("{}/static/morphic-logo.png", dir),
    )
    .context("Cannot copy Morphic logo to output directory")?;

    let mut handlebars = Handlebars::new();
    handlebars.set_strict_mode(true);
    handlebars.register_helper("nonempty", Box::new(nonempty));
    handlebars.register_helper("normalize-mod-name", Box::new(normalize_mod_name_));

    let layout_file = format!("{}/templates/layout.hbs", INPUT_DIR);
    let mut layout = File::open(&layout_file)
        .with_context(|| format!("Cannot open layout file \"{}\"", &layout_file))?;

    handlebars.register_template_source(LAYOUT, &mut layout)?;

    // TODO: take `AsRef<str>` parameters instead of unconditionally copying `title` and
    // `description`
    let ctx = GlobalContext {
        title: title.to_owned(),
        description: description.to_owned(),
        style: compile_scss("app", dir)?,
    };

    for mod_ in &pkg.mods {
        render_mod(mod_, &mut handlebars, &ctx, &pages_dir)?;
    }

    Ok(())
}
