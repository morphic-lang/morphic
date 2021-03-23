use crate::util::{IteratorStringExt, OptionStringExt};
use anyhow::Result;
use morphic::{
    data::{
        purity::Purity,
        raw_ast::{self as syntax, ModSpec},
        visibility::Visibility,
    },
    lex, parse,
};
use pulldown_cmark::{html::push_html, Event, Parser as CmarkParser, Tag};

#[derive(Debug, Clone)]
pub struct Item {
    name: String,
    def: String,
    summary: String,
    html: String,
}

#[derive(Debug, Clone)]
pub struct CustomType {
    custom: Item,
    variants: Vec<Item>,
}

#[derive(Debug, Clone)]
pub struct Mod {
    mod_: Item,
    children: Vec<Box<Mod>>,
    types: Vec<CustomType>,
    vals: Vec<Item>,
    funcs: Vec<Item>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModName {
    File(String),
    Inline(String),
}

fn doc_to_summary(doc: &str) -> String {
    let parser = CmarkParser::new(doc);
    parser
        .into_offset_iter()
        .find_map(|(event, range)| match event {
            Event::Start(Tag::Paragraph) => Some(range),
            _ => None,
        })
        .map(|range| doc[range].to_owned())
        .or_empty()
}

fn doc_to_html(doc: &str) -> String {
    let parser = CmarkParser::new(doc);
    let mut html = String::new();
    push_html(&mut html, parser);
    html
}

fn purity_str(purity: Purity) -> &'static str {
    if purity == Purity::Pure {
        ""
    } else {
        "proc "
    }
}

fn join_types(types: &Vec<syntax::Type>, delim: &str, group_app: bool) -> String {
    types
        .iter()
        .map(|type_| type_to_string_rec(type_, group_app))
        .join_strings(delim)
}

fn type_to_string_rec(type_: &syntax::Type, group_app: bool) -> String {
    match type_ {
        syntax::Type::Var(param) => param.0.to_owned(),
        syntax::Type::App(_, name, types) => {
            if types.len() == 0 {
                return name.0.clone();
            }
            let type_str = join_types(types, " ", types.len() > 1);
            if group_app {
                format!("({} {})", name.0, type_str)
            } else {
                format!("{} {}", name.0, type_str)
            }
        }
        syntax::Type::Tuple(types) => {
            let types = join_types(types, ", ", false);
            format!("({})", types)
        }
        syntax::Type::Func(purity, arg, ret) => format!(
            "{}{} -> {}",
            purity_str(*purity),
            type_to_string_rec(arg, false),
            type_to_string_rec(ret, false)
        ),
    }
}

fn type_to_string(type_: &syntax::Type) -> String {
    type_to_string_rec(type_, false)
}

fn type_to_paren_string(type_: &syntax::Type) -> String {
    let type_str = type_to_string(type_);
    match type_ {
        syntax::Type::Tuple(_) => type_str,
        _ => format!("({})", type_str),
    }
}

fn process_mod_docs(name: ModName, mod_: &syntax::Program) -> Mod {
    let (name, def) = match name {
        ModName::File(name) => {
            let def = format!("file \"{}\"", &name);
            (name, def)
        }
        ModName::Inline(name) => {
            let def = format!("pub module {}", &name);
            (name, def)
        }
    };

    let doc = &mod_.0;
    let summary = doc.as_ref().map(|doc| doc_to_summary(&doc.0)).or_empty();
    let html = doc.as_ref().map(|doc| doc_to_html(&doc.0)).or_empty();

    let mod_item = Item {
        name,
        def,
        summary,
        html,
    };

    let mut children = Vec::new();
    let mut types = Vec::new();
    let mut vals = Vec::new();
    let mut funcs = Vec::new();

    for item in &mod_.1 {
        match item {
            syntax::Item::TypeDef(doc, vis, name, params, variants) => {
                if *vis == Visibility::Private {
                    continue;
                }

                let variants: Vec<Item> = variants
                    .iter()
                    .filter(|(_, vis, _, _)| matches!(vis, Visibility::Public))
                    .map(|(doc, _, name, type_)| {
                        let name = if let Some(type_) = type_ {
                            format!("{}{}", name.0, type_to_paren_string(type_))
                        } else {
                            name.0.clone()
                        };
                        let def = format!("pub {}", name);
                        let summary = doc.as_ref().map(|doc| doc_to_summary(&doc.0)).or_empty();
                        let html = doc.as_ref().map(|doc| doc_to_html(&doc.0)).or_empty();
                        Item {
                            name,
                            def,
                            summary,
                            html,
                        }
                    })
                    .collect();

                let param_str = if params.len() == 0 {
                    " ".to_owned()
                } else {
                    format!(
                        " {} ",
                        params.iter().map(|param| &param.0).join_strings(" ")
                    )
                };

                let def = if variants.len() == 0 {
                    format!(
                        "pub type {}{}{{\n\t// NO PUBLIC VARIANTS\n}}",
                        name.0, param_str
                    )
                } else {
                    format!(
                        "pub type {}{}{{\n{},\n}}",
                        name.0,
                        param_str,
                        variants
                            .iter()
                            .map(|variant| "\t".to_owned() + &variant.def)
                            .join_strings(",\n")
                    )
                };

                let summary = doc.as_ref().map(|doc| doc_to_summary(&doc.0)).or_empty();
                let html = doc.as_ref().map(|doc| doc_to_html(&doc.0)).or_empty();
                let custom = Item {
                    name: name.0.clone(),
                    def,
                    summary,
                    html,
                };

                types.push(CustomType { custom, variants });
            }
            syntax::Item::ValDef(doc, vis, name, type_, _) => {
                if *vis == Visibility::Private {
                    continue;
                }

                let def = match type_ {
                    syntax::Type::Func(purity, arg_type, ret_type) => format!(
                        "pub {}{}{}: {}",
                        purity_str(*purity),
                        name.0,
                        type_to_paren_string(arg_type),
                        type_to_string(ret_type)
                    ),
                    _ => format!("pub {}: {}", name.0, type_to_string(type_)),
                };

                let summary = doc.as_ref().map(|doc| doc_to_summary(&doc.0)).or_empty();
                let html = doc.as_ref().map(|doc| doc_to_html(&doc.0)).or_empty();
                let item = Item {
                    name: name.0.clone(),
                    def,
                    summary,
                    html,
                };

                match type_ {
                    syntax::Type::Func(_, _, _) => funcs.push(item),
                    _ => vals.push(item),
                }
            }
            syntax::Item::ModDef(vis, name, spec, _, _) => {
                if *vis == Visibility::Private {
                    continue;
                }

                if let ModSpec::Inline(mod_) = spec {
                    children.push(Box::new(process_mod_docs(
                        ModName::Inline(name.0.clone()),
                        mod_,
                    )));
                }
            }
            _ => (),
        }
    }

    Mod {
        mod_: mod_item,
        children,
        types,
        vals,
        funcs,
    }
}

pub fn parse_mod_docs(name: String, src: &str) -> Result<Mod> {
    let mod_ = parse::ProgramParser::new().parse(lex::Lexer::new(src))?;
    Ok(process_mod_docs(ModName::File(name), &mod_))
}
