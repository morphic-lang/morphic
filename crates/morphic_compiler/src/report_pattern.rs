//! This module renders unhandled patterns detected by the exhaustivity cheker.

use crate::data::resolved_ast as res;
use id_collections::IdVec;

#[derive(Clone, Debug)]
pub enum Pattern {
    Any,
    Tuple(Vec<Pattern>),
    Ctor(res::TypeId, res::VariantId, Option<Box<Pattern>>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ParenContext {
    Parenthesized,
    Unparenthesized,
}

fn render_to(
    type_symbols: &IdVec<res::CustomTypeId, res::TypeSymbols>,
    pat: &Pattern,
    dest: &mut String,
    paren_ctx: ParenContext,
) {
    match pat {
        Pattern::Any => {
            dest.push('_');
        }

        Pattern::Tuple(items) => {
            let parenthesize = paren_ctx == ParenContext::Unparenthesized;

            if parenthesize {
                dest.push('(');
            }
            for (i, item) in items.iter().enumerate() {
                render_to(type_symbols, item, dest, ParenContext::Unparenthesized);
                if i + 1 != items.len() {
                    dest.push_str(", ");
                }
            }
            if parenthesize {
                dest.push(')');
            }
        }

        Pattern::Ctor(id, variant, content) => {
            match id {
                res::TypeId::Custom(custom) => {
                    dest.push_str(&type_symbols[custom].variant_symbols[variant].variant_name.0);
                }

                res::TypeId::Bool => match variant {
                    res::VariantId(0) => {
                        dest.push_str("False");
                    }
                    res::VariantId(1) => {
                        dest.push_str("True");
                    }
                    _ => unreachable!(),
                },

                res::TypeId::Array | res::TypeId::Byte | res::TypeId::Float | res::TypeId::Int => {
                    unreachable!()
                }
            }

            if let Some(content) = content {
                dest.push('(');
                render_to(type_symbols, content, dest, ParenContext::Parenthesized);
                dest.push(')');
            }
        }
    }
}

pub fn render(type_symbols: &IdVec<res::CustomTypeId, res::TypeSymbols>, pat: &Pattern) -> String {
    let mut result = String::new();
    render_to(
        type_symbols,
        pat,
        &mut result,
        ParenContext::Unparenthesized,
    );
    result
}
