use lalrpop_util::ParseError;

use crate::lex;
use crate::report_error::Report;

// Clean up a token name from the grammar for display to the user.
fn format_token_name(name: &str) -> &str {
    match name {
        "\"UpperName\"" => "uppercase name",
        "\"LowerName\"" => "lowercase name",
        "\"FloatLit\"" => "float literal",
        "\"ByteLit\"" => "byte literal",
        "\"IntLit\"" => "int literal",
        "\"StringLit\"" => "string literal",
        // Elder Backslash
        "\"\\\\\"" => "\"\\\"",
        _ => name,
    }
}

pub fn report(err: &ParseError<usize, lex::Token, ()>) -> Report {
    use ParseError::*;
    match err {
        InvalidToken { location }
        | User {
            error: lex::Error(location),
        } => Report {
            title: "Unexpected Character".to_string(),
            message: None,
        },

        UnrecognizedToken {
            token: (lo, token, hi),
            expected,
        } => Report {
            title: "Incorrect Syntax".to_string(),
            message: Some({
                let mut msg = format!("I don't know how to parse \"{}\" here.\n\n", token);
                if expected.len() == 1 {
                    msg.push_str(&format!(
                        "I expected to see {} here instead.",
                        format_token_name(&expected[0])
                    ));
                } else {
                    msg.push_str(&"I expected to see one of the following here instead:\n\n");
                    for name in expected {
                        msg.push_str(&format!("    {}\n", format_token_name(&name)));
                    }
                }

                msg
            }),
        },

        UnrecognizedEof {
            location: _,
            expected,
        } => Report {
            title: "Unexpected End of File".to_string(),
            message: Some({
                let mut msg = format!("The file ended before I expected.\n\n");
                msg.push_str("At the end of the file, I expected to see one of these instead:\n\n");
                for name in expected {
                    msg.push_str(&format!("    {}\n", format_token_name(&name)));
                }
                msg
            }),
        },

        ExtraToken {
            token: (lo, token, hi),
        } => Report {
            title: "Incorrect Syntax".to_string(),
            message: Some(format!(
                "I don't know how to parse \"{}\" here. I expected the file to end here instead.",
                token
            )),
        },
    }
}
