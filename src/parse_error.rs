use lalrpop_util::ParseError;
use std::io;
use std::path::Path;

use crate::file_cache::FileCache;
use crate::lex;
use crate::report_error::{report_error, Report};

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

pub fn report(
    dest: &mut impl io::Write,
    files: &FileCache,
    path: Option<&Path>,
    err: &ParseError<usize, lex::Token, lex::Error>,
) -> io::Result<()> {
    use ParseError::*;
    match err {
        InvalidToken { location }
        | User {
            error: lex::Error(location),
        } => {
            report_error(
                dest,
                files,
                Report {
                    path,
                    span: Some((*location, *location + 1)),
                    title: "Unexpected Character",
                    message: None,
                },
            )?;
        }

        UnrecognizedToken {
            token: (lo, token, hi),
            expected,
        } => {
            report_error(
                dest,
                files,
                Report {
                    path,
                    span: Some((*lo, *hi)),
                    title: "Incorrect Syntax",
                    message: Some(&{
                        let mut msg = format!("I don't know how to parse \"{}\" here.\n\n", token);
                        if expected.len() == 1 {
                            msg.push_str(&format!(
                                "I expected to see {} here instead.",
                                format_token_name(&expected[0])
                            ));
                        } else {
                            msg.push_str(
                                &"I expected to see one of the following here instead:\n\n",
                            );
                            for name in expected {
                                msg.push_str(&format!("    {}\n", format_token_name(&name)));
                            }
                        }

                        msg
                    }),
                },
            )?;
        }

        UnrecognizedEOF {
            location: _,
            expected,
        } => {
            report_error(
                dest,
                files,
                Report {
                    path,
                    span: None,
                    title: "Unexpected End of File",
                    message: Some(&{
                        let mut msg = format!("The file ended before I expected.\n\n");
                        msg.push_str(
                            &"At the end of the file, I expected to see one of these \
                              instead:\n\n",
                        );
                        for name in expected {
                            msg.push_str(&format!("    {}\n", format_token_name(&name)));
                        }
                        msg
                    }),
                },
            )?;
        }

        ExtraToken {
            token: (lo, token, hi),
        } => {
            report_error(
                dest,
                files,
                Report {
                    path,
                    span: Some((*lo, *hi)),
                    title: "Incorrect Syntax",
                    message: Some(&format!(
                        "I don't know how to parse \"{}\" here.  \
                         I expected the file to end here instead.",
                        token
                    )),
                },
            )?;
        }
    }

    Ok(())
}
