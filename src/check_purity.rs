use std::io;
use std::path::PathBuf;

use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::file_cache::FileCache;
use crate::report_error::{report_error, Report};

#[derive(Clone, Debug)]
pub struct Error {
    file: Option<PathBuf>,
    span: Option<(usize, usize)>,
}

impl Error {
    pub fn report(&self, dest: &mut impl io::Write, files: &FileCache) -> io::Result<()> {
        report_error(
            dest,
            files,
            Report {
                path: self.file.as_ref().map(|path| path.as_ref()),
                span: self.span,
                title: "Purity Mismatch",
                message: Some(lines![
                    "You cannot call a function with side effects from inside a pure function.",
                    "",
                    "Maybe you didn't mean to mark the calling function as pure?  All function \
                     definitions are considered pure by default.  You can mark the calling \
                     function as having side effects by adding the keyword 'proc' before the \
                     function's definition.",
                ]),
            },
        )
    }
}

fn check_expr(ctx: Purity, expr: &res::Expr) -> Result<(), Error> {
    match expr {
        res::Expr::Global(_) => Ok(()),

        res::Expr::Local(_) => Ok(()),

        res::Expr::Tuple(items) => {
            for item in items {
                check_expr(ctx, item)?;
            }
            Ok(())
        }

        res::Expr::Lam(purity, _, body) => {
            check_expr(*purity, body)?;
            Ok(())
        }

        res::Expr::App(purity, func, arg) => {
            if ctx == Purity::Pure && *purity == Purity::Impure {
                return Err(Error {
                    file: None,
                    span: None,
                });
            }

            check_expr(ctx, func)?;
            check_expr(ctx, arg)?;
            Ok(())
        }

        res::Expr::Match(discrim, cases) => {
            check_expr(ctx, discrim)?;
            for (_, body) in cases {
                check_expr(ctx, body)?;
            }
            Ok(())
        }

        res::Expr::Let(_, rhs, body) => {
            check_expr(ctx, rhs)?;
            check_expr(ctx, body)?;
            Ok(())
        }

        res::Expr::ArrayLit(items) => {
            for item in items {
                check_expr(ctx, item)?;
            }
            Ok(())
        }

        res::Expr::ByteLit(_) => Ok(()),

        res::Expr::IntLit(_) => Ok(()),

        res::Expr::FloatLit(_) => Ok(()),

        res::Expr::Span(lo, hi, body) => check_expr(ctx, body).map_err(|err| Error {
            span: Some(err.span.unwrap_or((*lo, *hi))),
            ..err
        }),
    }
}

pub fn check_purity(program: &res::Program) -> Result<(), Error> {
    for (id, def) in &program.vals {
        check_expr(Purity::Pure, &def.body).map_err(|err| {
            debug_assert!(err.file.is_none());
            let val_mod = program.val_symbols[id].mod_;
            Error {
                file: Some(program.mod_symbols[val_mod].file.clone()),
                ..err
            }
        })?;
    }
    Ok(())
}
