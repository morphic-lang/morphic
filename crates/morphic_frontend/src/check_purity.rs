use std::io;

use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::file_cache::FileCache;
use morphic_common::lines;
use morphic_common::report_error::{locate_path, locate_span, Locate, Reportable};

#[derive(Clone, Copy, Debug)]
pub struct PurityError;

type RawError = Locate<PurityError>;

#[derive(Debug)]
pub struct Error(RawError);

impl Reportable for Error {
    fn report(&self, dest: &mut impl io::Write, files: &FileCache) -> io::Result<()> {
        self.0.report_with(dest, files, |PurityError| {
            (
                "Purity Mismatch",
                lines![
                    "You cannot call a function with side effects from inside a pure function.",
                    "",
                    "Maybe you didn't mean to mark the calling function as pure?  All function \
                     definitions are considered pure by default.  You can mark the calling \
                     function as having side effects by adding the keyword 'proc' before the \
                     function's definition.",
                ],
            )
        })
    }

    fn exit_status(&self) -> i32 {
        1
    }
}

fn check_expr(ctx: Purity, expr: &res::Expr) -> Result<(), RawError> {
    match expr {
        res::Expr::Global(_) => Ok(()),

        res::Expr::Local(_) => Ok(()),

        res::Expr::Tuple(items) => {
            for item in items {
                check_expr(ctx, item)?;
            }
            Ok(())
        }

        res::Expr::Lam(purity, _, body, _) => {
            check_expr(*purity, body)?;
            Ok(())
        }

        res::Expr::App(purity, func, arg) => {
            if ctx == Purity::Pure && *purity == Purity::Impure {
                return Err(PurityError.into());
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

        res::Expr::LetMany(bindings, body) => {
            for (_lhs, rhs) in bindings {
                check_expr(ctx, rhs)?;
            }

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

        res::Expr::Span(lo, hi, body) => check_expr(ctx, body).map_err(locate_span(*lo, *hi)),
    }
}

pub fn check_purity(program: &res::Program) -> Result<(), Error> {
    for (id, def) in &program.vals {
        check_expr(Purity::Pure, &def.body)
            .map_err(locate_path(
                &program.mod_symbols[program.val_symbols[id].mod_].file,
            ))
            .map_err(Error)?;
    }
    Ok(())
}
