use failure::Fail;

use crate::data::purity::Purity;
use crate::data::resolved_ast as res;

// TODO: Improve the specificity of these error messages!
#[derive(Clone, Debug, Fail)]
#[fail(display = "Cannot call an impure function from a pure function")]
pub struct Error(res::CustomGlobalId);

fn check_expr(ctx: Purity, expr: &res::Expr) -> Result<(), ()> {
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
                return Err(());
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
    }
}

pub fn check_purity(program: &res::Program) -> Result<(), Error> {
    for (idx, def) in program.vals.iter().enumerate() {
        check_expr(Purity::Pure, &def.body).map_err(|()| Error(res::CustomGlobalId(idx)))?;
    }
    Ok(())
}
