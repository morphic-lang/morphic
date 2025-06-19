use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::lines::lines;

#[derive(Clone, Copy, Debug)]
pub struct PurityError;

pub type Error = Locate<PurityError>;

impl Error {
    pub fn report(&self) -> Report {
        Report {
            title: "Purity Mismatch".to_string(),
            message: Some(lines![
                "You cannot call a function with side effects from inside a pure function.",
                "",
                "Maybe you didn't mean to mark the calling function as pure?  All function \
                 definitions are considered pure by default.  You can mark the calling \
                 function as having side effects by adding the keyword 'proc' before the \
                 function's definition.",
            ]),
        }
    }
}

fn check_expr(ctx: Purity, expr: &res::Expr) -> Result<(), Error> {
    match &*expr.data {
        res::ExprData::Global(_) => Ok(()),

        res::ExprData::Local(_) => Ok(()),

        res::ExprData::Tuple(items) => {
            for item in items {
                check_expr(ctx, item)?;
            }
            Ok(())
        }

        res::ExprData::Lam(purity, _, body, _) => {
            check_expr(*purity, body)?;
            Ok(())
        }

        res::ExprData::App(purity, func, arg) => {
            if ctx == Purity::Pure && *purity == Purity::Impure {
                return Err(PurityError.into());
            }

            check_expr(ctx, func)?;
            check_expr(ctx, arg)?;
            Ok(())
        }

        res::ExprData::Match(discrim, cases) => {
            check_expr(ctx, discrim)?;
            for (_, body) in cases {
                check_expr(ctx, body)?;
            }
            Ok(())
        }

        res::ExprData::LetMany(bindings, body) => {
            for (_lhs, rhs) in bindings {
                check_expr(ctx, rhs)?;
            }

            check_expr(ctx, body)?;
            Ok(())
        }

        res::ExprData::ArrayLit(items) => {
            for item in items {
                check_expr(ctx, item)?;
            }
            Ok(())
        }

        res::ExprData::ByteLit(_) => Ok(()),

        res::ExprData::IntLit(_) => Ok(()),

        res::ExprData::FloatLit(_) => Ok(()),

        res::ExprData::Error(_) => Ok(()),
    }
}

pub fn check_purity(program: &res::Program) -> Result<(), Error> {
    for (id, def) in &program.vals {
        check_expr(Purity::Pure, &def.body).map_err(locate_path(
            &program.mod_symbols[program.val_symbols[id].mod_].file,
        ))?;
    }
    Ok(())
}
