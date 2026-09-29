use crate::data::elaborated_ast as elab;
use crate::data::purity::Purity;
use crate::data::solved_ast as solved;
use id_collections::IdVec;
use thiserror::Error;

#[derive(Clone, Debug, Error)]
#[error("`main` procedure must have type `proc () -> ()`")]
pub struct Error;

pub fn check_main(program: &solved::Program) -> Result<(), Error> {
    let main_scheme = &program.vals[program.main].scheme;

    let expected_scheme = elab::TypeScheme {
        param_kinds: IdVec::new(),
        trait_constrs: IdVec::new(),
        body: elab::Type::Func(
            Purity::Impure,
            Box::new(elab::Type::Tuple(vec![])),
            Box::new(elab::Type::Tuple(vec![])),
        ),
    };

    if main_scheme != &expected_scheme {
        return Err(Error);
    }

    Ok(())
}
