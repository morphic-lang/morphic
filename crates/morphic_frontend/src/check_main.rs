use crate::data::kinded_ast as kinded;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use id_collections::IdVec;
use thiserror::Error;

#[derive(Clone, Debug, Error)]
#[error("`main` procedure must have type `proc () -> ()`")]
pub struct Error;

pub fn check_main(program: &typed::Program) -> Result<(), Error> {
    let main_scheme = &program.vals[program.main].scheme;

    let expected_scheme = kinded::TypeScheme {
        param_kinds: IdVec::new(),
        body: res::Type::Func(
            Purity::Impure,
            Box::new(res::Type::Tuple(vec![])),
            Box::new(res::Type::Tuple(vec![])),
        ),
    };

    if main_scheme != &expected_scheme {
        return Err(Error);
    }

    Ok(())
}
