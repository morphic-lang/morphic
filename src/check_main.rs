use failure::Fail;

use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;

#[derive(Clone, Debug, Fail)]
#[fail(display = "`main` procedure must have type `proc () -> ()`")]
pub struct Error;

pub fn check_main(program: &typed::Program) -> Result<(), Error> {
    let main_scheme = &program.vals[program.main.0].scheme;

    let expected_scheme = res::TypeScheme {
        num_params: 0,
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
