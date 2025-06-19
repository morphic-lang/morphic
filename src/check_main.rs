use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use thiserror::Error;

#[derive(Clone, Debug, Error)]
#[error("`main` procedure must have type `proc () -> ()`")]
pub struct Error;

impl Error {
    pub fn report(&self) -> Report {
        Report {
            title: "Invalid `main`".to_string(),
            message: Some("`main` procedure must have type `proc () -> ()`".to_string()),
        }
    }
}

pub fn check_main(program: &typed::Program) -> Result<(), Error> {
    let main_scheme = &program.vals[program.main].scheme;

    if let res::TypeData::Func(purity, arg, ret) = &*main_scheme.body.data {
        if let res::TypeData::Tuple(arg_types) = &*arg.data {
            if let res::TypeData::Tuple(ret_types) = &*ret.data {
                if main_scheme.num_params == 0
                    && *purity == Purity::Impure
                    && arg_types.is_empty()
                    && ret_types.is_empty()
                {
                    return Ok(());
                }
            }
        }
    }

    Err(Error)
}
