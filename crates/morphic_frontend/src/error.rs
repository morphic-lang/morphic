use crate::{check_exhaustive, check_main, check_purity, resolve, type_infer};
use morphic_common::file_cache;
use morphic_common::report_error::Reportable;
use std::io;

#[derive(Debug)]
pub enum Error {
    CreateArtifactsFailed(io::Error),
    WriteIrFailed(io::Error),
    ResolveFailed(resolve::Error),
    PurityCheckFailed(check_purity::Error),
    TypeInferFailed(type_infer::Error),
    CheckExhaustiveFailed(check_exhaustive::Error),
    CheckMainFailed(check_main::Error),
}

impl Reportable for Error {
    fn report(&self, dest: &mut impl io::Write, files: &file_cache::FileCache) -> io::Result<()> {
        use Error::*;

        match &self {
            CreateArtifactsFailed(err) => {
                writeln!(dest, "Could not create artifacts directory: {}", err)
            }
            ResolveFailed(err) => err.report(dest, files),
            PurityCheckFailed(err) => err.report(dest, files),
            TypeInferFailed(err) => err.report(dest, files),
            CheckExhaustiveFailed(err) => err.report(dest, files),
            CheckMainFailed(err) => writeln!(dest, "{}", err),
            WriteIrFailed(err) => writeln!(
                dest,
                "Could not write intermediate representation artifacts: {}",
                err
            ),
        }
    }

    fn exit_status(&self) -> i32 {
        1
    }
}
