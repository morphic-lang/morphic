use crate::{
    check_exhaustive, check_main, check_polymorphic_recursion, check_purity, check_traits,
    kind_infer, resolve, solve_traits_in_bodies, solve_traits_in_signatures, type_infer,
};
use morphic_common::file_cache;
use morphic_common::report_error::{ColorMode, Reportable};
use std::io;

#[derive(Debug)]
pub enum Error {
    CreateArtifactsFailed(io::Error),
    WriteIrFailed(io::Error),
    ResolveFailed(resolve::Error),
    KindInferFailed(kind_infer::Error),
    PurityCheckFailed(check_purity::Error),
    CheckTraitsFailed(check_traits::Error),
    TypeInferFailed(type_infer::Error),
    SolveSignaturesFailed(solve_traits_in_signatures::Error),
    SolveTraitsFailed(solve_traits_in_bodies::Error),
    CheckExhaustiveFailed(check_exhaustive::Error),
    CheckMainFailed(check_main::Error),
    CheckPolymorphicRecursionFailed(check_polymorphic_recursion::Error),
    FindMltonFailed(String),
    RunMltonFailed(io::Error),
    FindOCamloptFailed(String),
    RunOCamloptFailed(io::Error),
}

impl Reportable for Error {
    fn report(
        &self,
        dest: &mut impl io::Write,
        files: &file_cache::FileCache,
        color: ColorMode,
    ) -> io::Result<()> {
        use Error::*;

        match &self {
            CreateArtifactsFailed(err) => {
                writeln!(dest, "Could not create artifacts directory: {}", err)
            }
            ResolveFailed(err) => err.report(dest, files, color),
            KindInferFailed(err) => err.report(dest, files, color),
            PurityCheckFailed(err) => err.report(dest, files, color),
            CheckTraitsFailed(err) => err.report(dest, files, color),
            TypeInferFailed(err) => err.report(dest, files, color),
            SolveSignaturesFailed(err) => err.report(dest, files, color),
            SolveTraitsFailed(err) => err.report(dest, files, color),
            CheckExhaustiveFailed(err) => err.report(dest, files, color),
            CheckMainFailed(err) => writeln!(dest, "{}", err),
            CheckPolymorphicRecursionFailed(err) => err.report(dest, files, color),
            WriteIrFailed(err) => writeln!(
                dest,
                "Could not write intermediate representation artifacts: {}",
                err
            ),
            FindMltonFailed(err) => writeln!(dest, "mlton not found:\n{}", err),
            RunMltonFailed(err) => writeln!(dest, "mlton failed: {}", err),
            FindOCamloptFailed(err) => writeln!(dest, "ocamlopt not found:\n{}", err),
            RunOCamloptFailed(err) => writeln!(dest, "ocamlopt failed: {}", err),
        }
    }

    fn exit_status(&self) -> i32 {
        1
    }
}
