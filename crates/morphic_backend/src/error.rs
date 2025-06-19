use crate::llvm_gen;
use morphic_common::file_cache;
use morphic_common::report_error::Reportable;
use std::io;

#[derive(Debug)]
pub enum Error {
    WriteIrFailed(io::Error),
    LlvmGenFailed(llvm_gen::Error),
}

impl Reportable for Error {
    fn report(&self, dest: &mut impl io::Write, _files: &file_cache::FileCache) -> io::Result<()> {
        use Error::*;

        match &self {
            WriteIrFailed(err) => writeln!(
                dest,
                "Could not write intermediate representation artifacts: {}",
                err
            ),
            LlvmGenFailed(err) => writeln!(dest, "{}", err),
        }
    }

    fn exit_status(&self) -> i32 {
        1
    }
}
