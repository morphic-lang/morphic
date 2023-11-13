use crate::cli;
use crate::file_cache::FileCache;
use crate::pseudoprocess::{ExitStatus, Stdio};
use std::path::Path;

// TODO: Add support for testing input/output sequences with "synchronization points," such as
// requiring that the program writes certain output before the test harness provides input, or
// requiring that the program conusmes certain input before the test harness expects output.

pub fn run_sample<SrcPath: AsRef<Path>, In: AsRef<[u8]>, Out: AsRef<[u8]>, Err: AsRef<[u8]>>(
    mode: cli::RunMode,
    rc_mode: cli::RcMode,
    mutation_mode: cli::MutationMode,
    path: SrcPath,
    given_in: In,
    expected_out: Out,
    expected_err: Err,
    expected_status: ExitStatus,
) {
    let config = cli::RunConfig {
        src_path: path.as_ref().to_owned(),
        mode,
        rc_mode,
        mutation_mode,
        stdio: Stdio::Piped,
    };

    let mut child = crate::run(config, &mut FileCache::new()).expect("Compilation failed");

    let mut stdin = child
        .stdin
        .take()
        .expect("Child process/thread should have captured stdin writer");

    let mut stdout = child
        .stdout
        .take()
        .expect("Child process/thread should have captured stdout reader");

    let mut stderr = child
        .stderr
        .take()
        .expect("Child process/thread should have captured stdout reader");

    stdin
        .write_all(given_in.as_ref())
        .expect("Writing to child stdin failed");

    let mut output = Vec::with_capacity(expected_out.as_ref().len());
    stdout
        .read_to_end(&mut output)
        .expect("Reading from child stdout failed");

    let mut err_output = Vec::with_capacity(expected_out.as_ref().len());
    stderr
        .read_to_end(&mut err_output)
        .expect("Reading from child stdout failed");

    let status = child
        .wait()
        .expect("Waiting on child process/thread failed");

    assert_eq!(
        status, expected_status,
        "Child process returned unexpected status"
    );

    assert!(
        &output[..] == expected_out.as_ref(),
        r#"Program output did not match expected output:
      actual: {actual:?}
    expected: {expected:?}"#,
        actual = String::from_utf8_lossy(&output),
        expected = String::from_utf8_lossy(expected_out.as_ref())
    );

    assert!(
        &err_output[..] == expected_err.as_ref(),
        r#"Program stderr did not match expected stderr:
      actual: {actual:?}
    expected: {expected:?}"#,
        actual = String::from_utf8_lossy(&err_output),
        expected = String::from_utf8_lossy(expected_err.as_ref())
    );
}

macro_rules! sample_interpret {
    (
        $name:ident $path:expr ;
        $( rc_mode = $rc_mode:expr ; )?
        $( mutation_mode = $mutation_mode:expr ; )?
        stdin = $stdin:expr ;
        stdout = $stdout:expr ;
        $( stderr = $stderr:expr; )?
        $( status = $status:expr; )?
    ) => {
        #[test]
        fn interpret() {
            #[allow(unused_mut, unused_assignments)]
            let mut rc_mode = crate::cli::RcMode::default();
            #[allow(unused_mut, unused_assignments)]
            let mut mutation_mode = crate::cli::MutationMode::default();
            #[allow(unused_mut, unused_assignments)]
            let mut stderr: String = "".into();
            #[allow(unused_mut, unused_assignments)]
            let mut status = crate::pseudoprocess::ExitStatus::Success;

            $(
                rc_mode = $rc_mode;
            )?

            $(
                mutation_mode = $mutation_mode;
            )?

            $(
                stderr = $stderr.into();
            )?

            $(
                status = $status;
            )?

            crate::test::run_sample::run_sample(
                crate::cli::RunMode::Interpret,
                rc_mode,
                mutation_mode,
                $path,
                $stdin,
                $stdout,
                stderr,
                status,
            );
        }
    };
}

macro_rules! sample_compile {
    (
        $name:ident $path:expr ;
        $( rc_mode = $rc_mode:expr ; )?
        $( mutation_mode = $mutation_mode:expr ; )?
        stdin = $stdin:expr ;
        stdout = $stdout:expr ;
        $( stderr = $stderr:expr; )?
        $( status = $status:expr; )?
        $( leak_check = $leak_check:expr; )?
    ) => {
        #[test]
        fn compile() {
            #[allow(unused_mut, unused_assignments)]
            let mut rc_mode = crate::cli::RcMode::default();
            #[allow(unused_mut, unused_assignments)]
            let mut mutation_mode = crate::cli::MutationMode::default();
            #[allow(unused_mut, unused_assignments)]
            let mut stderr: String = "".into();
            #[allow(unused_mut, unused_assignments)]
            let mut status = crate::pseudoprocess::ExitStatus::Success;

            $(
                rc_mode = $rc_mode;
            )?

            $(
                mutation_mode = $mutation_mode;
            )?

            $(
                stderr = $stderr.into();
            )?

            $(
                status = $status;
            )?

            #[allow(unused_mut)]
            let mut valgrind = crate::pseudoprocess::ValgrindConfig { leak_check: true };

            $(
                valgrind.leak_check = $leak_check;
            )?

            crate::test::run_sample::run_sample(
                crate::cli::RunMode::Compile { valgrind: Some(valgrind) },
                rc_mode,
                mutation_mode,
                $path,
                $stdin,
                $stdout,
                stderr,
                status,
            );
        }
    };
}

macro_rules! sample {
    (
        $name:ident $path:expr ;
        $( rc_mode = $rc_mode:expr ; )?
        $( mutation_mode = $mutation_mode:expr ; )?
        stdin = $stdin:expr ;
        stdout = $stdout:expr ;
        $( stderr = $stderr:expr; )?
        $( status = $status:expr; )?
        $( leak_check = $leak_check:expr; )?
    ) => {
        mod $name {
            #[allow(unused_imports)]
            use super::*;

            sample_interpret! {
                $name $path ;
                $( rc_mode = $rc_mode ; )?
                $( mutation_mode = $mutation_mode ; )?
                stdin = $stdin ;
                stdout = $stdout ;
                $( stderr = $stderr ; )?
                $( status = $status ; )?
            }

            sample_compile! {
                $name $path ;
                $( rc_mode = $rc_mode ; )?
                $( mutation_mode = $mutation_mode ; )?
                stdin = $stdin ;
                stdout = $stdout ;
                $( stderr = $stderr ; )?
                $( status = $status ; )?
                $( leak_check = $leak_check ; )?
            }
        }
    };

    (
        $name:ident $path:expr ;
        $( rc_mode = $rc_mode:expr ; )?
        $( mutation_mode = $mutation_mode:expr ; )?
        compile_only = true ;
        stdin = $stdin:expr ;
        stdout = $stdout:expr ;
        $( stderr = $stderr:expr; )?
        $( status = $status:expr; )?
        $( leak_check = $leak_check:expr; )?
    ) => {
        mod $name {
            #[allow(unused_imports)]
            use super::*;

            sample_compile! {
                $name $path ;
                $( rc_mode = $rc_mode ; )?
                $( mutation_mode = $mutation_mode ; )?
                stdin = $stdin ;
                stdout = $stdout ;
                $( stderr = $stderr ; )?
                $( status = $status ; )?
                $( leak_check = $leak_check ; )?
            }
        }
    };
}
