use crate::cli::{RunConfig, RunMode};
use crate::pseudoprocess::{ExitStatus, Stdio};
use morphic_common::config as cfg;
use morphic_common::file_cache::FileCache;
use std::path::Path;

// TODO: Add support for testing input/output sequences with "synchronization points," such as
// requiring that the program writes certain output before the test harness provides input, or
// requiring that the program conusmes certain input before the test harness expects output.

pub fn run_sample<SrcPath: AsRef<Path>, In: AsRef<[u8]>, Out: AsRef<[u8]>, Err: AsRef<[u8]>>(
    mode: RunMode,
    rc_strat: cfg::RcStrategy,
    path: SrcPath,
    given_in: In,
    expected_out: Out,
    expected_err: Err,
    expected_status: ExitStatus,
) {
    let config = RunConfig {
        src_path: path.as_ref().to_owned(),
        purity_mode: cfg::PurityMode::Checked,
        mode,
        pass_options: cfg::PassOptions {
            rc_strat,
            ..Default::default()
        },
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

    assert!(
        status == expected_status
            && &output[..] == expected_out.as_ref()
            && &err_output[..] == expected_err.as_ref(),
        r#"Program execution did not match expectations:
            status:   {actual_status:?}
            expected: {expected_status:?}
            ---------------------------------------------
            stdout (length = {actual_stdout_len} bytes):
{actual_stdout:?}
            expected stdout (length = {expected_stdout_len} bytes):
{expected_stdout:?}
            ---------------------------------------------
            stderr (length = {actual_stderr_len} bytes):
{actual_stderr:?}
            expected stderr (length = {expected_stderr_len} bytes):
{expected_stderr:?}"#,
        actual_status = status,
        expected_status = expected_status,
        actual_stdout = String::from_utf8_lossy(&output),
        expected_stdout = String::from_utf8_lossy(expected_out.as_ref()),
        actual_stderr = String::from_utf8_lossy(&err_output),
        expected_stderr = String::from_utf8_lossy(expected_err.as_ref()),
        actual_stdout_len = output.len(),
        expected_stdout_len = expected_out.as_ref().len(),
        actual_stderr_len = err_output.len(),
        expected_stderr_len = expected_err.as_ref().len(),
    );
}

macro_rules! sample_interpret {
    (
        $name:ident $path:expr ;
        $( rc_strat = $rc_strat:expr ; )?
        stdin = $stdin:expr ;
        stdout = $stdout:expr ;
        $( stderr = $stderr:expr; )?
        $( status = $status:expr; )?
    ) => {
        #[test]
        fn interpret() {
            #[allow(unused_mut, unused_assignments)]
            let mut rc_strat = crate::cfg::RcStrategy::Default;
            #[allow(unused_mut, unused_assignments)]
            let mut stderr: String = "".into();
            #[allow(unused_mut, unused_assignments)]
            let mut status = crate::pseudoprocess::ExitStatus::Success;

            $(
                rc_strat = $rc_strat;
            )?

            $(
                stderr = $stderr.into();
            )?

            $(
                status = $status;
            )?

            crate::test::run_sample::run_sample(
                crate::cli::RunMode::Interpret,
                rc_strat,
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
        $( rc_strat = $rc_strat:expr ; )?
        stdin = $stdin:expr ;
        stdout = $stdout:expr ;
        $( stderr = $stderr:expr; )?
        $( status = $status:expr; )?
        $( leak_check = $leak_check:expr; )?
    ) => {
        #[test]
        fn compile() {
            #[allow(unused_mut, unused_assignments)]
            let mut rc_strat = crate::cfg::RcStrategy::Default;
            #[allow(unused_mut, unused_assignments)]
            let mut stderr: String = "".into();
            #[allow(unused_mut, unused_assignments)]
            let mut status = crate::pseudoprocess::ExitStatus::Success;

            $(
                rc_strat = $rc_strat;
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
                rc_strat,
                $path,
                $stdin,
                $stdout,
                stderr,
                status,
            );
        }
    };
}

macro_rules! sample_rc_strat {
    (
        $name:ident $path:expr ;
        $( rc_strat = $rc_strat:expr ; )?
        stdin = $stdin:expr ;
        stdout = $stdout:expr ;
        $( stderr = $stderr:expr; )?
        $( status = $status:expr; )?
        $( leak_check = $leak_check:expr; )?
    ) => {
        sample_interpret! {
            $name $path ;
            $( rc_strat = $rc_strat ; )?
            stdin = $stdin ;
            stdout = $stdout ;
            $( stderr = $stderr ; )?
            $( status = $status ; )?
        }

        sample_compile! {
            $name $path ;
            $( rc_strat = $rc_strat ; )?
            stdin = $stdin ;
            stdout = $stdout ;
            $( stderr = $stderr ; )?
            $( status = $status ; )?
            $( leak_check = $leak_check ; )?
        }
    };

    (
        $name:ident $path:expr ;
        $( rc_strat = $rc_strat:expr ; )?
        compile_only = true ;
        stdin = $stdin:expr ;
        stdout = $stdout:expr ;
        $( stderr = $stderr:expr; )?
        $( status = $status:expr; )?
        $( leak_check = $leak_check:expr; )?
    ) => {
        sample_compile! {
            $name $path ;
            $( rc_strat = $rc_strat ; )?
            stdin = $stdin ;
            stdout = $stdout ;
            $( stderr = $stderr ; )?
            $( status = $status ; )?
            $( leak_check = $leak_check ; )?
        }
    };
}

macro_rules! sample {
    (
        $name:ident $path:expr ;
        $( compile_only = $compile_only:tt ; )?
        stdin = $stdin:expr ;
        stdout = $stdout:expr ;
        $( stderr = $stderr:expr; )?
        $( status = $status:expr; )?
        $( leak_check = $leak_check:expr; )?
    ) => {
        mod $name {
            #[allow(unused_imports)]
            use super::*;

            mod rc_default {
                #[allow(unused_imports)]
                use super::*;
                sample_rc_strat! {
                    $name $path ;
                    rc_strat = crate::cfg::RcStrategy::Default;
                    $( compile_only = $compile_only ; )?
                    stdin = $stdin ;
                    stdout = $stdout ;
                    $( stderr = $stderr ; )?
                    $( status = $status ; )?
                    $( leak_check = $leak_check ; )?
                }
            }

            mod rc_perceus {
                #[allow(unused_imports)]
                use super::*;
                sample_rc_strat! {
                    $name $path ;
                    rc_strat = crate::cfg::RcStrategy::Perceus;
                    $( compile_only = $compile_only ; )?
                    stdin = $stdin ;
                    stdout = $stdout ;
                    $( stderr = $stderr ; )?
                    $( status = $status ; )?
                    $( leak_check = $leak_check ; )?
                }
            }
        }
    };

    (
        $name:ident $path:expr ;
        rc_strat = $rc_strat:expr ;
        $( compile_only = $compile_only:tt ; )?
        stdin = $stdin:expr ;
        stdout = $stdout:expr ;
        $( stderr = $stderr:expr; )?
        $( status = $status:expr; )?
        $( leak_check = $leak_check:expr; )?
    ) => {
        mod $name {
            #[allow(unused_imports)]
            use super::*;

            sample_rc_strat! {
                $name $path ;
                rc_strat = $rc_strat;
                $( compile_only = $compile_only ; )?
                stdin = $stdin ;
                stdout = $stdout ;
                $( stderr = $stderr ; )?
                $( status = $status ; )?
                $( leak_check = $leak_check ; )?
            }
        }
    }
}
