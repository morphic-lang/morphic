use crate::cli;
use crate::pseudoprocess::{ExitStatus, Stdio};
use inkwell::targets::TargetMachine;
use std::path::Path;

// TODO: Add support for testing input/output sequences with "synchronization points," such as
// requiring that the program writes certain output before the test harness provides input, or
// requiring that the program conusmes certain input before the test harness expects output.

#[derive(Clone, Copy, Debug)]
pub enum Mode {
    Compile,
    Interpret,
}

pub fn run_sample<SrcPath: AsRef<Path>, In: AsRef<[u8]>, Out: AsRef<[u8]>>(
    mode: Mode,
    path: SrcPath,
    given_in: In,
    expected_out: Out,
) {
    let config = match mode {
        Mode::Compile => cli::Config::RunConfig(cli::RunConfig {
            src_path: path.as_ref().to_owned(),
            target: TargetMachine::get_default_triple(),
            target_cpu: TargetMachine::get_host_cpu_name().to_string(),
            target_features: TargetMachine::get_host_cpu_features().to_string(),
            stdio: Stdio::Piped,
        }),

        Mode::Interpret => cli::Config::InterpretConfig(cli::InterpretConfig {
            src_path: path.as_ref().to_owned(),
            stdio: Stdio::Piped,
        }),
    };

    let mut child = crate::run(config)
        .expect("Compilation failed")
        .expect("'run' should return a child process/thread");

    let mut stdin = child
        .stdin
        .take()
        .expect("Child process/thread should have captured stdin writer");

    let mut stdout = child
        .stdout
        .take()
        .expect("Child process/thread should have captured stdout reader");

    stdin
        .write_all(given_in.as_ref())
        .expect("Writing to child stdin failed");

    let mut output = Vec::with_capacity(expected_out.as_ref().len());
    stdout
        .read_to_end(&mut output)
        .expect("Reading from child stdout failed");

    let status = child
        .wait()
        .expect("Waiting on child process/thread failed");

    assert_eq!(
        status,
        ExitStatus::Success,
        "Child process returned failing exit status"
    );

    assert!(
        &output[..] == expected_out.as_ref(),
        r#"Program output did not match expected output:
      actual: {actual:?}
    expected: {expected:?}"#,
        actual = String::from_utf8_lossy(&output),
        expected = String::from_utf8_lossy(expected_out.as_ref())
    );
}
