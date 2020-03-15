use crate::cli;
use crate::pseudoprocess::{ExitStatus, Stdio};
use std::path::Path;

// TODO: Add support for testing input/output sequences with "synchronization points," such as
// requiring that the program writes certain output before the test harness provides input, or
// requiring that the program conusmes certain input before the test harness expects output.

pub fn run_sample<SrcPath: AsRef<Path>, In: AsRef<[u8]>, Out: AsRef<[u8]>>(
    mode: cli::RunMode,
    path: SrcPath,
    given_in: In,
    expected_out: Out,
) {
    let config = cli::Config::RunConfig(cli::RunConfig {
        src_path: path.as_ref().to_owned(),
        mode,
        stdio: Stdio::Piped,
    });

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

macro_rules! sample {
    ($name:ident $path:expr ; stdin = $stdin:expr ; stdout = $stdout:expr ; ) => {
        mod $name {
            #[test]
            fn interpret() {
                crate::test::run_sample::run_sample(
                    crate::cli::RunMode::Interpret,
                    $path,
                    $stdin,
                    $stdout,
                );
            }

            #[test]
            fn compile() {
                crate::test::run_sample::run_sample(
                    crate::cli::RunMode::Compile,
                    $path,
                    $stdin,
                    $stdout,
                );
            }
        }
    };
}

macro_rules! lines {
    ($($line:expr),* $(,)?) => { ( {
        let mut result = String::new();
        $(
            result.push_str(&$line);
            result.push('\n');
        )*
        result
    } ) }
}
