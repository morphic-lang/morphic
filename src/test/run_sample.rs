use crate::cli;
use inkwell::targets::TargetMachine;
use std::io::Cursor;
use std::path::Path;

// TODO: Add support for testing input/output sequences with "synchronization points," such as
// requiring that the program writes certain output before the test harness provides input, or
// requiring that certain the program conusmes certain input before the test harness expects output.

pub fn run_sample<SrcPath: AsRef<Path>, In: AsRef<[u8]>, Out: AsRef<[u8]>>(
    path: SrcPath,
    given_in: In,
    expected_out: Out,
) {
    println!("Simulating");

    let mut stdin = Cursor::new(given_in);
    let mut stdout = Vec::new();

    let result = crate::run(
        &mut stdin,
        &mut stdout,
        cli::Config {
            src_path: path.as_ref().to_owned(),
            target: TargetMachine::get_default_triple().to_string(),
            target_cpu: TargetMachine::get_host_cpu_name().to_string(),
            target_features: TargetMachine::get_host_cpu_features().to_string(),
            sub_command_config: cli::SubCommandConfig::RunConfig(),
        },
    );

    if let Err(err) = result {
        panic!("Compilation failed: {}\n{:?}", err, err);
    }

    let stdin_pos = stdin.position();
    let stdin_buf = stdin.get_ref().as_ref();
    assert!(
        stdin_pos == stdin_buf.len() as u64,
        "Too few bytes read.  Remaining expected: {:?}",
        String::from_utf8_lossy(stdin_buf)
    );

    assert!(
        &stdout[..] == expected_out.as_ref(),
        r#"Program output did not match expected output:
      actual: {actual:?}
    expected: {expected:?}"#,
        actual = String::from_utf8_lossy(&stdout),
        expected = String::from_utf8_lossy(expected_out.as_ref())
    );
}
