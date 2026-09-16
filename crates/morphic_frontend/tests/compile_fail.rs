//! Check that each program under `samples/compile-fail` is rejected by the frontend with the
//! error named in its `// expect-error:` header comment.

use morphic_common::report_error::Reportable;
use morphic_common::{config as cfg, file_cache::FileCache, progress_ui::ProgressMode};
use std::path::{Path, PathBuf};

#[test]
fn compile_fail_samples_report_expected_errors() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../samples/compile-fail");

    let mut entry_points: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "mor"))
        .collect();
    entry_points.sort();
    assert!(!entry_points.is_empty());

    let mut failures = Vec::new();
    for path in &entry_points {
        let src = std::fs::read_to_string(path).unwrap();
        let expected = src
            .lines()
            .next()
            .and_then(|line| line.strip_prefix("// expect-error:"))
            .map(str::trim)
            .unwrap_or_else(|| panic!("{}: missing '// expect-error:' header", path.display()));

        let mut files = FileCache::new();
        let result = morphic_frontend::compile_to_typed_ast(
            path,
            &[],
            cfg::ProfileMode::NoRecordRc,
            None,
            &mut files,
            ProgressMode::Hidden,
            cfg::PurityMode::Checked,
        );

        match result {
            Ok(_) => failures.push(format!(
                "{}: compiled successfully, but expected the error '{}'",
                path.display(),
                expected
            )),
            Err(err) => {
                let mut rendered = Vec::new();
                err.report(&mut rendered, &files).unwrap();
                let rendered = String::from_utf8_lossy(&rendered);
                if rendered.contains(expected) {
                    println!("ok: {}", path.display());
                } else {
                    failures.push(format!(
                        "{}: expected the error '{}', but got:\n{}",
                        path.display(),
                        expected,
                        rendered
                    ));
                }
            }
        }
    }

    assert!(
        failures.is_empty(),
        "{} compile-fail sample(s) misbehaved:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
