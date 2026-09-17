//! Check that every sample entry point still passes the frontend

use morphic_common::{config as cfg, file_cache::FileCache, progress_ui::ProgressMode};
use std::path::{Path, PathBuf};

#[test]
fn all_samples_compile_to_solved_ast() {
    let samples_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../samples");

    let mut entry_points: Vec<PathBuf> = Vec::new();
    for dir in [samples_root.clone(), samples_root.join("run-fail")] {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|ext| ext == "mor") {
                entry_points.push(path);
            }
        }
    }
    entry_points.sort();
    assert!(!entry_points.is_empty());

    let mut failures = Vec::new();
    for path in &entry_points {
        let result = morphic_frontend::compile_to_solved_ast(
            path,
            &[],
            cfg::ProfileMode::NoRecordRc,
            None,
            &mut FileCache::new(),
            ProgressMode::Hidden,
            cfg::PurityMode::Checked,
        );
        match result {
            Ok(_) => println!("ok: {}", path.display()),
            Err(err) => failures.push(format!("{}: {:?}", path.display(), err)),
        }
    }

    assert!(
        failures.is_empty(),
        "{} sample(s) failed to compile:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
