// When 'lib.rs' exists, cargo treats 'main.rs' as a separate crate
use morphic_common::file_cache::FileCache;
use morphic_common::report_error::{ColorMode, Reportable};
use morphic_compiler::cli::Config;
use morphic_compiler::handle_config;

use std::io;

fn main() {
    better_panic::install();

    let config = Config::from_args();
    let mut files = FileCache::new();
    let result = handle_config(config, &mut files);
    if let Err(err) = result {
        let stderr = io::stderr();
        let color = ColorMode::for_stream(&stderr);
        let _ = err.report(&mut stderr.lock(), &files, color);
        std::process::exit(err.exit_status());
    }
}
