// When 'lib.rs' exists, cargo treats 'main.rs' as a separate crate
use opt_proto::cli::Config;
use opt_proto::file_cache::FileCache;
use opt_proto::handle_config;

use std::io;

fn main() {
    better_panic::install();

    let config = Config::from_args();
    let mut files = FileCache::new();
    let result = handle_config(config, &mut files);
    if let Err(err) = result {
        let _ = err.report(&mut io::stderr().lock(), &files);
        std::process::exit(err.exit_status());
    }
}
