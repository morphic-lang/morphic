use std::convert::TryFrom;
use std::fs::File;
use std::io::{stdin, BufRead, Write};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

pub struct ProfileInfo {
    total_calls: AtomicU64,
    total_clock_nanos: AtomicU64,
}

impl ProfileInfo {
    pub const fn new() -> ProfileInfo {
        ProfileInfo {
            total_calls: AtomicU64::new(0),
            total_clock_nanos: AtomicU64::new(0),
        }
    }

    pub fn record_call<T>(&self, body: impl FnOnce() -> T) -> T {
        let start = Instant::now();
        let result = body();
        let elapsed = start.elapsed();

        self.total_calls.fetch_add(1, Ordering::SeqCst);
        self.total_clock_nanos
            .fetch_add(u64::try_from(elapsed.as_nanos()).unwrap(), Ordering::SeqCst);

        result
    }
}

pub fn write_report(info: &ProfileInfo) {
    let report_path = match std::env::var_os("MORPHIC_PROFILE_PATH") {
        Some(path) => path,
        None => {
            eprintln!("Warning: no MORPHIC_PROFILE_PATH provided");
            return;
        }
    };

    let mut report_file = File::create(&report_path).expect("Could not open profile report file");

    writeln!(
        &mut report_file,
        "{{\"total_calls\": {}, \"total_clock_nanos\": {}}}",
        info.total_calls.load(Ordering::SeqCst),
        info.total_clock_nanos.load(Ordering::SeqCst)
    )
    .expect("Could not write profiling informtion to report file");
}

pub fn read_line() -> String {
    let mut input = String::new();
    stdin().lock().read_line(&mut input).unwrap();
    input.pop();
    input
}

pub fn repeat<T>(iters: u64, mut body: impl FnMut() -> T) -> Option<T> {
    let mut result = None;
    for _ in 0..iters {
        result = Some(body());
    }
    result
}
