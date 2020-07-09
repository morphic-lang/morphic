mod common;

use common::{read_line, repeat, write_report, ProfileInfo};

static COUNT_PRIMES_INFO: ProfileInfo = ProfileInfo::new();

fn count_primes(limit: u64) -> u64 {
    COUNT_PRIMES_INFO.record_call(|| {
        let mut accum = 0;
        for n in (2..limit).rev() {
            let mut composite = false;
            let mut i = 2;
            while i * i <= n {
                if n % i == 0 {
                    composite = true;
                    break;
                }
                i += 1;
            }
            if !composite {
                accum += 1;
            }
        }
        accum
    })
}

fn main() {
    match (read_line().parse::<u64>(), read_line().parse::<u64>()) {
        (Ok(iters), Ok(limit)) => {
            if let Some(result) = repeat(iters, || count_primes(limit)) {
                println!("There are {} primes <= {}", result, limit);
            }
        }

        (_, _) => {
            eprintln!("Please enter two positive integers (an iteration count and a limit)");
        }
    }

    write_report(&COUNT_PRIMES_INFO);
}
