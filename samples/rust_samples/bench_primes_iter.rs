mod common;

use common::{read_line, repeat, write_report, ProfileInfo};

static COUNT_PRIMES_INFO: ProfileInfo = ProfileInfo::new();

fn is_prime(n: u64) -> bool {
    !(2..).take_while(|i| i * i <= n).any(|i| n % i == 0)
}

fn primes_to(limit: u64) -> impl Iterator<Item = u64> {
    (2..limit + 1).filter(|&n| is_prime(n))
}

fn count_primes(n: u64) -> u64 {
    COUNT_PRIMES_INFO.record_call(|| primes_to(n).count() as u64)
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
