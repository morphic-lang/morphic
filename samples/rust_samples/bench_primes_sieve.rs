mod common;

use common::{read_line, repeat, write_report, ProfileInfo};

static SIEVE_INFO: ProfileInfo = ProfileInfo::new();

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Primality {
    Prime,
    Composite,
}

fn sieve(limit: u64) -> Vec<Primality> {
    SIEVE_INFO.record_call(|| {
        let mut arr = vec![Primality::Prime; limit as usize];
        arr[0] = Primality::Composite;
        arr[1] = Primality::Composite;

        for n in 2..limit {
            if arr[n as usize] == Primality::Prime {
                let mut i = 2 * n;
                while i < limit {
                    arr[i as usize] = Primality::Composite;
                    i += n;
                }
            }
        }

        arr
    })
}

fn main() {
    match (read_line().parse::<u64>(), read_line().parse::<u64>()) {
        (Ok(iters), Ok(limit)) => {
            if let Some(primes) = repeat(iters, || sieve(limit)) {
                for i in 0..limit {
                    match primes[i as usize] {
                        Primality::Prime => println!("{}", i),
                        Primality::Composite => {}
                    }
                }
            }
        }

        (_, _) => eprintln!("Please enter two positive integers (an iteration count and a limit)"),
    }

    write_report(&SIEVE_INFO);
}
