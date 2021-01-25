mod common;

use common::{read_line, repeat, write_report, ProfileInfo, Int};

static COUNT_PRIMES_INFO: ProfileInfo = ProfileInfo::new();

fn partition(ints: &mut [Int]) -> usize {
    let pivot = ints[ints.len() - 1];
    let mut i = 0;
    for j in 0..(ints.len() - 1) {
        if ints[j] < pivot {
            ints.swap(i, j);
            i += 1;
        }
    }
    ints.swap(i, ints.len() - 1);
    return i;
}

fn quicksort_help(ints: &mut [Int]) {
    if ints.len() > 1 {
        let sep = partition(ints);
        quicksort_help(&mut ints[0..sep]);
        quicksort_help(&mut ints[sep + 1..]);
    }
}

fn quicksort(ints: &mut [Int]) {
    COUNT_PRIMES_INFO.record_call(|| {
        quicksort_help(ints);
    });
}

fn read_ints() -> Vec<Int> {
    let mut ints = Vec::new();
    while let Ok(int) = read_line().parse::<Int>() {
        ints.push(int);
    }
    ints
}

fn cpy(dst: &mut [Int], src: &[Int]) {
    for i in 0..dst.len() {
        dst[i] = src[i];
    }
}

fn main() {
    match (read_line().parse::<u64>(), read_line().parse::<u64>(), read_ints()) {
        (Ok(iters), _length, ints) => {
            let mut buf = ints.clone();
            let result = repeat(iters, || {
                cpy(&mut buf, &ints);
                quicksort(&mut buf);
            });
            if let Some(()) = result {
                println!("The sorted version of\n  {:?}", ints);
                println!("is\n  {:?}", buf);
            }
        }

        (_, _, _) => {
            eprintln!("Please enter two positive integers (an iteration count and a limit)");
        }
    }

    write_report(&COUNT_PRIMES_INFO);
}

