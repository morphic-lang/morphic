use crate::test::run_sample::{run_sample, Mode};

#[test]
fn io() {
    run_sample(Mode::Interpret, "samples/io.txt", "hello\n", "hello\n");
}

#[test]
fn iter() {
    run_sample(
        Mode::Interpret,
        "samples/iter.txt",
        "",
        "\
         it worked\n\
         it worked\n\
         ",
    );
}

#[test]
fn difference_lists() {
    run_sample(Mode::Interpret, "samples/difference_lists.txt", "", "123");
}

#[test]
fn increment() {
    run_sample(
        Mode::Interpret,
        "samples/increment.txt",
        "",
        "\
         The following should both be 5:\n\
         5\n\
         5\n\
         ",
    );
}

#[test]
fn arith() {
    run_sample(
        Mode::Interpret,
        "samples/arith.txt",
        "",
        "Completed all tests\n",
    );
}

// TODO: Carefully review 'samples/mutate.txt' to determine by hand what the expected output should
// be, then add a test for it.
