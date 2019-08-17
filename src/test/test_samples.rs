use crate::test::run_sample::run_sample;

#[test]
fn io() {
    run_sample("samples/io.txt", "hello\n", "hello\n\n");
}

#[test]
fn iter() {
    run_sample(
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
    run_sample("samples/difference_lists.txt", "", "123\n");
}

#[test]
fn increment() {
    run_sample(
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
    run_sample("samples/arith.txt", "", "Completed all tests\n");
}

// TODO: Carefully review 'samples/mutate.txt' to determine by hand what the expected output should
// be, then add a test for it.
