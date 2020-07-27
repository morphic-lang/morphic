use crate::pseudoprocess::ExitStatus::Failure;

sample! { io "samples/io.mor";
    stdin = "hello\n";
    stdout = "hello\n";
}

sample! { zero_sized_array "samples/zero_sized_array.mor";
    stdin = "";
    stdout = "Completed all tests\n";
}

sample! { iter "samples/iter.mor";
    stdin = "";
    stdout = lines! [
        "it worked",
        "it worked",
    ];
}

sample! { difference_lists "samples/difference_lists.mor";
    stdin = "";
    stdout = "123";
}

sample! { increment "samples/increment.mor";
    stdin = "";
    stdout = lines! [
        "The following should both be 5:",
        "5",
        "5",
    ];
}

sample! { arith "samples/arith.mor";
    stdin = "";
    stdout = "Completed all tests\n";
}

sample! { concat_persistent "samples/concat_persistent.mor";
    stdin = "";
    stdout = lines! [
        "hello",
        "hello world",
    ];
}

sample! { index_tree "samples/index_tree.mor";
    stdin = "";
    stdout = lines! [
        "Original tree:",
        "Branch(",
        "  Leaf(foo),",
        "  Branch(",
        "    Branch(",
        "      Leaf(bar),",
        "      Leaf(baz)",
        "    ),",
        "    Leaf(quux)",
        "  )",
        ")",
        "Indexed tree:",
        "Branch(",
        "  Leaf(0, foo),",
        "  Branch(",
        "    Branch(",
        "      Leaf(1, bar),",
        "      Leaf(2, baz)",
        "    ),",
        "    Leaf(3, quux)",
        "  )",
        ")",
        // Test again with persistent arrays in the leaves
        "Original tree:",
        "Branch(",
        "  Leaf(foo),",
        "  Branch(",
        "    Branch(",
        "      Leaf(bar),",
        "      Leaf(baz)",
        "    ),",
        "    Leaf(quux)",
        "  )",
        ")",
        "Indexed tree:",
        "Branch(",
        "  Leaf(0, foo),",
        "  Branch(",
        "    Branch(",
        "      Leaf(1, bar),",
        "      Leaf(2, baz)",
        "    ),",
        "    Leaf(3, quux)",
        "  )",
        ")",
    ];
}

sample! { nested "samples/nested.mor";
    stdin = "";
    stdout = lines! [
        "hello",
        "world",
        "hello",
        "moon",
        "hello",
        "mars",
    ];
}

sample! { mutual_tail_rec "samples/mutual_tail_rec.mor";
    stdin = "";
    stdout = lines! [
        "1000 is even",
        "1000 is not odd",
    ];
}

sample! { mutate "samples/mutate.mor";
    stdin = "";
    stdout = lines! [
        "vvvvvvv",
        "1",
        "2",
        "3",
        "4",
        "5",
        "^^^^^^^",
        "vvvvvvv",
        "2",
        "3",
        "4",
        "5",
        "6",
        "^^^^^^^",
        "vvvvvvv",
        "4",
        "9",
        "16",
        "25",
        "36",
        "^^^^^^^",
        "vvvvvvv",
        "36",
        "25",
        "16",
        "9",
        "4",
        "^^^^^^^",
    ];
}

sample! { recursive_array "samples/recursive_array.mor";
    stdin = "";
    stdout = "";
}

// Samples expected to fail at runtime:

sample! { item_oob1 "samples/run-fail/item_oob1.mor";
    stdin = "";
    stdout = "";
    stderr = "index out of bounds: attempt to access item 3 of array with length 3\n";
    status = Failure(Some(1));
    leak_check = false;
}

sample! { item_oob2 "samples/run-fail/item_oob2.mor";
    stdin = "";
    stdout = "";
    stderr = "index out of bounds: attempt to access item -1 of array with length 3\n";
    status = Failure(Some(1));
    leak_check = false;
}

sample! { pop_empty "samples/run-fail/pop_empty.mor";
    stdin = "";
    stdout = "";
    stderr = "pop: empty array\n";
    status = Failure(Some(1));
    leak_check = false;
}

sample! { div_zero_byte "samples/run-fail/div_zero_byte.mor";
    stdin = "";
    stdout = "";
    stderr = "panicked due to division by zero\n";
    status = Failure(Some(1));
    leak_check = false;
}

sample! { div_zero_int "samples/run-fail/div_zero_int.mor";
    stdin = "";
    stdout = "";
    stderr = "panicked due to division by zero\n";
    status = Failure(Some(1));
    leak_check = false;
}

// Test correctness of benchmarking samples

sample! { bench_primes "samples/bench_primes.mor";
    compile_only = true;
    // first number is iteration count
    stdin = "5\n100\n";
    stdout = "There are 25 primes <= 100\n";
}

sample! { bench_primes_iter "samples/bench_primes_iter.mor";
    compile_only = true;
    // first number is iteration count
    stdin = "5\n100\n";
    stdout = "There are 25 primes <= 100\n";
}

sample! { bench_primes_sieve "samples/bench_primes_sieve.mor";
    compile_only = true;
    // first number is iteration count
    stdin = "5\n10000\n";
    stdout = include_str!("../../samples/expected-output/primes_10000.txt");
}
