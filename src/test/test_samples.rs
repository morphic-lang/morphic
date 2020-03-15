use crate::pseudoprocess::ExitStatus::Failure;

sample! { io "samples/io.txt";
    stdin = "hello\n";
    stdout = "hello\n";
}

sample! { zero_sized_array "samples/zero_sized_array.txt";
    stdin = "";
    stdout = "Completed all tests\n";
}

sample! { iter "samples/iter.txt";
    stdin = "";
    stdout = lines! [
        "it worked",
        "it worked",
    ];
}

sample! { difference_lists "samples/difference_lists.txt";
    stdin = "";
    stdout = "123";
}

sample! { increment "samples/increment.txt";
    stdin = "";
    stdout = lines! [
        "The following should both be 5:",
        "5",
        "5",
    ];
}

sample! { arith "samples/arith.txt";
    stdin = "";
    stdout = "Completed all tests\n";
}

sample! { concat_persistent "samples/concat_persistent.txt";
    stdin = "";
    stdout = lines! [
        "hello",
        "hello world",
    ];
}

sample! { index_tree "samples/index_tree.txt";
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

sample! { nested "samples/nested.txt";
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

sample! { item_oob1 "samples/run-fail/item_oob1.txt";
    stdin = "";
    stdout = "";
    stderr = "index out of bounds: attempt to access item 3 of array with length 3\n";
    status = Failure;
}

sample! { item_oob2 "samples/run-fail/item_oob2.txt";
    stdin = "";
    stdout = "";
    stderr = "index out of bounds: attempt to access item -1 of array with length 3\n";
    status = Failure;
}

sample! { pop_empty "samples/run-fail/pop_empty.txt";
    stdin = "";
    stdout = "";
    stderr = "pop: empty array\n";
    status = Failure;
}

// TODO: Carefully review 'samples/mutate.txt' to determine by hand what the stdouted output should
// be, then add a test for it.
