sample! { io "samples/io.txt";
    stdin = "hello\n";
    stdout = "hello\n";
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

// TODO: Carefully review 'samples/mutate.txt' to determine by hand what the stdouted output should
// be, then add a test for it.
