<div align="center">
    <picture>
        <img alt="The Morphic Research Language" src="./morphic-logo.png" width="150px">
    </picture>

[Website](https://morphic-lang.org)
</div>

This is the source code for the Morphic compiler.

## What is Morphic?

Morphic is an experimental pure functional programming language designed to achieve performance competitive with imperative systems languages like C++ and Rust.

Morphic features three automatic optimizations which turn functional programming constructs into zero-cost abstractions:
- Lambdas: Morphic’s lambda set specialization makes lambdas unboxed and statically dispatched, and allows calls to lambdas to be inlined. You can find the details in our [paper](https://doi.org/10.1145/3591260) or [talk](https://www.youtube.com/watch?v=F3z39M0gdJU&t=3540s).
- Immutable Data Structures: Morphic’s mutation optimization transforms updates to logically-immutable data structures into in-place mutations when doing so does not affect semantics.
- Automatic Memory Management: Morphic uses a borrow-based reference counting scheme which is able to eliminate almost all reference count increments and decrements for a large class of programs.

```rust
type Primality {
  Prime,
  Composite,
}

sieve(limit: Int): Array Primality =
  // Array memory is automatically managed statically,
  // without any refcounting overhead in this case.
  let init_arr =
    Array.fill(limit, Prime)
    |> Array.set(0, Composite)
    |> Array.set(1, Composite)
  in
  // Iterator logic compiles to a simple loop, with
  // no heap allocations or virtual dispatch.
  Iter.range(2, limit)
  |> Iter.foldl(init_arr, \(arr, n) ->
    match Array.get(arr, n) {
      Prime ->
        Iter.ints(2)
        |> Iter.map(\i -> i * n)
        |> Iter.take_while(\i -> i < limit)
        |> Iter.foldl(
          arr,
          // Array updates logically copy the array,
          // but are automatically performed in-place
          // when safe.
          \(new, i) -> Array.set(new, i, Composite)
        ),
      Composite -> arr,
    }
  )
```

## Getting Started

To build Morphic you will need an up-to-date [Rust](https://rustup.rs/) compiler and a development copy of LLVM 16. Appropriate LLVM packages are available on Debian and Ubuntu from the [LLVM repository](https://apt.llvm.org/). On other platforms, you may need to build LLVM from scratch. See the [LLVM docs](https://llvm.org/docs/GettingStarted.html#getting-the-source-code-and-building-llvm) for details. Once you have installed Rust and LLVM 16, simply run `cargo build`.

Syntax highlighting is available via the Morphic [VSCode Extension](https://marketplace.visualstudio.com/items?itemName=morphic-lang.morphic).
