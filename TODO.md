# To Do

## LetMany everywhere
- [ ] modify parser to emit LetManys
- [ ] modify every other pass to take LetMany

## Tail call elimination
- [ ] add scc entry point analysis
- [ ] modify `llvm_gen.rs` to compile scc

## Profiling

## RC elision
- [ ] fate analysis pass
- [ ] add symbolic borrows
- [ ] monomorphize
- [ ] modify every subsequent pass
- [ ] replace item with get + replace

## `lower_structures.rs` v2
- [ ] don't emit retain/releases for types without heap content
- [ ] monomorphize builtins

## Source level array changes
- [ ] truncate
- [ ] swap
- [ ] capacity
- [ ] into_iter

## `lower_closures.rs`
- [x] don't call dispatch functions for funcreps that are isomorphic to unit
- [ ] eliminate globals that return funcreps that are isomorphic to unit
- [x] eliminate environments for lambdas that have no captures
- [x] inline calls to primitve functions when possible

## `shield_funcs.rs`

- [x] modify shield funcs to not shield non-recursive funtions


## thread debug symbols through more passes
- [ ] function monomorphization
- [ ] lower closures
- [ ] alias analysis
- [ ] lower structures
- [ ] thread variable names through

## `split_custom_types.rs`
- [ ] remove non-recursive custom types

## `llvm_gen.rs`
- [ ] make code generic over size of `size_t`
- [ ] support wasm
- [ ] add some command line flags (opt level, target, etc)
- [ ] add tail calls
- [ ] use fastcc calling convention

## `flat_array.rs`
- [ ] replace uses of `build_struct_gep` with `get_member`
- [ ] make things more private (conditionally)
- [ ] fix zero-sized arrays
- [ ] include capacity for new

## Source level changes
- [ ] expsose capacity for arrays
- [ ] do notation

## persistent arrays
- [X] actually implement them

## `core.rs`
- [ ] support wasm

## front end
- [ ] emit line numbers for errors
