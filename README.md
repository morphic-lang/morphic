# opt-proto
## lower_closures.rs
* [X] don't call dispatch functions for funcreps that are isomorphic to unit
* [ ] eliminate globals that return funcreps that are isomorphic to unit
* [X] eliminate environments for lambdas that have no captures
* [X] inline calls to primitve functions when possible

## shield_funcs.rs
* [X] modify shield funcs to not shield non-recursive funtions

## lower_structures.rs
* [ ] figure out how not to emit fewer tuple destructure retain/releases
* [ ] don't emit retain/releases for types without heap content

## thread debug symbols through rename data to symbols
* [ ] function monomorphization
* [ ] lower_closures
* [ ] alias analysis
* [ ] lower_structures
* [ ] thread variable names through

## split_custom_types.rs
* [ ] remove non-recursive custom types

## llvm_gen.rs
* [ ] make code generic over size of size_t
* [ ] support wasm
* [ ] add some command line flags (opt level, target, etc)
* [ ] add tail calls
* [ ] use fastcc calling convention

## flat_array.rs
* [ ] replace uses of build_struct_gep with get_member
* [ ] make things private

## core.rs
* [ ] support wasm

## front end
* [ ] emit line numbers for errors
