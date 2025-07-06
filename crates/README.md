> ⚠️ **FIXME: this file is very out of date.**

# Morphic compiler passes

Notice `lib.rs` in this directory. Here you can find the big-picture logic of the
compiler in the `compile` function, which invokes each pass of the compiler and
threads the appropriate state between them.

The compiler is primarily structured as a sequence alternating **abstract interpretation
passes** which analyze code, synthesize "type variables" (think: converting `Array<Int>` to
`Array<repr, Int>` where `repr` can concretely be either `persistent` or `flat`) with constraints based on
that analysis, and **monomorphization passes** which generate specialized instances of
each function to meet the type taken on by those "type variables" at each callsite
(think: generating `sum_mut : Array<flat, Int> -> Int` and `sum_immut : Array<persistent, Int> -> Int` from
a single `sum : Array<Int> -> Int` function).

In most of these passes there is only one public function, i.e. the one invoked in `fn compile`.

**A brief overview of the passes** (corresponding to the calls in `fn compile`) is as follows:

- `fn resolve::resolve_program` parses the given morphic file, and looks up and parses module dependencies.

- `fn type_infer::type_infer` runs Hindley-Milner type inference.
  (This is followed by several straightforward checks— exhaustiveness of pattern matches, existence of a main function, etc.)

- `fn monomorphize::monomorphize` monomorphizes functions (and types) with respect to generic type variables
  (starting from `main` to generate instantiations as needed).

- `fn shield_functions::shield_functions` produces "wrapper functions" for recursive functions
  (i.e., `forever x = forever (inc x)` generates the pair
  of functions `forever_internal x = forever_internal (inc x)` and `forever x = forever_internal x`, with
  `forever_internal` only referenced in those two places)
  (and likewise for mutually recursive functions).

- `fn lambda_lift::lambda_lift` extracts lambdas to top-level lambda definitions describing the
  types of variables they capture alongside argument types.

- `fn annot_closures::annot_closures` synthesizes _type variables for the types of closure-environments
  for each lambda callsite_. In other words, what was before a parameter with a concrete type `Int -> Int`
  is now a generic type, which can be thought of as `forall T. Closure<Arg=Int, Ret=Int, Env=T>` (in pseudocode).

  (Note that a lot of the complexity comes from counting the appropriate number
  of type variables to generate in mutually recursive functions, i.e. in strongly-connected-components of the
  function dependency graph; _this complication recurs in later passes_).

- `fn closure_specialize::closure_specialize` monormophizes with respect to closure-environments,
  to produce an AST in which the closure environments of each lambda are concrete.

- `fn lower_closures::lower_closures` reduces lambdas to ordinary functions and closure-environments (aka captures)
  to ordinary types.

  We now have the infamous `first_order_ast`.

- `fn split_custom_types::split_custom_types` adds a `Type::Boxed` variant to `Type` in the AST, and uses this
  to box fields as necessary in recursive type (e.g. so that the `cdr` field of a linked-list is boxed).

- `fn flatten::flatten` flattens the bodies of functions from trees of expressions to vectors of
  expressions which explicilty reference prior expressions by ID, instead of containing them as sub-trees.

- `fn annot_aliases::annot_aliases` abstractly interprets the program to compute an aliasing signature for
  each function, which describes _names_ (roughly, fields) in the arguments to the function alias
  names in the return value, and how names in the return value alias other names in the return value.

- `fn annot_mutation::annot_mutation` abstractly interprets the program to compute a mutation signature for
  each function, describing which names among its arguments are mutated, potentially subject to disjunctions of
  aliasing conditions (e.g. "the first argument is always mutated; the second argument is mutated _if_ it is aliased
  to the first argument").

- `fn annot_fates::annot_fates` abstractly interprets the program to compute _fate_ information for each
  name in the arguments to each function (as well as each local within each function). A fate of
  a local describes the set of last-accesses-points of the local (holding more than one last-access if the
  last access of a local depends on the results of branches, in which case there is a different last-access for
  each branch; note that this takes a complex collection of data structures to describe), including
  where arguments may be present in the return value.

- `fn specialize_aliases::specialize_aliases` monomorphizes functions with respect to _concrete_ aliasing
  graphs, such that functions' alias signatures describe (as preconditions) aliasing relationships
  between names in arguments and (as a postcondition) the consequent aliases between argument names and
  return value names.

- `fn annot_modes::annot_modes` synthesizes _mode variables_ on array types, which take one one of two
  concrete modes `Owned` or `Borrowed` (where `Owned` is a "subtype"/submode of `Borrowed`),
  as well as constraints on these mode variables based on fate and mutation information.

  _TODO: describe internals of this pass_

- `fn rc_specialize::rc_specialize` monomorphizes with respect to mode variables and synethesizes
  RC operations (`retain`s and `release`s) based on the concrete modes.

- `fn unify_reprs::unify_reprs` synthesizes _representation variables_ on array types (and unifies
  the synethsized type variables with Hindley-Milner).

- `fn constraint_reprs::constraint_reprs` applies constraints on those representation variables based
  on mutation information (describing the argument-aliasing and local-mutated conditions which are
  necessary and sufficient for the occurance to be an access to a mutated value, i.e. for the value
  to be forced to be a persistent array).

- `fn specialize_reprs::specialize_reprs` monomorphizes with respect to representation variables and
  the constraints on them.

- `fn tail_call_elim::tail_call_elim` performs tail-call elimination.

- `fn lower_structures::lower_structures` changes multi-condition branches to `if`s and flattens array
  literals to array initialization followed by several array `push`es.

- Note that `fn build`, which calls `fn compile`, then invokes `llvm_gen::build` on the `low_ast::Program`
  produced by `fn compile`.
