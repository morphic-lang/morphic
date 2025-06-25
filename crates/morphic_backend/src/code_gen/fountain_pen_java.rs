/*

even "hi"

even: String -> Nat
isodd: String -> Nat

switch (arg_name) {
}


function (arg: {kind: "even", evenArg: ...} | {kind: "odd", oddArg: ...}) {
tail_func_name= Infinity

  switch (arg.kind) {
    case "even":
      // tail_call(even_target, arg.evenArg)
      set the argument
      then break
    case "odd":
      tail_call(odd_target, arg.oddArg)
      set the argument
      break
  }


  somelabel: while (true) {
    switch (tail_func_name) {
      case "even":
      // do something with evenArg
      // oddArg = "...."
      // continue label;

      case "odd":
      // do something with evenArg
      // oddArg = "...."
      // continue label;

      default:
        switch (arg.kind) {
            case "even":
            tail_call(even_target, arg.evenArg)
            case "odd":
            tail_call(odd_target, arg.oddArg)
  }
    }
  }
}

*/

use crate::code_gen::java_builder as java;
use std::cell::RefCell;
use std::rc::Rc;

use id_collections::{id_type, IdVec};

#[id_type]
struct TailTarget(u32);

#[id_type]
struct Type(u32);

#[id_type]
struct GlobalValue(u32);

#[id_type]
struct FunctionValue(u32);

#[id_type]
struct Value(u32);

struct TailFunction {
    tail_targets: Vec<java::Expr>,
    body: java::Expr,
}

enum FunctionVariant {
    Function(java::Method),
    TailFunction(TailFunction),
}

struct ContextImpl {
    tail_targets: IdVec<TailTarget, (FunctionValue, u32)>,
    types: IdVec<Type, (java::Type, Option<java::Record>)>,
    global_values: IdVec<GlobalValue, java::Ident>,
    function_values: IdVec<FunctionValue, FunctionVariant>,
    values: IdVec<Value, java::Ident>,
}

struct Context {
    inner: Rc<RefCell<ContextImpl>>,
}
