//! A small specification language for borrowing signatures and specifications for each built-in
//! operation.

use crate::data::first_order_ast::NumType;
use crate::util::map_ext::set;
use id_collections::id_type;
use once_cell::sync::Lazy;
use std::collections::BTreeSet;

#[id_type]
pub struct ModelMode(usize);

#[id_type]
pub struct ModelLt(usize);

#[id_type]
pub struct ModelTVar(usize);

#[derive(Clone, Debug)]
pub enum ModelType {
    Var(ModelTVar),
    Num(NumType),
    Tuple(Vec<ModelType>),
    Array(ModelMode, ModelLt, Box<ModelType>),
    HoleArray(ModelMode, ModelLt, Box<ModelType>),
}

use ModelType::*;

/// A signature which can be used during expression instantiation to constrain the argument and
/// return types of calls to built-in operations. The modeling language is expressive enough to
/// represent the signatures of most (but not all) built-ins.
#[derive(Clone, Debug)]
pub struct BuiltinSig {
    pub args: Vec<ModelType>,
    pub ret: ModelType,
    pub owned: BTreeSet<ModelMode>,
    pub accessed: BTreeSet<ModelLt>,
}

fn var(n: usize) -> ModelType {
    ModelType::Var(ModelTVar(n))
}

#[rustfmt::skip]
pub static SIG_ARRAY_EXTRACT: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(ModelMode(0), ModelLt(0), Box::new(var(0))), Num(NumType::Int)],
    ret: Tuple(vec![HoleArray(ModelMode(0), ModelLt(0), Box::new(var(0))), var(0)]),
    owned: set![ModelMode(0)],
    accessed: set![ModelLt(0)],
});

/// Since the `len` field of an array lives on the stack, it's technically OK to read it after the
/// array has been release (i.e. it's backing buffer has been deallocated). Therefore, we set
/// `accessed` to the empty set.
#[rustfmt::skip]
pub static SIG_ARRAY_LEN: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(ModelMode(0), ModelLt(0), Box::new(var(0)))],
    ret: Num(NumType::Int),
    owned: set![],
    accessed: set![],
});

#[rustfmt::skip]
pub static SIG_ARRAY_PUSH: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(ModelMode(0), ModelLt(0), Box::new(var(0))), var(0)],
    ret: Array(ModelMode(0), ModelLt(0), Box::new(var(0))),
    owned: set![ModelMode(0)],
    accessed: set![ModelLt(0)],
});

#[rustfmt::skip]
pub static SIG_ARRAY_POP: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(ModelMode(0), ModelLt(0), Box::new(var(0)))],
    ret: Tuple(vec![Array(ModelMode(0), ModelLt(0), Box::new(var(0))), var(0)]),
    owned: set![ModelMode(0)],
    accessed: set![ModelLt(0)],
});

#[rustfmt::skip]
pub static SIG_ARRAY_REPLACE: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![HoleArray(ModelMode(0), ModelLt(0), Box::new(var(0))), var(0)],
    ret: Array(ModelMode(0), ModelLt(0), Box::new(var(0))),
    owned: set![ModelMode(0)],
    accessed: set![ModelLt(0)],
});

#[rustfmt::skip]
pub static SIG_ARRAY_RESERVE: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(ModelMode(0), ModelLt(0), Box::new(var(0))), Num(NumType::Int)],
    ret: Array(ModelMode(0), ModelLt(0), Box::new(var(0))),
    owned: set![ModelMode(0)],
    accessed: set![ModelLt(0)],
});

#[rustfmt::skip]
pub static SIG_IO_INPUT: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![],
    ret: Array(ModelMode(0), ModelLt(0), Box::new(Num(NumType::Byte))),
    owned: set![ModelMode(0)],
    accessed: set![],
});

#[rustfmt::skip]
pub static SIG_IO_OUTPUT: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(ModelMode(0), ModelLt(0), Box::new(Num(NumType::Byte)))],
    ret: Tuple(vec![]),
    owned: set![],
    accessed: set![ModelLt(0)],
});

/// Panic effectively returns bottom, but it's convenient to model it as returning unit and handle
/// the actual return type elsewhere.
#[rustfmt::skip]
pub static SIG_PANIC: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(ModelMode(0), ModelLt(0), Box::new(Num(NumType::Byte)))],
    ret: Tuple(vec![]),
    owned: set![],
    accessed: set![ModelLt(0)],
});
