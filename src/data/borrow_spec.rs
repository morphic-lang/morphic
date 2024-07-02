//! A small specification language for borrowing signatures and specifications for each built-in
//! operation.

use crate::data::first_order_ast::NumType;
use id_collections::id_type;
use once_cell::sync::Lazy;
use std::collections::BTreeSet;

#[id_type]
pub struct Mode(usize);

#[id_type]
pub struct Lt(usize);

#[id_type]
pub struct TypeVar(usize);

#[derive(Clone, Debug)]
pub enum ItemType {
    Var(TypeVar),
    Num(NumType),
}

#[derive(Clone, Debug)]
pub enum Type {
    Var(TypeVar),
    Num(NumType),
    Tuple(Vec<Type>),
    Array(Mode, Lt, ItemType),
    HoleArray(Mode, Lt, ItemType),
}

/// A signature which can be used during expression instantiation to constrain the argument and
/// return types of calls to built-in operations. The modeling language is expressive enough to
/// represent the signatures of most (but not all) built-ins.
#[derive(Clone, Debug)]
pub struct BuiltinSig {
    pub args: Vec<Type>,
    pub ret: Type,
    pub owned: BTreeSet<Mode>,
    pub accessed: BTreeSet<Lt>,
}

// Convenience items for constructing signatures:

macro_rules! set {
    ($($item:expr),*) => {
        {
            #[allow(unused_mut)] // This is a false positive
            let mut set = BTreeSet::new();
            $(set.insert($item);)*
            set
        }
    };
}

use ItemType::Num as NumItem;

use Type::{Array, HoleArray, Num, Tuple};

fn var_item(n: usize) -> ItemType {
    ItemType::Var(TypeVar(n))
}

fn var(n: usize) -> Type {
    Type::Var(TypeVar(n))
}

// Our modeling language is not expressive enough to represent `ArrayOp::Get`, but we can handle
// everything else:

pub static SIG_ARRAY_EXTRACT: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(Mode(0), Lt(0), var_item(0)), Num(NumType::Int)],
    ret: Tuple(vec![HoleArray(Mode(0), Lt(0), var_item(0)), var(0)]),
    owned: set![Mode(0)],
    accessed: set![Lt(0)],
});

pub static SIG_ARRAY_LEN: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(Mode(0), Lt(0), var_item(0))],
    ret: Num(NumType::Int),
    owned: set![],
    // Since the `len` field lives on the stack, it's technically OK to read it after the array has
    // been release (i.e. it's backing buffer has been deallocated).
    accessed: set![],
});

pub static SIG_ARRAY_PUSH: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(Mode(0), Lt(0), var_item(0)), var(0)],
    ret: Array(Mode(0), Lt(0), var_item(0)),
    owned: set![Mode(0)],
    accessed: set![Lt(0)],
});

pub static SIG_ARRAY_POP: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(Mode(0), Lt(0), var_item(0))],
    ret: Tuple(vec![Array(Mode(0), Lt(0), var_item(0)), var(0)]),
    owned: set![Mode(0)],
    accessed: set![Lt(0)],
});

pub static SIG_ARRAY_REPLACE: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![HoleArray(Mode(0), Lt(0), var_item(0)), var(0)],
    ret: Array(Mode(0), Lt(0), var_item(0)),
    owned: set![Mode(0)],
    accessed: set![Lt(0)],
});

pub static SIG_ARRAY_RESERVE: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(Mode(0), Lt(0), var_item(0)), Num(NumType::Int)],
    ret: Array(Mode(0), Lt(0), var_item(0)),
    owned: set![Mode(0)],
    accessed: set![Lt(0)],
});

pub static SIG_IO_INPUT: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![],
    ret: Array(Mode(0), Lt(0), NumItem(NumType::Byte)),
    owned: set![Mode(0)],
    accessed: set![],
});

pub static SIG_IO_OUTPUT: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(Mode(0), Lt(0), NumItem(NumType::Byte))],
    ret: Tuple(vec![]),
    owned: set![],
    accessed: set![Lt(0)],
});

/// Panic actually returns bottom, but it's convenient to model it as returning unit and handle
/// coercions elsewhere.
pub static SIG_PANIC: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(Mode(0), Lt(0), NumItem(NumType::Byte))],
    ret: Tuple(vec![]),
    owned: set![],
    accessed: set![Lt(0)],
});
