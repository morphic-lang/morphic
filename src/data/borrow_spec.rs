//! A small specification language for borrowing signatures and specifications for each built-in
//! operation.

use crate::data::first_order_ast::NumType;
use id_collections::id_type;
use once_cell::sync::Lazy;
use std::collections::BTreeSet;

#[id_type]
pub struct ModelMode(usize);

#[id_type]
pub struct ModelLt(usize);

#[id_type]
pub struct ModelTypeVar(usize);

#[derive(Clone, Debug)]
pub enum ModelItem {
    Var(ModelTypeVar),
    Num(NumType),
}

#[derive(Clone, Debug)]
pub enum ModelType {
    Var(ModelTypeVar),
    Num(NumType),
    Tuple(Vec<ModelType>),
    Array(ModelMode, ModelLt, ModelItem),
    HoleArray(ModelMode, ModelLt, ModelItem),
}

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

use ModelItem::Num as NumItem;
use ModelType::{Array, HoleArray, Num, Tuple};

fn item_var(n: usize) -> ModelItem {
    ModelItem::Var(ModelTypeVar(n))
}

fn var(n: usize) -> ModelType {
    ModelType::Var(ModelTypeVar(n))
}

// Our modeling language is not expressive enough to represent `ArrayOp::Get`, but we can handle
// everything else:

pub static SIG_ARRAY_EXTRACT: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![
        Array(ModelMode(0), ModelLt(0), item_var(0)),
        Num(NumType::Int),
    ],
    ret: Tuple(vec![
        HoleArray(ModelMode(0), ModelLt(0), item_var(0)),
        var(0),
    ]),
    owned: set![ModelMode(0)],
    accessed: set![ModelLt(0)],
});

pub static SIG_ARRAY_LEN: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(ModelMode(0), ModelLt(0), item_var(0))],
    ret: Num(NumType::Int),
    owned: set![],
    // Since the `len` field lives on the stack, it's technically OK to read it after the array has
    // been release (i.e. it's backing buffer has been deallocated).
    accessed: set![],
});

pub static SIG_ARRAY_PUSH: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(ModelMode(0), ModelLt(0), item_var(0)), var(0)],
    ret: Array(ModelMode(0), ModelLt(0), item_var(0)),
    owned: set![ModelMode(0)],
    accessed: set![ModelLt(0)],
});

pub static SIG_ARRAY_POP: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(ModelMode(0), ModelLt(0), item_var(0))],
    ret: Tuple(vec![Array(ModelMode(0), ModelLt(0), item_var(0)), var(0)]),
    owned: set![ModelMode(0)],
    accessed: set![ModelLt(0)],
});

pub static SIG_ARRAY_REPLACE: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![HoleArray(ModelMode(0), ModelLt(0), item_var(0)), var(0)],
    ret: Array(ModelMode(0), ModelLt(0), item_var(0)),
    owned: set![ModelMode(0)],
    accessed: set![ModelLt(0)],
});

pub static SIG_ARRAY_RESERVE: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![
        Array(ModelMode(0), ModelLt(0), item_var(0)),
        Num(NumType::Int),
    ],
    ret: Array(ModelMode(0), ModelLt(0), item_var(0)),
    owned: set![ModelMode(0)],
    accessed: set![ModelLt(0)],
});

pub static SIG_IO_INPUT: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![],
    ret: Array(ModelMode(0), ModelLt(0), NumItem(NumType::Byte)),
    owned: set![ModelMode(0)],
    accessed: set![],
});

pub static SIG_IO_OUTPUT: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(ModelMode(0), ModelLt(0), NumItem(NumType::Byte))],
    ret: Tuple(vec![]),
    owned: set![],
    accessed: set![ModelLt(0)],
});

/// Panic actually returns bottom, but it's convenient to model it as returning unit and handle
/// coercions elsewhere.
pub static SIG_PANIC: Lazy<BuiltinSig> = Lazy::new(|| BuiltinSig {
    args: vec![Array(ModelMode(0), ModelLt(0), NumItem(NumType::Byte))],
    ret: Tuple(vec![]),
    owned: set![],
    accessed: set![ModelLt(0)],
});
