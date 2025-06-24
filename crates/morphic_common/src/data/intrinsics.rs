use crate::data::num_type::NumType;
use crate::data::purity::Purity;

// To add an arithmetic intrinsic:
// 1. Add it to this file
// 2. Add its user-facing name and type signature to intrinsic_config.rs
// 3. Add support for it in interpreter.rs
// 4. Add support for it in codegen (NOTE: to do this you may need to declare a new LLVM
//    intrinsic in `src/builtins/tal.rs`)

// Non-arithmetic intrinsics (that is, intrinsics which require nontrivial handling in alias
// analysis, mutation analysis, rc op generation, etc.) are not yet supported.

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Intrinsic {
    // Basic arithmetic ops
    AddByte,
    SubByte,
    MulByte,
    DivByte,
    NegByte,

    EqByte,
    LtByte,
    LteByte,
    GtByte,
    GteByte,

    AddInt,
    SubInt,
    MulInt,
    DivInt,
    NegInt,

    EqInt,
    LtInt,
    LteInt,
    GtInt,
    GteInt,

    AddFloat,
    SubFloat,
    MulFloat,
    DivFloat,
    NegFloat,

    EqFloat,
    LtFloat,
    LteFloat,
    GtFloat,
    GteFloat,

    Not,

    // Intrinsic numeric functions
    ByteToInt,
    ByteToIntSigned,
    IntToByte,
    IntShiftLeft,
    IntShiftRight,
    IntBitAnd,
    IntBitOr,
    IntBitXor,
    IntCtpop,
    IntCtlz,
    IntCttz,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Num(NumType),
    Tuple(Vec<Type>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Signature {
    pub purity: Purity,
    pub arg: Type,
    pub ret: Type,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Name {
    Op { debug_name: &'static str },
    Func { source_name: &'static str },
}

impl Name {
    pub fn debug_name(&self) -> &'static str {
        match self {
            Name::Op { debug_name } => debug_name,
            Name::Func { source_name } => source_name,
        }
    }
}
