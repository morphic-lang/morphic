use crate::data::num_type::NumType;
use crate::data::purity::Purity;

// To add an arithmetic intrinsic:
// 1. Add it to this file
// 2. Add its user-facing name and type signature to src/intrinsic_config.rs
// 3. Add support for it in src/interpreter.rs
// 4. Add support for it in src/llvm_gen.rs

// Non-arithmetic intrinsics (that is, intrinsics which require nontrivial handling in alias
// analysis, mutation analysis, rc op generation, etc.) are not yet supported.

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Intrinsic {
    ByteToInt,
    ByteToIntSigned,
    IntToByte,
    IntShiftLeft,
    IntShiftRight,
    IntBitAnd,
    IntBitOr,
    IntBitXor,
    RandInt,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Num(NumType),
    Tuple(Vec<Type>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Signature {
    pub purity: Purity,
    pub arg: Type,
    pub ret: Type,
}
