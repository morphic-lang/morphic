use crate::data::num_type::{IntType, NumType};
use crate::data::purity::Purity;
use std::fmt;

// To add an arithmetic intrinsic:
// 1. Add it to this file, including to `Intrinsic::all` and its `Display`
// 2. Add its user-facing name and type signature to intrinsic_config.rs
// 3. Add support for it in interpreter.rs
// 4. Add support for it in codegen (NOTE: to do this you may need to declare a new LLVM
//    intrinsic in `code_gen/tal.rs`)
// 5. Define it in the ML preludes next to the pretty printers

// Non-arithmetic intrinsics (that is, intrinsics which require nontrivial handling in alias
// analysis, mutation analysis, rc op generation, etc.) are not yet supported.

/// An operation on the builtin scalar types that the backends implement directly.  The number
/// type an intrinsic works on is part of it, so each backend has one case per operation, which
/// it specializes by the type's kind, width, and signedness.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Intrinsic {
    // Arithmetic.  Integer arithmetic wraps, and integer division truncates toward zero and
    // panics on a zero divisor.
    Add(NumType),
    Sub(NumType),
    Mul(NumType),
    Div(NumType),
    Neg(NumType),

    // Comparison.  The floats compare as IEEE requires, so NaN is unequal to everything.
    Eq(NumType),
    Lt(NumType),
    Lte(NumType),
    Gt(NumType),
    Gte(NumType),
    EqBool,

    // Boolean and bitwise logic.  A shift amount is taken modulo the type's width, and a right
    // shift is logical.
    Not,
    BitAnd(IntType),
    BitOr(IntType),
    BitXor(IntType),
    BitNot(IntType),
    ShiftLeft(IntType),
    ShiftRight(IntType),
    /// The number of one bits.
    Ctpop(IntType),
    /// The number of leading zero bits, which is the width for zero.
    Ctlz(IntType),
    /// The number of trailing zero bits, which is the width for zero.
    Cttz(IntType),

    /// A conversion between two different number types.  Widening an integer extends it by its
    /// signedness; narrowing an integer keeps its low bits; converting between integers of one
    /// width keeps the bits; converting between the floats, or an integer to a float, rounds to
    /// nearest; and converting a float to an integer rounds toward zero, saturates at the
    /// integer's range, and takes NaN to zero.
    Convert(NumType, NumType),
}

impl Intrinsic {
    /// Every intrinsic, each once.
    pub fn all() -> impl Iterator<Item = Intrinsic> {
        use Intrinsic::*;
        let per_num = |make: fn(NumType) -> Intrinsic| NumType::ALL.into_iter().map(make);
        let per_int = |make: fn(IntType) -> Intrinsic| IntType::ALL.into_iter().map(make);
        let conversions = NumType::ALL.into_iter().flat_map(|from| {
            NumType::ALL
                .into_iter()
                .filter(move |&to| to != from)
                .map(move |to| Convert(from, to))
        });
        per_num(Add)
            .chain(per_num(Sub))
            .chain(per_num(Mul))
            .chain(per_num(Div))
            .chain(per_num(Neg))
            .chain(per_num(Eq))
            .chain(per_num(Lt))
            .chain(per_num(Lte))
            .chain(per_num(Gt))
            .chain(per_num(Gte))
            .chain([EqBool, Not])
            .chain(per_int(BitAnd))
            .chain(per_int(BitOr))
            .chain(per_int(BitXor))
            .chain(per_int(BitNot))
            .chain(per_int(ShiftLeft))
            .chain(per_int(ShiftRight))
            .chain(per_int(Ctpop))
            .chain(per_int(Ctlz))
            .chain(per_int(Cttz))
            .chain(conversions)
    }
}

/// The intrinsic's identifier in IR dumps and the ML preludes, such as `AddI64`, `I64BitAnd`,
/// or `U8ToI64`.
impl fmt::Display for Intrinsic {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Intrinsic::*;
        let int = |int: IntType| NumType::from(int).name();
        match *self {
            Add(num) => write!(f, "Add{}", num.name()),
            Sub(num) => write!(f, "Sub{}", num.name()),
            Mul(num) => write!(f, "Mul{}", num.name()),
            Div(num) => write!(f, "Div{}", num.name()),
            Neg(num) => write!(f, "Neg{}", num.name()),
            Eq(num) => write!(f, "Eq{}", num.name()),
            Lt(num) => write!(f, "Lt{}", num.name()),
            Lte(num) => write!(f, "Lte{}", num.name()),
            Gt(num) => write!(f, "Gt{}", num.name()),
            Gte(num) => write!(f, "Gte{}", num.name()),
            EqBool => write!(f, "EqBool"),
            Not => write!(f, "Not"),
            BitAnd(i) => write!(f, "{}BitAnd", int(i)),
            BitOr(i) => write!(f, "{}BitOr", int(i)),
            BitXor(i) => write!(f, "{}BitXor", int(i)),
            BitNot(i) => write!(f, "{}BitNot", int(i)),
            ShiftLeft(i) => write!(f, "{}ShiftLeft", int(i)),
            ShiftRight(i) => write!(f, "{}ShiftRight", int(i)),
            Ctpop(i) => write!(f, "{}Ctpop", int(i)),
            Ctlz(i) => write!(f, "{}Ctlz", int(i)),
            Cttz(i) => write!(f, "{}Cttz", int(i)),
            Convert(from, to) => write!(f, "{}To{}", from.name(), to.name()),
        }
    }
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

/// How the source language reaches an intrinsic.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Name {
    /// An operator's intrinsic, which the source reaches through a builtin trait's func; the
    /// name is for IR dumps.
    Op { debug_name: String },
    /// A builtin function the source calls by this name.
    Func { source_name: String },
}

impl Name {
    pub fn debug_name(&self) -> &str {
        match self {
            Name::Op { debug_name } => debug_name,
            Name::Func { source_name } => source_name,
        }
    }
}
