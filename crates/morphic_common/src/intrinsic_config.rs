use crate::data::intrinsics::{Intrinsic, Name, Signature, Type};
use crate::data::num_type::{IntType, NumType};
use crate::data::purity::Purity;

/// How the source language reaches an intrinsic: the operators' intrinsics, which are the funcs
/// of the builtin traits, are named only in IR dumps, and the rest are builtin functions.
pub fn intrinsic_to_name(intr: Intrinsic) -> Name {
    use Intrinsic::*;
    let num = |num: NumType| num.name().to_lowercase();
    let int = |int: IntType| NumType::from(int).name().to_lowercase();
    let op = |debug_name: String| Name::Op { debug_name };
    let func = |source_name: String| Name::Func { source_name };
    match intr {
        Add(t) => op(format!("add_{}", num(t))),
        Sub(t) => op(format!("sub_{}", num(t))),
        Mul(t) => op(format!("mul_{}", num(t))),
        Div(t) => op(format!("div_{}", num(t))),
        Neg(t) => op(format!("neg_{}", num(t))),
        Eq(t) => op(format!("eq_{}", num(t))),
        Lt(t) => op(format!("lt_{}", num(t))),
        Lte(t) => op(format!("lte_{}", num(t))),
        Gt(t) => op(format!("gt_{}", num(t))),
        Gte(t) => op(format!("gte_{}", num(t))),
        EqBool => op("eq_bool".to_owned()),
        Not => op("not".to_owned()),
        BitAnd(t) => op(format!("{}_bit_and", int(t))),
        BitOr(t) => op(format!("{}_bit_or", int(t))),
        BitXor(t) => op(format!("{}_bit_xor", int(t))),
        BitNot(t) => op(format!("{}_bit_not", int(t))),
        ShiftLeft(t) => op(format!("{}_shift_left", int(t))),
        ShiftRight(t) => op(format!("{}_shift_right", int(t))),
        Ctpop(t) => func(format!("{}_count_ones", int(t))),
        Ctlz(t) => func(format!("{}_leading_zeros", int(t))),
        Cttz(t) => func(format!("{}_trailing_zeros", int(t))),
        Convert(from, to) => func(format!("{}_to_{}", num(from), num(to))),
    }
}

/// Every intrinsic with its name.
pub fn intrinsic_names() -> impl Iterator<Item = (Intrinsic, Name)> {
    Intrinsic::all().map(|intr| (intr, intrinsic_to_name(intr)))
}

fn pure(arg: Type, ret: Type) -> Signature {
    Signature {
        purity: Purity::Pure,
        arg,
        ret,
    }
}

fn pair(left: Type, right: Type) -> Type {
    Type::Tuple(vec![left, right])
}

pub fn intrinsic_sig(intr: Intrinsic) -> Signature {
    use Intrinsic::*;
    let num = |num: NumType| Type::Num(num);
    let int = |int: IntType| Type::Num(NumType::from(int));
    match intr {
        Add(t) | Sub(t) | Mul(t) | Div(t) => pure(pair(num(t), num(t)), num(t)),
        Neg(t) => pure(num(t), num(t)),
        Eq(t) | Lt(t) | Lte(t) | Gt(t) | Gte(t) => pure(pair(num(t), num(t)), Type::Bool),
        EqBool => pure(pair(Type::Bool, Type::Bool), Type::Bool),
        Not => pure(Type::Bool, Type::Bool),
        BitAnd(t) | BitOr(t) | BitXor(t) | ShiftLeft(t) | ShiftRight(t) => {
            pure(pair(int(t), int(t)), int(t))
        }
        BitNot(t) | Ctpop(t) | Ctlz(t) | Cttz(t) => pure(int(t), int(t)),
        Convert(from, to) => pure(num(from), num(to)),
    }
}
