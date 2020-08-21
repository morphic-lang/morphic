use crate::data::intrinsics::*;
use crate::data::num_type::NumType;
use crate::data::purity::Purity;

// Names:

macro_rules! define_intrinsic_to_name {
    ($(($intrinsic : ident, $name : expr)),*) => {
        pub fn intrinsic_to_name(intr: Intrinsic) -> &'static str {
            match intr {
                $(Intrinsic::$intrinsic => $name),*
            }
        }
    };
}

macro_rules! define_name_to_intrinsic {
    ($(($intrinsic : ident, $name : expr)),*) => {
        pub fn name_to_intrinsic(name: &str) -> Option<Intrinsic> {
            match name {
                $($name => Some(Intrinsic::$intrinsic)),*,
                _ => None,
            }
        }
    }
}

macro_rules! define_intrinsic_names_const {
    ($(($intrinsic : ident, $name : expr)),*) => {
        pub const INTRINSIC_NAMES: &[(Intrinsic, &'static str)] = &[
            $((Intrinsic::$intrinsic, $name)),*
        ];
    }
}

// Watch out!  This macro expects a trailing comma, but the macros it invokes internally do not.
macro_rules! define_intrinsic_names {
    ($(($intrinsic : ident, $name : expr)),*,) => {
        define_intrinsic_to_name!($(($intrinsic, $name)),*);
        define_name_to_intrinsic!($(($intrinsic, $name)),*);
        define_intrinsic_names_const!($(($intrinsic, $name)),*);
    };
}

define_intrinsic_names![
    (ByteToInt, "byte_to_int"),
    (ByteToIntSigned, "byte_to_int_signed"),
    (IntToByte, "int_to_byte"),
    (IntShiftLeft, "int_shift_left"),
    (IntShiftRight, "int_shift_right"),
    (IntBitAnd, "int_bit_and"),
    (IntBitOr, "int_bit_or"),
    (IntBitXor, "int_bit_xor"),
    (RandInt, "rand_int"),
];

// Signatures:

fn byte() -> Type {
    Type::Num(NumType::Byte)
}

fn int() -> Type {
    Type::Num(NumType::Int)
}

fn float() -> Type {
    Type::Num(NumType::Float)
}

macro_rules! tuple {
    ($($item : expr),*) => {
        Type::Tuple(vec![$($item),*])
    };
}

fn pure(arg: Type, ret: Type) -> Signature {
    Signature {
        purity: Purity::Pure,
        arg,
        ret,
    }
}

fn impure(arg: Type, ret: Type) -> Signature {
    Signature {
        purity: Purity::Impure,
        arg,
        ret,
    }
}

pub fn intrinsic_sig(intr: Intrinsic) -> Signature {
    use Intrinsic::*;
    match intr {
        ByteToInt => pure(byte(), int()),
        ByteToIntSigned => pure(byte(), int()),
        IntToByte => pure(int(), byte()),
        IntShiftLeft => pure(tuple!(int(), int()), int()),
        IntShiftRight => pure(tuple!(int(), int()), int()),
        IntBitAnd => pure(tuple!(int(), int()), int()),
        IntBitOr => pure(tuple!(int(), int()), int()),
        IntBitXor => pure(tuple!(int(), int()), int()),
        RandInt => impure(tuple!(), int()),
    }
}
