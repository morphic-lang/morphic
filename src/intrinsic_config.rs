use crate::data::intrinsics::*;
use crate::data::num_type::NumType;
use crate::data::purity::Purity;

// Names:

macro_rules! define_intrinsic_to_name {
    ($(($intrinsic : ident, $name : expr)),*) => {
        pub fn intrinsic_to_name(intr: Intrinsic) -> Name {
            match intr {
                $(Intrinsic::$intrinsic => $name),*
            }
        }
    };
}

macro_rules! define_intrinsic_names_const {
    ($(($intrinsic : ident, $name : expr)),*) => {
        pub const INTRINSIC_NAMES: &[(Intrinsic, Name)] = &[
            $((Intrinsic::$intrinsic, $name)),*
        ];
    }
}

// Watch out!  This macro expects a trailing comma, but the macros it invokes internally do not.
macro_rules! define_intrinsic_names {
    ($(($intrinsic : ident, $name : expr)),*,) => {
        define_intrinsic_to_name!($(($intrinsic, $name)),*);
        define_intrinsic_names_const!($(($intrinsic, $name)),*);
    };
}

const fn op_name(debug_name: &'static str) -> Name {
    Name::Op { debug_name }
}

const fn name(source_name: &'static str) -> Name {
    Name::Func { source_name }
}

define_intrinsic_names![
    // Basic arithmetic ops
    // These names are used only for IR pretty-printing
    (AddByte, op_name("add_byte")),
    (SubByte, op_name("sub_byte")),
    (MulByte, op_name("mul_byte")),
    (DivByte, op_name("div_byte")),
    (NegByte, op_name("neg_byte")),
    (EqByte, op_name("eq_byte")),
    (LtByte, op_name("lt_byte")),
    (LteByte, op_name("lte_byte")),
    (GtByte, op_name("gt_byte")),
    (GteByte, op_name("gte_byte")),
    (AddInt, op_name("add_int")),
    (SubInt, op_name("sub_int")),
    (MulInt, op_name("mul_int")),
    (DivInt, op_name("div_int")),
    (NegInt, op_name("neg_int")),
    (EqInt, op_name("eq_int")),
    (LtInt, op_name("lt_int")),
    (LteInt, op_name("lte_int")),
    (GtInt, op_name("gt_int")),
    (GteInt, op_name("gte_int")),
    (AddFloat, op_name("add_float")),
    (SubFloat, op_name("sub_float")),
    (MulFloat, op_name("mul_float")),
    (DivFloat, op_name("div_float")),
    (NegFloat, op_name("neg_float")),
    (EqFloat, op_name("eq_float")),
    (LtFloat, op_name("lt_float")),
    (LteFloat, op_name("lte_float")),
    (GtFloat, op_name("gt_float")),
    (GteFloat, op_name("gte_float")),
    // Intrinsic numeric functions
    // These names are used in the source language
    (ByteToInt, name("byte_to_int")),
    (ByteToIntSigned, name("byte_to_int_signed")),
    (IntToByte, name("int_to_byte")),
    (IntShiftLeft, name("int_shift_left")),
    (IntShiftRight, name("int_shift_right")),
    (IntBitAnd, name("int_bit_and")),
    (IntBitOr, name("int_bit_or")),
    (IntBitXor, name("int_bit_xor")),
];

// Signatures:

fn bool() -> Type {
    Type::Bool
}

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
        AddByte | SubByte | MulByte | DivByte => pure(tuple!(byte(), byte()), byte()),
        AddInt | SubInt | MulInt | DivInt => pure(tuple!(int(), int()), int()),
        AddFloat | SubFloat | MulFloat | DivFloat => pure(tuple!(float(), float()), float()),

        NegInt => pure(int(), int()),
        NegByte => pure(byte(), byte()),
        NegFloat => pure(float(), float()),

        EqByte | LtByte | LteByte | GtByte | GteByte => pure(tuple!(byte(), byte()), bool()),
        EqInt | LtInt | LteInt | GtInt | GteInt => pure(tuple!(int(), int()), bool()),
        EqFloat | LtFloat | LteFloat | GtFloat | GteFloat => pure(tuple!(float(), float()), bool()),

        ByteToInt => pure(byte(), int()),
        ByteToIntSigned => pure(byte(), int()),
        IntToByte => pure(int(), byte()),
        IntShiftLeft => pure(tuple!(int(), int()), int()),
        IntShiftRight => pure(tuple!(int(), int()), int()),
        IntBitAnd => pure(tuple!(int(), int()), int()),
        IntBitOr => pure(tuple!(int(), int()), int()),
        IntBitXor => pure(tuple!(int(), int()), int()),
    }
}
