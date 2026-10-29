use std::fmt;

/// A builtin number type: the two's complement signed integers `I*`, the unsigned integers
/// `U*`, and the IEEE floats `F*`, each of the named width.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NumType {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
}

/// An integer number type, which the bitwise intrinsics are defined on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntType {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
}

/// The width of an integer type, which is what its bitwise operations and the LLVM intrinsics
/// depend on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntWidth {
    Bits8,
    Bits16,
    Bits32,
    Bits64,
}

/// A float number type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FloatType {
    F32,
    F64,
}

/// Whether an integer type reads its values as two's complement or as nonnegative, which decides
/// how it widens, divides, compares, and converts to a float.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Signedness {
    Signed,
    Unsigned,
}

/// A number type as an integer or a float type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NumKind {
    Int(IntType),
    Float(FloatType),
}

impl NumType {
    pub const ALL: [NumType; 10] = [
        NumType::I8,
        NumType::I16,
        NumType::I32,
        NumType::I64,
        NumType::U8,
        NumType::U16,
        NumType::U32,
        NumType::U64,
        NumType::F32,
        NumType::F64,
    ];

    /// The type's name in the source language.
    pub fn name(self) -> &'static str {
        match self {
            NumType::I8 => "I8",
            NumType::I16 => "I16",
            NumType::I32 => "I32",
            NumType::I64 => "I64",
            NumType::U8 => "U8",
            NumType::U16 => "U16",
            NumType::U32 => "U32",
            NumType::U64 => "U64",
            NumType::F32 => "F32",
            NumType::F64 => "F64",
        }
    }

    pub fn from_name(name: &str) -> Option<NumType> {
        NumType::ALL.into_iter().find(|num| num.name() == name)
    }

    pub fn kind(self) -> NumKind {
        match self {
            NumType::I8 => NumKind::Int(IntType::I8),
            NumType::I16 => NumKind::Int(IntType::I16),
            NumType::I32 => NumKind::Int(IntType::I32),
            NumType::I64 => NumKind::Int(IntType::I64),
            NumType::U8 => NumKind::Int(IntType::U8),
            NumType::U16 => NumKind::Int(IntType::U16),
            NumType::U32 => NumKind::Int(IntType::U32),
            NumType::U64 => NumKind::Int(IntType::U64),
            NumType::F32 => NumKind::Float(FloatType::F32),
            NumType::F64 => NumKind::Float(FloatType::F64),
        }
    }

    /// The width of a value of the type, in bits.
    pub fn bits(self) -> u32 {
        match self.kind() {
            NumKind::Int(int) => int.width().bits(),
            NumKind::Float(float) => float.bits(),
        }
    }
}

impl IntType {
    pub const ALL: [IntType; 8] = [
        IntType::I8,
        IntType::I16,
        IntType::I32,
        IntType::I64,
        IntType::U8,
        IntType::U16,
        IntType::U32,
        IntType::U64,
    ];

    pub fn new(width: IntWidth, signedness: Signedness) -> IntType {
        match (width, signedness) {
            (IntWidth::Bits8, Signedness::Signed) => IntType::I8,
            (IntWidth::Bits16, Signedness::Signed) => IntType::I16,
            (IntWidth::Bits32, Signedness::Signed) => IntType::I32,
            (IntWidth::Bits64, Signedness::Signed) => IntType::I64,
            (IntWidth::Bits8, Signedness::Unsigned) => IntType::U8,
            (IntWidth::Bits16, Signedness::Unsigned) => IntType::U16,
            (IntWidth::Bits32, Signedness::Unsigned) => IntType::U32,
            (IntWidth::Bits64, Signedness::Unsigned) => IntType::U64,
        }
    }

    pub fn width(self) -> IntWidth {
        match self {
            IntType::I8 | IntType::U8 => IntWidth::Bits8,
            IntType::I16 | IntType::U16 => IntWidth::Bits16,
            IntType::I32 | IntType::U32 => IntWidth::Bits32,
            IntType::I64 | IntType::U64 => IntWidth::Bits64,
        }
    }

    pub fn signedness(self) -> Signedness {
        match self {
            IntType::I8 | IntType::I16 | IntType::I32 | IntType::I64 => Signedness::Signed,
            IntType::U8 | IntType::U16 | IntType::U32 | IntType::U64 => Signedness::Unsigned,
        }
    }

    pub fn bits(self) -> u32 {
        self.width().bits()
    }
}

impl IntWidth {
    pub const ALL: [IntWidth; 4] = [
        IntWidth::Bits8,
        IntWidth::Bits16,
        IntWidth::Bits32,
        IntWidth::Bits64,
    ];

    pub fn bits(self) -> u32 {
        match self {
            IntWidth::Bits8 => 8,
            IntWidth::Bits16 => 16,
            IntWidth::Bits32 => 32,
            IntWidth::Bits64 => 64,
        }
    }
}

impl FloatType {
    pub const ALL: [FloatType; 2] = [FloatType::F32, FloatType::F64];

    pub fn bits(self) -> u32 {
        match self {
            FloatType::F32 => 32,
            FloatType::F64 => 64,
        }
    }
}

impl From<IntType> for NumType {
    fn from(int: IntType) -> NumType {
        match int {
            IntType::I8 => NumType::I8,
            IntType::I16 => NumType::I16,
            IntType::I32 => NumType::I32,
            IntType::I64 => NumType::I64,
            IntType::U8 => NumType::U8,
            IntType::U16 => NumType::U16,
            IntType::U32 => NumType::U32,
            IntType::U64 => NumType::U64,
        }
    }
}

impl From<FloatType> for NumType {
    fn from(float: FloatType) -> NumType {
        match float {
            FloatType::F32 => NumType::F32,
            FloatType::F64 => NumType::F64,
        }
    }
}

/// A number literal, of the type its variant names.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub enum NumLit {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    F32(f32),
    F64(f64),
}

impl NumLit {
    pub fn num_type(self) -> NumType {
        match self {
            NumLit::I8(_) => NumType::I8,
            NumLit::I16(_) => NumType::I16,
            NumLit::I32(_) => NumType::I32,
            NumLit::I64(_) => NumType::I64,
            NumLit::U8(_) => NumType::U8,
            NumLit::U16(_) => NumType::U16,
            NumLit::U32(_) => NumType::U32,
            NumLit::U64(_) => NumType::U64,
            NumLit::F32(_) => NumType::F32,
            NumLit::F64(_) => NumType::F64,
        }
    }
}

/// The literal as the source language spells it: a suffix names any type other than the
/// defaults `I64` and `F64`.
impl fmt::Display for NumLit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NumLit::I8(val) => write!(f, "{}i8", val),
            NumLit::I16(val) => write!(f, "{}i16", val),
            NumLit::I32(val) => write!(f, "{}i32", val),
            NumLit::I64(val) => write!(f, "{}", val),
            NumLit::U8(val) => write!(f, "{}u8", val),
            NumLit::U16(val) => write!(f, "{}u16", val),
            NumLit::U32(val) => write!(f, "{}u32", val),
            NumLit::U64(val) => write!(f, "{}u64", val),
            NumLit::F32(val) => write!(f, "{:?}f32", val),
            NumLit::F64(val) => write!(f, "{:?}", val),
        }
    }
}
