use crate::data::purity::Purity;
use crate::util::id_vec::IdVec;

id_type!(pub CustomTypeId);

id_type!(pub CustomFuncId);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Bool,
    Num(NumType),
    Array(Box<Type>),
    HoleArray(Box<Type>),
    Tuple(Vec<Type>),
    Custom(CustomTypeId),
}

id_type!(pub VariantId);

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub variants: IdVec<VariantId, Option<Type>>,
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input,
    Output(Box<Expr>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum NumType {
    Byte,
    Int,
    Float,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Comparison {
    Less,
    LessEqual,
    Equal,
}

#[derive(Clone, Debug)]
pub enum ArithOp {
    Op(NumType, BinOp, Box<Expr>, Box<Expr>),
    Cmp(NumType, Comparison, Box<Expr>, Box<Expr>),
    Negate(NumType, Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Item(
        Type,      // Item type
        Box<Expr>, // Array
        Box<Expr>, // Index
    ), // Returns tuple of (item, hole array)
    Len(
        Type,      // Item type
        Box<Expr>, // Array
    ), // Returns int
    Push(
        Type,      // Item type
        Box<Expr>, // Array
        Box<Expr>, // Item
    ), // Returns new array
    Pop(
        Type,      // Item type
        Box<Expr>, // Array
    ), // Returns tuple (array, item)
    Replace(
        Type,
        Box<Expr>, // Hole array
        Box<Expr>, // Item
    ), // Returns new array
    Concat(
        Type,
        Box<Expr>, // First Array
        Box<Expr>, // Second Array
    ), //Returns new array
}

id_type!(pub LocalId);

impl LocalId {
    pub const ARG: Self = LocalId(0);
}

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(ArithOp),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Ctor(CustomTypeId, VariantId, Option<Box<Expr>>),
    Local(LocalId),
    Tuple(Vec<Expr>),
    Call(Purity, CustomFuncId, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, Type),
    LetMany(Vec<(Pattern, Expr)>, Box<Expr>),

    ArrayLit(Type, Vec<Expr>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any(Type),
    Var(Type),
    Tuple(Vec<Pattern>),
    Ctor(CustomTypeId, VariantId, Option<Box<Pattern>>),
    BoolConst(bool),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: Type,
    pub ret_type: Type,
    pub arg: Pattern,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<CustomTypeId, TypeDef>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub main: CustomFuncId,
}
