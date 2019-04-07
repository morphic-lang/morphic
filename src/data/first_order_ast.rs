use crate::data::purity::Purity;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CustomTypeId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CustomFuncId(pub usize);

#[derive(Clone, Debug)]
pub enum Type {
    Bool,
    Byte,
    Int,
    Float,
    Array(Box<Type>),
    HoleArray(Box<Type>),
    Tuple(Vec<Type>),
    Custom(CustomTypeId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct VariantId(pub usize);

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub variants: Vec<Option<Type>>,
}

#[derive(Clone, Debug)]
pub enum IOOp {
    Input,
    Output(Box<Expr>),
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
    ByteOp(BinOp, Box<Expr>, Box<Expr>),
    IntOp(BinOp, Box<Expr>, Box<Expr>),
    FloatOp(BinOp, Box<Expr>, Box<Expr>),
    ByteCmp(Comparison, Box<Expr>, Box<Expr>),
    IntCmp(Comparison, Box<Expr>, Box<Expr>),
    FloatCmp(Comparison, Box<Expr>, Box<Expr>),
    NegateByte(Box<Expr>),
    NegateInt(Box<Expr>),
    NegateFloat(Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Item(
        Type,                              // Item type
        Box<Expr>,                         // Array
        Box<Expr>,                         // Index
        Option<(CustomTypeId, VariantId)>, // Constructor to wrap returned HoleArray in
    ), // Returns tuple of (item, (potentially wrapped) hole array)
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
    ), // Returns item
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalId(pub usize);

#[derive(Clone, Debug)]
pub enum Expr {
    ArithOp(ArithOp),
    ArrayOp(ArrayOp),
    IOOp(IOOp),
    Ctor(CustomTypeId, VariantId, Option<Box<Expr>>),
    Local(LocalId),
    Tuple(Vec<Expr>),
    Call(Purity, CustomFuncId, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, Type),
    Let(
        Pattern,   // lhs
        Box<Expr>, // rhs
        Box<Expr>, // body
    ),

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
    pub custom_types: Vec<TypeDef>,
    pub funcs: Vec<FuncDef>,
    pub main: CustomFuncId,
}
