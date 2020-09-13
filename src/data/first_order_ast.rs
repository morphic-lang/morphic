use crate::data::intrinsics::Intrinsic;
use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
pub use crate::data::num_type::NumType;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
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

#[derive(Clone, Debug)]
pub enum CustomTypeSymbols {
    CustomType(mono::TypeSymbols),
    ClosureType,
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
}

id_type!(pub LocalId);

impl LocalId {
    pub const ARG: Self = LocalId(0);
}

#[derive(Clone, Debug)]
pub enum Expr {
    Intrinsic(Intrinsic, Box<Expr>),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(Type, Box<Expr>),
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
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub enum FuncSymbols {
    Global(mono::ValSymbols),
    Lam(lifted::LamSymbols),
    MainWrapper,
    Dispatch,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<CustomTypeId, TypeDef>,
    pub custom_type_symbols: IdVec<CustomTypeId, CustomTypeSymbols>,
    pub funcs: IdVec<CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<CustomFuncId, FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}
