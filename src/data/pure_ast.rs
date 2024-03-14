use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;
use id_collections::{id_type, IdVec};

#[id_type]
pub struct TypeParamId(pub usize);

#[id_type]
pub struct TypeId(pub usize);

#[id_type]
pub struct CustomTypeId(pub usize);

#[id_type]
pub struct CustomGlobalId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum GlobalId {
    Intrinsic(Intrinsic),
    ArrayOp(res::ArrayOp),
    IoOp(IoOp),
    Panic,
    Ctor(res::TypeId, res::VariantId),
    Custom(res::CustomGlobalId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum IoOp {
    Input,
    Output,
}

pub fn io_op_purity(op: IoOp) -> Purity {
    match op {
        IoOp::Input => Purity::Impure,
        IoOp::Output => Purity::Impure,
    }
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<CustomTypeId, TypeDef<Purity>>,
    pub custom_type_symbols: IdVec<CustomTypeId, res::TypeSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub vals: IdVec<CustomGlobalId, ValDef<Purity>>,
    pub val_symbols: IdVec<CustomGlobalId, ValSymbols>,
    pub main: CustomGlobalId,
}

#[derive(Clone, Debug)]
pub struct TypeDef<P> {
    pub num_params: usize,
    pub variants: IdVec<res::VariantId, Option<Type<P>>>,
}

#[derive(Clone, Debug)]
pub struct ValDef<P> {
    pub scheme: TypeScheme<P>,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct ValSymbols {
    pub mod_: res::ModId,
    pub type_param_names: IdVec<TypeParamId, raw::TypeParam>,
    pub val_name: raw::ValName,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type<P> {
    Var(TypeParamId),
    App(TypeId, Vec<Type<P>>),
    Tuple(Vec<Type<P>>),
    Func(P, Box<Type<P>>, Box<Type<P>>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeScheme<P> {
    pub num_params: usize,
    pub body: Type<P>,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Global(res::GlobalId, IdVec<res::TypeParamId, res::Type>),
    Local(res::LocalId),
    Tuple(Vec<Expr>),
    Lam(
        Purity,
        res::Type, // Argument type
        res::Type, // Return type
        Pattern,
        Box<Expr>,
        Option<prof::ProfilePointId>,
    ),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, res::Type),
    LetMany(Vec<(Pattern, Expr)>, Box<Expr>),

    ArrayLit(res::Type, Vec<Expr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),

    Span(usize, usize, Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any(res::Type),
    Var(res::Type),
    Tuple(Vec<Pattern>),
    Ctor(
        res::TypeId,
        Vec<res::Type>,
        res::VariantId,
        Option<Box<Pattern>>,
    ),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),

    Span(usize, usize, Box<Pattern>),
}
