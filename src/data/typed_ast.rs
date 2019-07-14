use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::id_vec::IdVec;

#[derive(Clone, Debug)]
pub struct Program {
    pub custom_types: IdVec<res::CustomTypeId, res::TypeDef>,
    pub custom_type_data: IdVec<res::CustomTypeId, res::TypeData>,
    pub vals: IdVec<res::CustomGlobalId, ValDef>,
    pub val_data: IdVec<res::CustomGlobalId, res::ValData>,
    pub main: res::CustomGlobalId,
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: res::TypeScheme,
    pub body: Expr,
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
    ),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, res::Type),
    Let(Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(res::Type, Vec<Expr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
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
}
