use crate::data::purity::Purity;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeName(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CtorName(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeParam(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ValName(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModName(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModPath(pub Vec<ModName>);

// TODO: Rename 'Program' to 'Module'
#[derive(Clone, Debug)]
pub struct Program(pub Vec<Item>);

#[derive(Clone, Debug)]
pub enum Item {
    TypeDef(TypeName, Vec<TypeParam>, Vec<(CtorName, Option<Type>)>),
    ValDef(ValName, Type, Expr),
    ModDef(ModName, ModSpec, Vec<ModBinding>, ExposeSpec),
    ModImport(ModName, ExposeSpec),
    ModExpose(ModPath, ExposeSpec),
}

#[derive(Clone, Debug)]
pub struct ModBinding {
    pub name: ModName,
    pub binding: ModPath,
}

#[derive(Clone, Debug)]
pub enum ModSpec {
    File(Vec<String>),
    Inline(Program),
}

#[derive(Clone, Debug)]
pub enum ExposeItem {
    Val(ValName),
    Type(TypeName, Vec<CtorName>),
    Mod(ModName),
}

#[derive(Clone, Debug)]
pub enum ExposeSpec {
    // TODO: Add support for glob imports
    Specific(Vec<ExposeItem>),
}

#[derive(Clone, Debug)]
pub enum Type {
    Var(TypeParam),
    App(ModPath, TypeName, Vec<Type>),
    Tuple(Vec<Type>),
    Func(Purity, Box<Type>, Box<Type>),
}

#[derive(Clone, Debug)]
pub enum Expr {
    // Qualified and unqualified names have sufficiently different resolution rules that it is
    // useful to think of them as separate single syntactic constructs.  An unqualified name
    // *cannot* be regarded as a qualified name with an empty mod path, because unqualified names
    // are special in that they may refer to local variables as well as module-scoped values.
    Var(ValName),
    QualName(ModPath, ValName),
    Op(Op),
    Ctor(ModPath, CtorName),
    Tuple(Vec<Expr>),
    Lam(Purity, Pattern, Box<Expr>),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    Let(Pattern, Box<Expr>, Box<Expr>),

    ArrayLit(Vec<Expr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Op {
    AddByte,
    SubByte,
    MulByte,
    DivByte,
    NegByte,

    EqByte,
    LtByte,
    LteByte,

    AddInt,
    SubInt,
    MulInt,
    DivInt,
    NegInt,

    EqInt,
    LtInt,
    LteInt,

    AddFloat,
    SubFloat,
    MulFloat,
    DivFloat,
    NegFloat,

    EqFloat,
    LtFloat,
    LteFloat,
}

pub fn binop(op: Op, left: Expr, right: Expr) -> Expr {
    Expr::App(
        Purity::Pure,
        Box::new(Expr::Op(op)),
        Box::new(Expr::Tuple(vec![left, right])),
    )
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any,
    Var(ValName),
    Tuple(Vec<Pattern>),
    Ctor(ModPath, CtorName, Option<Box<Pattern>>),

    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}
