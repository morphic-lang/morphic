use crate::data::purity::Purity;
use crate::data::visibility::Visibility;
use std::collections::VecDeque;

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
    TypeDef(
        Visibility,
        TypeName,
        Vec<TypeParam>,
        Vec<(Visibility, CtorName, Option<Type>)>,
    ),
    ValDef(Visibility, ValName, Type, Expr),
    ModDef(Visibility, ModName, ModSpec, Vec<ModBinding>, ExposeSpec),
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
    Val(Visibility, ValName),
    Type(Visibility, TypeName, Vec<(Visibility, CtorName)>),
    Mod(Visibility, ModName, Box<ExposeSpec>),
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
    // App expressions in the raw AST need to explicitly distinguish between taking "multiple
    // arguments" and taking a single tuple as an argument, because this distinction is relevant for
    // pipe desugaring.  Subsequent passes in the compiler do not make this distinction.
    //
    // The `usize`s denote the span of the argument list.
    App(Purity, Box<Expr>, (usize, usize, Vec<Expr>)),
    // Without this variant, error messages for `(a + b) <| c` would be horrible
    OpApp(Op, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    LetMany(VecDeque<(Pattern, Expr)>, Box<Expr>),

    PipeLeft(Box<Expr>, Box<Expr>),
    PipeRight(Box<Expr>, Box<Expr>),

    ArrayLit(Vec<Expr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),

    Span(usize, usize, Box<Expr>),
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
    Expr::OpApp(op, Box::new(Expr::Tuple(vec![left, right])))
}

pub fn unop(op: Op, arg: Expr) -> Expr {
    Expr::OpApp(op, Box::new(arg))
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

    Span(usize, usize, Box<Pattern>),
}
