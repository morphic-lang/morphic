use crate::data::intrinsics::Intrinsic;
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TraitName(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ImplName(pub String);

/// A trait applied to type arguments, as written in a `where` clause, a trait's superclass
/// list, or an impl signature.
#[derive(Clone, Debug)]
pub struct TraitApp {
    pub path: ModPath,
    pub trait_name: TraitName,
    pub args: Vec<Type>,
    pub span: (usize, usize),
}

/// A func declared by a trait (a declaration with no body).
#[derive(Clone, Debug)]
pub struct TraitFunc {
    pub name: ValName,
    pub type_: Type,
    // The func's additional constraints beyond those of the trait.
    pub trait_constrs: Vec<TraitApp>,
    pub span: (usize, usize),
}

/// A func defined by an impl (a full value definition whose signature must agree with the trait's
/// declaration under substitution of the information from the impl signature).
#[derive(Clone, Debug)]
pub struct ImplFunc {
    pub name: ValName,
    pub type_: Type,
    // The func's additional constraints, which must agree with the trait's declaration.  The impl's
    // constraints are not repeated here.
    pub trait_constrs: Vec<TraitApp>,
    pub body: Expr,
    pub span: (usize, usize),
}

// TODO: Rename 'Program' to 'Module'
#[derive(Clone, Debug)]
pub struct Program(pub Vec<Item>);

#[derive(Clone, Debug)]
pub enum Item {
    TypeDef(
        Visibility,
        TypeName,
        Vec<TypeParam>,
        Vec<TraitApp>,
        // The `(usize, usize)` denotes the span of the variant declaration.
        Vec<(Visibility, CtorName, Option<Type>, (usize, usize))>,
    ),
    // The `(usize, usize)` denotes the span of the whole definition.
    ValDef(
        Visibility,
        ValName,
        Type,
        Vec<TraitApp>,
        Expr,
        (usize, usize),
    ),
    TraitDef(
        Visibility,
        TraitName,
        Vec<TypeParam>,
        Vec<TraitApp>,
        Vec<TraitFunc>,
    ),
    // The lone `TraitApp` is the impl signature, i.e., the trait being implemented, applied to
    // the types it is implemented for. The `Vec<TraitApp>` is a constraint list.
    ImplDef(Visibility, ImplName, TraitApp, Vec<TraitApp>, Vec<ImplFunc>),
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
    Trait(Visibility, TraitName, Vec<(Visibility, ValName)>),
    Impl(Visibility, ImplName),
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
    // A type parameter applied to one or more arguments, e.g. `f a`.
    AppVar(TypeParam, Vec<Type>),
    Tuple(Vec<Type>),
    Func(Purity, Box<Type>, Box<Type>),

    Span(usize, usize, Box<Type>),
}

#[derive(Clone, Debug)]
pub enum Expr {
    // Qualified and unqualified names have sufficiently different resolution rules that it is
    // useful to think of them as separate single syntactic constructs.  An unqualified name
    // *cannot* be regarded as a qualified name with an empty mod path, because unqualified names
    // are special in that they may refer to local variables as well as module-scoped values.
    Var(ValName),
    QualName(ModPath, ValName),
    Ctor(ModPath, CtorName),
    Tuple(Vec<Expr>),
    Lam(Purity, Pattern, Box<Expr>),
    // App expressions in the raw AST need to explicitly distinguish between taking "multiple
    // arguments" and taking a single tuple as an argument, because this distinction is relevant for
    // pipe desugaring.  Subsequent passes in the compiler do not make this distinction.
    //
    // The `usize`s denote the span of the argument list.
    App(Purity, Box<Expr>, (usize, usize, Vec<Expr>)),
    // This distinguishes function applications arising from operator expressions from all other
    // function applications. Without this variant, error messages for `(a + b) <| c` would be
    // horrible.
    OpApp(Intrinsic, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    LetMany(VecDeque<(Pattern, Expr)>, Box<Expr>),

    // `!` can be treated as an ordinary `OpApp`, since it follows normal evaluation rules
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),

    PipeLeft(Box<Expr>, Box<Expr>),
    PipeRight(Box<Expr>, Box<Expr>),

    ArrayLit(Vec<Expr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),

    Span(usize, usize, Box<Expr>),
}

pub fn binop(op: Intrinsic, left: Expr, right: Expr) -> Expr {
    Expr::OpApp(op, Box::new(Expr::Tuple(vec![left, right])))
}

pub fn unop(op: Intrinsic, arg: Expr) -> Expr {
    Expr::OpApp(op, Box::new(arg))
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any,
    Var(ValName),
    Tuple(Vec<Pattern>),
    Ctor(ModPath, CtorName, Option<Box<Pattern>>),
    // A pattern with a type annotation, e.g. `x: Int`. Type variables in the annotation refer to
    // the type parameters of the enclosing definition's signature.
    Annot(Box<Pattern>, Type),

    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),

    Span(usize, usize, Box<Pattern>),
}
