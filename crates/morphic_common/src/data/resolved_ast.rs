use std::path::PathBuf;

use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use id_collections::{id_type, IdVec};

// 'ModId' is used only for the purposes of reporting human-readable module information to the user,
// for example during error reporting. After the initial name resolution pass is complete, the
// module from which a particular type or value originated is semantically irrelevant.
#[id_type]
pub struct ModId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeId {
    Bool,
    Byte,
    Int,
    Float,
    Array,
    Custom(CustomTypeId),
}

#[id_type]
pub struct CustomTypeId(pub usize);

#[id_type]
pub struct VariantId(pub usize);

#[id_type]
pub struct TypeParamId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum GlobalId {
    Intrinsic(Intrinsic),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic,
    Ctor(TypeId, VariantId),
    Custom(CustomGlobalId),
}

#[id_type]
pub struct CustomGlobalId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum IoOp {
    Input,
    Output,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArrayOp {
    Get,
    Extract,
    Len,
    Push,
    Pop,
    Reserve,
}

#[id_type]
pub struct LocalId(pub usize);

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<ModId, ModSymbols>,
    pub custom_types: IdVec<CustomTypeId, TypeDef>,
    pub custom_type_symbols: IdVec<CustomTypeId, TypeSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub vals: IdVec<CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<CustomGlobalId, ValSymbols>,
    pub main: CustomGlobalId,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModDeclLoc {
    Root,
    ChildOf { parent: ModId, name: raw::ModName },
}

#[derive(Clone, Debug)]
pub struct ModSymbols {
    pub file: PathBuf,
    pub decl_loc: ModDeclLoc,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub num_params: usize,
    pub variants: IdVec<VariantId, Option<Type>>,
}

/// The source spans of a type.  Resolved types do not carry spans directly because they are
/// compared structurally and used as monomorphization keys. The spans are kept alongside the types
/// in symbol tables.  Each `TypeSpans` tree has the same shape as the type it describes: an
/// application's children are its arguments, a tuple's are its items, and a function type's are its
/// argument and its result.
#[derive(Clone, Debug)]
pub struct TypeSpans {
    pub span: Option<(usize, usize)>,
    pub children: Vec<TypeSpans>,
}

impl TypeSpans {
    pub fn of(type_: &raw::Type) -> TypeSpans {
        Self::of_rec(type_, None)
    }

    fn of_rec(type_: &raw::Type, span: Option<(usize, usize)>) -> TypeSpans {
        let children = |types: &[raw::Type]| types.iter().map(|t| Self::of_rec(t, None)).collect();
        match type_ {
            raw::Type::Span(lo, hi, inner) => Self::of_rec(inner, Some((*lo, *hi))),
            raw::Type::Var(_) => TypeSpans {
                span,
                children: Vec::new(),
            },
            raw::Type::App(_, _, args) | raw::Type::AppVar(_, args) => TypeSpans {
                span,
                children: children(args),
            },
            raw::Type::Tuple(items) => TypeSpans {
                span,
                children: children(items),
            },
            raw::Type::Func(_, arg, ret) => TypeSpans {
                span,
                children: vec![Self::of_rec(arg, None), Self::of_rec(ret, None)],
            },
        }
    }

    /// The span of the sub-term reached by following `path` (a sequence of child indices), or of
    /// the nearest enclosing sub-term that has one.
    pub fn span_at(&self, path: &[usize]) -> Option<(usize, usize)> {
        let mut node = self;
        let mut best = self.span;
        for &index in path {
            match node.children.get(index) {
                Some(child) => {
                    node = child;
                    if child.span.is_some() {
                        best = child.span;
                    }
                }
                None => break,
            }
        }
        best
    }
}

#[derive(Clone, Debug)]
pub struct VariantSymbols {
    pub variant_name: raw::CtorName,
    pub span: (usize, usize),
    pub content_spans: Option<TypeSpans>,
}

#[derive(Clone, Debug)]
pub struct TypeSymbols {
    pub mod_: ModId,
    pub type_name: raw::TypeName,
    pub variant_symbols: IdVec<VariantId, VariantSymbols>,
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: TypeScheme,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct ValSymbols {
    pub mod_: ModId,
    pub type_param_names: IdVec<TypeParamId, raw::TypeParam>,
    pub val_name: raw::ValName,
    pub type_spans: TypeSpans,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeHead {
    Ctor(TypeId),
    Var(TypeParamId),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    /// Application of a type constructor or type parameter to zero or more arguments.  A bare
    /// constructor or parameter is an application to zero arguments.  An argument may itself be a
    /// partial application (of a constructor, or of a parameter of higher kind), but a type in
    /// "value position" (the type of an expression, a variant payload, and so on) always has kind
    /// `Type`.  Tuples and functions are not applications: a parameter of higher kind never unifies
    /// with either.
    App(TypeHead, Vec<Type>),
    Tuple(Vec<Type>),
    Func(Purity, Box<Type>, Box<Type>),
}

impl Type {
    pub fn param(id: TypeParamId) -> Type {
        Type::App(TypeHead::Var(id), Vec::new())
    }

    pub fn ctor(id: TypeId) -> Type {
        Type::App(TypeHead::Ctor(id), Vec::new())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeScheme {
    pub num_params: usize,
    pub body: Type,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Global(GlobalId),
    Local(LocalId),
    Tuple(Vec<Expr>),
    Lam(Purity, Pattern, Box<Expr>, Option<prof::ProfilePointId>),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    LetMany(Vec<(Pattern, Expr)>, Box<Expr>),

    ArrayLit(Vec<Expr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),

    Span(usize, usize, Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Any,
    Var,
    Tuple(Vec<Pattern>),
    Ctor(TypeId, VariantId, Option<Box<Pattern>>),
    Annot(Box<Pattern>, Type),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),

    Span(usize, usize, Box<Pattern>),
}
