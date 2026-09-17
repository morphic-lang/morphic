use std::collections::BTreeSet;
use std::path::PathBuf;

use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use id_collections::{id_type, Count, IdVec};

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

/// A trait func is kept apart from ordinary globals because a reference to it stands for whichever
/// impl's func the trait solver selects.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum GlobalRef {
    Global(GlobalId),
    TraitFunc(TraitId, TraitFuncId),
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

#[id_type]
pub struct CustomTraitId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TraitId {
    Custom(CustomTraitId),
}

/// Indexes the funcs of a trait, in declaration order.
#[id_type]
pub struct TraitFuncId(pub usize);

#[id_type]
pub struct CustomImplId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ImplId {
    Custom(CustomImplId),
}

/// Indexes the trait constraints of a scheme or an impl, in declaration order.
#[id_type]
pub struct TraitConstrId(pub usize);

/// A superclass of a trait, by position in the trait's superclass list.
#[id_type]
pub struct SuperId(pub usize);

/// One of the type parameters a trait func's signature introduces beyond the trait's own.
#[id_type]
pub struct TraitFuncParamId(pub usize);

/// One of the trait constraints a trait func's signature declares beyond the trait's own.
#[id_type]
pub struct TraitFuncConstrId(pub usize);

/// A trait applied to type arguments, e.g., a constraint, a superclass, what is being impl'ed or a
/// goal to solve.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TraitApp {
    pub trait_: TraitId,
    pub args: Vec<Type>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<ModId, ModSymbols>,
    pub custom_types: IdVec<CustomTypeId, TypeDef>,
    pub custom_type_symbols: IdVec<CustomTypeId, TypeSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub vals: IdVec<CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<CustomGlobalId, ValSymbols>,
    pub traits: IdVec<CustomTraitId, TraitDef>,
    pub trait_symbols: IdVec<CustomTraitId, TraitSymbols>,
    pub impls: IdVec<CustomImplId, ImplDef>,
    pub impl_symbols: IdVec<CustomImplId, ImplSymbols>,
    /// The impls visible in each module: those declared in it and those imported into it.  This is
    /// the set the trait solver may use for constraints arising in the module's definitions.
    pub impl_scope: IdVec<ModId, BTreeSet<ImplId>>,
    pub main: CustomGlobalId,
}

#[derive(Clone, Debug)]
pub struct TraitDef {
    pub num_params: Count<TypeParamId>,
    /// Superclasses satisfied by the trait's own parameters.
    pub supers: IdVec<SuperId, TraitApp>,
    pub funcs: IdVec<TraitFuncId, TraitFuncSig>,
}

impl TraitDef {
    pub fn func_layout(&self, func: TraitFuncId) -> TraitFuncLayout {
        TraitFuncLayout {
            num_trait_params: self.num_params,
            num_own_params: self.funcs[func].num_own_params,
        }
    }
}

/// The signature a trait declares for one of its funcs, numbered as `TraitFuncLayout` describes.  A
/// reference to the func is a `TraitFuncInst`, and the definition implementing it has the layout
/// described by `ImplFuncLayout`.
#[derive(Clone, Debug)]
pub struct TraitFuncSig {
    pub num_own_params: Count<TraitFuncParamId>,
    pub own_constrs: IdVec<TraitFuncConstrId, TraitApp>,
    pub body: Type,
}

/// How a trait func's signature numbers its type parameters.
#[derive(Clone, Copy, Debug)]
pub struct TraitFuncLayout {
    pub num_trait_params: Count<TypeParamId>,
    pub num_own_params: Count<TraitFuncParamId>,
}

impl TraitFuncLayout {
    pub fn num_params(&self) -> Count<TypeParamId> {
        Count::from_value(self.num_trait_params.to_value() + self.num_own_params.to_value())
    }

    /// The signature's numbering of one of the func's own parameters.
    pub fn own_param(&self, param: TraitFuncParamId) -> TypeParamId {
        TypeParamId(self.num_trait_params.to_value() + param.0)
    }

    /// Something for each of the trait's parameters and each of the func's own, in the
    /// signature's numbering.
    pub fn params<T>(
        &self,
        trait_args: IdVec<TypeParamId, T>,
        own_args: IdVec<TraitFuncParamId, T>,
    ) -> IdVec<TypeParamId, T> {
        debug_assert_eq!(trait_args.count(), self.num_trait_params);
        debug_assert_eq!(own_args.count(), self.num_own_params);
        let mut result = trait_args;
        let _ = result.extend(own_args.into_values());
        result
    }
}

/// A reference to a trait func at particular types.  `D` is the evidence for a trait constraint:
/// an obligation id after type inference, a derivation after trait solving.
#[derive(Clone, Debug)]
pub struct TraitFuncInst<D> {
    /// The trait's parameters, and the evidence for the trait constraint at them, which is what
    /// determines the impl whose func is meant.
    pub trait_args: IdVec<TypeParamId, Type>,
    pub trait_deriv: D,
    /// The func's own parameters, and the evidence for its own constraints.
    pub func_args: IdVec<TraitFuncParamId, Type>,
    pub func_derivs: IdVec<TraitFuncConstrId, D>,
}

/// How the scheme of the definition implementing a trait func is laid out: the impl's parameters
/// and constraints come first, then the trait func's own.  Resolution builds such schemes and
/// monomorphization instantiates them through this type, so the layout is defined in one place.
#[derive(Clone, Copy, Debug)]
pub struct ImplFuncLayout {
    pub num_impl_params: Count<TypeParamId>,
    pub num_impl_constrs: Count<TraitConstrId>,
}

impl ImplFuncLayout {
    /// The impl func's numbering of one of the trait func's own parameters.
    pub fn own_param(&self, param: TraitFuncParamId) -> TypeParamId {
        TypeParamId(self.num_impl_params.to_value() + param.0)
    }

    /// The impl func's numbering of one of the trait func's own constraints.
    pub fn own_constr(&self, constr: TraitFuncConstrId) -> TraitConstrId {
        TraitConstrId(self.num_impl_constrs.to_value() + constr.0)
    }

    /// The number of parameters of an impl func whose trait func has `num_own_params` of its own.
    pub fn num_params(&self, num_own_params: Count<TraitFuncParamId>) -> Count<TypeParamId> {
        Count::from_value(self.num_impl_params.to_value() + num_own_params.to_value())
    }

    pub fn params<T>(
        &self,
        impl_args: IdVec<TypeParamId, T>,
        func_args: IdVec<TraitFuncParamId, T>,
    ) -> IdVec<TypeParamId, T> {
        debug_assert_eq!(impl_args.count(), self.num_impl_params);
        let mut result = impl_args;
        let _ = result.extend(func_args.into_values());
        result
    }

    pub fn constrs<D>(
        &self,
        impl_derivs: IdVec<TraitConstrId, D>,
        func_derivs: IdVec<TraitFuncConstrId, D>,
    ) -> IdVec<TraitConstrId, D> {
        debug_assert_eq!(impl_derivs.count(), self.num_impl_constrs);
        let mut result = impl_derivs;
        let _ = result.extend(func_derivs.into_values());
        result
    }
}

#[derive(Clone, Debug)]
pub struct TraitFuncSymbols {
    pub func_name: raw::ValName,
    pub span: (usize, usize),
    pub type_param_names: IdVec<TypeParamId, raw::TypeParam>,
    pub type_spans: TypeSpans,
    pub constr_spans: IdVec<TraitFuncConstrId, (usize, usize)>,
}

#[derive(Clone, Debug)]
pub struct TraitSymbols {
    pub mod_: ModId,
    pub trait_name: raw::TraitName,
    pub type_param_names: IdVec<TypeParamId, raw::TypeParam>,
    pub super_spans: IdVec<SuperId, (usize, usize)>,
    pub func_symbols: IdVec<TraitFuncId, TraitFuncSymbols>,
}

#[derive(Clone, Debug)]
pub struct ImplDef {
    pub trait_: TraitId,
    pub num_params: Count<TypeParamId>,
    /// The trait's arguments, over the impl's parameters.
    pub head: Vec<Type>,
    /// The impl's own requirements, which callers must discharge.
    pub trait_constrs: IdVec<TraitConstrId, TraitApp>,
    /// The definition implementing each func of the trait.  Its scheme is the trait's, with the
    /// head substituted in and the impl's parameters and constraints prepended.
    pub funcs: IdVec<TraitFuncId, CustomGlobalId>,
}

#[derive(Clone, Debug)]
pub struct ImplSymbols {
    pub mod_: ModId,
    pub impl_name: raw::ImplName,
    pub type_param_names: IdVec<TypeParamId, raw::TypeParam>,
    pub head_span: (usize, usize),
    pub constr_spans: IdVec<TraitConstrId, (usize, usize)>,
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
    pub num_params: Count<TypeParamId>,
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
    pub trait_constr_spans: IdVec<TraitConstrId, (usize, usize)>,
    // The impl this definition implements a func of, if any.
    pub impl_: Option<CustomImplId>,
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

/// Substitutes types for the type parameters of `type_`.  A parameter applied to arguments must
/// be substituted with a (possibly partial) application, which kind checking guarantees.
pub fn subst_type(subst: &IdVec<TypeParamId, Type>, type_: &Type) -> Type {
    match type_ {
        Type::App(TypeHead::Var(param), args) => {
            let mut result = subst[param].clone();
            if args.is_empty() {
                return result;
            }
            let subst_args = args.iter().map(|arg| subst_type(subst, arg));
            match &mut result {
                Type::App(_, result_args) => {
                    result_args.extend(subst_args);
                    result
                }
                Type::Tuple(_) | Type::Func(_, _, _) => unreachable!(),
            }
        }
        Type::App(head @ TypeHead::Ctor(_), args) => Type::App(
            *head,
            args.iter().map(|arg| subst_type(subst, arg)).collect(),
        ),
        Type::Tuple(items) => {
            Type::Tuple(items.iter().map(|item| subst_type(subst, item)).collect())
        }
        Type::Func(purity, arg, ret) => Type::Func(
            *purity,
            Box::new(subst_type(subst, arg)),
            Box::new(subst_type(subst, ret)),
        ),
    }
}

impl TraitApp {
    pub fn subst(&self, subst: &IdVec<TypeParamId, Type>) -> TraitApp {
        TraitApp {
            trait_: self.trait_,
            args: self.args.iter().map(|arg| subst_type(subst, arg)).collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeScheme {
    pub num_params: Count<TypeParamId>,
    pub trait_constrs: IdVec<TraitConstrId, TraitApp>,
    pub body: Type,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Global(GlobalRef),
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
