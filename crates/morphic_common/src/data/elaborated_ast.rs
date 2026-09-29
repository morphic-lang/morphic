//! The program after trait solving in signatures.  Every written type carries its evidence,
//! and every impl carries the derivations of its trait's superclasses.  Bodies are still
//! resolved expressions; inference is next.

use crate::data::kinded_ast::Kind;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::data::resolved_ast::{
    CustomGlobalId, CustomImplId, CustomTraitId, CustomTypeId, ImplFuncLayout, ImplId, ModId,
    SuperId, TraitConstrId, TraitFuncConstrId, TraitFuncId, TraitFuncLayout, TraitFuncParamId,
    TraitId, TypeHead, TypeParamId, VariantId,
};
use id_collections::{Count, IdVec};
use std::collections::BTreeSet;

/// A type in which every application of a constrained constructor carries evidence for each of
/// its constraints.  `E` is that evidence: a derivation in signatures, an obligation during
/// inference.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type<E = Derivation> {
    App(TypeHead, Vec<Type<E>>),
    /// A constructor with constraints, applied to at least the leading parameters its
    /// constraints mention (see `res::constrained_prefix`), with evidence for each constraint at
    /// these arguments.  Such an
    /// application carries all of the constructor's evidence, so it can stand for a constructor
    /// variable like any other application, and it never appears under `App`.
    Constrained(CustomTypeId, Vec<Type<E>>, IdVec<TraitConstrId, E>),
    Tuple(Vec<Type<E>>),
    Func(Purity, Box<Type<E>>, Box<Type<E>>),
}

/// A trait applied to type arguments; see `res::TraitApp`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TraitApp<E = Derivation> {
    pub trait_: TraitId,
    pub args: Vec<Type<E>>,
}

/// Evidence that a trait constraint holds, relative to the givens `G` of the enclosing item: a
/// definition's or impl's trait constraints, a type's constraints, or a trait's own constraint.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Derivation<G = TraitConstrId> {
    Given(G),
    /// An impl, instantiated at the given type arguments, whose own constraints are discharged
    /// by the sub-derivations.
    Impl(
        ImplId,
        IdVec<TypeParamId, Type<Derivation<G>>>,
        IdVec<TraitConstrId, Derivation<G>>,
    ),
    /// A superclass of the trait of the inner derivation.  The inner derivation is never an impl
    /// derivation, since that projection normalizes to the impl's stored superclass derivation.
    Super(Box<Derivation<G>>, SuperId),
}

/// A reference to a trait func at particular types; see `res::TraitFuncSig`.  `E` is the
/// evidence for a trait constraint, and also the evidence inside the types: an obligation after
/// inference, a derivation after solving.
#[derive(Clone, Debug)]
pub struct TraitFuncInst<E> {
    /// The trait's parameters, and the evidence for the trait constraint at them, which is what
    /// determines the impl whose func is meant.
    pub trait_args: IdVec<TypeParamId, Type<E>>,
    pub trait_deriv: E,
    /// The func's own parameters, and the evidence for its own constraints.
    pub func_args: IdVec<TraitFuncParamId, Type<E>>,
    pub func_derivs: IdVec<TraitFuncConstrId, E>,
}

/// The one given of a trait's superclass constraints: the trait's own constraint, over the
/// trait's parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TraitSelfConstr;

/// The givens of a trait func's signature: the trait's own constraint and the func's own.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TraitGiven {
    SelfConstr,
    Own(TraitFuncConstrId),
}

impl<E> Type<E> {
    pub fn param(id: TypeParamId) -> Type<E> {
        Type::App(TypeHead::Var(id), Vec::new())
    }

    pub fn ctor(id: res::TypeId) -> Type<E> {
        Type::App(TypeHead::Ctor(id), Vec::new())
    }

    /// Replaces every piece of evidence, outermost first.
    pub fn map_evidence<T>(&self, f: &mut impl FnMut(&E) -> T) -> Type<T> {
        match self {
            Type::App(head, args) => {
                Type::App(*head, args.iter().map(|arg| arg.map_evidence(f)).collect())
            }
            Type::Constrained(id, args, evidence) => Type::Constrained(
                *id,
                args.iter().map(|arg| arg.map_evidence(f)).collect(),
                evidence.map_refs(|_, e| f(e)),
            ),
            Type::Tuple(items) => {
                Type::Tuple(items.iter().map(|item| item.map_evidence(f)).collect())
            }
            Type::Func(purity, arg, ret) => Type::Func(
                *purity,
                Box::new(arg.map_evidence(f)),
                Box::new(ret.map_evidence(f)),
            ),
        }
    }
}

impl<E> TraitApp<E> {
    pub fn map_evidence<T>(&self, f: &mut impl FnMut(&E) -> T) -> TraitApp<T> {
        TraitApp {
            trait_: self.trait_,
            args: self.args.iter().map(|arg| arg.map_evidence(f)).collect(),
        }
    }
}

/// A simultaneous substitution of types for type parameters and of derivations for givens,
/// taking terms over givens `G` to terms over givens `H`.
pub struct Subst<'a, G, H> {
    pub types: &'a IdVec<TypeParamId, Type<Derivation<H>>>,
    pub givens: &'a dyn Fn(&G) -> Derivation<H>,
}

impl<'a, G, H: Clone> Subst<'a, G, H> {
    pub fn type_(&self, type_: &Type<Derivation<G>>) -> Type<Derivation<H>> {
        match type_ {
            Type::App(TypeHead::Var(param), args) => {
                let mut result = self.types[param].clone();
                if args.is_empty() {
                    return result;
                }
                let subst_args = args.iter().map(|arg| self.type_(arg));
                match &mut result {
                    // A constrained application keeps its evidence: its constraints mention none
                    // of the parameters the further arguments instantiate.
                    Type::App(_, result_args) | Type::Constrained(_, result_args, _) => {
                        result_args.extend(subst_args);
                        result
                    }
                    // Kind checking guarantees that a parameter applied to arguments is
                    // instantiated with a (possibly partial) application.
                    Type::Tuple(_) | Type::Func(_, _, _) => unreachable!(),
                }
            }
            Type::App(head @ TypeHead::Ctor(_), args) => {
                Type::App(*head, args.iter().map(|arg| self.type_(arg)).collect())
            }
            Type::Constrained(id, args, evidence) => Type::Constrained(
                *id,
                args.iter().map(|arg| self.type_(arg)).collect(),
                evidence.map_refs(|_, deriv| self.derivation(deriv)),
            ),
            Type::Tuple(items) => Type::Tuple(items.iter().map(|item| self.type_(item)).collect()),
            Type::Func(purity, arg, ret) => Type::Func(
                *purity,
                Box::new(self.type_(arg)),
                Box::new(self.type_(ret)),
            ),
        }
    }

    pub fn trait_app(&self, app: &TraitApp<Derivation<G>>) -> TraitApp<Derivation<H>> {
        TraitApp {
            trait_: app.trait_,
            args: app.args.iter().map(|arg| self.type_(arg)).collect(),
        }
    }

    pub fn derivation(&self, deriv: &Derivation<G>) -> Derivation<H> {
        match deriv {
            Derivation::Given(given) => (self.givens)(given),
            Derivation::Impl(id, args, subs) => Derivation::Impl(
                *id,
                args.map_refs(|_, arg| self.type_(arg)),
                subs.map_refs(|_, sub| self.derivation(sub)),
            ),
            Derivation::Super(inner, index) => {
                Derivation::Super(Box::new(self.derivation(inner)), *index)
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<ModId, res::ModSymbols>,
    pub custom_types: IdVec<CustomTypeId, TypeDef>,
    pub custom_type_symbols: IdVec<CustomTypeId, res::TypeSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub vals: IdVec<CustomGlobalId, ValDef>,
    pub val_symbols: IdVec<CustomGlobalId, res::ValSymbols>,
    pub traits: IdVec<CustomTraitId, TraitDef>,
    pub trait_symbols: IdVec<CustomTraitId, res::TraitSymbols>,
    pub impls: IdVec<CustomImplId, ImplDef>,
    pub impl_symbols: IdVec<CustomImplId, res::ImplSymbols>,
    pub impl_scope: IdVec<ModId, BTreeSet<ImplId>>,
    pub main: CustomGlobalId,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub param_kinds: IdVec<TypeParamId, Kind>,
    /// The type's constraints, over its parameters; evidence inside them refers to the
    /// constraints themselves.
    pub trait_constrs: IdVec<TraitConstrId, TraitApp>,
    /// Evidence inside variant types refers to the type's constraints.
    pub variants: IdVec<VariantId, Option<Type>>,
}

impl TypeDef {
    /// See `res::constrained_prefix`.  The evidence inside a constraint only mentions parameters
    /// that the constraint's own arguments mention, so evidence is not looked into.
    pub fn constrained_prefix(&self) -> Count<TypeParamId> {
        fn extend(type_: &Type, prefix: &mut usize) {
            match type_ {
                Type::App(head, args) => {
                    if let TypeHead::Var(param) = head {
                        *prefix = (*prefix).max(param.0 + 1);
                    }
                    args.iter().for_each(|arg| extend(arg, prefix));
                }
                Type::Constrained(_, args, _) => args.iter().for_each(|arg| extend(arg, prefix)),
                Type::Tuple(items) => items.iter().for_each(|item| extend(item, prefix)),
                Type::Func(_, arg, ret) => {
                    extend(arg, prefix);
                    extend(ret, prefix);
                }
            }
        }
        let mut prefix = 0;
        for (_, constr) in &self.trait_constrs {
            constr.args.iter().for_each(|arg| extend(arg, &mut prefix));
        }
        Count::from_value(prefix)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeScheme {
    pub param_kinds: IdVec<TypeParamId, Kind>,
    pub trait_constrs: IdVec<TraitConstrId, TraitApp>,
    pub body: Type,
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: TypeScheme,
    pub body: res::Expr,
}

#[derive(Clone, Debug)]
pub struct TraitDef {
    pub param_kinds: IdVec<TypeParamId, Kind>,
    /// Superclasses, over the trait's parameters; evidence inside them refers to the trait's own
    /// constraint.
    pub supers: IdVec<SuperId, TraitApp<Derivation<TraitSelfConstr>>>,
    pub funcs: IdVec<TraitFuncId, TraitFuncSig>,
}

impl TraitDef {
    pub fn func_layout(&self, func: TraitFuncId) -> TraitFuncLayout {
        TraitFuncLayout {
            num_trait_params: self.param_kinds.count(),
            num_own_params: self.funcs[func].own_param_kinds.count(),
        }
    }
}

/// See `res::TraitFuncSig`.  Evidence refers to the trait's own constraint and the func's own.
#[derive(Clone, Debug)]
pub struct TraitFuncSig {
    pub own_param_kinds: IdVec<TraitFuncParamId, Kind>,
    pub own_constrs: IdVec<TraitFuncConstrId, TraitApp<Derivation<TraitGiven>>>,
    pub body: Type<Derivation<TraitGiven>>,
}

#[derive(Clone, Debug)]
pub struct ImplDef {
    pub trait_: TraitId,
    pub param_kinds: IdVec<TypeParamId, Kind>,
    /// The trait's arguments, over the impl's parameters.  Evidence inside them refers to the
    /// impl's constraints.
    pub head: Vec<Type>,
    pub trait_constrs: IdVec<TraitConstrId, TraitApp>,
    /// A derivation of each superclass of the trait for the head, relative to the impl's own
    /// trait constraints.
    pub supers: IdVec<SuperId, Derivation>,
    pub funcs: IdVec<TraitFuncId, CustomGlobalId>,
}

impl ImplDef {
    pub fn func_layout(&self) -> ImplFuncLayout {
        ImplFuncLayout {
            num_impl_params: self.param_kinds.count(),
            num_impl_constrs: self.trait_constrs.count(),
        }
    }
}
