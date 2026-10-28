//! The trait solver, shared by signature elaboration and body solving.  It works over
//! elaborated types, so a goal's arguments carry their own evidence, which matching an impl head
//! reads off instead of searching for.

use crate::data::builtin_traits::BuiltinImpl;
use crate::data::elaborated_ast as elab;
use crate::data::elaborated_ast::{Derivation, Subst, TraitApp, TraitSelfConstr, Type};
use crate::data::resolved_ast::{
    CustomImplId, CustomTypeId, ImplId, SuperId, TraitConstrId, TraitId, TypeHead, TypeParamId,
};
use id_collections::{Count, IdVec};
use std::collections::BTreeSet;

/// What the solver needs to know about an impl: its head and constraints, over its own
/// parameters and givens.
#[derive(Clone, Debug)]
pub struct ImplFacts {
    pub trait_: TraitId,
    pub num_params: Count<TypeParamId>,
    pub head: Vec<elab::Type>,
    pub trait_constrs: IdVec<TraitConstrId, elab::TraitApp>,
}

/// The facts the solver consults.  During signature elaboration they are produced on demand,
/// which can fail; afterwards they are read off the program.
pub trait Facts {
    type Error;

    fn supers(
        &self,
        trait_: TraitId,
    ) -> Result<IdVec<SuperId, TraitApp<Derivation<TraitSelfConstr>>>, Self::Error>;

    fn impl_facts(&self, id: ImplId) -> Result<ImplFacts, Self::Error>;

    fn impl_supers(&self, id: ImplId) -> Result<IdVec<SuperId, elab::Derivation>, Self::Error>;

    /// The declared impls, in every module, for suggesting imports.
    fn all_impls(&self) -> Vec<ImplId>;

    /// See `res::constrained_prefix`.
    fn constrained_prefix(&self, id: CustomTypeId) -> Count<TypeParamId>;
}

/// The facts about a builtin impl: it is for one builtin type and has no constraints.
pub fn builtin_impl_facts(impl_: BuiltinImpl) -> ImplFacts {
    ImplFacts {
        trait_: TraitId::Builtin(impl_.trait_()),
        num_params: Count::from_value(0),
        head: vec![Type::ctor(impl_.type_().type_id())],
        trait_constrs: IdVec::new(),
    }
}

/// The facts about an impl, declared or builtin.
pub fn impl_facts_of(impls: &IdVec<CustomImplId, elab::ImplDef>, id: ImplId) -> ImplFacts {
    match id {
        ImplId::Builtin(builtin) => builtin_impl_facts(builtin),
        ImplId::Custom(custom) => {
            let def = &impls[custom];
            ImplFacts {
                trait_: def.trait_,
                num_params: def.param_kinds.count(),
                head: def.head.clone(),
                trait_constrs: def.trait_constrs.clone(),
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum SolveError<G, E> {
    NoImpl {
        goal: TraitApp<Derivation<G>>,
        chain: Vec<TraitApp<Derivation<G>>>,
        /// The impls declared in other modules that would match the goal if imported.
        importable: Vec<ImplId>,
        /// The builtin impls that would match the goal, but which impls of the same name
        /// declared or imported in the current module cover up.
        covered: Vec<ImplId>,
    },
    Ambiguous {
        goal: TraitApp<Derivation<G>>,
        candidates: Vec<ImplId>,
    },
    /// The constraints of an impl refer to each other's evidence in a cycle, so none of them
    /// can be solved first.
    CyclicConstrs {
        impl_: ImplId,
    },
    Facts(E),
}

impl<G, E> From<E> for SolveError<G, E> {
    fn from(err: E) -> Self {
        SolveError::Facts(err)
    }
}

/// The givens of an item, closed under superclass projection, each paired with its derivation.
pub fn closed_givens<G: Clone, F: Facts>(
    facts: &F,
    givens: Vec<(TraitApp<Derivation<G>>, Derivation<G>)>,
) -> Result<Vec<(TraitApp<Derivation<G>>, Derivation<G>)>, F::Error> {
    let mut result = givens;
    // The superclass graph is acyclic (see `check_traits`), so this terminates.
    let mut index = 0;
    while index < result.len() {
        let (constr, deriv) = result[index].clone();
        let supers = facts.supers(constr.trait_)?;
        let types = IdVec::from_vec(constr.args.clone());
        let subst = Subst {
            types: &types,
            givens: &|TraitSelfConstr| deriv.clone(),
        };
        for (super_id, super_) in &supers {
            result.push((
                subst.trait_app(super_),
                Derivation::Super(Box::new(deriv.clone()), super_id),
            ));
        }
        index += 1;
    }
    Ok(result)
}

/// Replaces every superclass projection out of an impl derivation by that impl's stored
/// superclass derivation, instantiated.  Substituting derivations for givens can create such
/// projections, so this follows every substitution whose givens may map to impl derivations.
pub fn normalize_derivation<G: Clone, F: Facts>(
    facts: &F,
    deriv: &Derivation<G>,
) -> Result<Derivation<G>, F::Error> {
    match deriv {
        Derivation::Given(given) => Ok(Derivation::Given(given.clone())),
        Derivation::Impl(id, args, subs) => Ok(Derivation::Impl(
            *id,
            args.try_map_refs(|_, arg| normalize_type(facts, arg))?,
            subs.try_map_refs(|_, sub| normalize_derivation(facts, sub))?,
        )),
        Derivation::Super(inner, index) => {
            let inner = normalize_derivation(facts, inner)?;
            project_super(facts, inner, *index)
        }
    }
}

/// `Super(inner, index)` for a normalized `inner`, normalized.
fn project_super<G: Clone, F: Facts>(
    facts: &F,
    inner: Derivation<G>,
    index: SuperId,
) -> Result<Derivation<G>, F::Error> {
    match inner {
        Derivation::Impl(id, args, subs) => {
            let stored = facts.impl_supers(id)?;
            let subst = Subst {
                types: &args,
                givens: &|given: &TraitConstrId| subs[*given].clone(),
            };
            // The stored derivation is normalized, but the givens substituted into it may be
            // impl derivations under projections.
            normalize_derivation(facts, &subst.derivation(&stored[index]))
        }
        inner => Ok(Derivation::Super(Box::new(inner), index)),
    }
}

pub fn normalize_type<G: Clone, F: Facts>(
    facts: &F,
    type_: &Type<Derivation<G>>,
) -> Result<Type<Derivation<G>>, F::Error> {
    match type_ {
        Type::App(head, args) => Ok(Type::App(
            *head,
            args.iter()
                .map(|arg| normalize_type(facts, arg))
                .collect::<Result<_, _>>()?,
        )),
        Type::Constrained(id, args, evidence) => Ok(Type::Constrained(
            *id,
            args.iter()
                .map(|arg| normalize_type(facts, arg))
                .collect::<Result<_, _>>()?,
            evidence.try_map_refs(|_, deriv| normalize_derivation(facts, deriv))?,
        )),
        Type::Tuple(items) => Ok(Type::Tuple(
            items
                .iter()
                .map(|item| normalize_type(facts, item))
                .collect::<Result<_, _>>()?,
        )),
        Type::Func(purity, arg, ret) => Ok(Type::Func(
            *purity,
            Box::new(normalize_type(facts, arg)?),
            Box::new(normalize_type(facts, ret)?),
        )),
    }
}

pub fn normalize_trait_app<G: Clone, F: Facts>(
    facts: &F,
    app: &TraitApp<Derivation<G>>,
) -> Result<TraitApp<Derivation<G>>, F::Error> {
    Ok(TraitApp {
        trait_: app.trait_,
        args: app
            .args
            .iter()
            .map(|arg| normalize_type(facts, arg))
            .collect::<Result<_, _>>()?,
    })
}

/// What matching an impl head against a goal determines: the impl's parameters, and whichever of
/// its givens occur in the head.
struct Bindings<G> {
    types: IdVec<TypeParamId, Option<Type<Derivation<G>>>>,
    givens: IdVec<TraitConstrId, Option<Derivation<G>>>,
}

fn bind_type<G: Eq>(
    param: TypeParamId,
    type_: Type<Derivation<G>>,
    bindings: &mut Bindings<G>,
) -> bool {
    match &bindings.types[param] {
        Some(existing) => *existing == type_,
        None => {
            bindings.types[param] = Some(type_);
            true
        }
    }
}

fn bind_given<G: Eq>(
    given: TraitConstrId,
    deriv: Derivation<G>,
    bindings: &mut Bindings<G>,
) -> bool {
    match &bindings.givens[given] {
        Some(existing) => *existing == deriv,
        None => {
            bindings.givens[given] = Some(deriv);
            true
        }
    }
}

/// Matches a pattern over an impl's parameters and givens against a target.  Type parameters of
/// the target are rigid: they only ever match a bare pattern parameter.
fn match_type<G: Clone + Eq, F: Facts>(
    facts: &F,
    pattern: &elab::Type,
    target: &Type<Derivation<G>>,
    bindings: &mut Bindings<G>,
) -> bool {
    match (pattern, target) {
        // A pattern parameter, possibly applied to further patterns, absorbs the corresponding
        // prefix of the target application: `f a` against `Result Int Bool` binds `f` to
        // `Result Int` and `a` to `Bool`.
        (Type::App(TypeHead::Var(param), pattern_args), Type::App(head, args)) => {
            if args.len() < pattern_args.len() {
                return false;
            }
            let split = args.len() - pattern_args.len();
            for (pattern_arg, arg) in pattern_args.iter().zip(&args[split..]) {
                if !match_type(facts, pattern_arg, arg, bindings) {
                    return false;
                }
            }
            bind_type(*param, Type::App(*head, args[..split].to_vec()), bindings)
        }

        // A constrained application splits the same way, as long as what is left is applied to
        // the parameters its constraints mention, so that it keeps carrying its evidence.
        (Type::App(TypeHead::Var(param), pattern_args), Type::Constrained(id, args, evidence)) => {
            if args.len() < pattern_args.len() {
                return false;
            }
            let split = args.len() - pattern_args.len();
            if split < facts.constrained_prefix(*id).to_value() {
                return false;
            }
            for (pattern_arg, arg) in pattern_args.iter().zip(&args[split..]) {
                if !match_type(facts, pattern_arg, arg, bindings) {
                    return false;
                }
            }
            bind_type(
                *param,
                Type::Constrained(*id, args[..split].to_vec(), evidence.clone()),
                bindings,
            )
        }

        (Type::App(TypeHead::Var(param), pattern_args), _) => {
            pattern_args.is_empty() && bind_type(*param, target.clone(), bindings)
        }

        (
            Type::App(TypeHead::Ctor(pattern_id), pattern_args),
            Type::App(TypeHead::Ctor(id), args),
        ) => {
            pattern_id == id
                && pattern_args.len() == args.len()
                && pattern_args
                    .iter()
                    .zip(args)
                    .all(|(pattern_arg, arg)| match_type(facts, pattern_arg, arg, bindings))
        }

        (
            Type::Constrained(pattern_id, pattern_args, pattern_evidence),
            Type::Constrained(id, args, evidence),
        ) => {
            pattern_id == id
                && pattern_args.len() == args.len()
                && pattern_args
                    .iter()
                    .zip(args)
                    .all(|(pattern_arg, arg)| match_type(facts, pattern_arg, arg, bindings))
                && pattern_evidence
                    .values()
                    .zip(evidence.values())
                    .all(|(pattern_deriv, deriv)| {
                        match_derivation(facts, pattern_deriv, deriv, bindings)
                    })
        }

        (Type::Tuple(pattern_items), Type::Tuple(items)) => {
            pattern_items.len() == items.len()
                && pattern_items
                    .iter()
                    .zip(items)
                    .all(|(pattern_item, item)| match_type(facts, pattern_item, item, bindings))
        }

        (Type::Func(pattern_purity, pattern_arg, pattern_ret), Type::Func(purity, arg, ret)) => {
            pattern_purity == purity
                && match_type(facts, pattern_arg, arg, bindings)
                && match_type(facts, pattern_ret, ret, bindings)
        }

        _ => false,
    }
}

/// Matches evidence in an impl head against the corresponding evidence in the goal.  A
/// given of the impl takes whatever the goal supplies; anything more specific has to agree.
fn match_derivation<G: Clone + Eq, F: Facts>(
    facts: &F,
    pattern: &elab::Derivation,
    target: &Derivation<G>,
    bindings: &mut Bindings<G>,
) -> bool {
    match (pattern, target) {
        (Derivation::Given(given), _) => bind_given(*given, target.clone(), bindings),

        (
            Derivation::Impl(pattern_id, pattern_args, pattern_subs),
            Derivation::Impl(id, args, subs),
        ) => {
            pattern_id == id
                && pattern_args
                    .values()
                    .zip(args.values())
                    .all(|(pattern_arg, arg)| match_type(facts, pattern_arg, arg, bindings))
                && pattern_subs
                    .values()
                    .zip(subs.values())
                    .all(|(pattern_sub, sub)| match_derivation(facts, pattern_sub, sub, bindings))
        }

        (Derivation::Super(pattern_inner, pattern_index), Derivation::Super(inner, index)) => {
            pattern_index == index && match_derivation(facts, pattern_inner, inner, bindings)
        }

        _ => false,
    }
}

fn match_head<G: Clone + Eq, F: Facts>(
    facts: &F,
    impl_facts: &ImplFacts,
    goal_args: &[Type<Derivation<G>>],
) -> Option<Bindings<G>> {
    debug_assert_eq!(impl_facts.head.len(), goal_args.len());
    let mut bindings = Bindings {
        types: IdVec::from_count_with(impl_facts.num_params, |_| None),
        givens: impl_facts.trait_constrs.map_refs(|_, _| None),
    };
    for (pattern, target) in impl_facts.head.iter().zip(goal_args) {
        if !match_type(facts, pattern, target, &mut bindings) {
            return None;
        }
    }
    Some(bindings)
}

/// The givens an impl constraint's evidence refers to, which have to be resolved before the
/// constraint can be instantiated.
pub fn add_referenced_givens(app: &elab::TraitApp, givens: &mut BTreeSet<TraitConstrId>) {
    fn add_type(type_: &elab::Type, givens: &mut BTreeSet<TraitConstrId>) {
        match type_ {
            Type::App(_, args) => args.iter().for_each(|arg| add_type(arg, givens)),
            Type::Constrained(_, args, evidence) => {
                args.iter().for_each(|arg| add_type(arg, givens));
                evidence.values().for_each(|deriv| add_deriv(deriv, givens));
            }
            Type::Tuple(items) => items.iter().for_each(|item| add_type(item, givens)),
            Type::Func(_, arg, ret) => {
                add_type(arg, givens);
                add_type(ret, givens);
            }
        }
    }
    fn add_deriv(deriv: &elab::Derivation, givens: &mut BTreeSet<TraitConstrId>) {
        match deriv {
            Derivation::Given(given) => {
                givens.insert(*given);
            }
            Derivation::Impl(_, args, subs) => {
                args.values().for_each(|arg| add_type(arg, givens));
                subs.values().for_each(|sub| add_deriv(sub, givens));
            }
            Derivation::Super(inner, _) => add_deriv(inner, givens),
        }
    }
    app.args.iter().for_each(|arg| add_type(arg, givens));
}

pub struct Solver<'a, G, F: Facts> {
    pub facts: &'a F,
    pub scope: &'a BTreeSet<ImplId>,
    /// Closed under superclasses; see `closed_givens`.
    pub givens: &'a [(TraitApp<Derivation<G>>, Derivation<G>)],
}

impl<'a, G: Clone + Eq + Ord, F: Facts> Solver<'a, G, F> {
    fn matching_impls(
        &self,
        goal: &TraitApp<Derivation<G>>,
        candidates: impl Iterator<Item = ImplId>,
    ) -> Result<Vec<(ImplId, ImplFacts, Bindings<G>)>, F::Error> {
        let mut result = Vec::new();
        for id in candidates {
            let facts = self.facts.impl_facts(id)?;
            if facts.trait_ != goal.trait_ {
                continue;
            }
            if let Some(bindings) = match_head(self.facts, &facts, &goal.args) {
                result.push((id, facts, bindings));
            }
        }
        Ok(result)
    }

    /// A derivation of `goal`, which must be normalized, from the givens and the impls in scope.
    /// `chain` is the goals whose solution required this one, for error messages.
    pub fn solve(
        &self,
        goal: &TraitApp<Derivation<G>>,
        chain: &mut Vec<TraitApp<Derivation<G>>>,
    ) -> Result<Derivation<G>, SolveError<G, F::Error>> {
        if let Some((_, deriv)) = self.givens.iter().find(|(constr, _)| constr == goal) {
            return Ok(deriv.clone());
        }

        let mut candidates = self.matching_impls(goal, self.scope.iter().copied())?;

        match candidates.len() {
            0 => {
                let elsewhere = self
                    .facts
                    .all_impls()
                    .into_iter()
                    .filter(|id| !self.scope.contains(id));
                let importable = self
                    .matching_impls(goal, elsewhere)?
                    .into_iter()
                    .map(|(id, _, _)| id)
                    .collect();
                // A builtin impl is out of scope only where an impl of the same name covers it up.
                let covered_up = BuiltinImpl::all()
                    .map(ImplId::Builtin)
                    .filter(|id| !self.scope.contains(id));
                let covered = self
                    .matching_impls(goal, covered_up)?
                    .into_iter()
                    .map(|(id, _, _)| id)
                    .collect();
                Err(SolveError::NoImpl {
                    goal: goal.clone(),
                    chain: chain.clone(),
                    importable,
                    covered,
                })
            }

            1 => {
                let (id, facts, bindings) = candidates.pop().unwrap();
                chain.push(goal.clone());
                let result = self.discharge(id, &facts, bindings, chain);
                chain.pop();
                result
            }

            _ => Err(SolveError::Ambiguous {
                goal: goal.clone(),
                candidates: candidates.into_iter().map(|(id, _, _)| id).collect(),
            }),
        }
    }

    /// The derivation by a matched impl: its constraints not determined by the head are solved,
    /// each after the givens its evidence refers to.
    fn discharge(
        &self,
        id: ImplId,
        facts: &ImplFacts,
        bindings: Bindings<G>,
        chain: &mut Vec<TraitApp<Derivation<G>>>,
    ) -> Result<Derivation<G>, SolveError<G, F::Error>> {
        // Every parameter of an impl occurs in its head (the Paterson conditions forbid a
        // parameter occurring only in a constraint).
        let types = bindings
            .types
            .map(|_, type_| type_.expect("every impl parameter occurs in its head"));
        let mut subs = bindings.givens;
        let mut in_progress = BTreeSet::new();
        for (given, _) in &facts.trait_constrs {
            self.impl_given(id, facts, &types, &mut subs, &mut in_progress, given, chain)?;
        }
        Ok(Derivation::Impl(
            id,
            types,
            subs.map(|_, sub| sub.expect("every constraint of the impl was discharged")),
        ))
    }

    fn impl_given(
        &self,
        id: ImplId,
        facts: &ImplFacts,
        types: &IdVec<TypeParamId, Type<Derivation<G>>>,
        subs: &mut IdVec<TraitConstrId, Option<Derivation<G>>>,
        in_progress: &mut BTreeSet<TraitConstrId>,
        given: TraitConstrId,
        chain: &mut Vec<TraitApp<Derivation<G>>>,
    ) -> Result<(), SolveError<G, F::Error>> {
        if subs[given].is_some() {
            return Ok(());
        }
        if !in_progress.insert(given) {
            return Err(SolveError::CyclicConstrs { impl_: id });
        }

        let constr = &facts.trait_constrs[given];
        let mut referenced = BTreeSet::new();
        add_referenced_givens(constr, &mut referenced);
        for other in referenced {
            self.impl_given(id, facts, types, subs, in_progress, other, chain)?;
        }

        let goal = {
            let subst = Subst {
                types,
                givens: &|other: &TraitConstrId| {
                    subs[*other]
                        .clone()
                        .expect("referenced givens were resolved first")
                },
            };
            normalize_trait_app(self.facts, &subst.trait_app(constr))?
        };
        let deriv = self.solve(&goal, chain)?;
        subs[given] = Some(deriv);
        Ok(())
    }
}
