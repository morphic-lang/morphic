//! *Anime guy with butterfly meme* "Is this Horn SAT?"
//!
//! (Answer: No.  We don't support conjunctions in premises, only implications between pairs of
//! variables.)

use im_rc::OrdSet;
use std::collections::BTreeMap;

use crate::util::graph::{strongly_connected, Graph};
use crate::util::id_vec::IdVec;

id_type!(pub SolverVarId);

id_type!(pub ExternalVarId);

/// Types for which you can take the infimum (i.e., minimum) of two elements, and which have a
/// greatest element.
///
/// TODO: `Infimum` doesn't seem like a great name for this trait.  Can we think of a better one?
/// Formally, this is a "bounded meet semilattice," but that may confuse more than it clarifies.
pub trait Infimum {
    /// Replace `self` with `min(self, other)`.
    fn min_mut(&mut self, other: &Self);

    /// The greatest element of the semilattice.
    fn greatest() -> Self;
}

#[derive(Clone, Debug)]
struct VarConstraints<T> {
    /// If a variable `v` has a `VarConstraints` struct whose `lte_vars` vec contains a variable
    /// `u`, that encodes the constraint `v <= u`.
    lte_vars: Vec<SolverVarId>,

    /// If a variable `v` has a `VarConstraints` struct whose `lte_const` field is a constant value
    /// `c`, that encodes the constraint `v <= c`.
    lte_const: T,
}

#[derive(Clone, Debug)]
pub struct ConstraintGraph<T> {
    vars: IdVec<SolverVarId, VarConstraints<T>>,
}

#[derive(Clone, Debug)]
pub struct UpperBound<T> {
    /// Iff a variable `v` has an `UpperBound` struct whose `lte_vars` set contains a variable `u`,
    /// then `v <= u`.
    pub lte_vars: OrdSet<ExternalVarId>,

    /// If a variable `v` has an `UpperBound` struct whose `lte_const` contains a constant value
    /// `c`, then `v <= c`.
    pub lte_const: T,
}

impl<T: Ord + Infimum + Clone> ConstraintGraph<T> {
    pub fn new() -> Self {
        ConstraintGraph { vars: IdVec::new() }
    }

    pub fn new_var(&mut self) -> SolverVarId {
        self.vars.push(VarConstraints {
            lte_vars: Vec::new(),
            lte_const: T::greatest(),
        })
    }

    /// Add the constraint `var1 <= var2`
    pub fn require_lte(&mut self, var1: SolverVarId, var2: SolverVarId) {
        // Small optimization (not necessary for correctness): don't add reflexive `<=` constraints.
        // This isn't very important, but it's so easy that it feels silly not to do it.
        if var1 != var2 {
            self.vars[var1].lte_vars.push(var2);
        }
    }

    /// Add the constraint `var1 = var2`
    pub fn require_eq(&mut self, var1: SolverVarId, var2: SolverVarId) {
        self.require_lte(var1, var2);
        self.require_lte(var2, var1);
    }

    /// Add the constraint `var <= value`
    pub fn require_lte_const(&mut self, var: SolverVarId, value: &T) {
        self.vars[var].lte_const.min_mut(&value);
    }

    // TODO: This does not "de-duplicate" identical external variables, even if they are related by
    // an equality constraint.  This could be a (probably minor) compiler performance issue.  Should
    // we change this?
    pub fn solve(
        &self,
        external: IdVec<ExternalVarId, SolverVarId>,
    ) -> IdVec<SolverVarId, UpperBound<T>> {
        // This is a "partial map"; it is keyed by only a subset of all the `SolverVarId` indices in
        // this graph, because `external` need not contain all `SolverVarId` indices as values.
        let internal_to_external = external
            .iter()
            .map(|(external, &var)| (var, external))
            .collect::<BTreeMap<_, _>>();

        let mut upper_bounds = self.vars.map(|_, _| UpperBound {
            lte_vars: OrdSet::new(),
            lte_const: T::greatest(),
        });

        // We iterate through all variables in topological order of greatest to least

        let sccs = strongly_connected(&Graph {
            edges_out: self.vars.map(|_, constr| constr.lte_vars.clone()),
        });

        for scc in sccs {
            let mut scc_lte_vars = OrdSet::new();
            let mut scc_lte_const = T::greatest();

            for &var in &scc {
                for gte_var in &self.vars[var].lte_vars {
                    // We have `var <= gte_var`.
                    let gte_var_bound = &upper_bounds[gte_var];
                    scc_lte_vars = scc_lte_vars.union(gte_var_bound.lte_vars.clone());
                    scc_lte_const.min_mut(&gte_var_bound.lte_const);
                }

                if let Some(external) = internal_to_external.get(&var) {
                    scc_lte_vars.insert(*external);
                }

                scc_lte_const.min_mut(&self.vars[var].lte_const);
            }

            for &var in &scc {
                upper_bounds[var] = UpperBound {
                    lte_vars: scc_lte_vars.clone(),
                    lte_const: scc_lte_const.clone(),
                }
            }
        }

        upper_bounds
    }

    pub fn instantiate_subgraph(
        &mut self,
        subgraph: &IdVec<ExternalVarId, UpperBound<T>>,
    ) -> IdVec<ExternalVarId, SolverVarId> {
        let vars = subgraph.map(|_, _| self.new_var());

        for (external, upper_bound) in subgraph {
            for other_external in &upper_bound.lte_vars {
                self.require_lte(vars[external], vars[other_external]);
            }
            self.require_lte_const(vars[external], &upper_bound.lte_const);
        }

        vars
    }
}
