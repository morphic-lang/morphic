//! *Anime guy with butterfly meme* "Is this Horn SAT?"
//!
//! (Answer: No. We don't support conjunctions in premises, only implications between pairs of
//! variables.)

use id_collections::{id_type, Count, Id, IdVec};
use id_graph_sccs::{find_components, Sccs};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Types for which you can take the join (i.e. least upper bound) of two elements, and which have a
/// least element.
pub trait BoundedSemilattice {
    /// Replace `self` with the join of `self` and `other`.
    fn join_mut(&mut self, other: &Self);

    /// The least element of the semilattice.
    fn least() -> Self;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VarConstrs<Var, T> {
    /// If a variable `v` has a `VarConstrs` struct whose `lb_vars` vec contains a variable `u`,
    /// that encodes the constraint `u <= v`.
    pub lb_vars: BTreeSet<Var>,

    /// If a variable `v` has a `VarConstrs` struct whose `lb_const` field is a constant value `c`,
    /// that encodes the constraint `c <= v`.
    pub lb_const: T,
}

#[derive(Clone, Debug)]
pub struct ConstrGraph<Var: Id, T> {
    vars: IdVec<Var, VarConstrs<Var, T>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LowerBound<Var, T> {
    /// If a variable `v` has a `LowerBound` struct whose `lb_vars` set contains a variable `u`,
    /// then `u <= v`.
    pub lb_vars: BTreeSet<Var>,

    /// If a variable `v` has a `LowerBound` struct whose `lb_const` contains a constant value `c`,
    /// then `c <= v`.
    pub lb_const: T,
}

impl<Var: Id, T: Clone + BoundedSemilattice> LowerBound<Var, T> {
    pub fn instantiate(&self, at: &IdVec<Var, T>) -> T {
        let mut result = self.lb_const.clone();
        for var in &self.lb_vars {
            result.join_mut(&at[var]);
        }
        result
    }
}

#[derive(Clone, Debug)]
pub struct Solution<SolverVar: Id, ExternalVar: Id, T> {
    pub num_external: Count<ExternalVar>,
    pub internal_to_external: BTreeMap<SolverVar, ExternalVar>,
    pub lower_bounds: IdVec<SolverVar, LowerBound<ExternalVar, T>>,
}

impl<SolverVar: Id, T> ConstrGraph<SolverVar, T>
where
    T: Clone + Ord + BoundedSemilattice,
{
    pub fn new() -> Self {
        ConstrGraph { vars: IdVec::new() }
    }

    pub fn inner(&self) -> &IdVec<SolverVar, VarConstrs<SolverVar, T>> {
        &self.vars
    }

    pub fn num_vars(&self) -> usize {
        self.vars.len()
    }

    pub fn num_constrs(&self) -> usize {
        self.vars.values().map(|v| v.lb_vars.len()).sum()
    }

    pub fn fresh_var(&mut self) -> SolverVar {
        self.vars.push(VarConstrs {
            lb_vars: BTreeSet::new(),
            lb_const: T::least(),
        })
    }

    /// Add the constraint `var1 <= var2`.
    pub fn require_le(&mut self, var1: SolverVar, var2: SolverVar) {
        // Small optimization (not necessary for correctness): don't add reflexive `<=` constraints.
        // This isn't very important, but it's so easy that it feels silly not to do it.
        if var1 != var2 {
            self.vars[var2].lb_vars.insert(var1);
        }
    }

    /// Add the constraint `var1 = var2`.
    pub fn require_eq(&mut self, var1: SolverVar, var2: SolverVar) {
        self.require_le(var1, var2);
        self.require_le(var2, var1);
    }

    /// Add the constraint `value <= var`.
    pub fn require_le_const(&mut self, value: &T, var: SolverVar) {
        self.vars[var].lb_const.join_mut(&value);
    }

    /// Find the least solution to the constraints in this graph, expressed in terms of a fresh set
    /// of *contiguous* "external" variables.
    pub fn solve<ExternalVar: Id>(
        &self,
        sig_vars: &BTreeSet<SolverVar>,
    ) -> Solution<SolverVar, ExternalVar, T> {
        #[id_type]
        struct EquivClass(usize);

        // Interpret `var1 <= var2` as an edge `var2 -> var1` so that iterating over the output of
        // `find_components` yields the SCC for `var1` before the SCC for `var2`.
        let sccs: Sccs<EquivClass, _> =
            find_components(self.vars.count(), |var| &self.vars[var].lb_vars);

        // Create one fresh external variable for each SCC containing a signature variable.
        let mut internal_to_external = BTreeMap::new();
        let mut num_external = Count::new();
        for (_, scc) in &sccs {
            if scc.nodes.iter().any(|&var| sig_vars.contains(&var)) {
                let fresh_external = num_external.inc();
                for &var in scc.nodes {
                    internal_to_external.insert(var, fresh_external);
                }
            }
        }

        // These are not just dummy values; they must be trivial bounds. When a variable depends on
        // a variable from the same SCC, we end up accessing this bound as we have yet to update it.
        let mut lower_bounds = IdVec::from_count_with(self.vars.count(), |_| LowerBound {
            lb_vars: BTreeSet::new(),
            lb_const: T::least(),
        });

        for (_, scc) in &sccs {
            let mut scc_lb_vars = BTreeSet::new();
            let mut scc_lb_const = T::least();

            // Solve for the lower bound of the SCC.
            for &var in scc.nodes {
                for lb_var in &self.vars[var].lb_vars {
                    let lb = &lower_bounds[lb_var];
                    scc_lb_vars.extend(&lb.lb_vars);
                    scc_lb_const.join_mut(&lb.lb_const);
                }

                if sig_vars.contains(&var) {
                    scc_lb_vars.insert(internal_to_external[&var]);
                }

                scc_lb_const.join_mut(&self.vars[var].lb_const);
            }

            // Assign the lower bound to all variables in the SCC.
            for &var in scc.nodes {
                lower_bounds[var] = LowerBound {
                    lb_vars: scc_lb_vars.clone(),
                    lb_const: scc_lb_const.clone(),
                };
            }
        }

        Solution {
            num_external,
            internal_to_external,
            lower_bounds,
        }
    }

    /// Given a set of "external" variables with associated constraints, introduce a corresponding
    /// set of fresh variables to the constraint graph.
    pub fn instantiate_subgraph<ExternalVar: Id>(
        &mut self,
        subgraph: &IdVec<ExternalVar, LowerBound<ExternalVar, T>>,
    ) -> IdVec<ExternalVar, SolverVar> {
        let vars = subgraph.map_refs(|_, _| self.fresh_var());

        for (rhs, lb) in subgraph {
            for lhs in &lb.lb_vars {
                self.require_le(vars[lhs], vars[rhs]);
            }
            self.require_le_const(&lb.lb_const, vars[rhs]);
        }

        vars
    }

    pub fn requires(&self, var1: SolverVar, var2: SolverVar) -> bool {
        self.vars[var2].lb_vars.contains(&var1)
    }

    pub fn lower_bounds(&self, var: SolverVar) -> &VarConstrs<SolverVar, T> {
        &self.vars[var]
    }

    pub fn saturate(&mut self) {
        loop {
            let mut new = Vec::new();
            for (rhs1, lb1) in self.vars.iter() {
                for &lhs1 in &lb1.lb_vars {
                    // lhs1 <= rhs1
                    for (rhs2, lb2) in self.vars.iter() {
                        for &lhs2 in &lb2.lb_vars {
                            if rhs1 == lhs2 {
                                // rhs1 = lhs2 <= rhs2`
                                new.push((lhs1, rhs2));
                            }
                        }
                    }
                }
            }

            let mut changed = false;
            for (lhs, rhs) in new {
                let lb = &mut self.vars[rhs].lb_vars;
                if !lb.contains(&lhs) {
                    lb.insert(lhs);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }
    }
}

impl<Var: Id, T: fmt::Display> fmt::Display for VarConstrs<Var, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{ ")?;
        write!(f, "{}, ", self.lb_const)?;
        for lb_var in self.lb_vars.iter() {
            write!(f, "{}, ", lb_var.to_index())?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<Var: Id, T: fmt::Display> fmt::Display for ConstrGraph<Var, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[ ")?;
        for (var, constrs) in self.vars.iter() {
            write!(f, "{} ≤ {}, ", constrs.lb_const, var.to_index())?;
            for lb_var in constrs.lb_vars.iter() {
                write!(f, "{} ≤ {}, ", lb_var.to_index(), var.to_index())?;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}
