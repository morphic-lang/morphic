use crate::graph;
use crate::util::id_vec::IdVec;
use std::collections::BTreeSet;

id_type!(pub SolverVarId);

#[derive(Clone, Debug)]
pub struct VarConstraints<Requirement> {
    pub equalities: BTreeSet<SolverVarId>,
    pub requirements: BTreeSet<Requirement>,
}

#[derive(Clone, Debug)]
pub struct ConstraintGraph<Requirement> {
    // Number of variables is implicit in the length of the vector
    pub var_constraints: IdVec<SolverVarId, VarConstraints<Requirement>>,
}

impl<Requirement: Ord> ConstraintGraph<Requirement> {
    pub fn new() -> Self {
        ConstraintGraph {
            var_constraints: IdVec::new(),
        }
    }

    pub fn new_var(&mut self) -> SolverVarId {
        self.var_constraints.push(VarConstraints {
            equalities: BTreeSet::new(),
            requirements: BTreeSet::new(),
        })
    }

    pub fn equate(&mut self, fst: SolverVarId, snd: SolverVarId) {
        self.var_constraints[fst].equalities.insert(snd);
        self.var_constraints[snd].equalities.insert(fst);
    }

    pub fn require(&mut self, var: SolverVarId, req: Requirement) {
        self.var_constraints[var].requirements.insert(req);
    }

    pub fn clear_requirements(&mut self) {
        for (_, c) in self.var_constraints.iter_mut() {
            c.requirements.clear();
        }
    }

    pub fn find_equiv_classes(&self) -> EquivClasses {
        let equality_graph = graph::Undirected::from_directed_unchecked(graph::Graph {
            edges_out: self
                .var_constraints
                .map(|_, var_constraints| var_constraints.equalities.iter().cloned().collect()),
        });

        let components = graph::connected_components(&equality_graph);

        let mut reverse_mapping: IdVec<EquivClass, _> = IdVec::new();
        let equiv_classes = {
            let mut equiv_classes = IdVec::from_items(vec![None; self.var_constraints.len()]);

            for (equiv_class_idx, solver_vars) in components.iter().enumerate() {
                {
                    let pushed_id = reverse_mapping.push(solver_vars[0]);
                    debug_assert_eq!(pushed_id.0, equiv_class_idx)
                }

                for &solver_var in solver_vars {
                    debug_assert!(equiv_classes[solver_var].is_none());
                    equiv_classes[solver_var] = Some(EquivClass(equiv_class_idx));
                }
            }

            equiv_classes.into_mapped(|_, vars| vars.unwrap())
        };

        EquivClasses {
            classes: equiv_classes,
            reverse: reverse_mapping,
        }
    }
}

id_type!(pub EquivClass);

#[derive(Clone, Debug)]
pub struct EquivClasses {
    classes: IdVec<SolverVarId, EquivClass>,
    reverse: IdVec<EquivClass, SolverVarId>,
}

impl EquivClasses {
    pub fn class(&self, var: SolverVarId) -> EquivClass {
        self.classes[var]
    }

    pub fn count(&self) -> usize {
        self.classes.len()
    }

    pub fn one_repr_var_of(&self, class: EquivClass) -> SolverVarId {
        self.reverse[class]
    }
}
