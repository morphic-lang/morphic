use crate::graph;
use std::collections::BTreeSet;

id_type!(pub SolverVarId);

#[derive(Clone, Debug)]
pub struct VarConstraints<Requirement> {
    pub equalities: BTreeSet<SolverVarId>,
    pub requirements: BTreeSet<Requirement>,
}

#[derive(Clone, Debug)]
pub struct ConstraintGraph<Requirement> {
    // Indexed by SolverVarId
    // Number of variables is implicit in the length of the vector
    pub var_constraints: Vec<VarConstraints<Requirement>>,
}

impl<Requirement: Ord> ConstraintGraph<Requirement> {
    pub fn new() -> Self {
        ConstraintGraph {
            var_constraints: Vec::new(),
        }
    }

    pub fn new_var(&mut self) -> SolverVarId {
        let id = SolverVarId(self.var_constraints.len());
        self.var_constraints.push(VarConstraints {
            equalities: BTreeSet::new(),
            requirements: BTreeSet::new(),
        });
        id
    }

    pub fn equate(&mut self, fst: SolverVarId, snd: SolverVarId) {
        self.var_constraints[fst.0].equalities.insert(snd);
        self.var_constraints[snd.0].equalities.insert(fst);
    }

    pub fn require(&mut self, var: SolverVarId, req: Requirement) {
        self.var_constraints[var.0].requirements.insert(req);
    }

    pub fn clear_requirements(&mut self) {
        for c in self.var_constraints.iter_mut() {
            c.requirements.clear();
        }
    }

    pub fn find_equiv_classes(&self) -> EquivClasses {
        let equality_graph = graph::Undirected::from_directed_unchecked(graph::Graph {
            edges_out: self
                .var_constraints
                .iter()
                .map(|var_constraints| {
                    var_constraints
                        .equalities
                        .iter()
                        .map(|&SolverVarId(other)| graph::NodeId(other))
                        .collect()
                })
                .collect(),
        });

        let components = graph::connected_components(&equality_graph);

        let mut reverse_mapping = Vec::new();
        let equiv_classes = {
            let mut equiv_classes = vec![None; self.var_constraints.len()];

            for (equiv_class, solver_vars) in components.iter().enumerate() {
                reverse_mapping.push(SolverVarId(solver_vars[0].0));
                for &graph::NodeId(solver_var) in solver_vars {
                    debug_assert!(equiv_classes[solver_var].is_none());
                    equiv_classes[solver_var] = Some(EquivClass(equiv_class));
                }
            }

            equiv_classes.into_iter().map(Option::unwrap).collect()
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
    classes: Vec<EquivClass>,  // indexed by SolverVarId
    reverse: Vec<SolverVarId>, // indexed by EquivClass
}

impl EquivClasses {
    pub fn class(&self, var: SolverVarId) -> EquivClass {
        self.classes[var.0]
    }

    pub fn count(&self) -> usize {
        self.classes.len()
    }

    pub fn one_repr_var_of(&self, class: EquivClass) -> SolverVarId {
        self.reverse[class.0]
    }
}
