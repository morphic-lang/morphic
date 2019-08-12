/// This module implements `fn annot_reprs`, which generates an AST annotated with the
/// solutions for representation variables for every array in the program (a
/// `data::repr_annot_ast`). Note that "repr vars" = "type-variables representing variable
/// representation (shared v. unique)". `mid_ast` defines the AST used at the internal
/// steps in this pipeline.
///
/// The pipeline, wired together in `fn annot_reprs`, is as follows:
///
/// 1. `mod flatten` and `mod parameterize` generate a `mid_ast` from the first order AST.
/// 2. `mod unify` runs Hindley-Milner and annotates each expression with its type.
/// 3. `mod aliasing` computes the internal aliasing graph for every function.
/// 4. `mod constrain` computes sharing constraints on repr vars based on usage patterns.
/// 5. `mod extract` generates solutions for repr vars and emits the `out_ast`.
use crate::data::first_order_ast as in_ast;
use crate::data::repr_annot_ast as out_ast;
use itertools::izip;
use std::rc::Rc;

mod mid_ast;

mod flatten;

mod parameterize;

mod unify;

mod aliasing;

mod constrain;

mod extract;

use crate::annot_aliases::{self, UniqueInfo};
use crate::graph;
use crate::util::constraint_graph::ConstraintGraph;
use std::collections::{BTreeMap, BTreeSet};

pub fn annot_reprs(program: &in_ast::Program, unique_infos: Vec<UniqueInfo>) -> out_ast::Program {
    let typedefs = parameterize::parameterize_typedefs(&program.custom_types);
    let func_graph = annot_aliases::func_dependency_graph(program);

    // Function information used by various passes:
    let mut alias_sigs: Vec<Option<aliasing::Signature>> = vec![None; program.funcs.len()];
    let mut type_sigs: Vec<Option<unify::Signature>> = vec![None; program.funcs.len()];
    let mut constraint_sigs: Vec<Option<constrain::Signature>> = vec![None; program.funcs.len()];

    // Final function bodies for output
    let mut out_func_bodies = vec![None; program.funcs.len()];

    for scc_nodes in graph::strongly_connected(&func_graph) {
        let mut graph = ConstraintGraph::new();
        let scc_funcs = scc_nodes
            .iter()
            .map(|&func_id| {
                (
                    func_id,
                    flatten::flatten_func(&mut graph, &typedefs, &program.funcs[func_id]),
                )
            })
            .collect::<BTreeMap<_, _>>();

        let func_bodies = {
            let context = unify::Context {
                first_order_typedefs: &program.custom_types.items,
                typedefs: &typedefs,
                func_sigs: &type_sigs,
                scc_funcdefs: &scc_funcs,
            };

            scc_funcs
                .iter()
                .map(|(id, func)| (*id, unify::unify_func(&mut graph, context, func)))
                .collect::<BTreeMap<_, _>>()
        };

        // Determine aliasing graph for each function
        let mut scc_alias_sigs = aliasing::initialize_sigs_for_scc(scc_funcs.keys());
        let mut scc_funcinfos = Vec::with_capacity(scc_funcs.len());
        loop {
            let mut new_scc_alias_sigs = aliasing::initialize_sigs_for_scc(scc_funcs.keys());
            scc_funcinfos.clear();
            for &func_id in scc_funcs.keys() {
                let context = aliasing::Context {
                    typedefs: &typedefs,
                    unique_infos: &unique_infos,
                    alias_sigs: &alias_sigs,
                    scc_alias_sigs: &new_scc_alias_sigs,
                };
                let (alias_sig, funcinfo) =
                    aliasing::alias_track_func(context, &func_bodies[&func_id], func_id);
                new_scc_alias_sigs.insert(func_id, alias_sig);
                scc_funcinfos.push(funcinfo);
            }
            if scc_alias_sigs == new_scc_alias_sigs {
                break;
            } else {
                scc_alias_sigs = new_scc_alias_sigs;
            }
        }
        for (func_id, alias_sig) in scc_alias_sigs {
            assert!(alias_sigs[func_id.0].is_none());
            alias_sigs[func_id.0] = Some(alias_sig);
        }

        // Determine representation params of functions and their constraints
        let equiv_classes = graph.find_equiv_classes();
        let mut scc_constraint_sigs =
            constrain::initialize_sigs_for_scc(&equiv_classes, &scc_funcs);
        loop {
            let mut new_scc_sigs = BTreeMap::new();
            for func in &scc_funcinfos {
                let sig = constrain::constrain_func(
                    constrain::Context {
                        constraint_sigs: &constraint_sigs,
                        equiv_classes: &equiv_classes,
                        scc_sigs: &scc_constraint_sigs,
                    },
                    &mut graph,
                    func,
                    &func_bodies[&func.id].1,
                );
                new_scc_sigs.insert(func.id, sig);
                graph.clear_requirements();
            }
            if new_scc_sigs == scc_constraint_sigs {
                break;
            }
            scc_constraint_sigs = new_scc_sigs;
        }

        // Extract `unify::Signature`s for this SCC
        let sig_gen = extract::gen_sigs(&equiv_classes, &func_bodies, &mut type_sigs);

        for func in &scc_funcinfos {
            // Compute constraints one more time to extract solutions for internal variables,
            // and assert that we are at a fixed point
            assert_eq!(
                &scc_constraint_sigs[&func.id],
                &constrain::constrain_func(
                    constrain::Context {
                        constraint_sigs: &constraint_sigs,
                        equiv_classes: &equiv_classes,
                        scc_sigs: &scc_constraint_sigs,
                    },
                    &mut graph,
                    func,
                    &func_bodies[&func.id].1,
                )
            );

            // Extract constraints on each equivalence class
            let mut class_constraints = (0..equiv_classes.count())
                .map(|_| BTreeSet::new())
                .collect::<Vec<_>>();
            for (var_id, graph_constraints) in &mut graph.var_constraints {
                // Empty the constraint list in the graph to avoid clone (resetting
                // constraints is necessary for next iteration anyway)
                let mut var_constraints = BTreeSet::new();
                std::mem::swap(&mut graph_constraints.requirements, &mut var_constraints);
                let equiv_class = equiv_classes.class(var_id);
                class_constraints[equiv_class.0].extend(var_constraints);
            }

            let mut extractor =
                extract::SolutionExtractor::from_sig_gen(&sig_gen, class_constraints);

            out_func_bodies[func.id.0] =
                Some(extract::gen_func(&mut extractor, &func_bodies[&func.id]));

            assert!(constraint_sigs[func.id.0].is_none());
            constraint_sigs[func.id.0] =
                Some(constrain::Signature::new(extractor.drain_constraints()));

            graph.clear_requirements();
        }
    }

    let mut out_funcs = Vec::new();
    let out_func_bodies = out_func_bodies.into_iter().map(Option::unwrap);
    assert_eq!(constraint_sigs.len(), unique_infos.len());
    assert_eq!(constraint_sigs.len(), out_func_bodies.len());
    for (constraint_sig, unique_info, alias_sig, (arg_type, body)) in
        izip!(constraint_sigs, unique_infos, alias_sigs, out_func_bodies)
    {
        out_funcs.push(out_ast::FuncDef {
            params: constraint_sig.unwrap().into_params(),
            arg_type: arg_type,
            body: body,
            unique_info: Rc::new(unique_info),
            ret_aliasing: Rc::new(alias_sig.unwrap().into_ret_aliases()),
        })
    }

    out_ast::Program {
        custom_types: typedefs,
        funcs: out_funcs,
        main: program.main,
    }
}
