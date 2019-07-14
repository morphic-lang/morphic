use std::collections::{BTreeMap, BTreeSet};

use crate::data::mono_ast as mono;
use crate::data::resolved_ast as res;
use crate::graph::{self, Graph};

fn add_expr_deps(expr: &mono::Expr, deps: &mut BTreeSet<mono::CustomGlobalId>) {
    match expr {
        mono::Expr::ArithOp(_) => {}

        mono::Expr::ArrayOp(_, _) => {}

        mono::Expr::IOOp(_) => {}

        mono::Expr::Ctor(_, _) => {}

        mono::Expr::Global(other) => {
            deps.insert(*other);
        }

        mono::Expr::Local(_) => {}

        mono::Expr::Tuple(items) => {
            for item in items {
                add_expr_deps(item, deps);
            }
        }

        mono::Expr::Lam(_purity, _arg, _ret, _arg_pat, body) => {
            add_expr_deps(body, deps);
        }

        mono::Expr::App(_purity, func, arg) => {
            add_expr_deps(func, deps);
            add_expr_deps(arg, deps);
        }

        mono::Expr::Match(discrim, cases, _result_type) => {
            add_expr_deps(discrim, deps);

            for (_, body) in cases {
                add_expr_deps(body, deps);
            }
        }

        mono::Expr::Let(_lhs, rhs, body) => {
            add_expr_deps(rhs, deps);
            add_expr_deps(body, deps);
        }

        mono::Expr::ArrayLit(_item_type, items) => {
            for item in items {
                add_expr_deps(item, deps);
            }
        }

        mono::Expr::BoolLit(_) => {}

        mono::Expr::ByteLit(_) => {}

        mono::Expr::IntLit(_) => {}

        mono::Expr::FloatLit(_) => {}
    }
}

fn global_sccs(program: &mono::Program) -> Vec<Vec<mono::CustomGlobalId>> {
    let dep_graph = Graph {
        edges_out: program
            .vals
            .iter()
            .map(|(_def_id, def)| {
                let mut deps = BTreeSet::new();
                add_expr_deps(&def.body, &mut deps);
                deps.into_iter()
                    .map(|mono::CustomGlobalId(id)| graph::NodeId(id))
                    .collect()
            })
            .collect(),
    };

    let sccs = graph::strongly_connected(&dep_graph);

    sccs.into_iter()
        .map(|scc| {
            scc.into_iter()
                .map(|graph::NodeId(id)| mono::CustomGlobalId(id))
                .collect()
        })
        .collect()
}

fn rebind_references(
    mapping: &BTreeMap<mono::CustomGlobalId, mono::CustomGlobalId>,
    expr: &mut mono::Expr,
) {
    match expr {
        mono::Expr::ArithOp(_) => {}

        mono::Expr::ArrayOp(_, _) => {}

        mono::Expr::IOOp(_) => {}

        mono::Expr::Ctor(_, _) => {}

        mono::Expr::Global(other) => {
            if let Some(&new) = mapping.get(other) {
                *other = new;
            }
        }

        mono::Expr::Local(_) => {}

        mono::Expr::Tuple(items) => {
            for item in items {
                rebind_references(mapping, item);
            }
        }

        mono::Expr::Lam(_purity, _arg, _ret, _arg_pat, body) => {
            rebind_references(mapping, body);
        }

        mono::Expr::App(_purity, func, arg) => {
            rebind_references(mapping, func);
            rebind_references(mapping, arg);
        }

        mono::Expr::Match(discrim, cases, _result_type) => {
            rebind_references(mapping, discrim);
            for (_, body) in cases {
                rebind_references(mapping, body);
            }
        }

        mono::Expr::Let(_lhs, rhs, body) => {
            rebind_references(mapping, rhs);
            rebind_references(mapping, body);
        }

        mono::Expr::ArrayLit(_item_type, items) => {
            for item in items {
                rebind_references(mapping, item);
            }
        }

        mono::Expr::BoolLit(_) => {}

        mono::Expr::ByteLit(_) => {}

        mono::Expr::IntLit(_) => {}

        mono::Expr::FloatLit(_) => {}
    }
}

pub fn shield_functions(mut program: mono::Program) -> mono::Program {
    let mut mapping = BTreeMap::new();

    for scc in global_sccs(&program) {
        for id in &scc {
            rebind_references(&mapping, &mut program.vals[id].body);
        }

        for &id in &scc {
            let val_def = &program.vals[id];

            if let mono::Type::Func(purity, arg, ret) = &val_def.type_ {
                let wrapper_def = mono::ValDef {
                    type_: val_def.type_.clone(),
                    body: mono::Expr::Lam(
                        *purity,
                        (**arg).clone(),
                        (**ret).clone(),
                        mono::Pattern::Var((**arg).clone()),
                        Box::new(mono::Expr::App(
                            *purity,
                            Box::new(mono::Expr::Global(id)),
                            Box::new(mono::Expr::Local(res::LocalId(0))),
                        )),
                    ),
                };

                let wrapper_data = mono::ValData {
                    is_wrapper: true,
                    ..program.val_data[id].clone()
                };

                let wrapper_id = program.vals.push(wrapper_def);
                let wrapper_data_id = program.val_data.push(wrapper_data);

                debug_assert_eq!(wrapper_id, wrapper_data_id);

                mapping.insert(id, wrapper_id);
            }
        }
    }

    if let Some(&new_main) = mapping.get(&program.main) {
        program.main = new_main;
    }

    program
}
