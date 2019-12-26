use im_rc::OrdMap;
use std::collections::{BTreeMap, BTreeSet};

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as mutation;
use crate::data::purity::Purity;
use crate::data::repr_unified_ast as unif;
use crate::util::graph::{strongly_connected, Graph, Scc};
use crate::util::id_gen::IdGen;
use crate::util::id_vec::IdVec;
use crate::util::local_context::LocalContext;

fn add_type_deps(type_: &anon::Type, deps: &mut BTreeSet<first_ord::CustomTypeId>) {
    match type_ {
        anon::Type::Bool | anon::Type::Num(_) => {}
        anon::Type::Array(item_type) => add_type_deps(item_type, deps),
        anon::Type::HoleArray(item_type) => add_type_deps(item_type, deps),
        anon::Type::Tuple(items) => {
            for item in items {
                add_type_deps(item, deps);
            }
        }
        anon::Type::Variants(variants) => {
            for (_, variant) in variants {
                add_type_deps(variant, deps);
            }
        }
        anon::Type::Custom(custom) => {
            deps.insert(*custom);
        }
    }
}

fn count_params(
    parameterized: &IdVec<first_ord::CustomTypeId, Option<unif::TypeDef>>,
    type_: &anon::Type,
) -> usize {
    match type_ {
        anon::Type::Bool | anon::Type::Num(_) => 0,
        anon::Type::Array(item_type) => 1 + count_params(parameterized, item_type),
        anon::Type::HoleArray(item_type) => 1 + count_params(parameterized, item_type),
        anon::Type::Tuple(items) => items
            .iter()
            .map(|item| count_params(parameterized, item))
            .sum(),
        anon::Type::Variants(variants) => variants
            .iter()
            .map(|(_, variant)| count_params(parameterized, variant))
            .sum(),
        anon::Type::Custom(custom) => match &parameterized[custom] {
            Some(typedef) => typedef.num_params,
            // This is a typedef in the same SCC; the reference to it here contributes no additional
            // parameters to the entire SCC.
            None => 0,
        },
    }
}

fn parameterize(
    parameterized: &IdVec<first_ord::CustomTypeId, Option<unif::TypeDef>>,
    scc_num_params: usize,
    id_gen: &mut IdGen<unif::RepParamId>,
    type_: &anon::Type,
) -> unif::Type<unif::RepParamId> {
    match type_ {
        anon::Type::Bool => unif::Type::Bool,
        anon::Type::Num(num) => unif::Type::Num(*num),

        anon::Type::Array(item_type) => unif::Type::Array(
            id_gen.fresh(),
            Box::new(parameterize(
                parameterized,
                scc_num_params,
                id_gen,
                item_type,
            )),
        ),

        anon::Type::HoleArray(item_type) => unif::Type::HoleArray(
            id_gen.fresh(),
            Box::new(parameterize(
                parameterized,
                scc_num_params,
                id_gen,
                item_type,
            )),
        ),

        anon::Type::Tuple(items) => unif::Type::Tuple(
            items
                .iter()
                .map(|item| parameterize(parameterized, scc_num_params, id_gen, item))
                .collect(),
        ),

        anon::Type::Variants(variants) => unif::Type::Variants(
            variants.map(|_, variant| parameterize(parameterized, scc_num_params, id_gen, variant)),
        ),

        anon::Type::Custom(custom) => match &parameterized[custom] {
            Some(typedef) => unif::Type::Custom(
                *custom,
                IdVec::from_items((0..typedef.num_params).map(|_| id_gen.fresh()).collect()),
            ),

            // This is a typedef in the same SCC, so we need to parameterize it by all the SCC parameters.
            None => unif::Type::Custom(
                *custom,
                IdVec::from_items((0..scc_num_params).map(unif::RepParamId).collect()),
            ),
        },
    }
}

fn parameterize_typedef_scc(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    parameterized: &IdVec<first_ord::CustomTypeId, Option<unif::TypeDef>>,
    scc: &[first_ord::CustomTypeId],
) -> BTreeMap<first_ord::CustomTypeId, unif::TypeDef> {
    let num_params = scc
        .iter()
        .map(|custom| count_params(parameterized, &typedefs[custom]))
        .sum::<usize>();

    let mut id_gen = IdGen::new();

    let to_populate = scc
        .iter()
        .map(|&custom| {
            (
                custom,
                unif::TypeDef {
                    num_params,
                    content: parameterize(
                        parameterized,
                        num_params,
                        &mut id_gen,
                        &typedefs[custom],
                    ),
                },
            )
        })
        .collect();

    debug_assert_eq!(id_gen.count(), num_params);

    to_populate
}

fn parameterize_typedefs(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
) -> IdVec<first_ord::CustomTypeId, unif::TypeDef> {
    let type_deps = Graph {
        edges_out: typedefs.map(|_, content| {
            let mut deps = BTreeSet::new();
            add_type_deps(content, &mut deps);
            deps.into_iter().collect()
        }),
    };

    let sccs = strongly_connected(&type_deps);

    let mut parameterized = IdVec::from_items(vec![None; typedefs.len()]);
    for scc in &sccs {
        let to_populate = parameterize_typedef_scc(typedefs, &parameterized, scc);

        debug_assert_eq!(
            to_populate.keys().collect::<BTreeSet<_>>(),
            scc.iter().collect::<BTreeSet<_>>()
        );

        for (custom, typedef) in to_populate {
            debug_assert!(parameterized[custom].is_none());
            parameterized[custom] = Some(typedef);
        }
    }

    parameterized.into_mapped(|_, typedef| typedef.unwrap())
}

id_type!(SolverVarId);

#[derive(Clone, Debug)]
struct PendingSig {
    arg: unif::Type<SolverVarId>,
    ret: unif::Type<SolverVarId>,
}

#[derive(Clone, Copy, Debug)]
struct GlobalContext<'a> {
    funcs_annot: &'a IdVec<first_ord::CustomFuncId, Option<unif::FuncDef>>,
    sigs_pending: &'a BTreeMap<first_ord::CustomFuncId, PendingSig>,
}

#[derive(Clone, Debug)]
enum SolverCall {
    KnownCall(unif::SolvedCall<SolverVarId>),
    PendingCall(
        Purity,
        first_ord::CustomFuncId,
        OrdMap<alias::FieldPath, alias::LocalAliases>,
        OrdMap<alias::FieldPath, alias::FoldedAliases>,
        OrdMap<alias::FieldPath, mutation::LocalStatus>,
        flat::LocalId,
    ),
}

type SolverExpr = unif::Expr<SolverCall, SolverVarId>;

type SolverType = unif::Type<SolverVarId>;

#[derive(Clone, Debug)]
struct ConstraintGraph {
    var_equalities: IdVec<SolverVarId, BTreeSet<SolverVarId>>,
}

impl ConstraintGraph {
    fn new() -> Self {
        ConstraintGraph {
            var_equalities: IdVec::new(),
        }
    }

    fn new_var(&mut self) -> SolverVarId {
        self.var_equalities.push(BTreeSet::new())
    }

    fn equate(&mut self, fst: SolverVarId, snd: SolverVarId) {
        self.var_equalities[fst].insert(snd);
        self.var_equalities[snd].insert(fst);
    }
}

fn instantiate_type(
    typedefs: &IdVec<first_ord::CustomTypeId, unif::TypeDef>,
    graph: &mut ConstraintGraph,
    type_: &anon::Type,
) -> SolverType {
    match type_ {
        anon::Type::Bool => unif::Type::Bool,
        anon::Type::Num(num) => unif::Type::Num(*num),

        anon::Type::Array(item_type) => unif::Type::Array(
            graph.new_var(),
            Box::new(instantiate_type(typedefs, graph, item_type)),
        ),

        anon::Type::HoleArray(item_type) => unif::Type::HoleArray(
            graph.new_var(),
            Box::new(instantiate_type(typedefs, graph, item_type)),
        ),

        anon::Type::Tuple(items) => unif::Type::Tuple(
            items
                .iter()
                .map(|item| instantiate_type(typedefs, graph, item))
                .collect(),
        ),

        anon::Type::Variants(variants) => unif::Type::Variants(
            variants.map(|_, variant| instantiate_type(typedefs, graph, variant)),
        ),

        anon::Type::Custom(custom) => unif::Type::Custom(
            *custom,
            IdVec::from_items(
                (0..typedefs[custom].num_params)
                    .map(|_| graph.new_var())
                    .collect(),
            ),
        ),
    }
}

fn equate_types(graph: &mut ConstraintGraph, type1: &SolverType, type2: &SolverType) {
    match (type1, type2) {
        (unif::Type::Bool, unif::Type::Bool) => {}

        (unif::Type::Num(num1), unif::Type::Num(num2)) => {
            debug_assert_eq!(num1, num2);
        }

        (unif::Type::Array(rep1, item_type1), unif::Type::Array(rep2, item_type2)) => {
            graph.equate(*rep1, *rep2);
            equate_types(graph, item_type1, item_type2);
        }

        (unif::Type::HoleArray(rep1, item_type1), unif::Type::HoleArray(rep2, item_type2)) => {
            graph.equate(*rep1, *rep2);
            equate_types(graph, item_type1, item_type2);
        }

        (unif::Type::Tuple(items1), unif::Type::Tuple(items2)) => {
            debug_assert_eq!(items1.len(), items2.len());
            for (item1, item2) in items1.iter().zip(items2) {
                equate_types(graph, item1, item2);
            }
        }

        (unif::Type::Variants(variants1), unif::Type::Variants(variants2)) => {
            for (_, variant1, variant2) in variants1
                .try_zip_exact(variants2)
                .expect("variants1.len() should equal variants2.len()")
            {
                equate_types(graph, variant1, variant2);
            }
        }

        (unif::Type::Custom(custom1, args1), unif::Type::Custom(custom2, args2)) => {
            debug_assert_eq!(custom1, custom2);
            for (_, arg1, arg2) in args1
                .try_zip_exact(args2)
                .expect("args1.len() should equal args2.len()")
            {
                graph.equate(*arg1, *arg2);
            }
        }

        _ => panic!("Cannot unify types {:?} and {:?}", type1, type2),
    }
}

fn instantiate_subst(
    vars: &IdVec<unif::RepParamId, SolverVarId>,
    type_: &unif::Type<unif::RepParamId>,
) -> SolverType {
    match type_ {
        unif::Type::Bool => unif::Type::Bool,
        unif::Type::Num(num) => unif::Type::Num(*num),

        unif::Type::Array(rep, item_type) => {
            unif::Type::Array(vars[rep], Box::new(instantiate_subst(vars, item_type)))
        }

        unif::Type::HoleArray(rep, item_type) => {
            unif::Type::HoleArray(vars[rep], Box::new(instantiate_subst(vars, item_type)))
        }

        unif::Type::Tuple(items) => unif::Type::Tuple(
            items
                .iter()
                .map(|item| instantiate_subst(vars, item))
                .collect(),
        ),

        unif::Type::Variants(variants) => {
            unif::Type::Variants(variants.map(|_, variant| instantiate_subst(vars, variant)))
        }

        unif::Type::Custom(custom, args) => {
            unif::Type::Custom(*custom, args.map(|_, arg| vars[arg]))
        }
    }
}

fn instantiate_expr(
    typedefs: &IdVec<first_ord::CustomTypeId, unif::TypeDef>,
    globals: GlobalContext,
    graph: &mut ConstraintGraph,
    locals: &mut LocalContext<flat::LocalId, SolverType>,
    expr: &mutation::Expr,
) -> (SolverExpr, SolverType) {
    match expr {
        mutation::Expr::Local(local) => {
            (unif::Expr::Local(*local), locals.local_type(*local).clone())
        }

        mutation::Expr::Call(purity, func, arg_aliases, arg_folded_aliases, arg_statuses, arg) => {
            match &globals.funcs_annot[func] {
                Some(def_annot) => {
                    let rep_vars = IdVec::from_items(
                        (0..def_annot.num_params).map(|_| graph.new_var()).collect(),
                    );

                    let arg_type = instantiate_subst(&rep_vars, &def_annot.arg_type);
                    let ret_type = instantiate_subst(&rep_vars, &def_annot.ret_type);

                    equate_types(graph, locals.local_type(*arg), &arg_type);

                    let expr_inst = unif::Expr::Call(SolverCall::KnownCall(unif::SolvedCall(
                        *purity,
                        *func,
                        rep_vars,
                        arg_aliases.clone(),
                        arg_folded_aliases.clone(),
                        arg_statuses.clone(),
                        *arg,
                    )));

                    (expr_inst, ret_type)
                }

                None => {
                    // This is a function in the current SCC

                    let pending_sig = &globals.sigs_pending[func];

                    equate_types(graph, locals.local_type(*arg), &pending_sig.arg);

                    let expr_inst = unif::Expr::Call(SolverCall::PendingCall(
                        *purity,
                        *func,
                        arg_aliases.clone(),
                        arg_folded_aliases.clone(),
                        arg_statuses.clone(),
                        *arg,
                    ));

                    (expr_inst, pending_sig.ret.clone())
                }
            }
        }

        mutation::Expr::Branch(discrim, cases, result_type) => {
            let result_type_inst = instantiate_type(typedefs, graph, result_type);

            let cases_inst = cases
                .iter()
                .map(|(cond, body)| {
                    let (body_inst, body_type) =
                        instantiate_expr(typedefs, globals, graph, locals, body);

                    equate_types(graph, &body_type, &result_type_inst);

                    (cond.clone(), body_inst)
                })
                .collect();

            let expr_inst = unif::Expr::Branch(*discrim, cases_inst, result_type_inst.clone());

            (expr_inst, result_type_inst)
        }

        mutation::Expr::LetMany(bindings, final_local) => locals.with_scope(|sub_locals| {
            let bindings_inst = bindings
                .iter()
                .map(|(_type, binding)| {
                    let (binding_inst, binding_type) =
                        instantiate_expr(typedefs, globals, graph, sub_locals, binding);

                    sub_locals.add_local(binding_type.clone());

                    (binding_type, binding_inst)
                })
                .collect();

            let expr_inst = unif::Expr::LetMany(bindings_inst, *final_local);

            let result_type = sub_locals.local_type(*final_local).clone();

            (expr_inst, result_type)
        }),

        mutation::Expr::Tuple(items) => {
            let item_types = items
                .iter()
                .map(|&item| locals.local_type(item).clone())
                .collect();

            (
                unif::Expr::Tuple(items.clone()),
                unif::Type::Tuple(item_types),
            )
        }

        mutation::Expr::TupleField(tuple, idx) => {
            let item_type = if let unif::Type::Tuple(item_types) = locals.local_type(*tuple) {
                item_types[*idx].clone()
            } else {
                unreachable!()
            };

            (unif::Expr::TupleField(*tuple, *idx), item_type)
        }

        mutation::Expr::WrapVariant(variant_types, variant, content) => {
            let variant_types_inst = variant_types
                .map(|_, variant_type| instantiate_type(typedefs, graph, variant_type));

            equate_types(
                graph,
                &variant_types_inst[variant],
                locals.local_type(*content),
            );

            (
                unif::Expr::WrapVariant(variant_types_inst.clone(), *variant, *content),
                unif::Type::Variants(variant_types_inst),
            )
        }

        mutation::Expr::UnwrapVariant(variant, wrapped) => {
            let variant_type =
                if let unif::Type::Variants(variant_types) = locals.local_type(*wrapped) {
                    variant_types[variant].clone()
                } else {
                    unreachable!()
                };

            (unif::Expr::UnwrapVariant(*variant, *wrapped), variant_type)
        }

        mutation::Expr::WrapCustom(custom, content) => {
            let typedef = &typedefs[custom];

            let rep_vars =
                IdVec::from_items((0..typedef.num_params).map(|_| graph.new_var()).collect());

            let content_type_inst = instantiate_subst(&rep_vars, &typedef.content);
            equate_types(graph, &content_type_inst, locals.local_type(*content));

            (
                unif::Expr::WrapCustom(*custom, rep_vars.clone(), *content),
                unif::Type::Custom(*custom, rep_vars),
            )
        }

        mutation::Expr::UnwrapCustom(custom, wrapped) => {
            let typedef = &typedefs[custom];

            let rep_vars =
                if let unif::Type::Custom(wrapped_custom, rep_vars) = locals.local_type(*wrapped) {
                    debug_assert_eq!(wrapped_custom, custom);
                    debug_assert_eq!(rep_vars.len(), typedef.num_params);
                    rep_vars
                } else {
                    unreachable!();
                };

            let content_type_inst = instantiate_subst(rep_vars, &typedef.content);

            (
                unif::Expr::UnwrapCustom(*custom, rep_vars.clone(), *wrapped),
                content_type_inst,
            )
        }

        _ => unimplemented!(),
    }
}

#[allow(unused_variables)]
fn unify_func_scc(
    typedefs: &IdVec<first_ord::CustomTypeId, unif::TypeDef>,
    orig_funcs: &IdVec<first_ord::CustomFuncId, mutation::FuncDef>,
    funcs_annot: &IdVec<first_ord::CustomFuncId, Option<unif::FuncDef>>,
    scc: &[first_ord::CustomFuncId],
) -> BTreeMap<first_ord::CustomFuncId, unif::FuncDef> {
    let mut graph = ConstraintGraph::new();

    let sigs_pending = scc
        .iter()
        .map(|&func| {
            let orig_sig = &orig_funcs[func];

            let arg_inst = instantiate_type(typedefs, &mut graph, &orig_sig.arg_type);
            let ret_inst = instantiate_type(typedefs, &mut graph, &orig_sig.ret_type);

            (
                func,
                PendingSig {
                    arg: arg_inst,
                    ret: ret_inst,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();

    let globals = GlobalContext {
        funcs_annot,
        sigs_pending: &sigs_pending,
    };

    let funcs_inst = scc
        .iter()
        .map(|&func| {
            let pending_sig = &sigs_pending[&func];

            let mut locals = LocalContext::new();
            locals.add_local(pending_sig.arg.clone());

            let (body_inst, body_type) = instantiate_expr(
                typedefs,
                globals,
                &mut graph,
                &mut locals,
                &orig_funcs[func].body,
            );

            equate_types(&mut graph, &pending_sig.ret, &body_type);

            (func, body_inst)
        })
        .collect::<Vec<_>>();

    unimplemented!()
}

pub fn unify_reprs(program: mutation::Program) -> unif::Program {
    let typedefs = parameterize_typedefs(&program.custom_types);

    let mut funcs_annot = IdVec::from_items(vec![None; program.funcs.len()]);
    for scc in &program.sccs {
        let scc_annot = match scc {
            Scc::Acyclic(func) => unify_func_scc(&typedefs, &program.funcs, &funcs_annot, &[*func]),
            Scc::Cyclic(funcs) => unify_func_scc(&typedefs, &program.funcs, &funcs_annot, funcs),
        };

        for (func_id, func_annot) in scc_annot {
            debug_assert!(funcs_annot[func_id].is_none());
            funcs_annot[func_id] = Some(func_annot);
        }
    }

    unif::Program {
        custom_types: typedefs,
        funcs: funcs_annot.into_mapped(|_, func| func.unwrap()),
        main: program.main,

        sccs: program.sccs,
    }
}
