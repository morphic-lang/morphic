use im_rc::OrdMap;
use std::collections::{BTreeMap, BTreeSet};

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as mutation;
use crate::data::purity::Purity;
use crate::data::repr_unified_ast as unif;
use crate::util::graph::{connected_components, strongly_connected, Graph, Scc, Undirected};
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

type SolverCondition = unif::Condition<SolverVarId>;

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

fn instantate_condition(
    typedefs: &IdVec<first_ord::CustomTypeId, unif::TypeDef>,
    type_matched: &SolverType,
    cond: &flat::Condition,
) -> SolverCondition {
    match (cond, type_matched) {
        (flat::Condition::Any, _) => unif::Condition::Any,

        (flat::Condition::Tuple(item_conds), unif::Type::Tuple(item_types)) => {
            debug_assert_eq!(item_conds.len(), item_types.len());

            unif::Condition::Tuple(
                item_types
                    .iter()
                    .zip(item_conds)
                    .map(|(item_type, item_cond)| {
                        instantate_condition(typedefs, item_type, item_cond)
                    })
                    .collect(),
            )
        }

        (flat::Condition::Variant(variant, content_cond), unif::Type::Variants(variant_types)) => {
            let content_type = &variant_types[variant];

            unif::Condition::Variant(
                *variant,
                Box::new(instantate_condition(typedefs, content_type, content_cond)),
            )
        }

        (
            flat::Condition::Custom(custom, content_cond),
            unif::Type::Custom(matched_custom, rep_vars),
        ) => {
            let typedef = &typedefs[custom];

            debug_assert_eq!(custom, matched_custom);
            debug_assert_eq!(typedef.num_params, rep_vars.len());

            let content_type_inst = instantiate_subst(&rep_vars, &typedef.content);

            unif::Condition::Custom(
                *custom,
                rep_vars.clone(),
                Box::new(instantate_condition(
                    typedefs,
                    &content_type_inst,
                    content_cond,
                )),
            )
        }

        (flat::Condition::BoolConst(val), unif::Type::Bool) => unif::Condition::BoolConst(*val),

        (flat::Condition::ByteConst(val), unif::Type::Num(first_ord::NumType::Byte)) => {
            unif::Condition::ByteConst(*val)
        }

        (flat::Condition::IntConst(val), unif::Type::Num(first_ord::NumType::Int)) => {
            unif::Condition::IntConst(*val)
        }

        (flat::Condition::FloatConst(val), unif::Type::Num(first_ord::NumType::Float)) => {
            unif::Condition::FloatConst(*val)
        }

        _ => unreachable!(),
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
        mutation::Expr::Local(local) => (
            unif::Expr::Local(*local),
            locals.local_binding(*local).clone(),
        ),

        mutation::Expr::Call(purity, func, arg_aliases, arg_folded_aliases, arg_statuses, arg) => {
            match &globals.funcs_annot[func] {
                Some(def_annot) => {
                    let rep_vars = IdVec::from_items(
                        (0..def_annot.num_params).map(|_| graph.new_var()).collect(),
                    );

                    let arg_type = instantiate_subst(&rep_vars, &def_annot.arg_type);
                    let ret_type = instantiate_subst(&rep_vars, &def_annot.ret_type);

                    equate_types(graph, locals.local_binding(*arg), &arg_type);

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

                    equate_types(graph, locals.local_binding(*arg), &pending_sig.arg);

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
                    let cond_inst =
                        instantate_condition(typedefs, locals.local_binding(*discrim), cond);

                    let (body_inst, body_type) =
                        instantiate_expr(typedefs, globals, graph, locals, body);

                    equate_types(graph, &body_type, &result_type_inst);

                    (cond_inst.clone(), body_inst)
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

            let result_type = sub_locals.local_binding(*final_local).clone();

            (expr_inst, result_type)
        }),

        mutation::Expr::Tuple(items) => {
            let item_types = items
                .iter()
                .map(|&item| locals.local_binding(item).clone())
                .collect();

            (
                unif::Expr::Tuple(items.clone()),
                unif::Type::Tuple(item_types),
            )
        }

        mutation::Expr::TupleField(tuple, idx) => {
            let item_type = if let unif::Type::Tuple(item_types) = locals.local_binding(*tuple) {
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
                locals.local_binding(*content),
            );

            (
                unif::Expr::WrapVariant(variant_types_inst.clone(), *variant, *content),
                unif::Type::Variants(variant_types_inst),
            )
        }

        mutation::Expr::UnwrapVariant(variant, wrapped) => {
            let variant_type =
                if let unif::Type::Variants(variant_types) = locals.local_binding(*wrapped) {
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
            equate_types(graph, &content_type_inst, locals.local_binding(*content));

            (
                unif::Expr::WrapCustom(*custom, rep_vars.clone(), *content),
                unif::Type::Custom(*custom, rep_vars),
            )
        }

        mutation::Expr::UnwrapCustom(custom, wrapped) => {
            let typedef = &typedefs[custom];

            let rep_vars = if let unif::Type::Custom(wrapped_custom, rep_vars) =
                locals.local_binding(*wrapped)
            {
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

        mutation::Expr::ArithOp(op) => {
            let ret_type = match op {
                flat::ArithOp::Op(num_type, _, _, _) => unif::Type::Num(*num_type),
                flat::ArithOp::Cmp(_, _, _, _) => unif::Type::Bool,
                flat::ArithOp::Negate(num_type, _) => unif::Type::Num(*num_type),
            };

            (unif::Expr::ArithOp(*op), ret_type)
        }

        mutation::Expr::ArrayOp(mutation::ArrayOp::Item(
            _item_type,
            array_status,
            array,
            index,
        )) => {
            let (rep_var, item_type_inst) =
                if let unif::Type::Array(rep_var, item_type_inst) = locals.local_binding(*array) {
                    (*rep_var, item_type_inst as &unif::Type<_>)
                } else {
                    unreachable!()
                };

            (
                unif::Expr::ArrayOp(
                    rep_var,
                    item_type_inst.clone(),
                    array_status.clone(),
                    unif::ArrayOp::Item(*array, *index),
                ),
                unif::Type::Tuple(vec![
                    item_type_inst.clone(),
                    unif::Type::HoleArray(rep_var, Box::new(item_type_inst.clone())),
                ]),
            )
        }

        mutation::Expr::ArrayOp(mutation::ArrayOp::Len(_item_type, array_status, array)) => {
            let (rep_var, item_type_inst) =
                if let unif::Type::Array(rep_var, item_type_inst) = locals.local_binding(*array) {
                    (*rep_var, item_type_inst as &unif::Type<_>)
                } else {
                    unreachable!()
                };

            (
                unif::Expr::ArrayOp(
                    rep_var,
                    item_type_inst.clone(),
                    array_status.clone(),
                    unif::ArrayOp::Len(*array),
                ),
                unif::Type::Num(first_ord::NumType::Int),
            )
        }

        mutation::Expr::ArrayOp(mutation::ArrayOp::Push(_item_type, array_status, array, item)) => {
            let (rep_var, array_item_type) =
                if let unif::Type::Array(rep_var, array_item_type) = locals.local_binding(*array) {
                    (*rep_var, array_item_type as &unif::Type<_>)
                } else {
                    unreachable!()
                };

            let item_type = locals.local_binding(*item);

            equate_types(graph, array_item_type, item_type);

            (
                unif::Expr::ArrayOp(
                    rep_var,
                    array_item_type.clone(),
                    array_status.clone(),
                    unif::ArrayOp::Push(*array, *item),
                ),
                unif::Type::Array(rep_var, Box::new(array_item_type.clone())),
            )
        }

        mutation::Expr::ArrayOp(mutation::ArrayOp::Pop(_item_type, array_status, array)) => {
            let (rep_var, item_type_inst) =
                if let unif::Type::Array(rep_var, item_type_inst) = locals.local_binding(*array) {
                    (*rep_var, item_type_inst as &unif::Type<_>)
                } else {
                    unreachable!()
                };

            (
                unif::Expr::ArrayOp(
                    rep_var,
                    item_type_inst.clone(),
                    array_status.clone(),
                    unif::ArrayOp::Pop(*array),
                ),
                unif::Type::Tuple(vec![
                    unif::Type::Array(rep_var, Box::new(item_type_inst.clone())),
                    item_type_inst.clone(),
                ]),
            )
        }

        mutation::Expr::ArrayOp(mutation::ArrayOp::Replace(
            _item_type,
            hole_array_status,
            hole_array,
            item,
        )) => {
            let (rep_var, array_item_type) =
                if let unif::Type::HoleArray(rep_var, array_item_type) =
                    locals.local_binding(*hole_array)
                {
                    (*rep_var, array_item_type as &unif::Type<_>)
                } else {
                    unreachable!()
                };

            let item_type = locals.local_binding(*item);

            equate_types(graph, array_item_type, item_type);

            (
                unif::Expr::ArrayOp(
                    rep_var,
                    array_item_type.clone(),
                    hole_array_status.clone(),
                    unif::ArrayOp::Replace(*hole_array, *item),
                ),
                unif::Type::Array(rep_var, Box::new(array_item_type.clone())),
            )
        }

        mutation::Expr::IoOp(mutation::IoOp::Input) => {
            let rep_var = graph.new_var();

            (
                unif::Expr::IoOp(rep_var, mutation::IoOp::Input),
                unif::Type::Array(rep_var, Box::new(unif::Type::Num(first_ord::NumType::Byte))),
            )
        }

        mutation::Expr::IoOp(mutation::IoOp::Output(array_status, byte_array)) => {
            let rep_var =
                if let unif::Type::Array(rep_var, item_type) = locals.local_binding(*byte_array) {
                    debug_assert_eq!(
                        item_type as &unif::Type<_>,
                        &unif::Type::Num(first_ord::NumType::Byte)
                    );
                    *rep_var
                } else {
                    unreachable!();
                };

            (
                unif::Expr::IoOp(
                    rep_var,
                    mutation::IoOp::Output(array_status.clone(), *byte_array),
                ),
                unif::Type::Tuple(Vec::new()),
            )
        }

        mutation::Expr::ArrayLit(item_type, items) => {
            let rep_var = graph.new_var();

            let item_type_inst = instantiate_type(typedefs, graph, item_type);

            for item in items {
                equate_types(graph, &item_type_inst, locals.local_binding(*item));
            }

            (
                unif::Expr::ArrayLit(rep_var, item_type_inst.clone(), items.clone()),
                unif::Type::Array(rep_var, Box::new(item_type_inst)),
            )
        }

        mutation::Expr::BoolLit(val) => (unif::Expr::BoolLit(*val), unif::Type::Bool),

        mutation::Expr::ByteLit(val) => (
            unif::Expr::ByteLit(*val),
            unif::Type::Num(first_ord::NumType::Byte),
        ),

        mutation::Expr::IntLit(val) => (
            unif::Expr::IntLit(*val),
            unif::Type::Num(first_ord::NumType::Int),
        ),

        mutation::Expr::FloatLit(val) => (
            unif::Expr::FloatLit(*val),
            unif::Type::Num(first_ord::NumType::Float),
        ),
    }
}

id_type!(UnifiedVarId);

// Partitions the set of unified solver variables into 'internal variables' and 'parameters' on a
// per-function basis, where the 'parameters' correspond to exactly those variables which appear in
// the function's signature, and all other variables are considered 'internal'.
struct FuncVarPartition {
    solutions: IdVec<UnifiedVarId, unif::RepSolution>,
    params: IdVec<unif::RepParamId, UnifiedVarId>,
}

fn get_param(
    to_params: &mut BTreeMap<UnifiedVarId, unif::RepParamId>,
    unified: UnifiedVarId,
) -> unif::RepParamId {
    if let Some(param) = to_params.get(&unified) {
        *param
    } else {
        let new_param = unif::RepParamId(to_params.len());
        to_params.insert(unified, new_param);
        new_param
    }
}

fn extract_sig_type(
    to_unified: &IdVec<SolverVarId, UnifiedVarId>,
    to_params: &mut BTreeMap<UnifiedVarId, unif::RepParamId>,
    type_: &SolverType,
) -> unif::Type<unif::RepParamId> {
    match type_ {
        unif::Type::Bool => unif::Type::Bool,
        unif::Type::Num(num_type) => unif::Type::Num(*num_type),

        unif::Type::Array(rep_var, item_type) => {
            let rep_param = get_param(to_params, to_unified[rep_var]);
            let item_type_extracted = extract_sig_type(to_unified, to_params, item_type);
            unif::Type::Array(rep_param, Box::new(item_type_extracted))
        }

        unif::Type::HoleArray(rep_var, item_type) => {
            let rep_param = get_param(to_params, to_unified[rep_var]);
            let item_type_extracted = extract_sig_type(to_unified, to_params, item_type);
            unif::Type::HoleArray(rep_param, Box::new(item_type_extracted))
        }

        unif::Type::Tuple(items) => unif::Type::Tuple(
            items
                .iter()
                .map(|item| extract_sig_type(to_unified, to_params, item))
                .collect(),
        ),

        unif::Type::Variants(variants) => unif::Type::Variants(
            variants.map(|_, variant| extract_sig_type(to_unified, to_params, variant)),
        ),

        unif::Type::Custom(custom, args) => {
            let arg_params = args.map(|_, arg_var| get_param(to_params, to_unified[arg_var]));
            unif::Type::Custom(*custom, arg_params)
        }
    }
}

fn partition_vars_for_sig(
    num_unified: usize,
    to_unified: &IdVec<SolverVarId, UnifiedVarId>,
    arg_type: &SolverType,
    ret_type: &SolverType,
) -> (
    unif::Type<unif::RepParamId>, // extracted arg type
    unif::Type<unif::RepParamId>, // extracted ret type
    FuncVarPartition,
) {
    let mut to_params = BTreeMap::new();

    let arg_extracted = extract_sig_type(to_unified, &mut to_params, arg_type);
    let ret_extracted = extract_sig_type(to_unified, &mut to_params, ret_type);

    let params = {
        let mut params = IdVec::from_items(vec![None; to_params.len()]);
        for (unified, &param) in &to_params {
            debug_assert!(params[param].is_none());
            params[param] = Some(*unified);
        }
        params.into_mapped(|_, unified| unified.unwrap())
    };

    let mut internal_var_gen = IdGen::<unif::InternalRepVarId>::new();

    let solutions = IdVec::from_items(
        (0..num_unified)
            .map(UnifiedVarId)
            .map(|unified| {
                if let Some(param) = to_params.get(&unified) {
                    unif::RepSolution::Param(*param)
                } else {
                    unif::RepSolution::Internal(internal_var_gen.fresh())
                }
            })
            .collect(),
    );

    (
        arg_extracted,
        ret_extracted,
        FuncVarPartition { solutions, params },
    )
}

fn extract_type(
    to_unified: &IdVec<SolverVarId, UnifiedVarId>,
    this_solutions: &IdVec<UnifiedVarId, unif::RepSolution>,
    type_: SolverType,
) -> unif::Type<unif::RepSolution> {
    match type_ {
        unif::Type::Bool => unif::Type::Bool,
        unif::Type::Num(num_type) => unif::Type::Num(num_type),

        unif::Type::Array(rep_var, item_type) => unif::Type::Array(
            this_solutions[to_unified[rep_var]],
            Box::new(extract_type(to_unified, this_solutions, *item_type)),
        ),

        unif::Type::HoleArray(rep_var, item_type) => unif::Type::HoleArray(
            this_solutions[to_unified[rep_var]],
            Box::new(extract_type(to_unified, this_solutions, *item_type)),
        ),

        unif::Type::Tuple(items) => unif::Type::Tuple(
            items
                .into_iter()
                .map(|item| extract_type(to_unified, this_solutions, item))
                .collect(),
        ),

        unif::Type::Variants(variants) => unif::Type::Variants(
            variants.into_mapped(|_, variant| extract_type(to_unified, this_solutions, variant)),
        ),

        unif::Type::Custom(custom, arg_vars) => unif::Type::Custom(
            custom,
            arg_vars.into_mapped(|_, arg_var| this_solutions[to_unified[arg_var]]),
        ),
    }
}

fn extract_condition(
    to_unified: &IdVec<SolverVarId, UnifiedVarId>,
    this_solutions: &IdVec<UnifiedVarId, unif::RepSolution>,
    cond: SolverCondition,
) -> unif::Condition<unif::RepSolution> {
    match cond {
        unif::Condition::Any => unif::Condition::Any,

        unif::Condition::Tuple(item_conds) => unif::Condition::Tuple(
            item_conds
                .into_iter()
                .map(|item_cond| extract_condition(to_unified, this_solutions, item_cond))
                .collect(),
        ),

        unif::Condition::Variant(variant, content_cond) => unif::Condition::Variant(
            variant,
            Box::new(extract_condition(to_unified, this_solutions, *content_cond)),
        ),

        unif::Condition::Custom(custom, rep_vars, content_cond) => unif::Condition::Custom(
            custom,
            rep_vars.into_mapped(|_, rep_var| this_solutions[to_unified[rep_var]]),
            Box::new(extract_condition(to_unified, this_solutions, *content_cond)),
        ),

        unif::Condition::BoolConst(val) => unif::Condition::BoolConst(val),
        unif::Condition::ByteConst(val) => unif::Condition::ByteConst(val),
        unif::Condition::IntConst(val) => unif::Condition::IntConst(val),
        unif::Condition::FloatConst(val) => unif::Condition::FloatConst(val),
    }
}

// TODO: This type signature needs to not be like this.
fn extract_expr(
    to_unified: &IdVec<SolverVarId, UnifiedVarId>,
    this_solutions: &IdVec<UnifiedVarId, unif::RepSolution>,
    scc_sigs: &BTreeMap<
        first_ord::CustomFuncId,
        (
            unif::Type<unif::RepParamId>,
            unif::Type<unif::RepParamId>,
            FuncVarPartition,
        ),
    >,
    expr: SolverExpr,
) -> unif::Expr<unif::SolvedCall<unif::RepSolution>, unif::RepSolution> {
    match expr {
        unif::Expr::Local(local) => unif::Expr::Local(local),

        unif::Expr::Call(SolverCall::KnownCall(unif::SolvedCall(
            purity,
            func,
            rep_args,
            arg_aliases,
            arg_folded_aliases,
            arg_statuses,
            arg,
        ))) => unif::Expr::Call(unif::SolvedCall(
            purity,
            func,
            rep_args.map(|_, arg| this_solutions[to_unified[arg]]),
            arg_aliases,
            arg_folded_aliases,
            arg_statuses,
            arg,
        )),

        unif::Expr::Call(SolverCall::PendingCall(
            purity,
            func,
            arg_aliases,
            arg_folded_aliases,
            arg_statuses,
            arg,
        )) => {
            let (_, _, func_partition) = &scc_sigs[&func];

            unif::Expr::Call(unif::SolvedCall(
                purity,
                func,
                func_partition
                    .params
                    .map(|_, unified| this_solutions[unified]),
                arg_aliases,
                arg_folded_aliases,
                arg_statuses,
                arg,
            ))
        }

        unif::Expr::Branch(discrim, cases, result_type) => {
            let cases_extracted = cases
                .into_iter()
                .map(|(cond, body)| {
                    (
                        extract_condition(to_unified, this_solutions, cond),
                        extract_expr(to_unified, this_solutions, scc_sigs, body),
                    )
                })
                .collect();

            let result_type_extracted = extract_type(to_unified, this_solutions, result_type);

            unif::Expr::Branch(discrim, cases_extracted, result_type_extracted)
        }

        unif::Expr::LetMany(bindings, final_local) => {
            let bindings_extracted = bindings
                .into_iter()
                .map(|(type_, binding)| {
                    (
                        extract_type(to_unified, this_solutions, type_),
                        extract_expr(to_unified, this_solutions, scc_sigs, binding),
                    )
                })
                .collect();

            unif::Expr::LetMany(bindings_extracted, final_local)
        }

        unif::Expr::Tuple(items) => unif::Expr::Tuple(items),

        unif::Expr::TupleField(tuple, idx) => unif::Expr::TupleField(tuple, idx),

        unif::Expr::WrapVariant(variants, variant, content) => {
            let variants_extracted = variants.into_mapped(|_, variant_type| {
                extract_type(to_unified, this_solutions, variant_type)
            });

            unif::Expr::WrapVariant(variants_extracted, variant, content)
        }

        unif::Expr::UnwrapVariant(variant, wrapped) => unif::Expr::UnwrapVariant(variant, wrapped),

        unif::Expr::WrapCustom(custom, rep_args, content) => {
            let rep_args_extracted =
                rep_args.into_mapped(|_, arg_var| this_solutions[to_unified[arg_var]]);

            unif::Expr::WrapCustom(custom, rep_args_extracted, content)
        }

        unif::Expr::UnwrapCustom(custom, rep_args, wrapped) => {
            let rep_args_extracted =
                rep_args.into_mapped(|_, arg_var| this_solutions[to_unified[arg_var]]);

            unif::Expr::UnwrapCustom(custom, rep_args_extracted, wrapped)
        }

        unif::Expr::ArithOp(op) => unif::Expr::ArithOp(op),

        unif::Expr::ArrayOp(rep_var, item_type, array_status, op) => unif::Expr::ArrayOp(
            this_solutions[to_unified[rep_var]],
            extract_type(to_unified, this_solutions, item_type),
            array_status,
            op,
        ),

        unif::Expr::IoOp(rep_var, op) => unif::Expr::IoOp(this_solutions[to_unified[rep_var]], op),

        unif::Expr::ArrayLit(rep_var, item_type, items) => unif::Expr::ArrayLit(
            this_solutions[to_unified[rep_var]],
            extract_type(to_unified, this_solutions, item_type),
            items,
        ),

        unif::Expr::BoolLit(val) => unif::Expr::BoolLit(val),
        unif::Expr::ByteLit(val) => unif::Expr::ByteLit(val),
        unif::Expr::IntLit(val) => unif::Expr::IntLit(val),
        unif::Expr::FloatLit(val) => unif::Expr::FloatLit(val),
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

    // TODO: This doesn't quite fit the structure of the utilities offer in utils::constraint_graph,
    // but it comes very close.  Can we factor this out into a reusable abstraction?
    let unified_vars: IdVec<UnifiedVarId, _> = IdVec::from_items(connected_components(
        &Undirected::from_directed_unchecked(Graph {
            edges_out: graph
                .var_equalities
                .map(|_, equalities| equalities.iter().cloned().collect()),
        }),
    ));

    let to_unified: IdVec<SolverVarId, _> = {
        let mut to_unified = IdVec::from_items(vec![None; graph.var_equalities.len()]);

        for (unified, solver_vars) in &unified_vars {
            for solver_var in solver_vars {
                debug_assert!(to_unified[solver_var].is_none());
                to_unified[solver_var] = Some(unified);
            }
        }

        to_unified.into_mapped(|_, unified| unified.unwrap())
    };

    let solved_sigs = sigs_pending
        .iter()
        .map(|(func, pending_sig)| {
            (
                *func,
                partition_vars_for_sig(
                    unified_vars.len(),
                    &to_unified,
                    &pending_sig.arg,
                    &pending_sig.ret,
                ),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let solved_bodies = funcs_inst
        .into_iter()
        .map(|(func, body_inst)| {
            let (_, _, func_partition) = &solved_sigs[&func];

            (
                func,
                extract_expr(
                    &to_unified,
                    &func_partition.solutions,
                    &solved_sigs,
                    body_inst,
                ),
            )
        })
        .collect::<BTreeMap<_, _>>();

    // Collect everything together into a single BTreeMap

    let mut solved_funcs = BTreeMap::new();

    let mut remaining_solved_sigs = solved_sigs;
    let mut remaining_solved_bodies = solved_bodies;

    for func in scc {
        let (arg_type, ret_type, partition) = remaining_solved_sigs
            .remove(func)
            .expect("func should be present in remaining_solved_sigs");

        let body = remaining_solved_bodies
            .remove(func)
            .expect("func should be present in remaining_solved_bodies");

        let orig_def = &orig_funcs[func];

        let solved_def = unif::FuncDef {
            purity: orig_def.purity,
            num_params: partition.params.len(),
            // This includes 'internal' variables which do not actually appear in this function,
            // and only appear inside other functions in the same SCC.
            num_internal_vars: unified_vars.len() - partition.params.len(),
            arg_type,
            ret_type,
            body,
        };

        solved_funcs.insert(*func, solved_def);
    }

    solved_funcs
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
        mod_symbols: program.mod_symbols,
        custom_types: typedefs,
        custom_type_symbols: program.custom_type_symbols,
        funcs: funcs_annot.into_mapped(|_, func| func.unwrap()),
        func_symbols: program.func_symbols,
        main: program.main,

        sccs: program.sccs,
    }
}
