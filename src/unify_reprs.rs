use std::collections::{BTreeMap, BTreeSet};

use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::mutation_annot_ast as mutation;
use crate::data::repr_unified_ast as unif;
use crate::util::graph::{strongly_connected, Graph, Scc};
use crate::util::id_gen::IdGen;
use crate::util::id_vec::IdVec;

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

#[allow(unused_variables)]
fn unify_func_scc(
    typedefs: &IdVec<first_ord::CustomTypeId, unif::TypeDef>,
    orig_funcs: &IdVec<first_ord::CustomFuncId, mutation::FuncDef>,
    funcs_annot: &IdVec<first_ord::CustomFuncId, Option<unif::FuncDef>>,
    scc: &[first_ord::CustomFuncId],
) -> BTreeMap<first_ord::CustomFuncId, unif::FuncDef> {
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
