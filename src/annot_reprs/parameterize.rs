/// See `annot_reprs` mod comment for details.
use super::{in_ast, mid_ast};
use crate::graph::{self, Graph};
use crate::util::id_vec::IdVec;
use std::collections::{BTreeMap, BTreeSet};

pub fn parameterize_typedefs(
    typedefs: &[in_ast::TypeDef],
) -> Vec<mid_ast::TypeDef<mid_ast::RepParamId>> {
    let dep_graph = Graph {
        edges_out: IdVec::from_items(
            typedefs
                .iter()
                .map(|typedef| {
                    let mut deps = BTreeSet::new();
                    for variant in &typedef.variants {
                        if let Some(content) = variant {
                            add_dependencies(content, &mut deps);
                        }
                    }
                    deps.into_iter().collect()
                })
                .collect(),
        ),
    };

    let sccs = graph::strongly_connected(&dep_graph);

    let mut parameterized = vec![None; typedefs.len()];

    for scc in sccs {
        parameterize_typedef_scc(typedefs, &mut parameterized, &scc);
    }

    parameterized
        .into_iter()
        .map(|typedef| typedef.unwrap())
        .collect()
}

fn add_dependencies(type_: &in_ast::Type, deps: &mut BTreeSet<in_ast::CustomTypeId>) {
    match type_ {
        in_ast::Type::Bool | in_ast::Type::Int | in_ast::Type::Byte | in_ast::Type::Float => {}
        in_ast::Type::Array(item) | in_ast::Type::HoleArray(item) => {
            add_dependencies(item, deps);
        }
        in_ast::Type::Tuple(items) => {
            for item in items {
                add_dependencies(item, deps);
            }
        }
        in_ast::Type::Custom(other) => {
            deps.insert(*other);
        }
    }
}

fn count_params(
    parameterized: &[Option<mid_ast::TypeDef<mid_ast::RepParamId>>],
    type_: &in_ast::Type,
) -> usize {
    match type_ {
        in_ast::Type::Bool | in_ast::Type::Int | in_ast::Type::Byte | in_ast::Type::Float => 0,
        in_ast::Type::Array(item) | in_ast::Type::HoleArray(item) => {
            1 + count_params(parameterized, item)
        }
        in_ast::Type::Tuple(items) => items
            .iter()
            .map(|item| count_params(parameterized, item))
            .sum(),
        in_ast::Type::Custom(other) => match &parameterized[other.0] {
            Some(typedef) => typedef.num_params,
            // This is a typedef in the same SCC; the reference to it here contributes no additional
            // parameters to the entire SCC.
            None => 0,
        },
    }
}

#[derive(Clone, Debug)]
struct ReprVarIdGen(usize);

impl ReprVarIdGen {
    fn fresh(&mut self) -> mid_ast::RepParamId {
        let result = mid_ast::RepParamId(self.0);
        self.0 += 1;
        result
    }
}

fn parameterize_typedef_scc(
    typedefs: &[in_ast::TypeDef],
    parameterized: &mut [Option<mid_ast::TypeDef<mid_ast::RepParamId>>],
    scc: &[in_ast::CustomTypeId],
) {
    let num_params = scc
        .iter()
        .map(|type_id| {
            typedefs[type_id.0]
                .variants
                .iter()
                .map(|variant| match variant {
                    Some(content) => count_params(parameterized, content),
                    None => 0,
                })
                .sum::<usize>()
        })
        .sum::<usize>();

    let mut id_gen = ReprVarIdGen(0);

    let to_populate: BTreeMap<in_ast::CustomTypeId, _> = scc
        .iter()
        .map(|&type_id| {
            let typedef = &typedefs[type_id.0];
            let parameterized_variants = typedef
                .variants
                .iter()
                .map(|variant| {
                    variant.as_ref().map(|content| {
                        parameterize(parameterized, num_params, &mut id_gen, content)
                    })
                })
                .collect();

            debug_assert!(parameterized[type_id.0].is_none());

            (
                type_id,
                mid_ast::TypeDef {
                    num_params,
                    variants: parameterized_variants,
                },
            )
        })
        .collect();

    for (type_id, typedef) in to_populate {
        debug_assert!(parameterized[type_id.0].is_none());
        parameterized[type_id.0] = Some(typedef);
    }
}

fn parameterize(
    parameterized: &[Option<mid_ast::TypeDef<mid_ast::RepParamId>>],
    scc_num_params: usize,
    id_gen: &mut ReprVarIdGen,
    type_: &in_ast::Type,
) -> mid_ast::Type<mid_ast::RepParamId> {
    match type_ {
        in_ast::Type::Bool => mid_ast::Type::Bool,
        in_ast::Type::Int => mid_ast::Type::Int,
        in_ast::Type::Byte => mid_ast::Type::Byte,
        in_ast::Type::Float => mid_ast::Type::Float,

        in_ast::Type::Array(item) => {
            let repr_param = id_gen.fresh();
            mid_ast::Type::Array(
                Box::new(parameterize(parameterized, scc_num_params, id_gen, item)),
                repr_param,
            )
        }

        in_ast::Type::HoleArray(item) => {
            let repr_param = id_gen.fresh();
            mid_ast::Type::HoleArray(
                Box::new(parameterize(parameterized, scc_num_params, id_gen, item)),
                repr_param,
            )
        }

        in_ast::Type::Tuple(items) => mid_ast::Type::Tuple(
            items
                .iter()
                .map(|item| parameterize(parameterized, scc_num_params, id_gen, item))
                .collect(),
        ),

        in_ast::Type::Custom(other) => {
            match &parameterized[other.0] {
                Some(typedef) => mid_ast::Type::Custom(
                    *other,
                    (0..typedef.num_params).map(|_| id_gen.fresh()).collect(),
                ),

                None => {
                    // This is a typedef in the same SCC, so we need to parameterize it by
                    // all the SCC parameters.
                    mid_ast::Type::Custom(
                        *other,
                        (0..scc_num_params).map(mid_ast::RepParamId).collect(),
                    )
                }
            }
        }
    }
}
