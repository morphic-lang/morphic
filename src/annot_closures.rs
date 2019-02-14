use std::collections::btree_map::{BTreeMap, Entry};

use crate::data::closure_annot_ast as annot;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::graph::{strongly_connected, Graph, NodeId};

fn invert_polarity(polarity: annot::Polarity) -> annot::Polarity {
    match polarity {
        annot::Polarity::Positive => annot::Polarity::Negative,
        annot::Polarity::Negative => annot::Polarity::Positive,
    }
}

fn compose_polarities(p1: annot::Polarity, p2: annot::Polarity) -> annot::Polarity {
    match p1 {
        annot::Polarity::Positive => p2,
        annot::Polarity::Negative => invert_polarity(p2),
    }
}

fn add_type_dependencies(
    type_: &mono::Type,
    polarity: annot::Polarity,
    target: &mut Vec<(mono::CustomTypeId, annot::Polarity)>,
) {
    match type_ {
        mono::Type::Bool => {}
        mono::Type::Int => {}
        mono::Type::Float => {}
        mono::Type::Text => {}
        mono::Type::Array(item) => add_type_dependencies(item, polarity, target),

        mono::Type::Tuple(items) => {
            for item in items {
                add_type_dependencies(item, polarity, target)
            }
        }

        mono::Type::Func(_, arg, ret) => {
            add_type_dependencies(arg, invert_polarity(polarity), target);
            add_type_dependencies(ret, polarity, target);
        }

        &mono::Type::Custom(other) => {
            target.push((other, polarity));
        }
    }
}

fn type_dependencies(typedef: &mono::TypeDef) -> Vec<(mono::CustomTypeId, annot::Polarity)> {
    let mut result = Vec::new();
    for variant in &typedef.variants {
        if let Some(content) = variant {
            add_type_dependencies(content, annot::Polarity::Positive, &mut result);
        }
    }
    result
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Color {
    Blue,
    Red,
}

fn opposite_color(color: Color) -> Color {
    match color {
        Color::Blue => Color::Red,
        Color::Red => Color::Blue,
    }
}

fn color_typedef_scc(
    typedefs: &[mono::TypeDef],
    scc: &[mono::CustomTypeId],
) -> Option<BTreeMap<mono::CustomTypeId, Color>> {
    let mut colors = BTreeMap::new();

    let mut fringe = vec![(scc[0], Color::Blue)];

    while let Some((node, color)) = fringe.pop() {
        match colors.entry(node) {
            Entry::Vacant(vacant) => {
                vacant.insert(color);

                for (dep, polarity) in type_dependencies(&typedefs[node.0]) {
                    match polarity {
                        annot::Polarity::Positive => fringe.push((dep, color)),
                        annot::Polarity::Negative => fringe.push((dep, opposite_color(color))),
                    }
                }
            }

            Entry::Occupied(occupied) => {
                if occupied.get() != &color {
                    return None;
                }
            }
        }
    }

    Some(colors)
}

#[derive(Clone, Debug)]
enum PendingPType {
    Bool,
    Int,
    Float,
    Text,
    Array(Box<PendingPType>),
    Tuple(Vec<PendingPType>),
    Func(
        Purity,
        annot::ClosureParamId,
        Box<PendingPType>,
        Box<PendingPType>,
    ),
    Custom(mono::CustomTypeId, Vec<annot::ClosureParamId>),
    CustomPending(mono::CustomTypeId),
}

fn register_typedef_param(
    color: Color,
    polarity: annot::Polarity,
    param_pos_colors: &mut Vec<Color>,
) -> annot::ClosureParamId {
    let id = annot::ClosureParamId(param_pos_colors.len());

    match polarity {
        annot::Polarity::Positive => {
            param_pos_colors.push(color);
        }

        annot::Polarity::Negative => {
            param_pos_colors.push(opposite_color(color));
        }
    }

    id
}

fn partial_parameterize_inner(
    parameterized: &[Option<annot::TypeDef>],
    color: Color,
    type_: &mono::Type,
    polarity: annot::Polarity,
    param_pos_colors: &mut Vec<Color>,
) -> PendingPType {
    match type_ {
        mono::Type::Bool => PendingPType::Bool,
        mono::Type::Int => PendingPType::Int,
        mono::Type::Float => PendingPType::Float,
        mono::Type::Text => PendingPType::Text,

        mono::Type::Array(item) => {
            let pending_item =
                partial_parameterize_inner(parameterized, color, item, polarity, param_pos_colors);

            PendingPType::Array(Box::new(pending_item))
        }

        mono::Type::Tuple(items) => {
            let pending_items = items
                .iter()
                .map(|item| {
                    partial_parameterize_inner(
                        parameterized,
                        color,
                        item,
                        polarity,
                        param_pos_colors,
                    )
                })
                .collect();

            PendingPType::Tuple(pending_items)
        }

        mono::Type::Func(purity, arg, ret) => {
            let param = register_typedef_param(color, polarity, param_pos_colors);

            let pending_arg = partial_parameterize_inner(
                parameterized,
                color,
                arg,
                invert_polarity(polarity),
                param_pos_colors,
            );

            let pending_ret =
                partial_parameterize_inner(parameterized, color, ret, polarity, param_pos_colors);

            PendingPType::Func(*purity, param, Box::new(pending_arg), Box::new(pending_ret))
        }

        mono::Type::Custom(other) => match &parameterized[other.0] {
            Some(annotated) => {
                let params = annotated
                    .param_polarities
                    .iter()
                    .map(|&sub_polarity| {
                        register_typedef_param(
                            color,
                            compose_polarities(polarity, sub_polarity),
                            param_pos_colors,
                        )
                    })
                    .collect();

                PendingPType::Custom(*other, params)
            }

            None => PendingPType::CustomPending(*other),
        },
    }
}

fn complete_pending(num_params: usize, pending: PendingPType) -> annot::PType {
    match pending {
        PendingPType::Bool => annot::PType::Bool,
        PendingPType::Int => annot::PType::Int,
        PendingPType::Float => annot::PType::Float,
        PendingPType::Text => annot::PType::Text,

        PendingPType::Array(item) => {
            annot::PType::Array(Box::new(complete_pending(num_params, *item)))
        }

        PendingPType::Tuple(items) => annot::PType::Tuple(
            items
                .into_iter()
                .map(|item| complete_pending(num_params, item))
                .collect(),
        ),

        PendingPType::Func(purity, param, arg, ret) => annot::PType::Func(
            purity,
            param,
            Box::new(complete_pending(num_params, *arg)),
            Box::new(complete_pending(num_params, *ret)),
        ),

        PendingPType::Custom(other, params) => annot::PType::Custom(other, params),

        PendingPType::CustomPending(other) => {
            annot::PType::Custom(other, (0..num_params).map(annot::ClosureParamId).collect())
        }
    }
}

fn parameterize_typedef_scc(
    typedefs: &[mono::TypeDef],
    parameterized: &mut [Option<annot::TypeDef>],
    scc: &[mono::CustomTypeId],
) {
    let coloring = color_typedef_scc(typedefs, scc)
        .expect("Internal compiler error: negative recursion in typedefs is not yet supported");

    let mut param_pos_colors = Vec::new();

    let pending_typedefs = scc
        .iter()
        .map(|typedef_id| {
            (
                typedef_id,
                typedefs[typedef_id.0]
                    .variants
                    .iter()
                    .map(|variant| {
                        variant.as_ref().map(|variant| {
                            partial_parameterize_inner(
                                parameterized,
                                coloring[typedef_id],
                                variant,
                                annot::Polarity::Positive,
                                &mut param_pos_colors,
                            )
                        })
                    })
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();

    for (typedef_id, pending_variants) in pending_typedefs {
        let completed = annot::TypeDef {
            param_polarities: param_pos_colors
                .iter()
                .map(|&color| {
                    if color == coloring[typedef_id] {
                        annot::Polarity::Positive
                    } else {
                        annot::Polarity::Negative
                    }
                })
                .collect(),

            variants: pending_variants
                .into_iter()
                .map(|variant| {
                    variant.map(|variant| complete_pending(param_pos_colors.len(), variant))
                })
                .collect(),
        };

        parameterized[typedef_id.0] = Some(completed);
    }
}

pub fn parameterize_typedefs(typedefs: &[mono::TypeDef]) -> Vec<annot::TypeDef> {
    let dependency_graph = Graph {
        edges_out: typedefs
            .iter()
            .map(|typedef| {
                type_dependencies(typedef)
                    .into_iter()
                    .map(|(mono::CustomTypeId(dep), _)| NodeId(dep))
                    .collect()
            })
            .collect(),
    };

    let sccs = strongly_connected(&dependency_graph);

    let mut parameterized: Vec<Option<annot::TypeDef>> = vec![None; typedefs.len()];

    for scc in sccs {
        parameterize_typedef_scc(
            typedefs,
            &mut parameterized,
            &scc.iter()
                .map(|&NodeId(idx)| mono::CustomTypeId(idx))
                .collect::<Vec<_>>(),
        );
    }

    parameterized
        .into_iter()
        .map(|typedef| typedef.unwrap())
        .collect()
}
