use crate::data::low_ast as low;
use crate::data::repr_specialized_ast_alt as special;
use crate::util::graph::{self, Graph};
use crate::util::id_vec::IdVec;
use std::collections::BTreeSet;

fn lower_type(type_: &special::Type) -> low::Type {
    match type_ {
        special::Type::Bool => low::Type::Bool,
        special::Type::Num(num) => low::Type::Num(*num),
        special::Type::Array(rep, item_type) => {
            low::Type::Array(*rep, Box::new(lower_type(item_type)))
        }
        special::Type::HoleArray(rep, item_type) => {
            low::Type::HoleArray(*rep, Box::new(lower_type(item_type)))
        }
        special::Type::Tuple(types) => low::Type::Tuple(
            types
                .iter()
                .map(|item_type| lower_type(item_type))
                .collect(),
        ),
        special::Type::Variants(variants) => low::Type::Variants(IdVec::from_items(
            variants
                .items
                .iter()
                .map(|item_type| lower_type(item_type))
                .collect(),
        )),
        special::Type::Custom(id) => low::Type::Custom(*id),
    }
}

fn add_size_deps(type_: &special::Type, deps: &mut BTreeSet<special::CustomTypeId>) {
    match type_ {
        special::Type::Bool | special::Type::Num(_) => {}

        special::Type::Array(_, _) | special::Type::HoleArray(_, _) => {}

        special::Type::Tuple(items) => {
            for item in items {
                add_size_deps(item, deps)
            }
        }

        special::Type::Variants(variants) => {
            for (_, variant) in variants {
                add_size_deps(variant, deps)
            }
        }

        special::Type::Custom(custom) => {
            deps.insert(*custom);
        }
    }
}

#[derive(Clone, Debug)]
struct BoxInfo {
    scc: BTreeSet<special::CustomTypeId>,
}

fn find_box_infos(
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
) -> IdVec<special::CustomTypeId, BoxInfo> {
    let size_deps = Graph {
        edges_out: typedefs.map(|_, def| {
            let mut deps = BTreeSet::new();
            add_size_deps(def, &mut deps);
            deps.into_iter().collect()
        }),
    };

    let sccs = graph::strongly_connected(&size_deps);

    let mut maybe_box_infos = IdVec::from_items(vec![None; typedefs.len()]);

    for scc_vec in sccs {
        let scc: BTreeSet<_> = scc_vec.iter().cloned().collect();

        for custom_type in &scc {
            maybe_box_infos[custom_type] = Some(BoxInfo { scc: scc.clone() });
        }
    }

    maybe_box_infos.into_mapped(|_, value| value.unwrap())
}

fn needs_boxing(boxinfo: &BoxInfo, type_: &special::Type) -> bool {
    match type_ {
        special::Type::Bool => false,
        special::Type::Num(_num_type) => false,
        special::Type::Array(_rep, _item_type) => false,
        special::Type::HoleArray(_rep, _item_type) => false,
        special::Type::Tuple(types) => types
            .iter()
            .any(|item_type| needs_boxing(boxinfo, item_type)),
        special::Type::Variants(variants) => variants
            .iter()
            .any(|(_, item_type)| needs_boxing(boxinfo, item_type)),
        special::Type::Custom(id) => boxinfo.scc.contains(id),
    }
}

fn box_type(boxinfo: &BoxInfo, type_: &special::Type) -> low::Type {
    match type_ {
        special::Type::Variants(variants) => low::Type::Variants(IdVec::from_items(
            variants
                .items
                .iter()
                .map(|variant_type| box_type(boxinfo, variant_type))
                .collect(),
        )),
        _ => {
            if needs_boxing(boxinfo, type_) {
                low::Type::Boxed(Box::new(lower_type(type_)))
            } else {
                lower_type(type_)
            }
        }
    }
}

fn find_boxed_types(
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
) -> (
    IdVec<special::CustomTypeId, low::Type>,
    IdVec<special::CustomTypeId, BoxInfo>,
) {
    let box_infos = find_box_infos(typedefs);

    (
        typedefs.map(|id, typedef| box_type(&box_infos[id], typedef)),
        box_infos,
    )
}

fn lower_structures(_program: special::Program) -> low::Program {
    todo![];
}
