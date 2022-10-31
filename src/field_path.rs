use im_rc::OrdSet;
use im_rc::{OrdMap, Vector};
use std::collections::BTreeMap;

use crate::data::alias_annot_ast as annot;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::util::disjunction::Disj;
use crate::util::im_rc_ext::VectorExtensions;

// Computes the fields in `type_` at which there is a name
//
// Currently, a 'name' means a field containing a heap structure participating in mutation
// optimization (which includes arrays and hole arrays, but excludes boxes).
fn get_names_in_excluding<'a>(
    type_defs: &'a flat::CustomTypes,
    type_: &'a anon::Type,
    exclude: &OrdSet<flat::CustomTypeSccId>,
) -> Vec<(annot::FieldPath, &'a anon::Type)> {
    let mut names = Vec::new();
    add_names_from_type(type_defs, &mut names, exclude, type_, Vector::new());
    return names;

    // Recursively appends paths to names in `type_` to `names`
    fn add_names_from_type<'a>(
        type_defs: &'a flat::CustomTypes,
        names: &mut Vec<(annot::FieldPath, &'a anon::Type)>,
        typedefs_on_path: &OrdSet<flat::CustomTypeSccId>,
        type_: &'a anon::Type,
        prefix: annot::FieldPath,
    ) {
        match type_ {
            anon::Type::Bool | anon::Type::Num(_) => {}
            anon::Type::Array(item_type) | anon::Type::HoleArray(item_type) => {
                // The array itself:
                names.push((prefix.clone(), type_));
                // The names in elements of the array:
                add_names_from_type(
                    type_defs,
                    names,
                    typedefs_on_path,
                    item_type,
                    prefix.add_back(annot::Field::ArrayMembers),
                );
            }
            anon::Type::Tuple(item_types) => {
                for (i, item_type) in item_types.iter().enumerate() {
                    add_names_from_type(
                        type_defs,
                        names,
                        typedefs_on_path,
                        item_type,
                        prefix.clone().add_back(annot::Field::Field(i)),
                    );
                }
            }
            anon::Type::Variants(variant_types) => {
                for (variant, variant_type) in variant_types {
                    add_names_from_type(
                        type_defs,
                        names,
                        typedefs_on_path,
                        variant_type,
                        prefix.clone().add_back(annot::Field::Variant(variant)),
                    );
                }
            }
            anon::Type::Boxed(content_type) => {
                add_names_from_type(
                    type_defs,
                    names,
                    typedefs_on_path,
                    content_type,
                    prefix.add_back(annot::Field::Boxed),
                );
            }
            anon::Type::Custom(id) => {
                let scc_id = type_defs.types[id].scc;
                if !typedefs_on_path.contains(&scc_id) {
                    let mut sub_typedefs_on_path = typedefs_on_path.clone();
                    sub_typedefs_on_path.insert(scc_id);
                    for scc_type in &type_defs.sccs[scc_id] {
                        add_names_from_type(
                            type_defs,
                            names,
                            &sub_typedefs_on_path,
                            &type_defs.types[scc_type].content,
                            prefix
                                .clone()
                                .add_back(annot::Field::CustomScc(scc_id, *id))
                                .add_back(annot::Field::Custom(*scc_type)),
                        );
                    }
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum FoldPointKind<'a> {
    ArrayItems(&'a anon::Type),
    CustomScc(flat::CustomTypeSccId),
}

#[derive(Clone, Debug)]
pub struct FoldPoint<'a> {
    pub exclude: OrdSet<flat::CustomTypeSccId>,
    pub kind: FoldPointKind<'a>,
}

// TODO: We currently introduce fold points even when their associated set of sub-paths is empty.
// For example, for the type `Array Int` we generate a fold point at the path `[ArrayMembers]`, even
// though `Int` contains no heap-cell names of its own.
//
// This is fine from a correctness standpoint, but it incurs a performance cost, and may be
// confusing during debugging.
pub fn get_fold_points_in<'a>(
    type_defs: &'a flat::CustomTypes,
    type_: &'a anon::Type,
) -> Vec<(annot::FieldPath, FoldPoint<'a>)> {
    let mut points = Vec::new();
    add_points_from_type(type_defs, &mut points, &OrdSet::new(), type_, Vector::new());
    return points;

    fn add_points_from_type<'a>(
        type_defs: &'a flat::CustomTypes,
        points: &mut Vec<(annot::FieldPath, FoldPoint<'a>)>,
        typedefs_on_path: &OrdSet<flat::CustomTypeSccId>,
        type_: &'a anon::Type,
        prefix: annot::FieldPath,
    ) {
        match type_ {
            anon::Type::Bool | anon::Type::Num(_) => {}
            anon::Type::Array(item_type) | anon::Type::HoleArray(item_type) => {
                let mut new_prefix = prefix.clone();
                new_prefix.push_back(annot::Field::ArrayMembers);

                // The array's elements are a fold point
                points.push((
                    new_prefix.clone(),
                    FoldPoint {
                        exclude: typedefs_on_path.clone(),
                        kind: FoldPointKind::ArrayItems(item_type),
                    },
                ));

                add_points_from_type(type_defs, points, typedefs_on_path, item_type, new_prefix);
            }
            anon::Type::Tuple(item_types) => {
                for (i, item_type) in item_types.iter().enumerate() {
                    add_points_from_type(
                        type_defs,
                        points,
                        typedefs_on_path,
                        item_type,
                        prefix.clone().add_back(annot::Field::Field(i)),
                    );
                }
            }
            anon::Type::Variants(variant_types) => {
                for (variant, variant_type) in variant_types {
                    add_points_from_type(
                        type_defs,
                        points,
                        typedefs_on_path,
                        variant_type,
                        prefix.clone().add_back(annot::Field::Variant(variant)),
                    );
                }
            }
            anon::Type::Boxed(content_type) => add_points_from_type(
                type_defs,
                points,
                typedefs_on_path,
                content_type,
                prefix.add_back(annot::Field::Boxed),
            ),
            anon::Type::Custom(id) => {
                let scc_id = type_defs.types[id].scc;
                if !typedefs_on_path.contains(&scc_id) {
                    let mut sub_typedefs_on_path = typedefs_on_path.clone();
                    sub_typedefs_on_path.insert(scc_id);

                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(annot::Field::CustomScc(scc_id, *id));

                    // This SCC induces a fold point
                    points.push((
                        new_prefix.clone(),
                        FoldPoint {
                            exclude: sub_typedefs_on_path.clone(),
                            kind: FoldPointKind::CustomScc(scc_id),
                        },
                    ));

                    for scc_type in &type_defs.sccs[scc_id] {
                        add_points_from_type(
                            type_defs,
                            points,
                            &sub_typedefs_on_path,
                            &type_defs.types[scc_type].content,
                            new_prefix.clone().add_back(annot::Field::Custom(*scc_type)),
                        );
                    }
                }
            }
        }
    }
}

/// See `get_names_in_excluding`.
pub fn get_names_in<'a>(
    type_defs: &'a flat::CustomTypes,
    type_: &'a anon::Type,
) -> Vec<(annot::FieldPath, &'a anon::Type)> {
    get_names_in_excluding(type_defs, type_, &OrdSet::new())
}

pub fn get_sub_names_in<'a>(
    type_defs: &'a flat::CustomTypes,
    fold_point: &FoldPoint<'a>,
) -> Vec<(annot::SubPath, &'a anon::Type)> {
    match &fold_point.kind {
        FoldPointKind::ArrayItems(item_type) => {
            get_names_in_excluding(type_defs, item_type, &fold_point.exclude)
                .into_iter()
                .map(|(path, type_)| (annot::SubPath(path), type_))
                .collect()
        }
        FoldPointKind::CustomScc(scc_id) => {
            let mut sub_names = Vec::new();
            for scc_type in &type_defs.sccs[*scc_id] {
                sub_names.extend(
                    get_names_in_excluding(
                        type_defs,
                        &type_defs.types[scc_type].content,
                        &fold_point.exclude,
                    )
                    .into_iter()
                    .map(|(path, type_)| {
                        (
                            annot::SubPath(path.add_front(annot::Field::Custom(*scc_type))),
                            type_,
                        )
                    }),
                );
            }
            sub_names
        }
    }
}

// Compute the fields in `type_` at which there is a heap reference participating in RC elision.
//
// This function differs from `get_names_in_excluding` in that it considers *all* heap structures,
// not only those which participate in mutation optimization.  In particular,
// `get_names_in_excluding` does not include paths to boxes, whereas this function does.
//
// This includes both top-level stack references (which are directly retained and released) and heap
// references inside other heap structures (which are tracked for the purpose of determining when
// it's safe for an item access to be borrowed rather than owned).
pub fn get_refs_in_excluding<'a>(
    type_defs: &'a flat::CustomTypes,
    type_: &'a anon::Type,
    exclude: &OrdSet<flat::CustomTypeSccId>,
) -> Vec<(annot::FieldPath, &'a anon::Type)> {
    let mut refs = Vec::new();
    add_refs_from_type(type_defs, &mut refs, exclude, type_, Vector::new());
    return refs;

    // Recursively appends paths to refs in `type_` to `refs`
    fn add_refs_from_type<'a>(
        type_defs: &'a flat::CustomTypes,
        refs: &mut Vec<(annot::FieldPath, &'a anon::Type)>,
        typedefs_on_path: &OrdSet<flat::CustomTypeSccId>,
        type_: &'a anon::Type,
        prefix: annot::FieldPath,
    ) {
        match type_ {
            anon::Type::Bool | anon::Type::Num(_) => {}
            anon::Type::Array(item_type) | anon::Type::HoleArray(item_type) => {
                // The array itself:
                refs.push((prefix.clone(), type_));
                // The refs in elements of the array:
                add_refs_from_type(
                    type_defs,
                    refs,
                    typedefs_on_path,
                    item_type,
                    prefix.add_back(annot::Field::ArrayMembers),
                );
            }
            anon::Type::Tuple(item_types) => {
                for (i, item_type) in item_types.iter().enumerate() {
                    add_refs_from_type(
                        type_defs,
                        refs,
                        typedefs_on_path,
                        item_type,
                        prefix.clone().add_back(annot::Field::Field(i)),
                    );
                }
            }
            anon::Type::Variants(variant_types) => {
                for (variant, variant_type) in variant_types {
                    add_refs_from_type(
                        type_defs,
                        refs,
                        typedefs_on_path,
                        variant_type,
                        prefix.clone().add_back(annot::Field::Variant(variant)),
                    );
                }
            }
            anon::Type::Boxed(content_type) => {
                // The box itself:
                refs.push((prefix.clone(), type_));
                // The refs inside the box:
                add_refs_from_type(
                    type_defs,
                    refs,
                    typedefs_on_path,
                    content_type,
                    prefix.add_back(annot::Field::Boxed),
                );
            }
            anon::Type::Custom(id) => {
                let scc_id = type_defs.types[id].scc;
                if !typedefs_on_path.contains(&scc_id) {
                    let mut sub_typedefs_on_path = typedefs_on_path.clone();
                    sub_typedefs_on_path.insert(scc_id);
                    for scc_type in &type_defs.sccs[scc_id] {
                        add_refs_from_type(
                            type_defs,
                            refs,
                            &sub_typedefs_on_path,
                            &type_defs.types[scc_type].content,
                            prefix
                                .clone()
                                .add_back(annot::Field::CustomScc(scc_id, *id))
                                .add_back(annot::Field::Custom(*scc_type)),
                        );
                    }
                }
            }
        }
    }
}

/// See `get_refs_in_excluding`.
pub fn get_refs_in<'a>(
    type_defs: &'a flat::CustomTypes,
    type_: &'a anon::Type,
) -> Vec<(annot::FieldPath, &'a anon::Type)> {
    get_refs_in_excluding(type_defs, type_, &OrdSet::new())
}

pub fn split_at_fold(
    scc: flat::CustomTypeSccId,
    custom: first_ord::CustomTypeId,
    path: annot::FieldPath,
) -> (annot::FieldPath, first_ord::CustomTypeId, annot::SubPath) {
    match path
        .iter()
        .enumerate()
        .find(|(_, field)| matches!(field, annot::Field::CustomScc(scc_id, _) if *scc_id == scc))
    {
        Some((split_point, _)) => {
            let (fold_point, sub_path) = path.split_at(split_point + 1);
            if let Some(annot::Field::Custom(id)) = sub_path.get(0) {
                (fold_point, *id, annot::SubPath(sub_path.skip(1)))
            } else {
                panic!(
                    "Expected a Custom field after CustomScc field in {:?}",
                    fold_point
                );
            }
        }
        None => (Vector::new(), custom, annot::SubPath(path)),
    }
}

pub fn split_fold_at_fold(
    scc: flat::CustomTypeSccId,
    custom: first_ord::CustomTypeId,
    path: annot::FieldPath,
) -> annot::FieldPath {
    match path
        .iter()
        .enumerate()
        .find(|(_, field)| matches!(field, annot::Field::CustomScc(scc_id, _) if *scc_id == scc))
    {
        Some((split_point, _)) => path.split_at(split_point + 1).1,
        None => path.add_front(annot::Field::Custom(custom)),
    }
}

pub fn group_unfolded_names_by_folded_form<'a>(
    type_defs: &'a flat::CustomTypes,
    custom: first_ord::CustomTypeId,
) -> BTreeMap<annot::SubPath, Vec<annot::FieldPath>> {
    let mut groups = BTreeMap::<_, Vec<_>>::new();
    for (path, _) in get_names_in(type_defs, &type_defs.types[custom].content) {
        let (_fold_point, in_custom, sub_path) =
            split_at_fold(type_defs.types[custom].scc, custom, path.clone());
        groups
            .entry(annot::SubPath(
                sub_path.0.add_front(annot::Field::Custom(in_custom)),
            ))
            .or_default()
            .push(path.clone());
    }
    groups
}

pub fn split_at_all_fold_points(
    path: &annot::FieldPath,
) -> BTreeMap<annot::FieldPath, annot::SubPath> {
    path.iter()
        .enumerate()
        .filter_map(|(i, field)| match field {
            annot::Field::CustomScc(_, _) | annot::Field::ArrayMembers => {
                let (fold_point, sub_path) = path.clone().split_at(i + 1);
                Some((fold_point, annot::SubPath(sub_path)))
            }
            _ => None,
        })
        .collect()
}

pub fn translate_callee_cond(
    arg_id: flat::LocalId,
    arg_aliases: &OrdMap<annot::FieldPath, annot::LocalAliases>,
    arg_folded_aliases: &OrdMap<annot::FieldPath, annot::FoldedAliases>,
    callee_cond: &annot::AliasCondition,
) -> Disj<annot::AliasCondition> {
    match callee_cond {
        annot::AliasCondition::AliasInArg(arg_pair) => {
            let annot::ArgName(arg_pair_fst) = arg_pair.fst();
            let annot::ArgName(arg_pair_snd) = arg_pair.snd();

            arg_aliases[arg_pair_fst]
                .aliases
                .get(&(arg_id, arg_pair_snd.clone()))
                .cloned()
                .unwrap_or_default()
        }

        annot::AliasCondition::FoldedAliasInArg(annot::ArgName(fold_point), sub_path_pair) => {
            arg_folded_aliases[fold_point]
                .inter_elem_aliases
                .get(sub_path_pair)
                .cloned()
                .unwrap_or_default()
        }
    }
}

pub fn translate_callee_cond_disj(
    arg_id: flat::LocalId,
    arg_aliases: &OrdMap<annot::FieldPath, annot::LocalAliases>,
    arg_folded_aliases: &OrdMap<annot::FieldPath, annot::FoldedAliases>,
    callee_cond: &Disj<annot::AliasCondition>,
) -> Disj<annot::AliasCondition> {
    callee_cond
        .flat_map(|cond| translate_callee_cond(arg_id, arg_aliases, arg_folded_aliases, cond))
}
