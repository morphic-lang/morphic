use im_rc::{OrdMap, Vector};
use std::collections::{BTreeMap, BTreeSet};

use crate::data::alias_annot_ast as annot;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::util::disjunction::Disj;
use crate::util::id_vec::IdVec;
use crate::util::im_rc_ext::VectorExtensions;

// Computes the fields in `type_` at which there is a name
//
// Currently, a 'name' means a field containing a heap structure participating in mutation
// optimization (which includes arrays and hole arrays, but excludes boxes).
pub fn get_names_in_excluding<'a>(
    type_defs: &'a IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &'a anon::Type,
    mut exclude: BTreeSet<first_ord::CustomTypeId>,
) -> Vec<(annot::FieldPath, &'a anon::Type)> {
    let mut names = Vec::new();
    add_names_from_type(type_defs, &mut names, &mut exclude, type_, Vector::new());
    return names;

    // Recursively appends paths to names in `type_` to `names`
    fn add_names_from_type<'a>(
        type_defs: &'a IdVec<first_ord::CustomTypeId, anon::Type>,
        names: &mut Vec<(annot::FieldPath, &'a anon::Type)>,
        typedefs_on_path: &mut BTreeSet<first_ord::CustomTypeId>,
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
                if !typedefs_on_path.contains(id) {
                    typedefs_on_path.insert(*id);
                    add_names_from_type(
                        type_defs,
                        names,
                        typedefs_on_path,
                        &type_defs[id],
                        prefix.add_back(annot::Field::Custom(*id)),
                    );
                    // Remove if we added it
                    typedefs_on_path.remove(id);
                }
            }
        }
    }
}

// TODO: We currently introduce fold points even when their associated set of sub-paths is empty.
// For example, for the type `Array Int` we generate a fold point at the path `[ArrayMembers]`, even
// though `Int` contains no heap-cell names of its own.
//
// This is fine from a correctness standpoint, but it incurs a performance cost, and may be
// confusing during debugging.
pub fn get_fold_points_in<'a>(
    type_defs: &'a IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &'a anon::Type,
) -> Vec<(annot::FieldPath, &'a anon::Type)> {
    let mut points = Vec::new();
    add_points_from_type(
        type_defs,
        &mut points,
        &mut BTreeSet::new(),
        type_,
        Vector::new(),
    );
    return points;

    fn add_points_from_type<'a>(
        type_defs: &'a IdVec<first_ord::CustomTypeId, anon::Type>,
        points: &mut Vec<(annot::FieldPath, &'a anon::Type)>,
        typedefs_on_path: &mut BTreeSet<first_ord::CustomTypeId>,
        type_: &'a anon::Type,
        prefix: annot::FieldPath,
    ) {
        match type_ {
            anon::Type::Bool | anon::Type::Num(_) => {}
            anon::Type::Array(item_type) | anon::Type::HoleArray(item_type) => {
                let mut new_prefix = prefix.clone();
                new_prefix.push_back(annot::Field::ArrayMembers);

                // The array's elements are a fold point
                points.push((new_prefix.clone(), item_type));

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
                if !typedefs_on_path.contains(id) {
                    typedefs_on_path.insert(*id);

                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(annot::Field::Custom(*id));

                    // This is a fold point
                    points.push((new_prefix.clone(), &type_defs[id]));

                    add_points_from_type(
                        type_defs,
                        points,
                        typedefs_on_path,
                        &type_defs[id],
                        new_prefix,
                    );

                    // Remove if we added it
                    typedefs_on_path.remove(id);
                }
            }
        }
    }
}

/// See `get_names_in_excluding`.
pub fn get_names_in<'a>(
    type_defs: &'a IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &'a anon::Type,
) -> Vec<(annot::FieldPath, &'a anon::Type)> {
    get_names_in_excluding(type_defs, type_, BTreeSet::new())
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
    type_defs: &'a IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &'a anon::Type,
    mut exclude: BTreeSet<first_ord::CustomTypeId>,
) -> Vec<(annot::FieldPath, &'a anon::Type)> {
    let mut refs = Vec::new();
    add_refs_from_type(type_defs, &mut refs, &mut exclude, type_, Vector::new());
    return refs;

    // Recursively appends paths to refs in `type_` to `refs`
    fn add_refs_from_type<'a>(
        type_defs: &'a IdVec<first_ord::CustomTypeId, anon::Type>,
        refs: &mut Vec<(annot::FieldPath, &'a anon::Type)>,
        typedefs_on_path: &mut BTreeSet<first_ord::CustomTypeId>,
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
                if !typedefs_on_path.contains(id) {
                    typedefs_on_path.insert(*id);
                    add_refs_from_type(
                        type_defs,
                        refs,
                        typedefs_on_path,
                        &type_defs[id],
                        prefix.add_back(annot::Field::Custom(*id)),
                    );
                    // Remove if we added it
                    typedefs_on_path.remove(id);
                }
            }
        }
    }
}

/// See `get_refs_in_excluding`.
pub fn get_refs_in<'a>(
    type_defs: &'a IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &'a anon::Type,
) -> Vec<(annot::FieldPath, &'a anon::Type)> {
    get_refs_in_excluding(type_defs, type_, BTreeSet::new())
}

pub fn split_at_fold(
    to_fold: first_ord::CustomTypeId,
    path: annot::FieldPath,
) -> (annot::FieldPath, annot::SubPath) {
    match path.index_of(&annot::Field::Custom(to_fold)) {
        Some(split_point) => {
            let (fold_point, sub_path) = path.split_at(split_point + 1);
            (fold_point, annot::SubPath(sub_path))
        }
        None => (Vector::new(), annot::SubPath(path)),
    }
}

pub fn split_stack_heap(path: annot::FieldPath) -> (annot::FieldPath, annot::SubPath) {
    match path.iter().enumerate().find(|(_, field)| match field {
        annot::Field::Boxed | annot::Field::ArrayMembers => true,
        annot::Field::Field(_) | annot::Field::Variant(_) | annot::Field::Custom(_) => false,
    }) {
        Some((split_point, _)) => {
            let (stack_path, heap_path) = path.split_at(split_point);
            (stack_path, annot::SubPath(heap_path))
        }
        None => (path, annot::SubPath(Vector::new())),
    }
}

pub fn group_unfolded_names_by_folded_form(
    type_defs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    custom_id: first_ord::CustomTypeId,
) -> BTreeMap<annot::SubPath, Vec<annot::FieldPath>> {
    let mut groups = BTreeMap::<_, Vec<_>>::new();
    for (path, _) in get_names_in(type_defs, &type_defs[custom_id]) {
        let (_fold_point, sub_path) = split_at_fold(custom_id, path.clone());
        groups.entry(sub_path).or_default().push(path.clone());
    }
    groups
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

#[cfg(test)]
mod test {
    use super::*;
    use im_rc::vector;
    use std::collections::BTreeSet;

    #[test]
    fn test_get_names_in() {
        fn set<T: Ord>(v: impl IntoIterator<Item = T>) -> BTreeSet<T> {
            use std::iter::FromIterator;
            BTreeSet::from_iter(v)
        }
        let with_single_recursive_type =
            IdVec::from_items(vec![anon::Type::Variants(IdVec::from_items(vec![
                anon::Type::Tuple(vec![
                    anon::Type::Array(Box::new(anon::Type::Num(first_ord::NumType::Byte))),
                    anon::Type::Custom(first_ord::CustomTypeId(0)),
                ]),
                anon::Type::Num(first_ord::NumType::Byte),
                anon::Type::HoleArray(Box::new(anon::Type::Num(first_ord::NumType::Byte))),
                anon::Type::Tuple(vec![]),
            ]))]);
        let mapping: Vec<(
            IdVec<first_ord::CustomTypeId, anon::Type>,
            anon::Type,
            BTreeSet<annot::FieldPath>,
        )> = vec![
            // Types without names:
            (
                IdVec::new(),
                anon::Type::Tuple(vec![
                    anon::Type::Num(first_ord::NumType::Byte),
                    anon::Type::Num(first_ord::NumType::Float),
                ]),
                set(vec![]),
            ),
            (
                IdVec::from_items(vec![anon::Type::Variants(IdVec::from_items(vec![
                    anon::Type::Num(first_ord::NumType::Byte),
                    anon::Type::Tuple(vec![]),
                ]))]),
                anon::Type::Tuple(vec![anon::Type::Custom(first_ord::CustomTypeId(0))]),
                set(vec![]),
            ),
            // Types with names, no typedefs:
            (
                IdVec::new(),
                anon::Type::Array(Box::new(anon::Type::Num(first_ord::NumType::Byte))),
                set(vec![vector![]]),
            ),
            (
                IdVec::new(),
                anon::Type::Array(Box::new(anon::Type::Array(Box::new(anon::Type::Num(
                    first_ord::NumType::Int,
                ))))),
                set(vec![vector![], vector![annot::Field::ArrayMembers]]),
            ),
            // Recursive types:
            (
                IdVec::new(),
                anon::Type::Tuple(vec![
                    anon::Type::Num(first_ord::NumType::Float),
                    anon::Type::Array(Box::new(anon::Type::Tuple(vec![
                        anon::Type::Array(Box::new(anon::Type::Bool)),
                        anon::Type::Num(first_ord::NumType::Byte),
                        anon::Type::HoleArray(Box::new(anon::Type::Bool)),
                    ]))),
                ]),
                set(vec![
                    vector![annot::Field::Field(1)],
                    vector![
                        annot::Field::Field(1),
                        annot::Field::ArrayMembers,
                        annot::Field::Field(0)
                    ],
                    vector![
                        annot::Field::Field(1),
                        annot::Field::ArrayMembers,
                        annot::Field::Field(2)
                    ],
                ]),
            ),
            (
                with_single_recursive_type.clone(),
                anon::Type::Custom(first_ord::CustomTypeId(0)),
                set(vec![
                    vector![
                        annot::Field::Custom(first_ord::CustomTypeId(0)),
                        annot::Field::Variant(first_ord::VariantId(0)),
                        annot::Field::Field(0)
                    ],
                    vector![
                        annot::Field::Custom(first_ord::CustomTypeId(0)),
                        annot::Field::Variant(first_ord::VariantId(2))
                    ],
                ]),
            ),
            (
                with_single_recursive_type.clone(),
                anon::Type::Array(Box::new(anon::Type::Custom(first_ord::CustomTypeId(0)))),
                set(vec![
                    vector![],
                    vector![
                        annot::Field::ArrayMembers,
                        annot::Field::Custom(first_ord::CustomTypeId(0)),
                        annot::Field::Variant(first_ord::VariantId(0)),
                        annot::Field::Field(0)
                    ],
                    vector![
                        annot::Field::ArrayMembers,
                        annot::Field::Custom(first_ord::CustomTypeId(0)),
                        annot::Field::Variant(first_ord::VariantId(2))
                    ],
                ]),
            ),
        ];
        for (typedefs, type_, expected_names) in mapping {
            assert_eq!(
                set(get_names_in(&typedefs, &type_)
                    .into_iter()
                    .map(|(name, _type)| name)),
                expected_names
            );
        }
    }
}
