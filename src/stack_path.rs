use im_rc::{OrdSet, Vector};

use crate::data::alias_annot_ast::{Field, FieldPath};
use crate::data::anon_sum_ast::Type;
use crate::data::first_order_ast::CustomTypeId;
use crate::data::flat_ast::{CustomTypeSccId, CustomTypes};
use crate::data::mode_annot_ast::{StackField, StackPath};
use crate::util::im_rc_ext::VectorExtensions;

impl From<StackField> for Field {
    fn from(field: StackField) -> Field {
        match field {
            StackField::Field(idx) => Field::Field(idx),
            StackField::Variant(variant) => Field::Variant(variant),
            StackField::CustomScc(scc, custom) => Field::CustomScc(scc, custom),
            StackField::Custom(custom) => Field::Custom(custom),
        }
    }
}

pub fn to_field_path(path: &StackPath) -> FieldPath {
    path.iter().cloned().map(Into::into).collect()
}

fn to_stack_path(path: &FieldPath) -> Option<StackPath> {
    path.iter()
        .map(|field| match field {
            &Field::Field(idx) => Some(StackField::Field(idx)),
            &Field::Variant(variant) => Some(StackField::Variant(variant)),
            &Field::CustomScc(scc, custom) => Some(StackField::CustomScc(scc, custom)),
            &Field::Custom(custom) => Some(StackField::Custom(custom)),
            _ => None,
        })
        .collect()
}

#[derive(Clone, Debug)]
pub enum PathTruncation {
    Stack(StackPath),
    Heap(Vec<StackPath>),
}

impl PathTruncation {
    pub fn stack_paths(self) -> Vec<StackPath> {
        match self {
            PathTruncation::Stack(stack_path) => vec![stack_path],
            PathTruncation::Heap(stack_paths) => stack_paths,
        }
    }
}

#[deprecated]
pub fn split_stack_heap_3(typedefs: &CustomTypes, path: FieldPath) -> PathTruncation {
    for (i, &field) in path.iter().enumerate() {
        match field {
            Field::Boxed | Field::ArrayMembers => {
                let (stack_path, _) = path.split_at(i);
                return PathTruncation::Heap(vec![to_stack_path(&stack_path).unwrap()]);
            }
            Field::CustomScc(_, entry_custom_id) if matches!(path[i + 1], Field::Custom(inner_custom_id) if inner_custom_id != entry_custom_id) =>
            {
                debug_assert!(matches!(path[i + 1], Field::Custom(_)));
                // Any content inside other custom types in the same SCC as 'type_' will
                // necessarily be stored on the heap.
                //
                // We over-approximate the relevant stack paths by simply taking all stack paths
                // in 'type_'.
                //
                // TODO: This is an unecessarily coarse approximation! We should return just the
                // stack paths that actually recursively mention other custom types in the SCC.
                let prefix = path.split_at(i).0;
                return PathTruncation::Heap(
                    #[allow(deprecated)]
                    stack_paths_in(typedefs, &Type::Custom(entry_custom_id))
                        .into_iter()
                        .map(|stack_path| to_stack_path(&prefix).unwrap() + stack_path)
                        .collect(),
                );
            }
            Field::Field(_) | Field::Variant(_) | Field::CustomScc(_, _) | Field::Custom(_) => {}
        }
    }

    PathTruncation::Stack(to_stack_path(&path).unwrap())
}

pub fn split_stack_heap_4(typedefs: &CustomTypes, path: FieldPath) -> PathTruncation {
    for (i, &field) in path.iter().enumerate() {
        match field {
            Field::Boxed | Field::ArrayMembers => {
                let (stack_path, _) = path.split_at(i);
                return PathTruncation::Heap(vec![to_stack_path(&stack_path).unwrap()]);
            }
            Field::Field(_) | Field::Variant(_) | Field::CustomScc(_, _) | Field::Custom(_) => {}
        }
    }

    PathTruncation::Stack(to_stack_path(&path).unwrap())
}

#[deprecated]
pub fn stack_paths_in(typedefs: &CustomTypes, root: &Type) -> Vec<StackPath> {
    fn add_paths(
        typedefs: &CustomTypes,
        type_: &Type,
        prefix: StackPath,
        paths: &mut Vec<StackPath>,
    ) {
        match type_ {
            Type::Bool | Type::Num(_) => {}

            Type::Array(_) | Type::HoleArray(_) | Type::Boxed(_) => paths.push(prefix),

            Type::Tuple(items) => {
                for (idx, item) in items.iter().enumerate() {
                    add_paths(
                        typedefs,
                        item,
                        prefix.clone().add_back(StackField::Field(idx)),
                        paths,
                    );
                }
            }

            Type::Variants(variants) => {
                for (variant, content) in variants {
                    add_paths(
                        typedefs,
                        content,
                        prefix.clone().add_back(StackField::Variant(variant)),
                        paths,
                    );
                }
            }

            Type::Custom(custom) => {
                // We only need to add paths corresponding to one type out of the SCC, because there
                // is no way for a single stack value to contain multiple nested types from the same
                // SCC without any indirection.
                let scc_id = typedefs.types[custom].scc;
                add_paths(
                    typedefs,
                    &typedefs.types[custom].content,
                    prefix
                        .clone()
                        .add_back(StackField::CustomScc(scc_id, *custom))
                        .add_back(StackField::Custom(*custom)),
                    paths,
                );
            }
        }
    }

    let mut paths = Vec::new();
    add_paths(typedefs, root, Vector::new(), &mut paths);
    paths
}

pub fn stack_paths_in_excluding(
    typedefs: &CustomTypes,
    root: &Type,
    exclude: &OrdSet<CustomTypeSccId>,
) -> Vec<StackPath> {
    let mut paths = Vec::new();
    add_paths(typedefs, &mut paths, exclude, root, Vector::new());
    return paths;

    fn add_paths(
        typedefs: &CustomTypes,
        paths: &mut Vec<StackPath>,
        exclude: &OrdSet<CustomTypeSccId>,
        type_: &Type,
        prefix: StackPath,
    ) {
        match type_ {
            Type::Bool | Type::Num(_) => {}

            Type::Array(_) | Type::HoleArray(_) | Type::Boxed(_) => paths.push(prefix),

            Type::Tuple(items) => {
                for (idx, item) in items.iter().enumerate() {
                    add_paths(
                        typedefs,
                        paths,
                        exclude,
                        item,
                        prefix.clone().add_back(StackField::Field(idx)),
                    );
                }
            }

            Type::Variants(variants) => {
                for (variant, content) in variants {
                    add_paths(
                        typedefs,
                        paths,
                        exclude,
                        content,
                        prefix.clone().add_back(StackField::Variant(variant)),
                    );
                }
            }

            Type::Custom(custom) => {
                let scc_id = typedefs.types[custom].scc;
                if !exclude.contains(&scc_id) {
                    let mut sub_exclude = exclude.clone();
                    sub_exclude.insert(scc_id);
                    for scc_type in &typedefs.sccs[scc_id] {
                        add_paths(
                            typedefs,
                            paths,
                            &sub_exclude,
                            &typedefs.types[scc_type].content,
                            prefix
                                .clone()
                                .add_back(StackField::CustomScc(scc_id, *custom))
                                .add_back(StackField::Custom(*scc_type)),
                        );
                    }
                }
            }
        }
    }
}

pub fn stack_paths_in_2(typedefs: &CustomTypes, root: &Type) -> Vec<StackPath> {
    stack_paths_in_excluding(typedefs, root, &OrdSet::new())
}

pub fn unfold_to_unnormalized(typedefs: &CustomTypes, path: &StackPath) -> Vec<StackPath> {
    let mut paths = Vec::new();
    add_path(typedefs, Vector::new(), path.iter(), &mut paths);
    return paths;

    fn add_path(
        typedefs: &CustomTypes,
        prefix: StackPath,
        mut path: im_rc::vector::Iter<StackField>,
        paths: &mut Vec<StackPath>,
    ) {
        match path.next() {
            None => {
                paths.push(prefix);
            }
            Some(&StackField::Field(idx)) => {
                add_path(
                    typedefs,
                    prefix.clone().add_back(StackField::Field(idx)),
                    path,
                    paths,
                );
            }
            Some(&StackField::Variant(variant)) => {
                add_path(
                    typedefs,
                    prefix.clone().add_back(StackField::Variant(variant)),
                    path,
                    paths,
                );
            }
            Some(&StackField::CustomScc(scc, type_custom)) => {
                let path_custom = if let Some(&StackField::Custom(path_custom)) = path.next() {
                    path_custom
                } else {
                    panic!("malformed path")
                };
                if path_custom == type_custom {
                    add_path(
                        typedefs,
                        prefix
                            .clone()
                            .add_back(StackField::CustomScc(scc, type_custom))
                            .add_back(StackField::Custom(type_custom)),
                        path,
                        paths,
                    );
                } else {
                    let path = path.cloned().collect();
                    unfold(
                        typedefs,
                        &typedefs.types[type_custom].content,
                        path_custom,
                        &path,
                        prefix
                            .clone()
                            .add_back(StackField::CustomScc(scc, type_custom))
                            .add_back(StackField::Custom(type_custom)),
                        paths,
                    );
                }
            }
            Some(StackField::Custom(_)) => {
                panic!("malformed path");
            }
        }
    }

    fn unfold(
        typedefs: &CustomTypes,
        type_: &Type,
        target_custom: CustomTypeId,
        target_path: &StackPath,
        prefix: StackPath,
        paths: &mut Vec<StackPath>,
    ) {
        match type_ {
            Type::Bool | Type::Num(_) | Type::Array(_) | Type::HoleArray(_) | Type::Boxed(_) => {}

            Type::Tuple(items) => {
                for (idx, item) in items.iter().enumerate() {
                    unfold(
                        typedefs,
                        item,
                        target_custom,
                        target_path,
                        prefix.clone().add_back(StackField::Field(idx)),
                        paths,
                    );
                }
            }

            Type::Variants(variants) => {
                for (variant, content) in variants {
                    unfold(
                        typedefs,
                        content,
                        target_custom,
                        target_path,
                        prefix.clone().add_back(StackField::Variant(variant)),
                        paths,
                    );
                }
            }

            &Type::Custom(custom) => {
                let target_scc_id = typedefs.types[target_custom].scc;
                let scc_id = typedefs.types[custom].scc;
                if scc_id != target_scc_id {
                    return;
                }
                if custom == target_custom {
                    add_path(
                        typedefs,
                        prefix
                            .add_back(StackField::CustomScc(scc_id, custom))
                            .add_back(StackField::Custom(custom)),
                        target_path.iter(),
                        paths,
                    );
                } else {
                    unfold(
                        typedefs,
                        &typedefs.types[custom].content,
                        target_custom,
                        target_path,
                        prefix
                            .clone()
                            .add_back(StackField::CustomScc(scc_id, custom))
                            .add_back(StackField::Custom(custom)),
                        paths,
                    );
                }
            }
        }
    }
}
