use im_rc::Vector;

use crate::data::alias_annot_ast::{Field, FieldPath, SubPath};
use crate::data::anon_sum_ast::Type;
use crate::data::first_order_ast::CustomTypeId;
use crate::data::mode_annot_ast::{StackField, StackPath};
use crate::util::id_vec::IdVec;
use crate::util::im_rc_ext::VectorExtensions;

impl From<StackField> for Field {
    fn from(field: StackField) -> Field {
        match field {
            StackField::Field(idx) => Field::Field(idx),
            StackField::Variant(variant) => Field::Variant(variant),
            StackField::Custom(custom) => Field::Custom(custom),
        }
    }
}

pub fn to_field_path(path: &StackPath) -> FieldPath {
    path.iter().cloned().map(Into::into).collect()
}

pub fn to_stack_path(path: &FieldPath) -> Option<StackPath> {
    path.iter()
        .map(|field| match field {
            &Field::Field(idx) => Some(StackField::Field(idx)),
            &Field::Variant(variant) => Some(StackField::Variant(variant)),
            &Field::Custom(custom) => Some(StackField::Custom(custom)),
            _ => None,
        })
        .collect()
}

pub fn split_stack_heap(path: FieldPath) -> (StackPath, SubPath) {
    match path.iter().enumerate().find(|(_, field)| match field {
        Field::Boxed | Field::ArrayMembers => true,
        Field::Field(_) | Field::Variant(_) | Field::Custom(_) => false,
    }) {
        Some((split_point, _)) => {
            let (stack_path, heap_path) = path.split_at(split_point);
            (
                to_stack_path(&stack_path)
                    .expect("all field before the split point should be stack fields"),
                SubPath(heap_path),
            )
        }
        None => (
            to_stack_path(&path).expect("all fields in the path should be stack fields"),
            SubPath(Vector::new()),
        ),
    }
}

pub fn stack_paths_in(typedefs: &IdVec<CustomTypeId, Type>, root: &Type) -> Vec<StackPath> {
    fn add_paths(
        typedefs: &IdVec<CustomTypeId, Type>,
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
                add_paths(
                    typedefs,
                    &typedefs[custom],
                    prefix.add_back(StackField::Custom(*custom)),
                    paths,
                );
            }
        }
    }

    let mut paths = Vec::new();
    add_paths(typedefs, root, Vector::new(), &mut paths);
    paths
}
