#[macro_use]
pub mod id_type;

pub mod id_vec;

pub mod constraint_graph;

pub mod norm_pair;

pub mod disjunction;

pub fn with_scope<T, R, F: for<'a> FnOnce(&'a mut Vec<T>) -> R>(vec: &mut Vec<T>, func: F) -> R {
    let old_len = vec.len();
    let result = func(vec);
    assert!(vec.len() >= old_len);
    vec.truncate(old_len);
    result
}
