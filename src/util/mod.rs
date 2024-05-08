#[macro_use]
pub mod lines;

pub mod id_gen;

pub mod local_context;

pub mod graph;

pub mod constraint_graph;

pub mod norm_pair;

pub mod disjunction;

pub mod instance_queue;

pub mod im_rc_ext;

pub mod inequality_graph;
pub mod inequality_graph2;

pub mod event_set;

pub mod progress_logger;

pub mod iter;

pub mod map_ext;

pub mod intern;

pub fn with_scope<T, R, F: for<'a> FnOnce(&'a mut Vec<T>) -> R>(vec: &mut Vec<T>, func: F) -> R {
    let old_len = vec.len();
    let result = func(vec);
    assert!(vec.len() >= old_len);
    vec.truncate(old_len);
    result
}
