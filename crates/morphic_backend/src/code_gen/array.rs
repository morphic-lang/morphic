use crate::code_gen::fountain_pen::{Context, Scope};
use crate::code_gen::{Globals, Instances};

// Some panics are part of the public API in the sense that the test suite expects them to occur
// under well-defined circumstances and have a particular message. We define those here.
pub mod panic {
    use super::*;

    pub fn pop_empty<S: Scope>(s: &S) {
        s.panic("pop: empty array\n", &[]);
    }

    pub fn index_out_of_bounds<S: Scope>(s: &S, idx: S::Value, len: S::Value) {
        s.panic(
            "index out of bounds: attempt to access item %lld of array with length %llu\n",
            &[idx, len],
        );
    }

    pub fn obtain_unique_alloc_failed<S: Scope>(s: &S, alloc_size: S::Value) {
        s.panic(
            "obtain_unique: failed to allocate %zu bytes\n",
            &[alloc_size],
        );
    }
}

pub trait ArrayImpl<T: Context> {
    fn define(&self, globals: &Globals<T>, instances: &mut Instances<T>);

    fn item_type(&self) -> T::Type;
    fn array_type(&self) -> T::Type;
    fn hole_array_type(&self) -> T::Type;

    fn new(&self) -> T::FunctionValue;
    fn get(&self) -> T::FunctionValue;
    fn extract(&self) -> T::FunctionValue;
    fn len(&self) -> T::FunctionValue;
    fn push(&self) -> T::FunctionValue;
    fn pop(&self) -> T::FunctionValue;
    fn replace(&self) -> T::FunctionValue;
    fn reserve(&self) -> T::FunctionValue;

    fn retain_array(&self) -> T::FunctionValue;
    fn derived_retain_array(&self) -> T::FunctionValue;
    fn release_array(&self) -> T::FunctionValue;

    fn retain_hole(&self) -> T::FunctionValue;
    fn derived_retain_hole(&self) -> T::FunctionValue;
    fn release_hole(&self) -> T::FunctionValue;
}

pub trait ArrayIoImpl<T: Context> {
    fn define(&self, globals: &Globals<T>);

    fn input(&self) -> T::FunctionValue;
    fn output(&self) -> T::FunctionValue;
    fn output_error(&self) -> T::FunctionValue;
}
