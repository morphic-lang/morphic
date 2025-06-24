use crate::code_gen::fountain_pen::Context;
use crate::code_gen::{Globals, Instances};

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
