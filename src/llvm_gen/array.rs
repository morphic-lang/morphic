use crate::llvm_gen::tal::Tal;
use inkwell::context::Context;
use inkwell::targets::TargetData;
use inkwell::types::BasicTypeEnum;
use inkwell::values::FunctionValue;

pub trait ArrayImpl<'a> {
    fn define(&self, context: &'a Context, target: &TargetData, tal: &Tal<'a>);

    fn item_type(&self) -> BasicTypeEnum<'a>;
    fn array_type(&self) -> BasicTypeEnum<'a>;
    fn hole_array_type(&self) -> BasicTypeEnum<'a>;

    fn new(&self) -> FunctionValue<'a>;
    fn get(&self) -> FunctionValue<'a>;
    fn extract(&self) -> FunctionValue<'a>;
    fn len(&self) -> FunctionValue<'a>;
    fn push(&self) -> FunctionValue<'a>;
    fn pop(&self) -> FunctionValue<'a>;
    fn replace(&self) -> FunctionValue<'a>;
    fn reserve(&self) -> FunctionValue<'a>;

    fn retain_array(&self) -> FunctionValue<'a>;
    fn derived_retain_array(&self) -> FunctionValue<'a>;
    fn release_array(&self) -> FunctionValue<'a>;

    fn retain_hole(&self) -> FunctionValue<'a>;
    fn derived_retain_hole(&self) -> FunctionValue<'a>;
    fn release_hole(&self) -> FunctionValue<'a>;
}
