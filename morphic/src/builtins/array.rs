use crate::builtins::tal::Tal;
use inkwell::context::Context;
use inkwell::targets::TargetData;
use inkwell::types::BasicTypeEnum;
use inkwell::values::FunctionValue;

#[derive(Clone, Copy, Debug)]
pub struct ArrayInterface<'a> {
    pub item_type: BasicTypeEnum<'a>,
    pub array_type: BasicTypeEnum<'a>,
    pub hole_array_type: BasicTypeEnum<'a>,

    pub new: FunctionValue<'a>,
    pub item: FunctionValue<'a>,
    pub len: FunctionValue<'a>,
    pub push: FunctionValue<'a>,
    pub pop: FunctionValue<'a>,
    pub replace: FunctionValue<'a>,
    pub retain_array: FunctionValue<'a>,
    pub release_array: FunctionValue<'a>,
    pub retain_hole: FunctionValue<'a>,
    pub release_hole: FunctionValue<'a>,
}

pub trait ArrayImpl<'a> {
    fn define(
        &self,
        context: &'a Context,
        target: &TargetData,
        tal: &Tal<'a>,
        item_retain: Option<FunctionValue<'a>>,
        item_release: Option<FunctionValue<'a>>,
    );

    fn interface(&self) -> &ArrayInterface<'a>;
}
