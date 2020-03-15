use crate::builtins::core::*;
use crate::builtins::fountain_pen::scope;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::FunctionValue;

pub enum ImplentationChoice {
    Flat,
    Persistent,
}

#[derive(Clone, Copy, Debug)]
pub struct ZeroSizedArrayBuiltin<'a> {
    // related types
    pub item_type: BasicTypeEnum<'a>,
    pub array_type: BasicTypeEnum<'a>,
    pub hole_array_type: BasicTypeEnum<'a>,

    // public API
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

pub fn declare<'a>(
    choice: ImplentationChoice,
    context: &'a Context,
    module: &Module<'a>,
    item_type: BasicTypeEnum<'a>,
) -> ZeroSizedArrayBuiltin<'a> {
    let i64_type = context.i64_type();
    let void_type = context.void_type();

    let array_type = i64_type.into();
    let hole_array_type = i64_type.into();

    let choice_name = match choice {
        ImplentationChoice::Flat => "flat",
        ImplentationChoice::Persistent => "pers",
    };

    // Convenience utilities
    let fun = |name: &str, ret: BasicTypeEnum<'a>, args: &[BasicTypeEnum<'a>]| {
        module.add_function(
            &format!("builtin_{}_array_{}", choice_name, name),
            ret.fn_type(args, false),
            Some(Linkage::Internal),
        )
    };

    let void_fun = |name: &str, args: &[BasicTypeEnum<'a>]| {
        module.add_function(
            &format!("builtin_{}_array_{}", choice_name, name),
            void_type.fn_type(args, false),
            Some(Linkage::Internal),
        )
    };

    let new = fun("new", array_type, &[]);

    let item = fun(
        "item",
        context
            .struct_type(&[item_type, hole_array_type], false)
            .into(),
        &[array_type.into(), i64_type.into()],
    );

    let len = fun("len", i64_type.into(), &[array_type.into()]);

    let push = fun(
        "push",
        array_type.into(),
        &[array_type.into(), item_type.into()],
    );

    let pop = fun(
        "pop",
        context
            .struct_type(&[array_type.into(), item_type], false)
            .into(),
        &[array_type.into()],
    );

    let replace = fun(
        "replace",
        array_type.into(),
        &[hole_array_type.into(), item_type.into()],
    );

    let retain_array = void_fun("retain", &[array_type.into()]);

    let release_array = void_fun("release", &[array_type.into()]);

    let retain_hole = void_fun("retain_hole", &[hole_array_type.into()]);

    let release_hole = void_fun("release_hole", &[hole_array_type.into()]);

    ZeroSizedArrayBuiltin {
        item_type,
        array_type,
        hole_array_type,

        new,
        item,
        len,
        push,
        pop,
        replace,
        retain_array,
        release_array,
        retain_hole,
        release_hole,
    }
}

pub fn define<'a>(builtin: &ZeroSizedArrayBuiltin, context: &'a Context, libc: &LibC<'a>) {
    // define 'new'
    {
        let s = scope(builtin.new, context);
        s.ret(s.i64(0));
    }

    // define 'item'
    {
        let s = scope(builtin.item, context);
        let array = s.arg(0);
        let idx = s.arg(1);

        s.if_(s.uge(idx, array), |s| {
            s.panic(
                "idx %d is out of bounds for array of length %d",
                &[idx, array],
                libc,
            )
        });

        s.ret(s.make_tup(&[s.undef(builtin.item_type), array]));
    }

    // define 'len'
    {
        let s = scope(builtin.len, context);
        let array = s.arg(0);
        s.ret(array);
    }

    // define 'push'
    {
        let s = scope(builtin.push, context);
        let array = s.arg(0);
        s.ret(s.add(array, s.i64(1)));
    }

    // define 'pop'
    {
        let s = scope(builtin.pop, context);
        let array = s.arg(0);

        s.if_(s.sub(array, s.i64(1)), |s| {
            s.panic("cannot pop array of length 0", &[], libc);
        });

        s.ret(s.make_tup(&[s.sub(array, s.i64(1)), s.undef(builtin.item_type)]));
    }

    // define 'replace'
    {
        let s = scope(builtin.replace, context);
        let hole = s.arg(0);
        // let item = s.arg(1); UNUSED ARGUMENT
        s.ret(hole);
    }

    // define 'retain_array'
    {
        let s = scope(builtin.retain_array, context);
        // let array = s.arg(0); UNUSED ARGUMENT
        s.ret_void();
    }

    // define 'release_array'
    {
        let s = scope(builtin.release_array, context);
        // let array = s.arg(0); UNUSED ARGUMENT
        s.ret_void();
    }

    // define 'retain_hole'
    {
        let s = scope(builtin.retain_hole, context);
        // let hole = s.arg(0); UNUSED ARGUMENT
        s.ret_void();
    }

    // define 'release_hole'
    {
        let s = scope(builtin.release_hole, context);
        // let hole = s.arg(0); UNUSED ARGUMENT
        s.ret_void();
    }
}
