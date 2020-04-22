use crate::builtins::array::{ArrayImpl, ArrayInterface};
use crate::builtins::fountain_pen::scope;
use crate::builtins::libc::LibC;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::TargetData;
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::FunctionValue;

pub struct ZeroSizedArrayImpl<'a> {
    interface: ArrayInterface<'a>,
}

impl<'a> ZeroSizedArrayImpl<'a> {
    pub fn declare(
        context: &'a Context,
        _target: &TargetData,
        module: &Module<'a>,
        item_type: BasicTypeEnum<'a>,
    ) -> Self {
        let i64_type = context.i64_type();
        let void_type = context.void_type();

        let array_type = i64_type.into();
        let hole_array_type = i64_type.into();

        // Convenience utilities
        let fun = |name: &str, ret: BasicTypeEnum<'a>, args: &[BasicTypeEnum<'a>]| {
            module.add_function(
                &format!("builtin_zero_array_{}", name),
                ret.fn_type(args, false),
                Some(Linkage::Internal),
            )
        };

        let void_fun = |name: &str, args: &[BasicTypeEnum<'a>]| {
            module.add_function(
                &format!("builtin_zero_array_{}", name),
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

        let interface = ArrayInterface {
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
        };

        Self { interface }
    }
}

impl<'a> ArrayImpl<'a> for ZeroSizedArrayImpl<'a> {
    fn define(
        &self,
        context: &'a Context,
        target: &TargetData,
        libc: &LibC<'a>,
        item_retain: Option<FunctionValue<'a>>,
        item_release: Option<FunctionValue<'a>>,
    ) {
        assert!(item_retain.is_none());
        assert!(item_release.is_none());

        // define 'new'
        {
            let s = scope(self.interface.new, context, target);
            s.ret(s.i64(0));
        }

        // define 'item'
        {
            let s = scope(self.interface.item, context, target);
            let array = s.arg(0);
            let idx = s.arg(1);

            s.if_(s.uge(idx, array), |s| {
                s.panic(
                    "idx %d is out of bounds for array of length %d",
                    &[idx, array],
                    libc,
                )
            });

            s.ret(s.make_tup(&[s.undef(self.interface.item_type), array]));
        }

        // define 'len'
        {
            let s = scope(self.interface.len, context, target);
            let array = s.arg(0);
            s.ret(array);
        }

        // define 'push'
        {
            let s = scope(self.interface.push, context, target);
            let array = s.arg(0);
            s.ret(s.add(array, s.i64(1)));
        }

        // define 'pop'
        {
            let s = scope(self.interface.pop, context, target);
            let array = s.arg(0);

            s.if_(s.eq(array, s.i64(0)), |s| {
                s.panic("cannot pop array of length 0", &[], libc);
            });

            s.ret(s.make_tup(&[s.sub(array, s.i64(1)), s.undef(self.interface.item_type)]));
        }

        // define 'replace'
        {
            let s = scope(self.interface.replace, context, target);
            let hole = s.arg(0);
            // let item = s.arg(1); UNUSED ARGUMENT
            s.ret(hole);
        }

        // define 'retain_array'
        {
            let s = scope(self.interface.retain_array, context, target);
            // let array = s.arg(0); UNUSED ARGUMENT
            s.ret_void();
        }

        // define 'release_array'
        {
            let s = scope(self.interface.release_array, context, target);
            // let array = s.arg(0); UNUSED ARGUMENT
            s.ret_void();
        }

        // define 'retain_hole'
        {
            let s = scope(self.interface.retain_hole, context, target);
            // let hole = s.arg(0); UNUSED ARGUMENT
            s.ret_void();
        }

        // define 'release_hole'
        {
            let s = scope(self.interface.release_hole, context, target);
            // let hole = s.arg(0); UNUSED ARGUMENT
            s.ret_void();
        }
    }

    fn interface(&self) -> &ArrayInterface<'a> {
        &self.interface
    }
}
