use crate::data::mode_annot_ast::Mode;
use crate::data::rc_specialized_ast::ModeScheme;
use crate::llvm_gen::array::ArrayImpl;
use crate::llvm_gen::fountain_pen::scope;
use crate::llvm_gen::tal::{ProfileRc, Tal};
use crate::llvm_gen::{get_llvm_type, is_zero_sized, Globals, Instances};
use inkwell::module::Linkage;
use inkwell::targets::TargetData;
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum};
use inkwell::values::FunctionValue;

#[derive(Clone, Debug)]
pub struct ZeroSizedArrayImpl<'a> {
    mode: Mode,
    item_type: BasicTypeEnum<'a>,
    array_type: BasicTypeEnum<'a>,
    hole_array_type: BasicTypeEnum<'a>,
    new: FunctionValue<'a>,
    get: FunctionValue<'a>,
    extract: FunctionValue<'a>,
    len: FunctionValue<'a>,
    push: FunctionValue<'a>,
    pop: FunctionValue<'a>,
    replace: FunctionValue<'a>,
    reserve: FunctionValue<'a>,
    retain_array: FunctionValue<'a>,
    derived_retain_array: FunctionValue<'a>,
    release_array: FunctionValue<'a>,
    retain_hole: FunctionValue<'a>,
    derived_retain_hole: FunctionValue<'a>,
    release_hole: FunctionValue<'a>,
}

impl<'a> ZeroSizedArrayImpl<'a> {
    pub fn declare(
        globals: &Globals<'a, '_>,
        _instances: &Instances<'a>,
        scheme: &ModeScheme,
    ) -> Self {
        let context = globals.context;
        let module = globals.module;

        let (ModeScheme::Array(mode, item_scheme) | ModeScheme::HoleArray(mode, item_scheme)) =
            scheme
        else {
            panic!();
        };

        let item_type = get_llvm_type(globals, &item_scheme.as_type());

        debug_assert!(is_zero_sized(globals, &item_scheme.as_type()));
        let i64_type = context.i64_type();
        let void_type = context.void_type();

        let array_type = i64_type.into();
        let hole_array_type = i64_type.into();

        // Convenience utilities
        let fun = |name: &str, ret: BasicTypeEnum<'a>, args: &[BasicMetadataTypeEnum<'a>]| {
            module.add_function(
                &format!("builtin_zero_array_{}", name),
                ret.fn_type(args, false),
                Some(Linkage::Internal),
            )
        };

        let void_fun = |name: &str, args: &[BasicMetadataTypeEnum<'a>]| {
            module.add_function(
                &format!("builtin_zero_array_{}", name),
                void_type.fn_type(args, false),
                Some(Linkage::Internal),
            )
        };

        let new = fun("new", array_type, &[]);

        let get = fun(
            "get",
            item_type.into(),
            &[array_type.into(), i64_type.into()],
        );

        let extract = fun(
            "extract",
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

        let reserve = fun(
            "reserve",
            array_type.into(),
            &[array_type.into(), i64_type.into()],
        );

        let retain_array = void_fun("retain", &[array_type.into()]);

        let derived_retain_array = void_fun("derived_retain", &[array_type.into()]);

        let release_array = void_fun("release", &[array_type.into()]);

        let retain_hole = void_fun("retain_hole", &[hole_array_type.into()]);

        let derived_retain_hole = void_fun("derived_retain_hole", &[hole_array_type.into()]);

        let release_hole = void_fun("release_hole", &[hole_array_type.into()]);

        Self {
            mode: *mode,
            item_type,
            array_type,
            hole_array_type,
            new,
            get,
            extract,
            len,
            push,
            pop,
            replace,
            reserve,
            retain_array,
            derived_retain_array,
            release_array,
            retain_hole,
            derived_retain_hole,
            release_hole,
        }
    }
}

impl<'a> ArrayImpl<'a> for ZeroSizedArrayImpl<'a> {
    fn define(
        &self,
        globals: &Globals<'a, '_>,
        _instance: &mut Instances<'a>,
        target: &TargetData,
        tal: &Tal<'a>,
    ) {
        let context = globals.context;
        // define 'new'
        {
            let s = scope(self.new, context, target);
            s.ret(s.i64(0));
        }

        // define 'get'
        {
            let s = scope(self.get, context, target);
            let array = s.arg(0);
            let idx = s.arg(1);

            s.if_(s.uge(idx, array), |s| {
                s.panic(
                    "idx %d is out of bounds for array of length %d",
                    &[idx, array],
                    tal,
                )
            });

            s.ret(s.undef(self.item_type));
        }

        // define 'extract'
        {
            let s = scope(self.extract, context, target);
            let array = s.arg(0);
            let idx = s.arg(1);

            s.if_(s.uge(idx, array), |s| {
                s.panic(
                    "idx %d is out of bounds for array of length %d",
                    &[idx, array],
                    tal,
                )
            });

            s.ret(s.make_tup(&[s.undef(self.item_type), array]));
        }

        // define 'len'
        {
            let s = scope(self.len, context, target);
            let array = s.arg(0);
            s.ret(array);
        }

        // define 'push'
        {
            let s = scope(self.push, context, target);
            let array = s.arg(0);
            s.ret(s.add(array, s.i64(1)));
        }

        // define 'pop'
        {
            let s = scope(self.pop, context, target);
            let array = s.arg(0);

            s.if_(s.eq(array, s.i64(0)), |s| {
                s.panic("cannot pop array of length 0", &[], tal);
            });

            s.ret(s.make_tup(&[s.sub(array, s.i64(1)), s.undef(self.item_type)]));
        }

        // define 'replace'
        {
            let s = scope(self.replace, context, target);
            let hole = s.arg(0);
            // let item = s.arg(1); UNUSED ARGUMENT
            s.ret(hole);
        }

        // define 'reserve'
        {
            let s = scope(self.reserve, context, target);
            let me = s.arg(0);
            // let capacity = s.arg(1); UNUSED ARGUMENT
            s.ret(me);
        }

        // define 'retain_array'
        {
            let s = scope(self.retain_array, context, target);
            // let array = s.arg(0); UNUSED ARGUMENT

            if let Some(ProfileRc { record_retain, .. }) = tal.prof_rc {
                s.call_void(record_retain, &[]);
            }

            s.ret_void();
        }

        // define 'derived_retain_array'
        {
            let s = scope(self.derived_retain_array, context, target);
            // let array = s.arg(0); UNUSED ARGUMENT

            if self.mode == Mode::Owned {
                if let Some(ProfileRc { record_retain, .. }) = tal.prof_rc {
                    s.call_void(record_retain, &[]);
                }
            }

            s.ret_void();
        }

        // define 'release_array'
        {
            let s = scope(self.release_array, context, target);
            // let array = s.arg(0); UNUSED ARGUMENT

            if let Some(ProfileRc { record_release, .. }) = tal.prof_rc {
                s.call_void(record_release, &[]);
            }

            s.ret_void();
        }

        // define 'retain_hole'
        {
            let s = scope(self.retain_hole, context, target);
            // let hole = s.arg(0); UNUSED ARGUMENT

            if let Some(ProfileRc { record_retain, .. }) = tal.prof_rc {
                s.call_void(record_retain, &[]);
            }

            s.ret_void();
        }

        // define 'derived_retain_hole_array'
        {
            let s = scope(self.derived_retain_hole, context, target);
            // let array = s.arg(0); UNUSED ARGUMENT

            if self.mode == Mode::Owned {
                if let Some(ProfileRc { record_retain, .. }) = tal.prof_rc {
                    s.call_void(record_retain, &[]);
                }
            }

            s.ret_void();
        }

        // define 'release_hole'
        {
            let s = scope(self.release_hole, context, target);
            // let hole = s.arg(0); UNUSED ARGUMENT

            if let Some(ProfileRc { record_release, .. }) = tal.prof_rc {
                s.call_void(record_release, &[]);
            }

            s.ret_void();
        }
    }

    fn item_type(&self) -> BasicTypeEnum<'a> {
        self.item_type
    }

    fn array_type(&self) -> BasicTypeEnum<'a> {
        self.array_type
    }

    fn hole_array_type(&self) -> BasicTypeEnum<'a> {
        self.hole_array_type
    }

    fn new(&self) -> FunctionValue<'a> {
        self.new
    }

    fn get(&self) -> FunctionValue<'a> {
        self.get
    }

    fn extract(&self) -> FunctionValue<'a> {
        self.extract
    }

    fn len(&self) -> FunctionValue<'a> {
        self.len
    }

    fn push(&self) -> FunctionValue<'a> {
        self.push
    }

    fn pop(&self) -> FunctionValue<'a> {
        self.pop
    }

    fn replace(&self) -> FunctionValue<'a> {
        self.replace
    }

    fn reserve(&self) -> FunctionValue<'a> {
        self.reserve
    }

    fn retain_array(&self) -> FunctionValue<'a> {
        self.retain_array
    }

    fn derived_retain_array(&self) -> FunctionValue<'a> {
        self.derived_retain_array
    }

    fn release_array(&self) -> FunctionValue<'a> {
        self.release_array
    }

    fn retain_hole(&self) -> FunctionValue<'a> {
        self.retain_hole
    }

    fn derived_retain_hole(&self) -> FunctionValue<'a> {
        self.derived_retain_hole
    }

    fn release_hole(&self) -> FunctionValue<'a> {
        self.release_hole
    }
}
