use crate::code_gen::array::ArrayImpl;
use crate::code_gen::fountain_pen::{Context, ProfileRc, Scope, Tal};
use crate::code_gen::{low_type_in_context, Globals, Instances};
use crate::data::mode_annot_ast::Mode;
use crate::data::rc_specialized_ast::ModeScheme;

pub fn zero_sized_array_t<T: Context>(context: &T) -> T::Type {
    return context.i64_t();
}

pub fn zero_sized_hole_array_t<T: Context>(context: &T) -> T::Type {
    return context.i64_t();
}

#[derive(Clone, Debug)]
pub struct ZeroSizedArrayImpl<T: Context> {
    mode: Mode,

    item_t: T::Type,
    array_t: T::Type,
    hole_array_t: T::Type,

    new: T::FunctionValue,
    get: T::FunctionValue,
    extract: T::FunctionValue,
    len: T::FunctionValue,
    push: T::FunctionValue,
    pop: T::FunctionValue,
    replace: T::FunctionValue,
    reserve: T::FunctionValue,

    retain_array: T::FunctionValue,
    derived_retain_array: T::FunctionValue,
    release_array: T::FunctionValue,

    retain_hole: T::FunctionValue,
    derived_retain_hole: T::FunctionValue,
    release_hole: T::FunctionValue,
}

impl<T: Context> ZeroSizedArrayImpl<T> {
    pub fn declare(globals: &Globals<T>, _instances: &Instances<T>, scheme: &ModeScheme) -> Self {
        let context = &globals.context;

        let (ModeScheme::Array(mode, item_scheme) | ModeScheme::HoleArray(mode, item_scheme)) =
            scheme
        else {
            panic!();
        };

        debug_assert!(globals.is_zero_sized(&item_scheme.as_type()));
        let item_t = low_type_in_context(globals, &item_scheme.as_type());

        let i64_t = context.i64_t();
        let array_t = i64_t;
        let hole_array_t = i64_t;

        // Convenience utilities
        let fun = |name: &str, ret: T::Type, args: &[T::Type]| {
            context.declare_func(&format!("builtin_zero_array_{}", name), args, Some(ret))
        };

        let void_fun = |name: &str, args: &[T::Type]| {
            context.declare_func(&format!("builtin_zero_array_{}", name), args, None)
        };

        let new = fun("new", array_t, &[]);

        let get = fun("get", item_t, &[array_t, i64_t]);

        let extract = fun(
            "extract",
            context.struct_t(&[item_t, hole_array_t]),
            &[array_t, i64_t],
        );

        let len = fun("len", i64_t, &[array_t]);

        let push = fun("push", array_t, &[array_t, item_t]);

        let pop = fun("pop", context.struct_t(&[array_t, item_t]), &[array_t]);

        let replace = fun("replace", array_t, &[hole_array_t, item_t]);

        let reserve = fun("reserve", array_t, &[array_t, i64_t]);

        let retain_array = void_fun("retain", &[array_t]);

        let derived_retain_array = void_fun("derived_retain", &[array_t]);

        let release_array = void_fun("release", &[array_t]);

        let retain_hole = void_fun("retain_hole", &[hole_array_t]);

        let derived_retain_hole = void_fun("derived_retain_hole", &[hole_array_t]);

        let release_hole = void_fun("release_hole", &[hole_array_t]);

        Self {
            mode: *mode,
            item_t,
            array_t,
            hole_array_t,
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

impl<T: Context> ArrayImpl<T> for ZeroSizedArrayImpl<T> {
    fn define(&self, globals: &Globals<T>, _instance: &mut Instances<T>) {
        let context = &globals.context;

        // define 'new'
        {
            let s = context.scope(self.new);
            s.ret(s.i64(0));
        }

        // define 'get'
        {
            let s = context.scope(self.get);
            let array = s.arg(0);
            let idx = s.arg(1);

            s.if_(s.uge(idx, array), |s| {
                s.panic(
                    "idx %d is out of bounds for array of length %d",
                    &[idx, array],
                )
            });

            s.ret(s.undef(self.item_t));
        }

        // define 'extract'
        {
            let s = context.scope(self.extract);
            let array = s.arg(0);
            let idx = s.arg(1);

            s.if_(s.uge(idx, array), |s| {
                s.panic(
                    "idx %d is out of bounds for array of length %d",
                    &[idx, array],
                )
            });

            s.ret(s.make_tup(&[s.undef(self.item_t), array]));
        }

        // define 'len'
        {
            let s = context.scope(self.len);
            let array = s.arg(0);
            s.ret(array);
        }

        // define 'push'
        {
            let s = context.scope(self.push);
            let array = s.arg(0);
            s.ret(s.add(array, s.i64(1)));
        }

        // define 'pop'
        {
            let s = context.scope(self.pop);
            let array = s.arg(0);

            s.if_(s.eq(array, s.i64(0)), |s| {
                s.panic("cannot pop array of length 0", &[]);
            });

            s.ret(s.make_tup(&[s.sub(array, s.i64(1)), s.undef(self.item_t)]));
        }

        // define 'replace'
        {
            let s = context.scope(self.replace);
            let hole = s.arg(0);
            // let item = s.arg(1); UNUSED ARGUMENT
            s.ret(hole);
        }

        // define 'reserve'
        {
            let s = context.scope(self.reserve);
            let me = s.arg(0);
            // let capacity = s.arg(1); UNUSED ARGUMENT
            s.ret(me);
        }

        if context.is_gc_on() {
            for func in [
                self.retain_array,
                self.derived_retain_array,
                self.release_array,
                self.retain_hole,
                self.derived_retain_hole,
                self.release_hole,
            ] {
                let s = context.scope(func);
                s.panic("cannot use rc operations in garbage collected mode\n", &[]);
                s.ret_void();
            }
        } else {
            // define 'retain_array'
            {
                let s = context.scope(self.retain_array);
                // let array = s.arg(0); UNUSED ARGUMENT

                if let Some(prof_rc) = context.tal().prof_rc() {
                    s.call_void(prof_rc.record_retain(), &[]);
                }

                s.ret_void();
            }

            // define 'derived_retain_array'
            {
                let s = context.scope(self.derived_retain_array);
                // let array = s.arg(0); UNUSED ARGUMENT

                if self.mode == Mode::Owned {
                    if let Some(prof_rc) = context.tal().prof_rc() {
                        s.call_void(prof_rc.record_retain(), &[]);
                    }
                }

                s.ret_void();
            }

            // define 'release_array'
            {
                let s = context.scope(self.release_array);
                // let array = s.arg(0); UNUSED ARGUMENT

                if let Some(prof_rc) = context.tal().prof_rc() {
                    s.call_void(prof_rc.record_release(), &[]);
                }

                s.ret_void();
            }

            // define 'retain_hole'
            {
                let s = context.scope(self.retain_hole);
                // let hole = s.arg(0); UNUSED ARGUMENT

                if let Some(prof_rc) = context.tal().prof_rc() {
                    s.call_void(prof_rc.record_retain(), &[]);
                }

                s.ret_void();
            }

            // define 'derived_retain_hole_array'
            {
                let s = context.scope(self.derived_retain_hole);
                // let array = s.arg(0); UNUSED ARGUMENT

                if self.mode == Mode::Owned {
                    if let Some(prof_rc) = context.tal().prof_rc() {
                        s.call_void(prof_rc.record_retain(), &[]);
                    }
                }

                s.ret_void();
            }

            // define 'release_hole'
            {
                let s = context.scope(self.release_hole);
                // let hole = s.arg(0); UNUSED ARGUMENT

                if let Some(prof_rc) = context.tal().prof_rc() {
                    s.call_void(prof_rc.record_release(), &[]);
                }

                s.ret_void();
            }
        }
    }

    fn item_type(&self) -> T::Type {
        self.item_t
    }

    fn array_type(&self) -> T::Type {
        self.array_t
    }

    fn hole_array_type(&self) -> T::Type {
        self.hole_array_t
    }

    fn new(&self) -> T::FunctionValue {
        self.new
    }

    fn get(&self) -> T::FunctionValue {
        self.get
    }

    fn extract(&self) -> T::FunctionValue {
        self.extract
    }

    fn len(&self) -> T::FunctionValue {
        self.len
    }

    fn push(&self) -> T::FunctionValue {
        self.push
    }

    fn pop(&self) -> T::FunctionValue {
        self.pop
    }

    fn replace(&self) -> T::FunctionValue {
        self.replace
    }

    fn reserve(&self) -> T::FunctionValue {
        self.reserve
    }

    fn retain_array(&self) -> T::FunctionValue {
        self.retain_array
    }

    fn derived_retain_array(&self) -> T::FunctionValue {
        self.derived_retain_array
    }

    fn release_array(&self) -> T::FunctionValue {
        self.release_array
    }

    fn retain_hole(&self) -> T::FunctionValue {
        self.retain_hole
    }

    fn derived_retain_hole(&self) -> T::FunctionValue {
        self.derived_retain_hole
    }

    fn release_hole(&self) -> T::FunctionValue {
        self.release_hole
    }
}
