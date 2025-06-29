use crate::code_gen::fountain_pen::{Context, ProfileRc, Scope, Tal};
use crate::code_gen::{gen_rc_op, low_type_in_context, DerivedRcOp, Globals, Instances};
use crate::data::mode_annot_ast::Mode;
use crate::data::rc_specialized_ast::ModeScheme;

const F_REFCOUNT: u32 = 0; // has type u64
const F_ITEM: u32 = 1; // has type T

pub fn rc_ptr_t<T: Context>(context: &T) -> T::Type {
    context.ptr_t()
}

pub trait RcBuiltin<T: Context>: Clone {
    fn define(&self, globals: &Globals<T>, instances: &mut Instances<T>);

    fn mode(&self) -> Mode;
    fn item_scheme(&self) -> &ModeScheme;

    fn item_t(&self) -> T::Type;
    fn rc_t(&self) -> T::Type;

    fn new(&self) -> T::FunctionValue;
    fn get(&self) -> T::FunctionValue;
    fn retain(&self) -> T::FunctionValue;
    fn derived_retain(&self) -> T::FunctionValue;
    fn release(&self) -> T::FunctionValue;
}

#[derive(Clone, Debug)]
pub struct RcBuiltinImpl<T: Context> {
    mode: Mode,
    item_scheme: ModeScheme,

    // related types
    item_t: T::Type,
    rc_t: T::Type,

    // public API
    new: T::FunctionValue,
    get: T::FunctionValue,
    retain: T::FunctionValue,
    derived_retain: T::FunctionValue,
    release: T::FunctionValue,
}

impl<T: Context> RcBuiltinImpl<T> {
    pub fn declare(globals: &Globals<T>, scheme: &ModeScheme) -> Self {
        let context = &globals.context;

        let ModeScheme::Boxed(mode, item_scheme) = scheme else {
            panic!();
        };

        let item_type = low_type_in_context(globals, &item_scheme.as_type());

        let i64_t = context.i64_t();
        let item_ptr_t = context.ptr_t();

        let rc_t = context.struct_t(&[i64_t, item_type]);
        let rc_ptr_t = context.ptr_t();

        let new = context.declare_func("builtin_rc_new", &[item_type], Some(rc_ptr_t));

        let get = context.declare_func("builtin_rc_get", &[rc_ptr_t], Some(item_ptr_t));

        let retain = context.declare_func("builtin_rc_retain", &[rc_ptr_t], None);

        let derived_retain = context.declare_func("builtin_rc_derived_retain", &[rc_ptr_t], None);

        let release = context.declare_func("builtin_rc_release", &[rc_ptr_t], None);

        Self {
            mode: *mode,
            item_scheme: (**item_scheme).clone(),
            item_t: item_type,
            rc_t,
            new,
            get,
            retain,
            derived_retain,
            release,
        }
    }
}

impl<T: Context> RcBuiltin<T> for RcBuiltinImpl<T> {
    fn define(&self, globals: &Globals<T>, instances: &mut Instances<T>) {
        let context = &globals.context;
        let i64_t = context.i64_t();

        // define 'new'
        {
            let s = context.scope(self.new);
            let item = s.arg(0);

            let rc = s.malloc(s.usize(1), self.rc_t);
            s.arrow_set(self.rc_t, rc, F_REFCOUNT, s.i64(1));
            s.arrow_set(self.rc_t, rc, F_ITEM, item);
            s.ret(rc);
        }

        // define 'get'
        {
            let s = context.scope(self.get);
            let rc = s.arg(0);
            s.ret(s.gep(self.rc_t, rc, F_ITEM));
        }

        // define 'retain'
        {
            let s = context.scope(self.retain);
            let rc = s.arg(0);

            if let Some(prof_rc) = context.tal().prof_rc() {
                s.call_void(prof_rc.record_retain(), &[]);
            }

            let new_refcount = s.add(s.arrow(self.rc_t, i64_t, rc, F_REFCOUNT), s.i64(1));
            s.arrow_set(self.rc_t, rc, F_REFCOUNT, new_refcount);

            s.ret_void();
        }

        // define 'derived_retain'
        {
            let s = context.scope(self.derived_retain);
            let rc = s.arg(0);

            if self.mode == Mode::Owned {
                if let Some(prof_rc) = context.tal().prof_rc() {
                    s.call_void(prof_rc.record_retain(), &[]);
                }

                let new_refcount = s.add(s.arrow(self.rc_t, i64_t, rc, F_REFCOUNT), s.i64(1));
                s.arrow_set(self.rc_t, rc, F_REFCOUNT, new_refcount);
            }

            s.ret_void();
        }

        // define 'release'
        {
            let s = context.scope(self.release);
            let rc = s.arg(0);

            if self.mode == Mode::Owned {
                if let Some(prof_rc) = context.tal().prof_rc() {
                    s.call_void(prof_rc.record_release(), &[]);
                }

                let new_refcount = s.sub(s.arrow(self.rc_t, i64_t, rc, F_REFCOUNT), s.i64(1));
                s.arrow_set(self.rc_t, rc, F_REFCOUNT, new_refcount);

                s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                    gen_rc_op(
                        DerivedRcOp::Release,
                        s,
                        instances,
                        globals,
                        &self.item_scheme,
                        s.ptr_get(self.item_t, s.gep(self.rc_t, rc, F_ITEM)),
                    );

                    s.free(rc);
                });
            }

            s.ret_void();
        }
    }

    fn mode(&self) -> Mode {
        self.mode
    }

    fn item_scheme(&self) -> &ModeScheme {
        &self.item_scheme
    }

    fn item_t(&self) -> <T as Context>::Type {
        self.item_t
    }

    fn rc_t(&self) -> <T as Context>::Type {
        self.rc_t
    }

    fn new(&self) -> <T as Context>::FunctionValue {
        self.new
    }

    fn get(&self) -> <T as Context>::FunctionValue {
        self.get
    }

    fn retain(&self) -> <T as Context>::FunctionValue {
        self.retain
    }

    fn derived_retain(&self) -> <T as Context>::FunctionValue {
        self.derived_retain
    }

    fn release(&self) -> <T as Context>::FunctionValue {
        self.release
    }
}
