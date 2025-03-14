use crate::data::mode_annot_ast::Mode;
use crate::data::rc_specialized_ast::ModeScheme;
use crate::llvm_gen::fountain_pen::scope;
use crate::llvm_gen::tal::{ProfileRc, Tal};
use crate::llvm_gen::{gen_rc_op, get_llvm_type, DerivedRcOp, Globals, Instances};
use inkwell::module::{Linkage, Module};
use inkwell::targets::TargetData;
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::FunctionValue;
use inkwell::AddressSpace;

const F_REFCOUNT: u32 = 0; // has type u64
const F_ITEM: u32 = 1; // has type T

pub fn rc_ptr_type<'a, 'b>(globals: &Globals<'a, 'b>) -> BasicTypeEnum<'a> {
    let i8_type = globals.context.i8_type();
    let rc_ptr_type = i8_type.ptr_type(AddressSpace::default());

    rc_ptr_type.into()
}

#[derive(Clone, Debug)]
pub struct RcBoxBuiltin<'a> {
    pub mode: Mode,
    pub item_scheme: ModeScheme,
    // related types
    pub item_type: BasicTypeEnum<'a>,
    pub rc_type: BasicTypeEnum<'a>,

    // public API
    pub new: FunctionValue<'a>,
    pub get: FunctionValue<'a>,
    pub retain: FunctionValue<'a>,
    pub derived_retain: FunctionValue<'a>,
    pub release: FunctionValue<'a>,
}

impl<'a> RcBoxBuiltin<'a> {
    pub fn declare(globals: &Globals<'a, '_>, module: &Module<'a>, scheme: &ModeScheme) -> Self {
        let ModeScheme::Boxed(mode, item_scheme) = scheme else {
            panic!();
        };

        let item_type = get_llvm_type(globals, &item_scheme.as_type());
        let context = globals.context;

        let void_type = context.void_type();
        let i64_t = context.i64_type();
        let item_ptr_type = item_type.ptr_type(AddressSpace::default());

        let rc_type = context.struct_type(&[i64_t.into(), item_type.into()], false);
        let rc_ptr_type = rc_type.ptr_type(AddressSpace::default());

        let new = module.add_function(
            "builtin_rc_new",
            rc_ptr_type.fn_type(&[item_type.into()], false),
            Some(Linkage::Internal),
        );

        let get = module.add_function(
            "builtin_rc_get",
            item_ptr_type.fn_type(&[rc_ptr_type.into()], false),
            Some(Linkage::Internal),
        );

        let retain = module.add_function(
            "builtin_rc_retain",
            void_type.fn_type(&[rc_ptr_type.into()], false),
            Some(Linkage::Internal),
        );

        let derived_retain = module.add_function(
            "builtin_rc_derived_retain",
            void_type.fn_type(&[rc_ptr_type.into()], false),
            Some(Linkage::Internal),
        );

        let release = module.add_function(
            "builtin_rc_release",
            void_type.fn_type(&[rc_ptr_type.into()], false),
            Some(Linkage::Internal),
        );

        Self {
            mode: *mode,
            item_scheme: (**item_scheme).clone(),
            item_type,
            rc_type: rc_type.into(),
            new,
            get,
            retain,
            derived_retain,
            release,
        }
    }

    pub fn define(
        &self,
        globals: &Globals<'a, '_>,
        instances: &mut Instances<'a>,
        target: &TargetData,
        tal: &Tal<'a>,
    ) {
        let context = globals.context;
        let i64_t = context.i64_type().as_basic_type_enum();

        // define 'new'
        {
            let s = scope(self.new, context, target);
            let item = s.arg(0);

            let rc = s.malloc(s.usize(1), self.rc_type, tal);
            s.arrow_set(self.rc_type, rc, F_REFCOUNT, s.i64(1));
            s.arrow_set(self.rc_type, rc, F_ITEM, item);
            s.ret(rc);
        }

        // define 'get'
        {
            let s = scope(self.get, context, target);
            let rc = s.arg(0);
            s.ret(s.gep(self.rc_type, rc, F_ITEM));
        }

        // define 'retain'
        {
            let s = scope(self.retain, context, target);
            let rc = s.arg(0);

            if let Some(ProfileRc { record_retain, .. }) = tal.prof_rc {
                s.call_void(record_retain, &[]);
            }

            let new_refcount = s.add(s.arrow(self.rc_type, i64_t, rc, F_REFCOUNT), s.i64(1));
            s.arrow_set(self.rc_type, rc, F_REFCOUNT, new_refcount);

            s.ret_void();
        }

        // define 'derived_retain'
        {
            let s = scope(self.derived_retain, context, target);
            let rc = s.arg(0);

            if self.mode == Mode::Owned {
                if let Some(ProfileRc { record_retain, .. }) = tal.prof_rc {
                    s.call_void(record_retain, &[]);
                }

                let new_refcount = s.add(s.arrow(self.rc_type, i64_t, rc, F_REFCOUNT), s.i64(1));
                s.arrow_set(self.rc_type, rc, F_REFCOUNT, new_refcount);
            }

            s.ret_void();
        }

        // define 'release'
        {
            let s = scope(self.release, context, target);
            let rc = s.arg(0);

            if self.mode == Mode::Owned {
                if let Some(ProfileRc { record_release, .. }) = tal.prof_rc {
                    s.call_void(record_release, &[]);
                }

                let new_refcount = s.sub(s.arrow(self.rc_type, i64_t, rc, F_REFCOUNT), s.i64(1));
                s.arrow_set(self.rc_type, rc, F_REFCOUNT, new_refcount);

                s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                    gen_rc_op(
                        DerivedRcOp::Release,
                        s.builder(),
                        instances,
                        globals,
                        s.func(),
                        &self.item_scheme,
                        s.ptr_get(self.item_type, s.gep(self.rc_type, rc, F_ITEM)),
                    );

                    if let Some(ProfileRc { memory_free, .. }) = tal.prof_rc {
                        s.call_void(memory_free, &[s.size(self.rc_type)]);
                    }

                    s.free(s.ptr_cast(s.i8_t(), rc), tal);
                });
            }

            s.ret_void();
        }
    }
}
