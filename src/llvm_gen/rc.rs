use crate::llvm_gen::fountain_pen::scope;
use crate::llvm_gen::tal::{ProfileRc, Tal};
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::TargetData;
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::FunctionValue;
use inkwell::AddressSpace;

const F_REFCOUNT: u32 = 0; // has type u64
const F_ITEM: u32 = 1; // has type T

#[derive(Clone, Copy, Debug)]
pub struct RcBoxBuiltin<'a> {
    // related types
    pub item_type: BasicTypeEnum<'a>,
    pub rc_type: BasicTypeEnum<'a>,

    // public API
    pub new: FunctionValue<'a>,
    pub get: FunctionValue<'a>,
    pub retain: FunctionValue<'a>,
    pub release: FunctionValue<'a>,
}

impl<'a> RcBoxBuiltin<'a> {
    pub fn declare(
        context: &'a Context,
        module: &Module<'a>,
        item_type: BasicTypeEnum<'a>,
    ) -> Self {
        let void_type = context.void_type();
        let item_ptr_type = item_type.ptr_type(AddressSpace::default());

        let rc_type = context.opaque_struct_type("builtin_rc");
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

        let release = module.add_function(
            "builtin_rc_release",
            void_type.fn_type(&[rc_ptr_type.into()], false),
            Some(Linkage::Internal),
        );

        Self {
            item_type,
            rc_type: rc_type.into(),
            new,
            get,
            retain,
            release,
        }
    }

    pub fn define(
        &self,
        context: &'a Context,
        target: &TargetData,
        tal: &Tal<'a>,
        item_release: Option<FunctionValue<'a>>,
    ) {
        let i64_t = context.i64_type().as_basic_type_enum();

        self.rc_type
            .into_struct_type()
            .set_body(&[i64_t, self.item_type.into()], false);

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

        // define 'release'
        {
            let s = scope(self.release, context, target);
            let rc = s.arg(0);

            if let Some(ProfileRc { record_release, .. }) = tal.prof_rc {
                s.call_void(record_release, &[]);
            }

            let new_refcount = s.sub(s.arrow(self.rc_type, i64_t, rc, F_REFCOUNT), s.i64(1));
            s.arrow_set(self.rc_type, rc, F_REFCOUNT, new_refcount);

            s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                if let Some(item_release) = item_release {
                    s.call_void(item_release, &[s.gep(self.rc_type, rc, F_ITEM)]);
                }
                s.free(s.ptr_cast(s.i8_t(), rc), tal);
            });

            s.ret_void();
        }
    }
}
