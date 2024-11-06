use core::panic;

use crate::data::mode_annot_ast::Mode;
use crate::data::rc_specialized_ast::ModeScheme;
use crate::llvm_gen::array::ArrayImpl;
use crate::llvm_gen::fountain_pen::{scope, Scope};
use crate::llvm_gen::tal::Tal;
use crate::llvm_gen::{gen_rc_op, get_llvm_type, DerivedRcOp, Globals, Instances};
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::TargetData;
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::{BasicValueEnum, FunctionValue};
use inkwell::AddressSpace;

// fields of 'array_type'
const F_ARR_DATA: u32 = 0; // has type T* (points to *after* refcount)
const F_ARR_CAP: u32 = 1; // has type u64
const F_ARR_LEN: u32 = 2; // has type u64

// fields of 'hole_array_type'
const F_HOLE_IDX: u32 = 0; // has type u64
const F_HOLE_ARR: u32 = 1; // has type CowArray<T>

pub fn cow_array_type<'a>(globals: &Globals<'a, '_>) -> BasicTypeEnum<'a> {
    let context = globals.context;
    let i64_type = context.i64_type();
    let i8_type = context.i8_type();

    let ptr_type = i8_type.ptr_type(AddressSpace::default());

    let array_type =
        context.struct_type(&[ptr_type.into(), i64_type.into(), i64_type.into()], false);

    array_type.into()
}

pub fn cow_hole_array_type<'a>(globals: &Globals<'a, '_>) -> BasicTypeEnum<'a> {
    let i64_type = globals.context.i64_type();
    let array_type = cow_array_type(globals);

    let hole_array_type = globals
        .context
        .struct_type(&[i64_type.into(), array_type.into()], false);

    hole_array_type.into()
}

#[derive(Clone, Debug)]
pub struct CowArrayImpl<'a> {
    pub mode: Mode,
    pub item_scheme: ModeScheme,

    // implementation details
    ensure_cap: FunctionValue<'a>,
    obtain_unique: FunctionValue<'a>,
    bounds_check: FunctionValue<'a>,

    // public interface
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

impl<'a> CowArrayImpl<'a> {
    pub fn declare(globals: &Globals<'a, '_>, scheme: &ModeScheme) -> Self {
        let context = globals.context;
        let module = globals.module;

        let (ModeScheme::Array(mode, item_scheme) | ModeScheme::HoleArray(mode, item_scheme)) =
            scheme
        else {
            panic!();
        };

        let item_type = get_llvm_type(globals, &item_scheme.as_type());
        let void_type = context.void_type();
        let i64_type = context.i64_type();
        let item_ptr_type = item_type.ptr_type(AddressSpace::default());

        let array_type = context.struct_type(
            &[item_ptr_type.into(), i64_type.into(), i64_type.into()],
            false,
        );

        let hole_array_type = context.struct_type(&[i64_type.into(), array_type.into()], false);
        let extract_ret_type =
            context.struct_type(&[item_type.into(), hole_array_type.into()], false);
        let pop_ret_type = context.struct_type(&[array_type.into(), item_type.into()], false);

        let new = module.add_function(
            "builtin_cow_array_new",
            array_type.fn_type(&[], false),
            Some(Linkage::Internal),
        );

        let get = module.add_function(
            "builtin_cow_array_get",
            item_type.fn_type(&[array_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        let extract = module.add_function(
            "builtin_cow_array_extract",
            extract_ret_type.fn_type(&[array_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        let len = module.add_function(
            "builtin_cow_array_len",
            i64_type.fn_type(&[array_type.into()], false),
            Some(Linkage::Internal),
        );

        let push = module.add_function(
            "builtin_cow_array_push",
            array_type.fn_type(&[array_type.into(), item_type.into()], false),
            Some(Linkage::Internal),
        );

        let pop = module.add_function(
            "builtin_cow_array_pop",
            pop_ret_type.fn_type(&[array_type.into()], false),
            Some(Linkage::Internal),
        );

        let replace = module.add_function(
            "builtin_cow_array_replace",
            array_type.fn_type(&[hole_array_type.into(), item_type.into()], false),
            Some(Linkage::Internal),
        );

        let reserve = module.add_function(
            "builtin_cow_array_reserve",
            array_type.fn_type(&[array_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        let retain_array = module.add_function(
            "builtin_cow_array_retain",
            void_type.fn_type(&[array_type.into()], false),
            Some(Linkage::Internal),
        );

        let derived_retain_array = module.add_function(
            "builtin_cow_array_derived_retain",
            void_type.fn_type(&[array_type.into()], false),
            Some(Linkage::Internal),
        );

        let release_array = module.add_function(
            "builtin_cow_array_release",
            void_type.fn_type(&[array_type.into()], false),
            Some(Linkage::Internal),
        );

        let retain_hole = module.add_function(
            "builtin_cow_array_retain_hole",
            void_type.fn_type(&[hole_array_type.into()], false),
            Some(Linkage::Internal),
        );

        let derived_retain_hole = module.add_function(
            "builtin_cow_array_derived_retain_hole",
            void_type.fn_type(&[hole_array_type.into()], false),
            Some(Linkage::Internal),
        );

        let release_hole = module.add_function(
            "builtin_cow_array_release_hole",
            void_type.fn_type(&[hole_array_type.into()], false),
            Some(Linkage::Internal),
        );

        let ensure_cap = module.add_function(
            "builtin_cow_array_ensure_cap",
            array_type.fn_type(&[array_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        let bounds_check = module.add_function(
            "builtin_cow_array_bounds_check",
            void_type.fn_type(&[array_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        let obtain_unique = module.add_function(
            "bulitin_cow_array_obtain_unique",
            array_type.fn_type(&[array_type.into()], false),
            Some(Linkage::Internal),
        );

        Self {
            mode: *mode,
            item_scheme: (**item_scheme).clone(),

            obtain_unique,
            ensure_cap,
            bounds_check,

            item_type,
            array_type: array_type.into(),
            hole_array_type: hole_array_type.into(),
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

impl<'a> ArrayImpl<'a> for CowArrayImpl<'a> {
    fn define<'b>(
        &self,
        globals: &Globals<'a, 'b>,
        instances: &mut Instances<'a>,
        target: &'b TargetData,
        tal: &Tal<'a>,
    ) {
        let context = globals.context;
        let array_type = self.array_type;

        // Offset a reference (an *i64) into the underlying heap buffer by sizeof(i64) to skip the leading
        // refcount, obtaining a reference to the data array.
        let buf_to_data = |s: &Scope<'a, 'b>, buf_ptr: BasicValueEnum<'a>| {
            s.ptr_cast(self.item_type, s.buf_addr_oob(s.i64_t(), buf_ptr, s.i32(1)))
        };

        // Offset a reference to the beginning of the data array by -sizeof(i64) to obtain a
        // reference to the beginning of the underlying heap buffer, including the leading refcount.
        let data_to_buf = |s: &Scope<'a, 'b>, buf_ptr: BasicValueEnum<'a>| {
            s.buf_addr_oob(
                s.i64_t(),
                s.ptr_cast(s.i64_t(), buf_ptr),
                s.i32(-1i32 as u32),
            )
        };

        // define 'new'
        {
            let s = scope(self.new, context, target);

            let me = s.make_struct(
                array_type, //;
                &[
                    (F_ARR_DATA, buf_to_data(&s, s.null(s.i64_t()))),
                    (F_ARR_CAP, s.i64(0)),
                    (F_ARR_LEN, s.i64(0)),
                ],
            );

            s.ret(me);
        }

        // define 'get'
        {
            let s = scope(self.get, context, target);
            let me = s.arg(0);
            let idx = s.arg(1);

            s.call_void(self.bounds_check, &[me, idx]);
            let data = s.field(me, F_ARR_DATA);

            s.ret(s.buf_get(self.item_type, data, idx));
        }

        // define 'extract'
        {
            let s = scope(self.extract, context, target);
            let me = s.call(self.obtain_unique, &[s.arg(0)]);
            let idx = s.arg(1);

            s.call_void(self.bounds_check, &[me, idx]);
            let data = s.field(me, F_ARR_DATA);

            s.ret(s.make_tup(&[
                s.buf_get(self.item_type, data, idx),
                s.make_struct(self.hole_array_type, &[(F_HOLE_IDX, idx), (F_HOLE_ARR, me)]),
            ]));
        }

        // define 'len'
        {
            let s = scope(self.len, context, target);
            let me = s.arg(0);
            s.ret(s.field(me, F_ARR_LEN));
        }

        // define 'push'
        {
            let s = scope(self.push, context, target);

            let me = s.call(self.obtain_unique, &[s.arg(0)]);
            let old_len = s.field(me, F_ARR_LEN);
            let new_len = s.add(old_len, s.i64(1));

            let new_me = s.call(self.ensure_cap, &[me, new_len]);

            s.buf_set(
                self.item_type,
                s.field(new_me, F_ARR_DATA),
                old_len,
                s.arg(1),
            );

            s.ret(s.make_struct(
                array_type,
                &[
                    (F_ARR_DATA, s.field(new_me, F_ARR_DATA)),
                    (F_ARR_CAP, s.field(new_me, F_ARR_CAP)),
                    (F_ARR_LEN, new_len),
                ],
            ));
        }

        // define 'pop'
        {
            let s = scope(self.pop, context, target);
            let me = s.call(self.obtain_unique, &[s.arg(0)]);

            s.if_(s.eq(s.field(me, F_ARR_LEN), s.i64(0)), |s| {
                s.panic("pop: empty array\n", &[], tal);
            });

            let new_len = s.sub(s.field(me, F_ARR_LEN), s.i64(1));

            let new_me = s.make_struct(
                array_type,
                &[
                    (F_ARR_DATA, s.field(me, F_ARR_DATA)),
                    (F_ARR_CAP, s.field(me, F_ARR_CAP)),
                    (F_ARR_LEN, new_len),
                ],
            );

            let item = s.buf_get(self.item_type, s.field(me, F_ARR_DATA), new_len);

            s.ret(s.make_tup(&[new_me, item]))
        }

        // define 'replace'
        {
            let s = scope(self.replace, context, target);

            let hole = s.arg(0);
            let item = s.arg(1);
            let idx = s.field(hole, F_HOLE_IDX);
            let me = s.field(hole, F_HOLE_ARR);
            let me = s.call(self.obtain_unique, &[me]);

            s.buf_set(self.item_type, s.field(me, F_ARR_DATA), idx, item);

            s.ret(me);
        }

        // define 'reserve'
        {
            let s = scope(self.reserve, context, target);

            let me = s.arg(0);
            let me = s.call(self.obtain_unique, &[me]);
            let min_cap = s.arg(1);

            let curr_cap = s.field(me, F_ARR_CAP);

            // We perform a signed comparison so that e.g. `reserve(arr, -1)` is a no-op, rather
            // than an instant out-of-memory error.  On any reasonable system `curr_cap` should
            // never exceed 2^63 - 1, so if we have `curr_cap < min_cap` as signed integers then we
            // should also have `curr_cap < min_cap` as unsigned integers, so using `min_cap` as the
            // new capacity is safe.
            let should_resize = s.slt(curr_cap, min_cap);
            s.if_(should_resize, |s| {
                let alloc_size_umul_result = s.call(
                    tal.umul_with_overflow_i64,
                    &[s.size(self.item_type), min_cap],
                );

                let is_overflow = s.field(alloc_size_umul_result, 1);
                s.if_(is_overflow, |s| {
                    s.panic(
                        "reserve: requested size overflows 64-bit integer type",
                        &[],
                        tal,
                    );
                });

                // TODO: Should we check for overflow in this addition?
                let alloc_size = s.add(s.size(s.i64_t()), s.field(alloc_size_umul_result, 0));

                let old_buf = data_to_buf(&s, s.field(me, F_ARR_DATA));

                // TODO: Check for overflow on truncation (for 32-bit systems)
                let new_buf = s.ptr_cast(
                    s.i64_t(), // Type of leading refcount
                    s.call(
                        tal.realloc,
                        &[
                            s.ptr_cast(s.i8_t(), old_buf),
                            s.int_cast(s.usize_t(), alloc_size),
                        ],
                    ),
                );

                // Initialize refcount if the allocation was 'null' before.
                // The refcount is necessarily 1 immediately after a mutating operation.
                s.ptr_set(new_buf, s.i64(1));

                s.if_(s.is_null(new_buf), |s| {
                    s.panic(
                        "reserve: failed to allocate %zu bytes\n",
                        &[alloc_size],
                        tal,
                    );
                });

                s.ret(s.make_struct(
                    array_type,
                    &[
                        (F_ARR_DATA, buf_to_data(&s, new_buf)),
                        (F_ARR_CAP, min_cap),
                        (F_ARR_LEN, s.field(me, F_ARR_LEN)),
                    ],
                ));
            });

            s.ret(me);
        }

        // define 'retain_array'
        {
            let s = scope(self.retain_array, context, target);
            let me = s.arg(0);

            let refcount_ptr = data_to_buf(&s, s.field(me, F_ARR_DATA));

            s.if_(s.not(s.is_null(refcount_ptr)), |s| {
                s.ptr_set(
                    refcount_ptr,
                    s.add(s.ptr_get(s.i64_t(), refcount_ptr), s.i64(1)),
                );
            });

            s.ret_void();
        }

        // define 'derived_retain_array'
        {
            let s = scope(self.derived_retain_array, context, target);
            let me = s.arg(0);

            let refcount_ptr = data_to_buf(&s, s.field(me, F_ARR_DATA));

            if self.mode == Mode::Owned {
                s.if_(s.not(s.is_null(refcount_ptr)), |s| {
                    s.ptr_set(
                        refcount_ptr,
                        s.add(s.ptr_get(s.i64_t(), refcount_ptr), s.i64(1)),
                    );
                });
            }

            s.ret_void();
        }

        // define 'release_array'
        {
            let s = scope(self.release_array, context, target);
            let me = s.arg(0);

            let refcount_ptr = data_to_buf(&s, s.field(me, F_ARR_DATA));

            s.if_(s.not(s.is_null(refcount_ptr)), |s| {
                let new_refcount: BasicValueEnum<'_> =
                    s.sub(s.ptr_get(s.i64_t(), refcount_ptr), s.i64(1));
                s.ptr_set(refcount_ptr, new_refcount);

                let data = s.field(me, F_ARR_DATA);

                s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                    s.for_(s.field(me, F_ARR_LEN), |s, i| {
                        gen_rc_op(
                            DerivedRcOp::Release,
                            s.builder(),
                            instances,
                            globals,
                            s.func(),
                            &self.item_scheme,
                            s.ptr_get(self.item_type, s.buf_addr(self.item_type, data, i)),
                        );
                    });
                    s.call_void(tal.free, &[s.ptr_cast(s.i8_t(), refcount_ptr)]);
                });
            });

            s.ret_void();
        }

        // define 'retain_hole'
        {
            let s = scope(self.retain_hole, context, target);
            let me = s.arg(0);

            s.call_void(self.retain_array, &[s.field(me, F_HOLE_ARR)]);
            s.ret_void();
        }

        // define 'derived_retain_hole'
        {
            let s = scope(self.derived_retain_hole, context, target);
            let me = s.arg(0);

            s.call_void(self.derived_retain_array, &[s.field(me, F_HOLE_ARR)]);
            s.ret_void();
        }

        // define 'release_hole'
        {
            let s = scope(self.release_hole, context, target);
            let me = s.arg(0);
            let hole_idx = s.field(me, F_HOLE_IDX);

            let me = s.field(me, F_HOLE_ARR);

            let refcount_ptr = data_to_buf(&s, s.field(me, F_ARR_DATA));

            s.if_(s.not(s.is_null(refcount_ptr)), |s| {
                let new_refcount: BasicValueEnum<'_> =
                    s.sub(s.ptr_get(s.i64_t(), refcount_ptr), s.i64(1));
                s.ptr_set(refcount_ptr, new_refcount);

                let data = s.field(me, F_ARR_DATA);

                s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                    s.for_(s.field(me, F_ARR_LEN), |s, i| {
                        // TODO: investigate if using two for loops is faster than a for loop with a branch
                        s.if_(s.ne(i, hole_idx), |s| {
                            gen_rc_op(
                                DerivedRcOp::Release,
                                s.builder(),
                                instances,
                                globals,
                                s.func(),
                                &self.item_scheme,
                                s.ptr_get(self.item_type, s.buf_addr(self.item_type, data, i)),
                            );
                        });
                    });
                    s.call_void(tal.free, &[s.ptr_cast(s.i8_t(), refcount_ptr)]);
                });
            });

            s.ret_void();
        }

        // define 'ensure_cap'
        {
            let s = scope(self.ensure_cap, context, target);
            let me = s.call(self.obtain_unique, &[s.arg(0)]);

            let min_cap = s.arg(1);
            let curr_cap = s.field(me, F_ARR_CAP);
            let should_resize = s.ult(curr_cap, min_cap);

            s.if_(should_resize, |s| {
                // TODO: Determine if we need to check for overflow here
                let candidate_cap = s.mul(curr_cap, s.i64(2));
                let use_candidate_cap = s.uge(candidate_cap, min_cap);
                let new_cap = s.ternary(use_candidate_cap, candidate_cap, min_cap);

                // TODO: Should we check for arithmetic overflow here?
                let alloc_size = s.add(
                    s.size(s.i64_t()), // Refcount
                    s.mul(s.size(self.item_type), new_cap),
                );

                let old_buf = data_to_buf(&s, s.field(me, F_ARR_DATA));

                let new_buf = s.ptr_cast(
                    s.i64_t(), // Type of leading refcount
                    s.call(
                        tal.realloc,
                        &[
                            s.ptr_cast(s.i8_t(), old_buf),
                            // TODO: Should we check for truncation overflow here (on 32-bit
                            // systems)?
                            s.int_cast(s.usize_t(), alloc_size),
                        ],
                    ),
                );

                s.if_(s.is_null(new_buf), |s| {
                    s.panic(
                        "ensure_capacity: failed to allocate %zu bytes\n",
                        &[alloc_size],
                        tal,
                    );
                });

                // Initialize refcount if the allocation was 'null' before.
                // The refcount is necessarily 1 immediately after a mutating operation.
                s.ptr_set(new_buf, s.i64(1));

                s.ret(s.make_struct(
                    array_type,
                    &[
                        (F_ARR_DATA, buf_to_data(&s, new_buf)),
                        (F_ARR_CAP, new_cap),
                        (F_ARR_LEN, s.field(me, F_ARR_LEN)),
                    ],
                ))
            });

            s.ret(me);
        }

        // define 'bounds_check'
        {
            let s = scope(self.bounds_check, context, target);
            let me = s.arg(0);
            let idx = s.arg(1);

            let len = s.field(me, F_ARR_LEN);
            let out_of_bounds = s.uge(idx, len);

            s.if_(out_of_bounds, |s| {
                let error_str =
                    "index out of bounds: attempt to access item %lld of array with length %llu\n";
                s.panic(error_str, &[idx, len], tal);
            });

            s.ret_void();
        }

        // define 'obtain_unique'
        {
            let s = scope(self.obtain_unique, context, target);
            let me = s.arg(0);

            let refcount: BasicValueEnum<'a> = data_to_buf(&s, s.field(me, F_ARR_DATA));

            s.if_(s.is_null(refcount), |s| {
                let me = s.make_struct(
                    array_type,
                    &[
                        (F_ARR_DATA, buf_to_data(&s, s.null(s.i64_t()))),
                        (F_ARR_CAP, s.i64(0)),
                        (F_ARR_LEN, s.i64(0)),
                    ],
                );

                s.ret(me);
            });

            let len = s.field(me, F_ARR_LEN);
            let cap = s.field(me, F_ARR_CAP);

            s.if_(s.eq(s.ptr_get(s.i64_t(), refcount), s.i64(1)), |s| {
                s.ret(me);
            });

            let new_refcount = s.sub(s.ptr_get(s.i64_t(), refcount), s.i64(1));
            s.ptr_set(refcount, new_refcount);

            let alloc_size = s.add(
                s.size(s.i64_t()), // Refcount
                s.mul(s.size(self.item_type), cap),
            );

            let new_buf = s.ptr_cast(
                s.i64_t(), // Type of leading refcount
                s.call(tal.malloc, &[s.int_cast(s.usize_t(), alloc_size)]),
            );

            s.if_(s.is_null(new_buf), |s| {
                s.panic(
                    "obtain_unique: failed to allocate %zu bytes\n",
                    &[alloc_size],
                    tal,
                );
            });

            s.for_(len, |s, i| {
                gen_rc_op(
                    DerivedRcOp::DerivedRetain,
                    s.builder(),
                    instances,
                    globals,
                    s.func(),
                    &self.item_scheme,
                    s.ptr_get(
                        self.item_type,
                        s.buf_addr(
                            self.item_type,
                            s.ptr_cast(self.item_type.into(), s.field(me, F_ARR_DATA)),
                            i,
                        ),
                    ),
                );
            });

            s.call(
                tal.memcpy,
                &[
                    s.ptr_cast(s.i8_t(), buf_to_data(&s, new_buf)),
                    s.ptr_cast(s.i8_t(), s.field(me, F_ARR_DATA)),
                    s.mul(s.size(self.item_type), cap),
                ],
            );

            // Initialize refcount if the allocation was 'null' before.
            // The refcount is necessarily 1 immediately after a mutating operation.
            s.ptr_set(new_buf, s.i64(1));

            s.ret(s.make_struct(
                array_type,
                &[
                    (F_ARR_DATA, buf_to_data(&s, new_buf)),
                    (F_ARR_CAP, cap),
                    (F_ARR_LEN, len),
                ],
            ))
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

#[derive(Clone, Debug)]
pub struct CowArrayIoImpl<'a> {
    pub owned_byte_array: CowArrayImpl<'a>,
    pub borrowed_byte_array: CowArrayImpl<'a>,
    pub input: FunctionValue<'a>,
    pub output: FunctionValue<'a>,
    pub output_error: FunctionValue<'a>,
}

impl<'a> CowArrayIoImpl<'a> {
    pub fn declare(
        context: &'a Context,
        module: &Module<'a>,
        owned_byte_array: CowArrayImpl<'a>,
        borrowed_byte_array: CowArrayImpl<'a>,
    ) -> Self {
        let void_type = context.void_type();

        let input = module.add_function(
            "builtin_cow_array_input",
            owned_byte_array.array_type.fn_type(&[], false),
            Some(Linkage::Internal),
        );

        let output = module.add_function(
            "builtin_cow_array_output",
            void_type.fn_type(&[borrowed_byte_array.array_type.into()], false),
            Some(Linkage::Internal),
        );

        let output_error = module.add_function(
            "builtin_cow_array_output_error",
            void_type.fn_type(&[borrowed_byte_array.array_type.into()], false),
            Some(Linkage::Internal),
        );

        Self {
            owned_byte_array,
            borrowed_byte_array,
            input,
            output,
            output_error,
        }
    }

    pub fn define(&self, context: &'a Context, target: &TargetData, tal: &Tal<'a>) {
        // define 'input'
        {
            let s = scope(self.input, context, target);

            s.call(tal.flush, &[]);
            let array = s.alloca(self.owned_byte_array.array_type);
            s.ptr_set(array, s.call(self.owned_byte_array.new, &[]));

            let getchar_result = s.alloca(s.i32_t());
            s.while_(
                |s| {
                    let getchar_result_value = s.call(tal.getchar, &[]);
                    s.ptr_set(getchar_result, getchar_result_value);
                    s.not(s.or(
                        s.eq(getchar_result_value, s.i32(-1i32 as u32)), // EOF
                        s.eq(getchar_result_value, s.i32('\n' as u32)),
                    ))
                },
                |s| {
                    let input_byte = s.truncate(s.i8_t(), s.ptr_get(s.i32_t(), getchar_result));
                    s.ptr_set(
                        array,
                        s.call(
                            self.owned_byte_array.push,
                            &[
                                s.ptr_get(self.owned_byte_array.array_type, array),
                                input_byte,
                            ],
                        ),
                    );
                },
            );

            s.ret(s.ptr_get(self.owned_byte_array.array_type, array));
        }

        // define 'output'
        {
            let s = scope(self.output, context, target);
            let me = s.arg(0);

            // TODO: check bytes_written for errors
            let _bytes_written = s.call_void(
                tal.write,
                &[
                    s.field(me, F_ARR_DATA),
                    s.usize(1),
                    s.int_cast(s.usize_t(), s.field(me, F_ARR_LEN)),
                ],
            );
            s.ret_void();
        }

        // define 'output_error'
        {
            let s = scope(self.output_error, context, target);
            let me = s.arg(0);

            // TODO: check bytes_written for errors
            let _bytes_written = s.call_void(
                tal.write_error,
                &[
                    s.field(me, F_ARR_DATA),
                    s.usize(1),
                    s.int_cast(s.usize_t(), s.field(me, F_ARR_LEN)),
                ],
            );
            s.ret_void();
        }
    }
}
