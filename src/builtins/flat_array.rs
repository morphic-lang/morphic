use crate::builtins::array::{ArrayImpl, ArrayInterface};
use crate::builtins::fountain_pen::{scope, Scope};
use crate::builtins::tal::{ProfileRc, Tal};
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
const F_HOLE_ARR: u32 = 1; // has type FlatArray<T>

#[derive(Clone, Copy, Debug)]
pub struct FlatArrayImpl<'a> {
    interface: ArrayInterface<'a>,
    ensure_cap: FunctionValue<'a>,
    bounds_check: FunctionValue<'a>,
}

impl<'a> FlatArrayImpl<'a> {
    pub fn declare(
        context: &'a Context,
        _target: &TargetData,
        module: &Module<'a>,
        item_type: BasicTypeEnum<'a>,
    ) -> Self {
        let void_type = context.void_type();
        let i64_type = context.i64_type();
        let item_ptr_type = item_type.ptr_type(AddressSpace::Generic);

        let array_type = context.opaque_struct_type("builtin_flat_array");
        array_type.set_body(
            &[item_ptr_type.into(), i64_type.into(), i64_type.into()],
            false,
        );

        let hole_array_type = context.struct_type(&[i64_type.into(), array_type.into()], false);
        let extract_ret_type =
            context.struct_type(&[item_type.into(), hole_array_type.into()], false);
        let pop_ret_type = context.struct_type(&[array_type.into(), item_type.into()], false);

        let new = module.add_function(
            "builtin_flat_array_new",
            array_type.fn_type(&[], false),
            Some(Linkage::Internal),
        );

        let get = module.add_function(
            "builtin_flat_array_get",
            item_type.fn_type(&[array_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        let extract = module.add_function(
            "builtin_flat_array_extract",
            extract_ret_type.fn_type(&[array_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        let len = module.add_function(
            "builtin_flat_array_len",
            i64_type.fn_type(&[array_type.into()], false),
            Some(Linkage::Internal),
        );

        let push = module.add_function(
            "builtin_flat_array_push",
            array_type.fn_type(&[array_type.into(), item_type.into()], false),
            Some(Linkage::Internal),
        );

        let pop = module.add_function(
            "builtin_flat_array_pop",
            pop_ret_type.fn_type(&[array_type.into()], false),
            Some(Linkage::Internal),
        );

        let replace = module.add_function(
            "builtin_flat_array_replace",
            array_type.fn_type(&[hole_array_type.into(), item_type.into()], false),
            Some(Linkage::Internal),
        );

        let reserve = module.add_function(
            "builtin_flat_array_reserve",
            array_type.fn_type(&[array_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        let retain_array = module.add_function(
            "builtin_flat_array_retain",
            void_type.fn_type(&[array_type.into()], false),
            Some(Linkage::Internal),
        );

        let release_array = module.add_function(
            "builtin_flat_array_release",
            void_type.fn_type(&[array_type.into()], false),
            Some(Linkage::Internal),
        );

        let retain_hole = module.add_function(
            "builtin_flat_array_retain_hole",
            void_type.fn_type(&[hole_array_type.into()], false),
            Some(Linkage::Internal),
        );

        let release_hole = module.add_function(
            "builtin_flat_array_release_hole",
            void_type.fn_type(&[hole_array_type.into()], false),
            Some(Linkage::Internal),
        );

        let ensure_cap = module.add_function(
            "builtin_flat_array_ensure_cap",
            array_type.fn_type(&[array_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        let bounds_check = module.add_function(
            "builtin_flat_array_bounds_check",
            void_type.fn_type(&[array_type.into(), i64_type.into()], false),
            Some(Linkage::Internal),
        );

        let interface = ArrayInterface {
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
            release_array,
            retain_hole,
            release_hole,
        };

        Self {
            interface,
            ensure_cap,
            bounds_check,
        }
    }
}

impl<'a> ArrayImpl<'a> for FlatArrayImpl<'a> {
    fn define<'b>(
        &self,
        context: &'a Context,
        target: &'b TargetData,
        tal: &Tal<'a>,
        _item_retain: Option<FunctionValue<'a>>,
        item_release: Option<FunctionValue<'a>>,
    ) {
        let array_type = self.interface.array_type;

        // Offset a reference (an *i64) into the underlying heap buffer by sizeof(i64) to skip the leading
        // refcount, obtaining a reference to the data array.
        let buf_to_data = |s: &Scope<'a, 'b>, buf_ptr: BasicValueEnum<'a>| {
            debug_assert_eq!(
                buf_ptr
                    .get_type()
                    .into_pointer_type()
                    .get_element_type()
                    .into_int_type()
                    .get_bit_width(),
                64,
            );
            s.ptr_cast(self.interface.item_type, s.buf_addr_oob(buf_ptr, s.i32(1)))
        };

        // Offset a reference to the beginning of the data array by -sizeof(i64) to obtain a
        // reference to the beginning of the underlying heap buffer, including the leading refcount.
        let data_to_buf = |s: &Scope<'a, 'b>, buf_ptr: BasicValueEnum<'a>| {
            s.buf_addr_oob(s.ptr_cast(s.i64_t(), buf_ptr), s.i32(-1i32 as u32))
        };

        // define 'new'
        {
            let s = scope(self.interface.new, context, target);

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
            let s = scope(self.interface.get, context, target);
            let me = s.arg(0);
            let idx = s.arg(1);

            s.call_void(self.bounds_check, &[me, idx]);
            let data = s.field(me, F_ARR_DATA);

            s.ret(s.buf_get(data, idx));
        }

        // define 'extract'
        {
            let s = scope(self.interface.extract, context, target);
            let me = s.arg(0);
            let idx = s.arg(1);

            s.call_void(self.bounds_check, &[me, idx]);
            let data = s.field(me, F_ARR_DATA);

            s.ret(s.make_tup(&[
                s.buf_get(data, idx),
                s.make_struct(
                    self.interface.hole_array_type,
                    &[(F_HOLE_IDX, idx), (F_HOLE_ARR, me)],
                ),
            ]));
        }

        // define 'len'
        {
            let s = scope(self.interface.len, context, target);
            let me = s.arg(0);
            s.ret(s.field(me, F_ARR_LEN));
        }

        // define 'push'
        {
            let s = scope(self.interface.push, context, target);

            let me = s.arg(0);
            let old_len = s.field(me, F_ARR_LEN);
            let new_len = s.add(old_len, s.i64(1));

            let new_me = s.call(self.ensure_cap, &[me, new_len]);

            s.buf_set(s.field(new_me, F_ARR_DATA), old_len, s.arg(1));

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
            let s = scope(self.interface.pop, context, target);
            let me = s.arg(0);

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

            let item = s.buf_get(s.field(me, F_ARR_DATA), new_len);

            s.ret(s.make_tup(&[new_me, item]))
        }

        // define 'replace'
        {
            let s = scope(self.interface.replace, context, target);

            let hole = s.arg(0);
            let item = s.arg(1);
            let idx = s.field(hole, F_HOLE_IDX);
            let me = s.field(hole, F_HOLE_ARR);

            s.buf_set(s.field(me, F_ARR_DATA), idx, item);

            s.ret(me);
        }

        // define 'reserve'
        {
            let s = scope(self.interface.reserve, context, target);

            let me = s.arg(0);
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
                    &[s.size(self.interface.item_type), min_cap],
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
            let s = scope(self.interface.retain_array, context, target);
            let me = s.arg(0);

            if let Some(ProfileRc { record_retain, .. }) = tal.prof_rc {
                s.call_void(record_retain, &[]);
            }

            let refcount_ptr = data_to_buf(&s, s.field(me, F_ARR_DATA));

            s.if_(s.not(s.is_null(refcount_ptr)), |s| {
                s.ptr_set(refcount_ptr, s.add(s.ptr_get(refcount_ptr), s.i64(1)));
            });

            s.ret_void();
        }

        // define 'release_array'
        {
            let s = scope(self.interface.release_array, context, target);
            let me = s.arg(0);

            if let Some(ProfileRc { record_release, .. }) = tal.prof_rc {
                s.call_void(record_release, &[]);
            }

            let refcount_ptr = data_to_buf(&s, s.field(me, F_ARR_DATA));

            s.if_(s.not(s.is_null(refcount_ptr)), |s| {
                let new_refcount = s.sub(s.ptr_get(refcount_ptr), s.i64(1));
                s.ptr_set(refcount_ptr, new_refcount);

                let data = s.field(me, F_ARR_DATA);

                s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                    if let Some(item_release) = item_release {
                        s.for_(s.field(me, F_ARR_LEN), |s, i| {
                            s.call_void(item_release, &[s.buf_addr(data, i)]);
                        });
                    }
                    s.call_void(tal.free, &[s.ptr_cast(s.i8_t(), refcount_ptr)]);
                });
            });

            s.ret_void();
        }

        // define 'retain_hole'
        {
            let s = scope(self.interface.retain_hole, context, target);
            let me = s.arg(0);

            s.call_void(self.interface.retain_array, &[s.field(me, F_HOLE_ARR)]);
            s.ret_void();
        }

        // define 'release_hole'
        {
            let s = scope(self.interface.release_hole, context, target);
            let me = s.arg(0);

            if let Some(ProfileRc { record_release, .. }) = tal.prof_rc {
                s.call_void(record_release, &[]);
            }

            let hole_idx = s.field(me, F_HOLE_IDX);
            let arr = s.field(me, F_HOLE_ARR);

            let refcount_ptr = data_to_buf(&s, s.field(arr, F_ARR_DATA));

            let new_refcount = s.sub(s.ptr_get(refcount_ptr), s.i64(1));
            s.ptr_set(refcount_ptr, new_refcount);

            let data = s.field(arr, F_ARR_DATA);

            s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                if let Some(item_release) = item_release {
                    // TODO: Investigate implementing this as two 'for' loops covering the ranges
                    // [0, hole_idx) and [hole_idx + 1, len), and determine if this would be faster
                    // than using a single 'for' loop with an internal branch.
                    s.for_(s.field(arr, F_ARR_LEN), |s, i| {
                        s.if_(s.ne(i, hole_idx), |s| {
                            s.call_void(item_release, &[s.buf_addr(data, i)]);
                        });
                    });
                }
                s.call_void(tal.free, &[s.ptr_cast(s.i8_t(), refcount_ptr)]);
            });

            s.ret_void();
        }

        // define 'ensure_cap'
        {
            let s = scope(self.ensure_cap, context, target);
            let me = s.arg(0);

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
                    s.mul(s.size(self.interface.item_type), new_cap),
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
    }

    fn interface(&self) -> &ArrayInterface<'a> {
        &self.interface
    }
}

#[derive(Clone, Copy, Debug)]
pub struct FlatArrayIoImpl<'a> {
    pub byte_array_type: FlatArrayImpl<'a>,
    pub input: FunctionValue<'a>,
    pub output: FunctionValue<'a>,
    pub output_error: FunctionValue<'a>,
}

impl<'a> FlatArrayIoImpl<'a> {
    pub fn declare(
        context: &'a Context,
        module: &Module<'a>,
        byte_array_type: FlatArrayImpl<'a>,
    ) -> Self {
        let void_type = context.void_type();

        let input = module.add_function(
            "builtin_flat_array_input",
            byte_array_type.interface.array_type.fn_type(&[], false),
            Some(Linkage::Internal),
        );

        let output = module.add_function(
            "builtin_flat_array_output",
            void_type.fn_type(&[byte_array_type.interface.array_type.into()], false),
            Some(Linkage::Internal),
        );

        let output_error = module.add_function(
            "builtin_flat_array_output_error",
            void_type.fn_type(&[byte_array_type.interface.array_type.into()], false),
            Some(Linkage::Internal),
        );

        Self {
            byte_array_type,
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
            let array = s.alloca(self.byte_array_type.interface().array_type);
            s.ptr_set(array, s.call(self.byte_array_type.interface().new, &[]));

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
                    let input_byte = s.truncate(s.i8_t(), s.ptr_get(getchar_result));
                    s.ptr_set(
                        array,
                        s.call(
                            self.byte_array_type.interface().push,
                            &[s.ptr_get(array), input_byte],
                        ),
                    );
                },
            );

            s.ret(s.ptr_get(array));
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
