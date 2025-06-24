use crate::data::mode_annot_ast::Mode;
use crate::data::rc_specialized_ast::ModeScheme;
use crate::llvm_gen::array::ArrayImpl;
use crate::llvm_gen::fountain_pen::{Context, ProfileRc, Scope, Tal};
use crate::llvm_gen::{gen_rc_op, low_type_in_context, DerivedRcOp, Globals, Instances};

// fields of 'array_type'
const F_ARR_DATA: u32 = 0; // has type T* (points to *after* refcount)
const F_ARR_CAP: u32 = 1; // has type u64
const F_ARR_LEN: u32 = 2; // has type u64

// fields of 'hole_array_type'
const F_HOLE_IDX: u32 = 0; // has type u64
const F_HOLE_ARR: u32 = 1; // has type CowArray<T>

pub fn cow_array_t<T: Context>(context: &T) -> T::Type {
    let i64_type = context.i64_t();
    let ptr_type = context.ptr_t();
    context.struct_t(&[ptr_type, i64_type, i64_type])
}

pub fn cow_hole_array_t<T: Context>(context: &T) -> T::Type {
    let i64_type = context.i64_t();
    let array_type = cow_array_t(context);
    context.struct_t(&[i64_type, array_type])
}

#[derive(Clone, Debug)]
pub struct CowArrayImpl<T: Context> {
    pub mode: Mode,
    pub item_scheme: ModeScheme,

    // implementation details
    ensure_cap: T::FunctionValue,
    obtain_unique: T::FunctionValue,
    bounds_check: T::FunctionValue,

    // public interface
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

impl<T: Context> CowArrayImpl<T> {
    pub fn declare(globals: &Globals<T>, scheme: &ModeScheme) -> Self {
        let context = &globals.context;

        let (ModeScheme::Array(mode, item_scheme) | ModeScheme::HoleArray(mode, item_scheme)) =
            scheme
        else {
            panic!();
        };

        let item_t = low_type_in_context(globals, &item_scheme.as_type());
        let i64_t = context.i64_t();
        let array_t = cow_array_t(context);
        let hole_array_t = cow_hole_array_t(context);

        let extract_ret_t = context.struct_t(&[item_t, hole_array_t]);
        let pop_ret_t = context.struct_t(&[array_t, item_t]);

        let new = context.declare_func("builtin_cow_array_new", &[], Some(array_t));

        let get = context.declare_func("builtin_cow_array_get", &[array_t, i64_t], Some(item_t));

        let extract = context.declare_func(
            "builtin_cow_array_extract",
            &[array_t, i64_t],
            Some(extract_ret_t),
        );

        let len = context.declare_func("builtin_cow_array_len", &[array_t], Some(i64_t));

        let push =
            context.declare_func("builtin_cow_array_push", &[array_t, item_t], Some(array_t));

        let pop = context.declare_func("builtin_cow_array_pop", &[array_t], Some(pop_ret_t));

        let replace = context.declare_func(
            "builtin_cow_array_replace",
            &[hole_array_t, item_t],
            Some(array_t),
        );

        let reserve = context.declare_func(
            "builtin_cow_array_reserve",
            &[array_t, i64_t],
            Some(array_t),
        );

        let retain_array = context.declare_func("builtin_cow_array_retain", &[array_t], None);

        let derived_retain_array =
            context.declare_func("builtin_cow_array_derived_retain", &[array_t], None);

        let release_array = context.declare_func("builtin_cow_array_release", &[array_t], None);

        let retain_hole =
            context.declare_func("builtin_cow_array_retain_hole", &[hole_array_t], None);

        let derived_retain_hole = context.declare_func(
            "builtin_cow_array_derived_retain_hole",
            &[hole_array_t],
            None,
        );

        let release_hole =
            context.declare_func("builtin_cow_array_release_hole", &[hole_array_t], None);

        let ensure_cap = context.declare_func(
            "builtin_cow_array_ensure_cap",
            &[array_t, i64_t],
            Some(array_t),
        );

        let bounds_check =
            context.declare_func("builtin_cow_array_bounds_check", &[array_t, i64_t], None);

        let obtain_unique =
            context.declare_func("bulitin_cow_array_obtain_unique", &[array_t], Some(array_t));

        Self {
            mode: *mode,
            item_scheme: (**item_scheme).clone(),

            obtain_unique,
            ensure_cap,
            bounds_check,

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

impl<T: Context> ArrayImpl<T> for CowArrayImpl<T> {
    fn define<'a, 'b>(&self, globals: &Globals<T>, instances: &mut Instances<T>) {
        let context = &globals.context;

        // Offset a reference (an *i64) into the underlying heap buffer by sizeof(i64) to skip the leading
        // refcount, obtaining a reference to the data array.
        let buf_to_data =
            |s: &T::Scope, buf_ptr: T::Value| s.buf_addr_oob(s.i64_t(), buf_ptr, s.i32(1));

        // Offset a reference to the beginning of the data array by -sizeof(i64) to obtain a
        // reference to the beginning of the underlying heap buffer, including the leading refcount.
        let data_to_buf = |s: &T::Scope, buf_ptr: T::Value| {
            s.buf_addr_oob(s.i64_t(), buf_ptr, s.i32(-1i32 as u32))
        };

        // define 'new'
        {
            let s = context.scope(self.new);

            let me = s.make_struct(&[
                (F_ARR_DATA, buf_to_data(&s, s.null())),
                (F_ARR_CAP, s.i64(0)),
                (F_ARR_LEN, s.i64(0)),
            ]);

            s.ret(me);
        }

        // define 'get'
        {
            let s = context.scope(self.get);
            let me = s.arg(0);
            let idx = s.arg(1);

            s.call_void(self.bounds_check, &[me, idx]);
            let data = s.field(me, F_ARR_DATA);

            s.ret(s.buf_get(self.item_t, data, idx));
        }

        // define 'extract'
        {
            let s = context.scope(self.extract);
            let me = s.call(self.obtain_unique, &[s.arg(0)]);
            let idx = s.arg(1);

            s.call_void(self.bounds_check, &[me, idx]);
            let data = s.field(me, F_ARR_DATA);

            s.ret(s.make_tup(&[
                s.buf_get(self.item_t, data, idx),
                s.make_struct(&[(F_HOLE_IDX, idx), (F_HOLE_ARR, me)]),
            ]));
        }

        // define 'len'
        {
            let s = context.scope(self.len);
            let me = s.arg(0);
            s.ret(s.field(me, F_ARR_LEN));
        }

        // define 'push'
        {
            let s = context.scope(self.push);

            let me = s.call(self.obtain_unique, &[s.arg(0)]);
            let old_len = s.field(me, F_ARR_LEN);
            let new_len = s.add(old_len, s.i64(1));

            let new_me = s.call(self.ensure_cap, &[me, new_len]);

            s.buf_set(self.item_t, s.field(new_me, F_ARR_DATA), old_len, s.arg(1));

            s.ret(s.make_struct(&[
                (F_ARR_DATA, s.field(new_me, F_ARR_DATA)),
                (F_ARR_CAP, s.field(new_me, F_ARR_CAP)),
                (F_ARR_LEN, new_len),
            ]));
        }

        // define 'pop'
        {
            let s = context.scope(self.pop);
            let me = s.call(self.obtain_unique, &[s.arg(0)]);

            s.if_(s.eq(s.field(me, F_ARR_LEN), s.i64(0)), |s| {
                s.panic("pop: empty array\n", &[]);
            });

            let new_len = s.sub(s.field(me, F_ARR_LEN), s.i64(1));

            let new_me = s.make_struct(&[
                (F_ARR_DATA, s.field(me, F_ARR_DATA)),
                (F_ARR_CAP, s.field(me, F_ARR_CAP)),
                (F_ARR_LEN, new_len),
            ]);

            let item = s.buf_get(self.item_t, s.field(me, F_ARR_DATA), new_len);

            s.ret(s.make_tup(&[new_me, item]))
        }

        // define 'replace'
        {
            let s = context.scope(self.replace);

            let hole = s.arg(0);
            let item = s.arg(1);
            let idx = s.field(hole, F_HOLE_IDX);
            let me = s.field(hole, F_HOLE_ARR);
            let me = s.call(self.obtain_unique, &[me]);

            s.buf_set(self.item_t, s.field(me, F_ARR_DATA), idx, item);

            s.ret(me);
        }

        // define 'reserve'
        {
            let s = context.scope(self.reserve);

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
                    context.tal().umul_with_overflow_i64(),
                    &[s.size(self.item_t), min_cap],
                );

                let is_overflow = s.field(alloc_size_umul_result, 1);
                s.if_(is_overflow, |s| {
                    s.panic("reserve: requested size overflows 64-bit integer type", &[]);
                });

                // TODO: Should we check for overflow in this addition?
                let alloc_size = s.add(s.size(s.i64_t()), s.field(alloc_size_umul_result, 0));

                let old_buf = data_to_buf(&s, s.field(me, F_ARR_DATA));

                // TODO: Check for overflow on truncation (for 32-bit systems)
                let new_buf = s.call(
                    context.tal().realloc(),
                    &[old_buf, s.int_cast(s.usize_t(), alloc_size)],
                );

                // Initialize refcount if the allocation was 'null' before.
                // The refcount is necessarily 1 immediately after a mutating operation.
                s.ptr_set(new_buf, s.i64(1));

                s.if_(s.is_null(new_buf), |s| {
                    s.panic("reserve: failed to allocate %zu bytes\n", &[alloc_size]);
                });

                s.ret(s.make_struct(&[
                    (F_ARR_DATA, buf_to_data(&s, new_buf)),
                    (F_ARR_CAP, min_cap),
                    (F_ARR_LEN, s.field(me, F_ARR_LEN)),
                ]));
            });

            s.ret(me);
        }

        // define 'retain_array'
        {
            let s = context.scope(self.retain_array);
            let me = s.arg(0);

            let refcount_ptr = data_to_buf(&s, s.field(me, F_ARR_DATA));

            if let Some(prof_rc) = context.tal().prof_rc() {
                s.call_void(prof_rc.record_retain(), &[]);
            }

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
            let s = context.scope(self.derived_retain_array);
            let me = s.arg(0);

            let refcount_ptr = data_to_buf(&s, s.field(me, F_ARR_DATA));

            if self.mode == Mode::Owned {
                if let Some(prof_rc) = context.tal().prof_rc() {
                    s.call_void(prof_rc.record_retain(), &[]);
                }

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
            let s = context.scope(self.release_array);
            let me = s.arg(0);

            let refcount_ptr = data_to_buf(&s, s.field(me, F_ARR_DATA));

            if self.mode == Mode::Owned {
                if let Some(prof_rc) = context.tal().prof_rc() {
                    s.call_void(prof_rc.record_release(), &[]);
                }

                s.if_(s.not(s.is_null(refcount_ptr)), |s| {
                    let new_refcount: T::Value =
                        s.sub(s.ptr_get(s.i64_t(), refcount_ptr), s.i64(1));
                    s.ptr_set(refcount_ptr, new_refcount);

                    let data = s.field(me, F_ARR_DATA);

                    s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                        s.for_(s.field(me, F_ARR_LEN), |s, i| {
                            gen_rc_op(
                                DerivedRcOp::Release,
                                s,
                                instances,
                                globals,
                                &self.item_scheme,
                                s.ptr_get(self.item_t, s.buf_addr(self.item_t, data, i)),
                            );
                        });
                        s.call_void(context.tal().free(), &[refcount_ptr]);
                    });
                });
            }

            s.ret_void();
        }

        // define 'retain_hole'
        {
            let s = context.scope(self.retain_hole);
            let me = s.arg(0);

            s.call_void(self.retain_array, &[s.field(me, F_HOLE_ARR)]);
            s.ret_void();
        }

        // define 'derived_retain_hole'
        {
            let s = context.scope(self.derived_retain_hole);
            let me = s.arg(0);

            s.call_void(self.derived_retain_array, &[s.field(me, F_HOLE_ARR)]);
            s.ret_void();
        }

        // define 'release_hole'
        {
            let s = context.scope(self.release_hole);
            let me = s.arg(0);
            let hole_idx = s.field(me, F_HOLE_IDX);

            let me = s.field(me, F_HOLE_ARR);

            let refcount_ptr = data_to_buf(&s, s.field(me, F_ARR_DATA));

            if self.mode == Mode::Owned {
                if let Some(prof_rc) = context.tal().prof_rc() {
                    s.call_void(prof_rc.record_release(), &[]);
                }

                s.if_(s.not(s.is_null(refcount_ptr)), |s| {
                    let new_refcount: T::Value =
                        s.sub(s.ptr_get(s.i64_t(), refcount_ptr), s.i64(1));
                    s.ptr_set(refcount_ptr, new_refcount);

                    let data = s.field(me, F_ARR_DATA);

                    s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                        s.for_(s.field(me, F_ARR_LEN), |s, i| {
                            // TODO: investigate if using two for loops is faster than a for loop with a branch
                            s.if_(s.ne(i, hole_idx), |s| {
                                gen_rc_op(
                                    DerivedRcOp::Release,
                                    s,
                                    instances,
                                    globals,
                                    &self.item_scheme,
                                    s.ptr_get(self.item_t, s.buf_addr(self.item_t, data, i)),
                                );
                            });
                        });
                        s.call_void(context.tal().free(), &[refcount_ptr]);
                    });
                });
            }
            s.ret_void();
        }

        // define 'ensure_cap'
        {
            let s = context.scope(self.ensure_cap);
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
                    s.mul(s.size(self.item_t), new_cap),
                );

                let old_buf = data_to_buf(&s, s.field(me, F_ARR_DATA));

                let new_buf = s.call(
                    context.tal().realloc(),
                    &[
                        old_buf,
                        // TODO: Should we check for truncation overflow here (on 32-bit
                        // systems)?
                        s.int_cast(s.usize_t(), alloc_size),
                    ],
                );

                s.if_(s.is_null(new_buf), |s| {
                    s.panic(
                        "ensure_capacity: failed to allocate %zu bytes\n",
                        &[alloc_size],
                    );
                });

                // Initialize refcount if the allocation was 'null' before.
                // The refcount is necessarily 1 immediately after a mutating operation.
                s.ptr_set(new_buf, s.i64(1));

                s.ret(s.make_struct(&[
                    (F_ARR_DATA, buf_to_data(&s, new_buf)),
                    (F_ARR_CAP, new_cap),
                    (F_ARR_LEN, s.field(me, F_ARR_LEN)),
                ]))
            });

            s.ret(me);
        }

        // define 'bounds_check'
        {
            let s = context.scope(self.bounds_check);
            let me = s.arg(0);
            let idx = s.arg(1);

            let len = s.field(me, F_ARR_LEN);
            let out_of_bounds = s.uge(idx, len);

            s.if_(out_of_bounds, |s| {
                let error_str =
                    "index out of bounds: attempt to access item %lld of array with length %llu\n";
                s.panic(error_str, &[idx, len]);
            });

            s.ret_void();
        }

        // define 'obtain_unique'
        {
            let s = context.scope(self.obtain_unique);
            let me = s.arg(0);

            let refcount: T::Value = data_to_buf(&s, s.field(me, F_ARR_DATA));

            s.if_(s.is_null(refcount), |s| {
                let me = s.make_struct(&[
                    (F_ARR_DATA, buf_to_data(&s, s.null())),
                    (F_ARR_CAP, s.i64(0)),
                    (F_ARR_LEN, s.i64(0)),
                ]);

                s.ret(me);
            });

            let len = s.field(me, F_ARR_LEN);
            let cap = s.field(me, F_ARR_CAP);

            s.if_(s.eq(s.ptr_get(s.i64_t(), refcount), s.i64(1)), |s| {
                if let Some(prof_rc) = context.tal().prof_rc() {
                    s.call_void(prof_rc.record_rc1(), &[]);
                }

                s.ret(me);
            });

            let new_refcount = s.sub(s.ptr_get(s.i64_t(), refcount), s.i64(1));
            s.ptr_set(refcount, new_refcount);

            let alloc_size = s.add(
                s.size(s.i64_t()), // Refcount
                s.mul(s.size(self.item_t), cap),
            );

            let new_buf = s.call(
                context.tal().malloc(),
                &[s.int_cast(s.usize_t(), alloc_size)],
            );

            s.if_(s.is_null(new_buf), |s| {
                s.panic(
                    "obtain_unique: failed to allocate %zu bytes\n",
                    &[alloc_size],
                );
            });

            s.for_(len, |s, i| {
                gen_rc_op(
                    DerivedRcOp::DerivedRetain,
                    s,
                    instances,
                    globals,
                    &self.item_scheme,
                    s.ptr_get(
                        self.item_t,
                        s.buf_addr(self.item_t, s.field(me, F_ARR_DATA), i),
                    ),
                );
            });

            s.call(
                context.tal().memcpy(),
                &[
                    buf_to_data(&s, new_buf),
                    s.field(me, F_ARR_DATA),
                    s.mul(s.size(self.item_t), cap),
                ],
            );

            // Initialize refcount if the allocation was 'null' before.
            // The refcount is necessarily 1 immediately after a mutating operation.
            s.ptr_set(new_buf, s.i64(1));

            s.ret(s.make_struct(&[
                (F_ARR_DATA, buf_to_data(&s, new_buf)),
                (F_ARR_CAP, cap),
                (F_ARR_LEN, len),
            ]))
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

#[derive(Clone)]
pub struct CowArrayIoImpl<T: Context> {
    pub owned_byte_array: CowArrayImpl<T>,
    pub borrowed_byte_array: CowArrayImpl<T>,
    pub input: T::FunctionValue,
    pub output: T::FunctionValue,
    pub output_error: T::FunctionValue,
}

impl<T: Context> CowArrayIoImpl<T> {
    pub fn declare(
        context: &T,
        owned_byte_array: CowArrayImpl<T>,
        borrowed_byte_array: CowArrayImpl<T>,
    ) -> Self {
        let input = context.declare_func(
            "builtin_cow_array_input",
            &[],
            Some(owned_byte_array.array_t),
        );

        let output = context.declare_func(
            "builtin_cow_array_output",
            &[borrowed_byte_array.array_t],
            None,
        );

        let output_error = context.declare_func(
            "builtin_cow_array_output_error",
            &[borrowed_byte_array.array_t],
            None,
        );

        Self {
            owned_byte_array,
            borrowed_byte_array,
            input,
            output,
            output_error,
        }
    }

    pub fn define(&self, context: &T) {
        // define 'input'
        {
            let s = context.scope(self.input);

            s.call(context.tal().flush(), &[]);
            let array = s.alloca(self.owned_byte_array.array_t);
            s.ptr_set(array, s.call(self.owned_byte_array.new, &[]));

            let getchar_result = s.alloca(s.i32_t());
            s.while_(
                |s| {
                    let getchar_result_value = s.call(context.tal().getchar(), &[]);
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
                            &[s.ptr_get(self.owned_byte_array.array_t, array), input_byte],
                        ),
                    );
                },
            );

            s.ret(s.ptr_get(self.owned_byte_array.array_t, array));
        }

        // define 'output'
        {
            let s = context.scope(self.output);
            let me = s.arg(0);

            // TODO: check bytes_written for errors
            let _bytes_written = s.call_void(
                context.tal().write(),
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
            let s = context.scope(self.output_error);
            let me = s.arg(0);

            // TODO: check bytes_written for errors
            let _bytes_written = s.call_void(
                context.tal().write_error(),
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
