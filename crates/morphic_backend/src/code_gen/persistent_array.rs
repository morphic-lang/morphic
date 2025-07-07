//! A Clojure-style persistent array implementation.

// TODO:
// - Define 'obtain_unique' for array and implement 'extract' in terms of it so that we get the RC-1
//   optimization for nested arrays
// - We could optimize some memcpy calls by passing down the size of branches/leaves. Right now, we
//   just copy the whole thing, even if some slots are empty.

use crate::code_gen::array::{panic, ArrayImpl, ArrayIoImpl};
use crate::code_gen::fountain_pen::{Context, ProfileRc, Scope, Tal};
use crate::code_gen::{gen_rc_op, low_type_in_context, DerivedRcOp, Globals, Instances};
use morphic_common::data::mode_annot_ast::Mode;
use morphic_common::data::rc_specialized_ast::ModeScheme;

// Performance-tuning parameters
const LOG2_BRANCHING_FACTOR: u64 = 5;
const BRANCHING_FACTOR: u64 = 1 << LOG2_BRANCHING_FACTOR;
const MIN_LEAF_BYTES: u64 = 128;

// Fields of 'branch_type'
const F_BRANCH_REFCOUNT: u32 = 0; // i64
const F_BRANCH_CHILDREN: u32 = 1; // [_ x (branch | leaf)*]

// Fields of 'leaf_type'
const F_LEAF_REFCOUNT: u32 = 0; // i64
const F_LEAF_ITEMS: u32 = 1; // [_ x item]

// Fields of 'array_type'
const F_ARR_LEN: u32 = 0; // i64
const F_ARR_HEIGHT: u32 = 1; // i64
const F_ARR_TAIL: u32 = 2; // leaf*
const F_ARR_BODY: u32 = 3; // (branch | leaf)*

// Fields of 'hole_array_type'
const F_HOLE_IDX: u32 = 0; // i64
const F_HOLE_ARRAY: u32 = 1; // array

// Fields of return value of set_next_path
const F_CHILD_HEIGHT: u32 = 0; // i64
const F_CHILD_NODE_NUMBER: u32 = 1; // i64
const F_CHILD_INDEX: u32 = 2; // i64

pub fn persistent_array_t<T: Context>(context: &T) -> T::Type {
    return context.struct_t(&[
        context.i64_t(), // len
        context.i64_t(), // height
        context.ptr_t(), // tail
        context.ptr_t(), // body
    ]);
}

pub fn persistent_hole_array_t<T: Context>(context: &T) -> T::Type {
    return context.struct_t(&[
        context.i64_t(),             // idx
        persistent_array_t(context), // array
    ]);
}

fn get_items_per_leaf(item_bytes: u64) -> u64 {
    if item_bytes == 0 {
        unimplemented!("Persistent arrays of zero-sized types are not yet implemented");
    }

    let mut items_per_leaf = 1;
    while items_per_leaf * item_bytes < MIN_LEAF_BYTES as u64 {
        items_per_leaf *= 2;
    }
    items_per_leaf
}

#[derive(Clone)]
pub struct PersistentArrayImpl<T: Context> {
    mode: Mode,
    item_scheme: ModeScheme,
    items_per_leaf: u64,

    // related types
    branch_t: T::Type,
    leaf_t: T::Type,

    item_t: T::Type,
    array_t: T::Type,
    hole_array_t: T::Type,

    // helper functions
    print_branch_ptr: T::FunctionValue,
    print_leaf_ptr: T::FunctionValue,
    print_array: T::FunctionValue,

    set_next_path: T::FunctionValue,
    retain_node: T::FunctionValue,
    release_node: T::FunctionValue,
    retain_tail: T::FunctionValue,
    release_tail: T::FunctionValue,
    tail_len: T::FunctionValue,
    obtain_unique_leaf: T::FunctionValue,
    obtain_unique_branch: T::FunctionValue,
    obtain_unique_tail: T::FunctionValue,
    set_tail: T::FunctionValue,
    set_node: T::FunctionValue,
    set: T::FunctionValue,
    push_tail: T::FunctionValue,
    put_tail: T::FunctionValue,
    pop_tail: T::FunctionValue,
    pop_node: T::FunctionValue,

    // interface
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

impl<T: Context> PersistentArrayImpl<T> {
    pub fn declare(globals: &Globals<T>, scheme: &ModeScheme) -> Self {
        let context = &globals.context;

        let (ModeScheme::Array(mode, item_scheme) | ModeScheme::HoleArray(mode, item_scheme)) =
            scheme
        else {
            panic!();
        };

        let item_t = low_type_in_context(globals, &item_scheme.as_type());
        let i64_t = context.i64_t();
        let node_ptr_t = context.ptr_t();

        // Type declarations

        let items_per_leaf = get_items_per_leaf(context.get_abi_size(item_t));

        let branch_t = context.struct_t(&[
            i64_t,                                                // refcount
            context.array_t(node_ptr_t, BRANCHING_FACTOR as u32), // children
        ]);

        let leaf_t = context.struct_t(&[
            i64_t,                                          // refcount
            context.array_t(item_t, items_per_leaf as u32), // items
        ]);

        let branch_ptr_t = context.ptr_t();
        let leaf_ptr_t = context.ptr_t();

        let array_t = persistent_array_t(context);

        let hole_array_t = persistent_hole_array_t(context);

        // Convenience utilities

        let fun = |name: &str, args: &[T::Type], ret: T::Type| {
            context.declare_func(&format!("builtin_pers_array_{}", name), args, Some(ret))
        };

        let void_fun = |name: &str, args: &[T::Type]| {
            context.declare_func(&format!("builtin_pers_array_{}", name), args, None)
        };

        // Function declarations

        let print_branch_ptr = void_fun("print_branch", &[branch_ptr_t]);

        let print_leaf_ptr = void_fun("print_leaf", &[leaf_ptr_t]);

        let print_array = void_fun("print_array", &[array_t]);

        let new = fun("new", &[], array_t);

        let extract = fun(
            "extract",
            &[array_t, i64_t],
            context.struct_t(&[item_t, hole_array_t]),
        );

        let len = fun("len", &[array_t], i64_t);

        let push = fun("push", &[array_t, item_t], array_t);

        let pop = fun("pop", &[array_t], context.struct_t(&[array_t, item_t]));

        let replace = fun("replace", &[hole_array_t, item_t], array_t);

        let reserve = fun("reserve", &[array_t, i64_t], array_t);

        let retain_array = void_fun("retain", &[array_t]);

        let derived_retain_array = void_fun("derived_retain", &[array_t]);

        let release_array = void_fun("release", &[array_t]);

        let retain_hole = void_fun("retain_hole", &[hole_array_t]);

        let derived_retain_hole = void_fun("derived_retain_hole", &[hole_array_t]);

        let release_hole = void_fun("release_hole", &[hole_array_t]);

        let set_next_path = fun(
            "set_next_path",
            &[
                i64_t, // node height
                i64_t, // target node number
            ],
            context.struct_t(&[
                i64_t, // child height
                i64_t, // child node number
                i64_t, // child index
            ]),
        );

        let get = fun("get", &[array_t, i64_t], item_t);

        let retain_node = void_fun("retain_node", &[node_ptr_t, i64_t]);

        let release_node = void_fun("release_node", &[node_ptr_t, i64_t]);

        let retain_tail = void_fun("retain_tail", &[leaf_ptr_t]);

        let release_tail = void_fun("release_tail", &[leaf_ptr_t, i64_t]);

        let tail_len = fun("tail_len", &[i64_t], i64_t);

        let obtain_unique_leaf = fun("obtain_unique_leaf", &[leaf_ptr_t], leaf_ptr_t);

        let obtain_unique_branch =
            fun("obtain_unique_branch", &[branch_ptr_t, i64_t], branch_ptr_t);

        let obtain_unique_tail = fun("obtain_unique_tail", &[leaf_ptr_t, i64_t], leaf_ptr_t);

        let set_tail = fun("set_tail", &[leaf_ptr_t, i64_t, i64_t, item_t], leaf_ptr_t);

        let set_node = fun(
            "set_node",
            &[
                node_ptr_t, // node
                i64_t,      // node height
                i64_t,      // node number
                i64_t,      // index in child
                item_t,     // item
            ],
            node_ptr_t,
        );

        let set = fun("set", &[array_t, i64_t, item_t], array_t);

        let push_tail = fun("push_tail", &[leaf_ptr_t, i64_t, item_t], leaf_ptr_t);

        let put_tail = fun(
            "put_tail",
            &[
                branch_ptr_t, // branch
                i64_t,        // node height
                i64_t,        // node number
                leaf_ptr_t,   // tail
            ],
            branch_ptr_t,
        );

        let pop_tail = fun(
            "pop_tail",
            &[leaf_ptr_t, i64_t],
            context.struct_t(&[item_t, leaf_ptr_t]),
        );

        let pop_node = fun(
            "pop_node",
            &[
                branch_ptr_t, // branch
                i64_t,        // node height
                i64_t,        // node number
            ],
            context.struct_t(&[
                leaf_ptr_t,   // new tail
                branch_ptr_t, // new branch
            ]),
        );

        Self {
            mode: *mode,
            item_scheme: (**item_scheme).clone(),
            items_per_leaf,

            branch_t,
            leaf_t,

            item_t,
            array_t,
            hole_array_t,

            print_branch_ptr,
            print_leaf_ptr,
            print_array,

            set_next_path,
            retain_node,
            release_node,
            retain_tail,
            release_tail,
            tail_len,
            obtain_unique_leaf,
            obtain_unique_branch,
            obtain_unique_tail,
            set_tail,
            set_node,
            set,
            push_tail,
            put_tail,
            pop_tail,
            pop_node,

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

impl<T: Context> ArrayImpl<T> for PersistentArrayImpl<T> {
    fn define(&self, globals: &Globals<T>, instances: &mut Instances<T>) {
        let context = &globals.context;
        let i64_t = context.i64_t();
        let node_ptr_t = context.ptr_t();
        let branch_ptr_t = context.ptr_t();
        let leaf_ptr_t = context.ptr_t();

        // define 'print_branch_ptr'
        {
            let s = context.scope(self.print_branch_ptr);
            let branch = s.arg(0);
            s.if_else2(
                s.is_null(branch),
                |s| {
                    s.print("branch is null\n", &[]);
                },
                |s| {
                    s.print("branch %p:\n", &[branch]);
                    s.print(
                        "  refcount: %lld\n",
                        &[s.arrow(self.branch_t, i64_t, branch, F_BRANCH_REFCOUNT)],
                    );
                    s.print("  children:\n", &[]);
                    s.print("    [", &[]);
                    for i in 0..BRANCHING_FACTOR {
                        let child = s.arr_get(
                            node_ptr_t,
                            s.gep(self.branch_t, branch, F_BRANCH_CHILDREN),
                            s.i64(i),
                        );
                        if i > 0 {
                            s.print(", ", &[]);
                        }
                        s.print("%lld: %p", &[s.i64(i), child]);
                    }
                    s.print("]\n", &[]);
                },
            );
            s.ret_void();
        }

        // define 'print_leaf_ptr'
        {
            let s = context.scope(self.print_leaf_ptr);
            let leaf = s.arg(0);
            s.if_else2(
                s.is_null(leaf),
                |s| {
                    s.print("leaf is null\n", &[]);
                },
                |s| {
                    s.print("leaf %p:\n", &[leaf]);
                    s.print(
                        "  refcount: %lld\n",
                        &[s.arrow(self.leaf_t, i64_t, leaf, F_LEAF_REFCOUNT)],
                    );
                    s.print("  items: [", &[]);
                    for i in 0..self.items_per_leaf {
                        let item_ptr = s.gep(self.leaf_t, leaf, F_LEAF_ITEMS);

                        if i > 0 {
                            s.print(", ", &[]);
                        }

                        s.print("%lld: ", &[s.i64(i)]);

                        let item_size = context.get_abi_size(self.item_t);
                        for byte_idx in 0..item_size {
                            let byte = s.buf_get(context.i8_t(), item_ptr, s.i64(byte_idx));
                            if byte_idx > 0 && byte_idx % 8 == 0 {
                                s.print("_", &[]);
                            }
                            s.print("%02x", &[byte]);
                        }
                    }
                    s.print("]\n", &[]);
                },
            );
            s.ret_void();
        }

        // define 'print_array'
        {
            let s = context.scope(self.print_array);
            let array = s.arg(0);
            s.print("array:\n", &[]);
            s.print("  len: %lld\n", &[s.field(array, F_ARR_LEN)]);
            s.print("  height: %lld\n", &[s.field(array, F_ARR_HEIGHT)]);
            s.print("  tail: %p\n", &[s.field(array, F_ARR_TAIL)]);
            s.print("  body: %p\n", &[s.field(array, F_ARR_BODY)]);
            s.ret_void();
        }

        // define 'new'
        {
            let s = context.scope(self.new);
            s.ret(s.make_struct(
                self.array_t,
                &[
                    (F_ARR_LEN, s.i64(0)),
                    (F_ARR_HEIGHT, s.i64(-1i64 as u64)),
                    (F_ARR_TAIL, s.null()),
                    (F_ARR_BODY, s.null()),
                ],
            ));
        }

        // define 'extract'
        {
            let s = context.scope(self.extract);
            let arr = s.arg(0);
            let idx = s.arg(1);

            let len = s.field(arr, F_ARR_LEN);
            s.if_(s.uge(idx, len), |s| {
                panic::index_out_of_bounds(s, idx, len);
            });

            let hole_array =
                s.make_struct(self.hole_array_t, &[(F_HOLE_IDX, idx), (F_HOLE_ARRAY, arr)]);

            let item = s.call(self.get, &[arr, idx]);

            if !context.is_gc_on() {
                gen_rc_op(
                    DerivedRcOp::DerivedRetain,
                    &s,
                    instances,
                    globals,
                    &self.item_scheme,
                    item,
                );
            }

            s.ret(s.make_tup(&[item, hole_array]));
        }

        // define 'len'
        {
            let s = context.scope(self.len);
            let array = s.arg(0);
            s.ret(s.field(array, F_ARR_LEN));
        }

        // define 'push'
        {
            let s = context.scope(self.push);
            let array = s.arg(0);
            let item = s.arg(1);

            let len = s.field(array, F_ARR_LEN);
            let height = s.field(array, F_ARR_HEIGHT);

            s.if_(s.eq(len, s.i64(0)), |s| {
                let tail = s.calloc(s.usize(1), self.leaf_t);
                s.arrow_set(self.leaf_t, tail, F_LEAF_REFCOUNT, s.i64(1));
                s.arr_set(
                    self.item_t,
                    s.gep(self.leaf_t, tail, F_LEAF_ITEMS),
                    s.i32(0),
                    item,
                );

                s.ret(s.make_struct(
                    self.array_t,
                    &[
                        (F_ARR_LEN, s.i64(1)),
                        (F_ARR_HEIGHT, s.i64(-1i64 as u64)),
                        (F_ARR_TAIL, tail),
                        (F_ARR_BODY, s.null()),
                    ],
                ));
            });

            let tail_len = s.call(self.tail_len, &[len]);

            s.if_(s.ne(tail_len, s.i64(self.items_per_leaf)), |s| {
                let new_tail = s.call(
                    self.push_tail,
                    &[s.field(array, F_ARR_TAIL), tail_len, item],
                );

                s.ret(s.make_struct(
                    self.array_t,
                    &[
                        (F_ARR_LEN, s.add(len, s.i64(1))),
                        (F_ARR_HEIGHT, height),
                        (F_ARR_TAIL, new_tail),
                        (F_ARR_BODY, s.field(array, F_ARR_BODY)),
                    ],
                ));
            });

            s.if_(s.eq(len, s.i64(self.items_per_leaf)), |s| {
                let new_tail = s.calloc(s.usize(1), self.leaf_t);

                s.arrow_set(self.leaf_t, new_tail, F_LEAF_REFCOUNT, s.i64(1));
                s.arr_set(
                    self.item_t,
                    s.gep(self.leaf_t, new_tail, F_LEAF_ITEMS),
                    s.i64(0),
                    item,
                );

                s.ret(s.make_struct(
                    self.array_t,
                    &[
                        (F_ARR_LEN, s.add(len, s.i64(1))),
                        (F_ARR_HEIGHT, s.i64(0)),
                        (F_ARR_TAIL, new_tail),
                        (F_ARR_BODY, s.field(array, F_ARR_TAIL)),
                    ],
                ));
            });

            let next_missing_node_number =
                s.sll(s.i64(1), s.mul(height, s.i64(LOG2_BRANCHING_FACTOR)));
            let target_node_number = s.udiv(
                s.sub(len, s.i64(self.items_per_leaf)),
                s.i64(self.items_per_leaf),
            );

            s.if_(s.eq(next_missing_node_number, target_node_number), |s| {
                let new_body = s.calloc(s.usize(1), self.branch_t);
                s.arrow_set(self.branch_t, new_body, F_BRANCH_REFCOUNT, s.i64(1));
                s.arr_set(
                    node_ptr_t,
                    s.gep(self.branch_t, new_body, F_BRANCH_CHILDREN),
                    s.i32(0),
                    s.field(array, F_ARR_BODY),
                );

                let new_body = s.call(
                    self.put_tail,
                    &[
                        new_body,
                        s.add(s.field(array, F_ARR_HEIGHT), s.i64(1)),
                        next_missing_node_number,
                        s.field(array, F_ARR_TAIL),
                    ],
                );

                let new_tail = s.calloc(s.usize(1), self.leaf_t);
                s.arrow_set(self.leaf_t, new_tail, F_LEAF_REFCOUNT, s.i64(1));
                s.arr_set(
                    self.item_t,
                    s.gep(self.leaf_t, new_tail, F_LEAF_ITEMS),
                    s.i64(0),
                    item,
                );

                s.ret(s.make_struct(
                    self.array_t,
                    &[
                        (F_ARR_LEN, s.add(len, s.i64(1))),
                        (F_ARR_HEIGHT, s.add(height, s.i64(1))),
                        (F_ARR_TAIL, new_tail),
                        (F_ARR_BODY, new_body),
                    ],
                ));
            });

            let result = s.call(
                self.obtain_unique_branch,
                &[s.field(array, F_ARR_BODY), height],
            );

            let new_body = s.call(
                self.put_tail,
                &[
                    result,
                    height,
                    target_node_number,
                    s.field(array, F_ARR_TAIL),
                ],
            );

            let new_tail = s.calloc(s.usize(1), self.leaf_t);
            s.arrow_set(self.leaf_t, new_tail, F_LEAF_REFCOUNT, s.i64(1));
            s.arr_set(
                self.item_t,
                s.gep(self.leaf_t, new_tail, F_LEAF_ITEMS),
                s.i64(0),
                item,
            );
            s.arrow_set(self.leaf_t, new_tail, F_LEAF_REFCOUNT, s.i64(1));
            s.arr_set(
                self.item_t,
                s.gep(self.leaf_t, new_tail, F_LEAF_ITEMS),
                s.i64(0),
                item,
            );

            s.ret(s.make_struct(
                self.array_t,
                &[
                    (F_ARR_LEN, s.add(len, s.i64(1))),
                    (F_ARR_HEIGHT, height),
                    (F_ARR_TAIL, new_tail),
                    (F_ARR_BODY, new_body),
                ],
            ));
        }

        // define 'pop'
        {
            let s = context.scope(self.pop);
            let array = s.arg(0);
            let len = s.field(s.arg(0), F_ARR_LEN);

            s.if_(s.eq(len, s.i64(0)), |s| {
                panic::pop_empty(s);
            });

            s.if_(s.eq(len, s.i64(1)), |s| {
                let result_tail = s.call(
                    self.obtain_unique_tail,
                    &[s.field(array, F_ARR_TAIL), s.i64(1)],
                );

                let item = s.arr_get(
                    self.item_t,
                    s.gep(self.leaf_t, result_tail, F_LEAF_ITEMS),
                    s.i64(0),
                );

                s.free(result_tail);

                let empty_arr = s.call(self.new, &[]);

                s.ret(s.make_tup(&[empty_arr, item]));
            });

            let tail_len = s.call(self.tail_len, &[len]);

            s.if_(s.ne(tail_len, s.i64(1)), |s| {
                let poptail_ret = s.call(self.pop_tail, &[s.field(array, F_ARR_TAIL), tail_len]);

                let new_array = s.make_struct(
                    self.array_t,
                    &[
                        (F_ARR_LEN, s.sub(len, s.i64(1))),
                        (F_ARR_HEIGHT, s.field(array, F_ARR_HEIGHT)),
                        (F_ARR_TAIL, s.field(poptail_ret, 1)),
                        (F_ARR_BODY, s.field(array, F_ARR_BODY)),
                    ],
                );

                s.ret(s.make_tup(&[new_array, s.field(poptail_ret, 0)]));
            });

            let result_tail = s.call(
                self.obtain_unique_tail,
                &[s.field(array, F_ARR_TAIL), s.i64(1)],
            );

            let item = s.arr_get(
                self.item_t,
                s.gep(self.leaf_t, result_tail, F_LEAF_ITEMS),
                s.i64(0),
            );

            s.free(result_tail);

            s.if_(s.eq(len, s.i64(self.items_per_leaf + 1)), |s| {
                let new_array = s.make_struct(
                    self.array_t,
                    &[
                        (F_ARR_LEN, s.sub(len, s.i64(1))),
                        (F_ARR_HEIGHT, s.i64(-1i64 as u64)),
                        (F_ARR_TAIL, s.field(array, F_ARR_BODY)),
                        (F_ARR_BODY, s.null()),
                    ],
                );

                s.ret(s.make_tup(&[new_array, item]));
            });

            let new_array_len = s.sub(len, s.i64(1));
            let target_node_numebr =
                s.udiv(s.sub(new_array_len, s.i64(1)), s.i64(self.items_per_leaf));

            let pop_node_ret = s.call(
                self.pop_node,
                &[
                    s.field(array, F_ARR_BODY),
                    s.field(array, F_ARR_HEIGHT),
                    target_node_numebr,
                ],
            );

            s.if_(
                s.is_null(s.arr_get(
                    node_ptr_t,
                    s.gep(self.branch_t, s.field(pop_node_ret, 1), F_BRANCH_CHILDREN),
                    s.i64(1),
                )),
                |s| {
                    let grandchild = s.arr_get(
                        node_ptr_t,
                        s.gep(self.branch_t, s.field(pop_node_ret, 1), F_BRANCH_CHILDREN),
                        s.i64(0),
                    );

                    let new_array = s.make_struct(
                        self.array_t,
                        &[
                            (F_ARR_LEN, s.sub(len, s.i64(1))),
                            (F_ARR_HEIGHT, s.sub(s.field(array, F_ARR_HEIGHT), s.i64(1))),
                            (F_ARR_TAIL, s.field(pop_node_ret, 0)),
                            (F_ARR_BODY, grandchild),
                        ],
                    );

                    s.free(s.field(pop_node_ret, 1));

                    s.ret(s.make_tup(&[new_array, item]));
                },
            );

            let new_array = s.make_struct(
                self.array_t,
                &[
                    (F_ARR_LEN, s.sub(len, s.i64(1))),
                    (F_ARR_HEIGHT, s.field(array, F_ARR_HEIGHT)),
                    (F_ARR_TAIL, s.field(pop_node_ret, 0)),
                    (F_ARR_BODY, s.field(pop_node_ret, 1)),
                ],
            );

            s.ret(s.make_tup(&[new_array, item]));
        }

        // define 'replace'
        {
            let s = context.scope(self.replace);
            let hole = s.arg(0);
            let item = s.arg(1);

            let idx = s.field(hole, F_HOLE_IDX);
            let array = s.field(hole, F_HOLE_ARRAY);
            s.ret(s.call(self.set, &[array, idx, item]));
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
                self.retain_node,
                self.release_node,
                self.retain_tail,
                self.release_tail,
                self.retain_array,
                self.derived_retain_array,
                self.release_array,
                self.retain_hole,
                self.derived_retain_hole,
                self.release_hole,
            ] {
                let s = context.scope(func);
                s.panic(
                    &format!(
                        "{:?}: cannot use rc operations in garbage collected mode\n",
                        func
                    ),
                    &[],
                );
                s.ret_void();
            }
        } else {
            // define 'retain_node'
            {
                let s = context.scope(self.retain_node);
                let leaf_or_branch_ptr = s.arg(0);
                let height = s.arg(1);

                s.if_else2(
                    s.eq(height, s.i64(0)),
                    |s| {
                        let leaf_ptr = leaf_or_branch_ptr;
                        let refcount = s.arrow(self.leaf_t, i64_t, leaf_ptr, F_LEAF_REFCOUNT);
                        s.arrow_set(
                            self.leaf_t,
                            leaf_ptr,
                            F_LEAF_REFCOUNT,
                            s.add(refcount, s.i64(1)),
                        );
                    },
                    |s| {
                        let branch_ptr = leaf_or_branch_ptr;
                        let refcount = s.arrow(self.branch_t, i64_t, branch_ptr, F_BRANCH_REFCOUNT);
                        s.arrow_set(
                            self.branch_t,
                            branch_ptr,
                            F_BRANCH_REFCOUNT,
                            s.add(refcount, s.i64(1)),
                        );
                    },
                );

                s.ret_void();
            }

            // define 'release_node'
            {
                let s = context.scope(self.release_node);
                let leaf_or_branch_ptr = s.arg(0);
                let height = s.arg(1);

                s.if_else2(
                    s.eq(height, s.i64(0)),
                    |s| {
                        let leaf_ptr = leaf_or_branch_ptr;
                        let new_refcount = s.sub(
                            s.arrow(self.leaf_t, i64_t, leaf_ptr, F_LEAF_REFCOUNT),
                            s.i64(1),
                        );
                        s.arrow_set(self.leaf_t, leaf_ptr, F_LEAF_REFCOUNT, new_refcount);

                        s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                            s.for_(s.i64(self.items_per_leaf), |s, i| {
                                gen_rc_op(
                                    DerivedRcOp::Release,
                                    s,
                                    instances,
                                    globals,
                                    &self.item_scheme,
                                    s.arr_get(
                                        self.item_t,
                                        s.gep(self.leaf_t, leaf_ptr, F_LEAF_ITEMS),
                                        i,
                                    ),
                                )
                            });
                            s.free(leaf_ptr);
                        });
                    },
                    |s| {
                        let branch_ptr = leaf_or_branch_ptr;
                        let new_refcount = s.sub(
                            s.arrow(self.branch_t, i64_t, branch_ptr, F_BRANCH_REFCOUNT),
                            s.i64(1),
                        );
                        s.arrow_set(self.branch_t, branch_ptr, F_BRANCH_REFCOUNT, new_refcount);

                        s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                            let i = s.alloca(i64_t);
                            s.ptr_set(i, s.i64(0));

                            s.while_(
                                |s| {
                                    s.and_lazy(
                                        s.ult(s.ptr_get(i64_t, i), s.i64(BRANCHING_FACTOR)),
                                        |s| {
                                            s.not(s.is_null(s.arr_get(
                                                node_ptr_t,
                                                s.gep(self.branch_t, branch_ptr, F_BRANCH_CHILDREN),
                                                s.ptr_get(i64_t, i),
                                            )))
                                        },
                                    )
                                },
                                |s| {
                                    s.call_void(
                                        self.release_node,
                                        &[
                                            s.arr_get(
                                                node_ptr_t,
                                                s.gep(self.branch_t, branch_ptr, F_BRANCH_CHILDREN),
                                                s.ptr_get(i64_t, i),
                                            ),
                                            s.sub(height, s.i64(1)),
                                        ],
                                    );
                                    s.ptr_set(i, s.add(s.ptr_get(i64_t, i), s.i64(1)));
                                },
                            );
                            s.free(branch_ptr);
                        });
                    },
                );

                s.ret_void();
            }

            // define 'retain_tail'
            {
                let s = context.scope(self.retain_tail);
                let tail = s.arg(0);

                let refcount = s.arrow(self.leaf_t, i64_t, tail, F_LEAF_REFCOUNT);
                s.arrow_set(
                    self.leaf_t,
                    tail,
                    F_LEAF_REFCOUNT,
                    s.add(refcount, s.i64(1)),
                );

                s.ret_void();
            }

            // define 'release_tail'
            {
                let s = context.scope(self.release_tail);
                let tail = s.arg(0);
                let tail_len = s.arg(1);

                let refcount = s.arrow(self.leaf_t, i64_t, tail, F_LEAF_REFCOUNT);
                s.arrow_set(
                    self.leaf_t,
                    tail,
                    F_LEAF_REFCOUNT,
                    s.sub(refcount, s.i64(1)),
                );

                s.if_(
                    s.eq(s.arrow(self.leaf_t, i64_t, tail, F_LEAF_REFCOUNT), s.i64(0)),
                    |s| {
                        s.for_(tail_len, |s, i| {
                            gen_rc_op(
                                DerivedRcOp::Release,
                                s,
                                instances,
                                globals,
                                &self.item_scheme,
                                s.arr_get(self.item_t, s.gep(self.leaf_t, tail, F_LEAF_ITEMS), i),
                            );
                        });
                        s.free(tail);
                    },
                );

                s.ret_void();
            }

            // define 'retain_array'
            {
                let s = context.scope(self.retain_array);
                let array = s.arg(0);

                if let Some(prof_rc) = context.tal().prof_rc() {
                    s.call_void(prof_rc.record_retain(), &[]);
                }

                s.if_(s.not(s.eq(s.field(array, F_ARR_LEN), s.i64(0))), |s| {
                    s.call_void(self.retain_tail, &[s.field(array, F_ARR_TAIL)]);
                });

                s.if_(
                    s.ugt(s.field(array, F_ARR_LEN), s.i64(self.items_per_leaf)),
                    |s| {
                        s.call_void(
                            self.retain_node,
                            &[s.field(array, F_ARR_BODY), s.field(array, F_ARR_HEIGHT)],
                        );
                    },
                );

                s.ret_void();
            }

            // define 'derived_retain_array'
            {
                let s = context.scope(self.derived_retain_array);
                let array = s.arg(0);

                if self.mode == Mode::Owned {
                    if let Some(prof_rc) = context.tal().prof_rc() {
                        s.call_void(prof_rc.record_retain(), &[]);
                    }

                    s.if_(s.not(s.eq(s.field(array, F_ARR_LEN), s.i64(0))), |s| {
                        s.call_void(self.retain_tail, &[s.field(array, F_ARR_TAIL)]);
                    });

                    s.if_(
                        s.ugt(s.field(array, F_ARR_LEN), s.i64(self.items_per_leaf)),
                        |s| {
                            s.call_void(
                                self.retain_node,
                                &[s.field(array, F_ARR_BODY), s.field(array, F_ARR_HEIGHT)],
                            );
                        },
                    );
                }

                s.ret_void();
            }

            // define 'release_array'
            {
                let s = context.scope(self.release_array);
                let array = s.arg(0);

                if self.mode == Mode::Owned {
                    if let Some(prof_rc) = context.tal().prof_rc() {
                        s.call_void(prof_rc.record_release(), &[]);
                    }

                    s.if_(s.not(s.eq(s.field(array, F_ARR_LEN), s.i64(0))), |s| {
                        s.call_void(
                            self.release_tail,
                            &[
                                s.field(array, F_ARR_TAIL),
                                s.call(self.tail_len, &[s.field(array, F_ARR_LEN)]),
                            ],
                        );
                    });

                    s.if_(
                        s.ugt(s.field(array, F_ARR_LEN), s.i64(self.items_per_leaf)),
                        |s| {
                            s.call_void(
                                self.release_node,
                                &[s.field(array, F_ARR_BODY), s.field(array, F_ARR_HEIGHT)],
                            );
                        },
                    );
                }

                s.ret_void();
            }

            // define 'retain_hole'
            {
                let s = context.scope(self.retain_hole);
                let hole = s.arg(0);

                let array = s.field(hole, F_HOLE_ARRAY);
                s.call_void(self.retain_array, &[array]);
                s.ret_void();
            }

            // define 'derived_retain_hole'
            {
                let s = context.scope(self.derived_retain_hole);
                let hole = s.arg(0);

                let array = s.field(hole, F_HOLE_ARRAY);
                s.call_void(self.derived_retain_array, &[array]);
                s.ret_void();
            }

            // define 'release_hole'
            {
                let s = context.scope(self.release_hole);
                let hole = s.arg(0);

                let array = s.field(hole, F_HOLE_ARRAY);
                s.call_void(self.release_array, &[array]);
                s.ret_void();
            }
        }

        // define 'set_next_path'
        {
            let s = context.scope(self.set_next_path);
            let node_height = s.arg(0);
            let node_number = s.arg(1);

            let num_shift_bits = s.mul(s.sub(node_height, s.i64(1)), s.i64(LOG2_BRANCHING_FACTOR));

            let child_index = s.srl(node_number, num_shift_bits);

            let child_node_number = s.sub(node_number, s.sll(child_index, num_shift_bits));

            let child_node_height = s.sub(node_height, s.i64(1));

            s.ret(s.make_tup(&[child_node_height, child_node_number, child_index]));
        }

        // define 'get'
        {
            let s = context.scope(self.get);
            let array = s.arg(0);
            let index = s.arg(1);

            s.if_(s.uge(index, s.field(array, F_ARR_LEN)), |s| {
                panic::index_out_of_bounds(s, index, s.field(array, F_ARR_LEN));
            });

            s.if_(
                s.eq(s.field(array, F_ARR_HEIGHT), s.i64(-1i64 as u64)),
                |s| {
                    s.ret(s.arr_get(
                        self.item_t,
                        s.gep(self.leaf_t, s.field(array, F_ARR_TAIL), F_LEAF_ITEMS),
                        index,
                    ));
                },
            );

            let target_node_number = s.udiv(index, s.i64(self.items_per_leaf));

            let tail_node_number = s.udiv(
                s.sub(s.field(array, F_ARR_LEN), s.i64(1)),
                s.i64(self.items_per_leaf),
            );

            let index_in_leaf = s.urem(index, s.i64(self.items_per_leaf));

            s.if_(s.eq(target_node_number, tail_node_number), |s| {
                s.ret(s.arr_get(
                    self.item_t,
                    s.gep(self.leaf_t, s.field(array, F_ARR_TAIL), F_LEAF_ITEMS),
                    index_in_leaf,
                ));
            });

            let curr_node = s.alloca(context.ptr_t());
            s.ptr_set(curr_node, s.field(array, F_ARR_BODY));

            let curr_node_height = s.alloca(i64_t);
            s.ptr_set(curr_node_height, s.field(array, F_ARR_HEIGHT));

            let curr_node_number = s.alloca(i64_t);
            s.ptr_set(curr_node_number, target_node_number);

            s.while_(
                |s| s.not(s.eq(s.ptr_get(i64_t, curr_node_height), s.i64(0))),
                |s| {
                    let child_info = s.call(
                        self.set_next_path,
                        &[
                            s.ptr_get(i64_t, curr_node_height),
                            s.ptr_get(i64_t, curr_node_number),
                        ],
                    );

                    s.ptr_set(curr_node_height, s.field(child_info, F_CHILD_HEIGHT));
                    s.ptr_set(curr_node_number, s.field(child_info, F_CHILD_NODE_NUMBER));

                    s.ptr_set(
                        curr_node,
                        s.arr_get(
                            node_ptr_t,
                            s.gep(
                                self.branch_t,
                                s.ptr_get(node_ptr_t, curr_node),
                                F_BRANCH_CHILDREN,
                            ),
                            s.field(child_info, F_CHILD_INDEX),
                        ),
                    );
                },
            );

            let target_leaf = s.ptr_get(node_ptr_t, curr_node);

            s.ret(s.arr_get(
                self.item_t,
                s.gep(self.leaf_t, target_leaf, F_LEAF_ITEMS),
                index_in_leaf,
            ));
        }

        // define 'tail_len'
        {
            let s = context.scope(self.tail_len);
            let len = s.arg(0);

            s.ret(s.add(
                s.urem(s.sub(len, s.i64(1)), s.i64(self.items_per_leaf)),
                s.i64(1),
            ));
        }

        // define 'obtain_unique_leaf'
        {
            let s = context.scope(self.obtain_unique_leaf);
            let leaf = s.arg(0);

            if context.is_gc_on() {
                let result = s.calloc(s.usize(1), self.leaf_t);
                s.arrow_set(self.leaf_t, result, F_LEAF_REFCOUNT, s.i64(1));
                s.call(
                    context.tal().memcpy(),
                    &[
                        s.gep(self.leaf_t, result, F_LEAF_ITEMS),
                        s.gep(self.leaf_t, leaf, F_LEAF_ITEMS),
                        s.mul(s.size(self.item_t), s.usize(self.items_per_leaf)),
                    ],
                );

                s.ret(result);
            } else {
                s.if_(
                    s.eq(s.arrow(self.leaf_t, i64_t, leaf, F_LEAF_REFCOUNT), s.i64(1)),
                    |s| {
                        s.ret(leaf);
                    },
                );

                let result = s.calloc(s.usize(1), self.leaf_t);
                s.arrow_set(self.leaf_t, result, F_LEAF_REFCOUNT, s.i64(1));
                s.call(
                    context.tal().memcpy(),
                    &[
                        s.gep(self.leaf_t, result, F_LEAF_ITEMS),
                        s.gep(self.leaf_t, leaf, F_LEAF_ITEMS),
                        s.mul(s.size(self.item_t), s.usize(self.items_per_leaf)),
                    ],
                );

                s.for_(s.i64(self.items_per_leaf), |s, i| {
                    gen_rc_op(
                        DerivedRcOp::DerivedRetain,
                        s,
                        instances,
                        globals,
                        &self.item_scheme,
                        s.arr_get(self.item_t, s.gep(self.leaf_t, leaf, F_LEAF_ITEMS), i),
                    );
                });

                let refcount = s.arrow(self.leaf_t, i64_t, leaf, F_LEAF_REFCOUNT);
                s.arrow_set(
                    self.leaf_t,
                    leaf,
                    F_LEAF_REFCOUNT,
                    s.sub(refcount, s.i64(1)),
                );

                s.ret(result);
            }
        }

        // define 'obtain_unique_branch'
        {
            let s = context.scope(self.obtain_unique_branch);
            let branch = s.arg(0);
            let height = s.arg(1);

            if context.is_gc_on() {
                let result = s.calloc(s.usize(1), self.branch_t);
                s.arrow_set(self.branch_t, result, F_BRANCH_REFCOUNT, s.i64(1));
                s.call(
                    context.tal().memcpy(),
                    &[
                        s.gep(self.branch_t, result, F_BRANCH_CHILDREN),
                        s.gep(self.branch_t, branch, F_BRANCH_CHILDREN),
                        s.mul(s.size(node_ptr_t), s.usize(BRANCHING_FACTOR)),
                    ],
                );

                s.ret(result);
            } else {
                s.if_(
                    s.eq(
                        s.arrow(self.branch_t, i64_t, branch, F_BRANCH_REFCOUNT),
                        s.i64(1),
                    ),
                    |s| {
                        s.ret(branch);
                    },
                );

                let result = s.calloc(s.usize(1), self.branch_t);
                s.arrow_set(self.branch_t, result, F_BRANCH_REFCOUNT, s.i64(1));
                s.call(
                    context.tal().memcpy(),
                    &[
                        s.gep(self.branch_t, result, F_BRANCH_CHILDREN),
                        s.gep(self.branch_t, branch, F_BRANCH_CHILDREN),
                        s.mul(s.size(node_ptr_t), s.usize(BRANCHING_FACTOR)),
                    ],
                );

                let i = s.alloca(i64_t);
                s.ptr_set(i, s.i64(0));
                s.while_(
                    |s| {
                        s.and_lazy(s.ult(s.ptr_get(i64_t, i), s.i64(BRANCHING_FACTOR)), |s| {
                            s.not(s.is_null(s.arr_get(
                                node_ptr_t,
                                s.gep(self.branch_t, branch, F_BRANCH_CHILDREN),
                                s.ptr_get(i64_t, i),
                            )))
                        })
                    },
                    |s| {
                        s.call_void(
                            self.retain_node,
                            &[
                                s.arr_get(
                                    node_ptr_t,
                                    s.gep(self.branch_t, branch, F_BRANCH_CHILDREN),
                                    s.ptr_get(i64_t, i),
                                ),
                                s.sub(height, s.i64(1)),
                            ],
                        );
                        s.ptr_set(i, s.add(s.ptr_get(i64_t, i), s.i64(1)));
                    },
                );

                s.arrow_set(
                    self.branch_t,
                    branch,
                    F_BRANCH_REFCOUNT,
                    s.sub(
                        s.arrow(self.branch_t, i64_t, branch, F_BRANCH_REFCOUNT),
                        s.i64(1),
                    ),
                );

                s.ret(result);
            }
        }

        // define 'obtain_unique_tail'
        {
            let s = context.scope(self.obtain_unique_tail);
            let tail = s.arg(0);
            let tail_len = s.arg(1);

            if context.is_gc_on() {
                let result = s.calloc(s.usize(1), self.leaf_t);
                s.arrow_set(self.leaf_t, result, F_LEAF_REFCOUNT, s.i64(1));
                s.call(
                    context.tal().memcpy(),
                    &[
                        s.gep(self.leaf_t, result, F_LEAF_ITEMS),
                        s.gep(self.leaf_t, tail, F_LEAF_ITEMS),
                        s.mul(s.size(self.item_t), tail_len),
                    ],
                );

                s.ret(result);
            } else {
                let refcount = s.arrow(self.leaf_t, i64_t, tail, F_LEAF_REFCOUNT);

                s.if_(s.eq(refcount, s.i64(1)), |s| {
                    s.ret(tail);
                });

                let result = s.calloc(s.usize(1), self.leaf_t);
                s.arrow_set(self.leaf_t, result, F_LEAF_REFCOUNT, s.i64(1));
                s.call(
                    context.tal().memcpy(),
                    &[
                        s.gep(self.leaf_t, result, F_LEAF_ITEMS),
                        s.gep(self.leaf_t, tail, F_LEAF_ITEMS),
                        s.mul(s.size(self.item_t), tail_len),
                    ],
                );

                s.for_(tail_len, |s, i| {
                    gen_rc_op(
                        DerivedRcOp::DerivedRetain,
                        s,
                        instances,
                        globals,
                        &self.item_scheme,
                        s.arr_get(self.item_t, s.gep(self.leaf_t, tail, F_LEAF_ITEMS), i),
                    );
                });

                s.arrow_set(
                    self.leaf_t,
                    tail,
                    F_LEAF_REFCOUNT,
                    s.sub(refcount, s.i64(1)),
                );

                s.ret(result);
            }
        }

        // define 'set_tail'
        {
            let s = context.scope(self.set_tail);
            let tail = s.arg(0);
            let tail_len = s.arg(1);
            let index_in_tail = s.arg(2);
            let item = s.arg(3);

            if self.mode == Mode::Owned {
                let result = s.call(self.obtain_unique_tail, &[tail, tail_len]);

                if !context.is_gc_on() {
                    gen_rc_op(
                        DerivedRcOp::Release,
                        &s,
                        instances,
                        globals,
                        &self.item_scheme,
                        s.arr_get(
                            self.item_t,
                            s.gep(self.leaf_t, result, F_LEAF_ITEMS),
                            index_in_tail,
                        ),
                    );
                }

                s.arr_set(
                    self.item_t,
                    s.gep(self.leaf_t, result, F_LEAF_ITEMS),
                    index_in_tail,
                    item,
                );

                s.ret(result);
            } else {
                s.panic("cannot call set_tail on a borrowed array", &[]);
                s.ret(s.undef(leaf_ptr_t))
            }
        }

        // define 'set_node'
        {
            let s = context.scope(self.set_node);
            let node = s.arg(0);
            let node_height = s.arg(1);
            let node_number = s.arg(2);
            let index_in_child = s.arg(3);
            let item = s.arg(4);

            if self.mode == Mode::Owned {
                s.if_(s.eq(node_height, s.i64(0)), |s| {
                    let result = s.call(self.obtain_unique_leaf, &[node]);

                    if !context.is_gc_on() {
                        gen_rc_op(
                            DerivedRcOp::Release,
                            s,
                            instances,
                            globals,
                            &self.item_scheme,
                            s.arr_get(
                                self.item_t,
                                s.gep(self.leaf_t, result, F_LEAF_ITEMS),
                                index_in_child,
                            ),
                        );
                    }

                    s.arr_set(
                        self.item_t,
                        s.gep(self.leaf_t, result, F_LEAF_ITEMS),
                        index_in_child,
                        item,
                    );

                    s.ret(result);
                });

                let result = s.call(self.obtain_unique_branch, &[node, node_height]);

                let child_info = s.call(self.set_next_path, &[node_height, node_number]);

                let child_index = s.field(child_info, F_CHILD_INDEX);
                let child_node_number = s.field(child_info, F_CHILD_NODE_NUMBER);
                let child_node_height = s.field(child_info, F_CHILD_HEIGHT);

                let child_node = s.call(
                    self.set_node,
                    &[
                        s.arr_get(
                            node_ptr_t,
                            s.gep(self.branch_t, result, F_BRANCH_CHILDREN),
                            child_index,
                        ),
                        child_node_height,
                        child_node_number,
                        index_in_child,
                        item,
                    ],
                );

                s.arr_set(
                    node_ptr_t,
                    s.gep(self.branch_t, result, F_BRANCH_CHILDREN),
                    child_index,
                    child_node,
                );

                s.ret(result);
            } else {
                s.panic("cannot call set_node on a borrowed array", &[]);
                s.ret(s.undef(branch_ptr_t))
            }
        }

        // define 'set'
        {
            let s = context.scope(self.set);
            let array = s.arg(0);
            let index = s.arg(1);
            let item = s.arg(2);

            let len = s.field(array, F_ARR_LEN);
            let height = s.field(array, F_ARR_HEIGHT);

            s.if_(s.uge(index, len), |s| {
                panic::index_out_of_bounds(s, index, len);
            });

            let target_node_number = s.udiv(index, s.i64(self.items_per_leaf));

            let tail_node_number = s.udiv(s.sub(len, s.i64(1)), s.i64(self.items_per_leaf));

            let index_in_leaf = s.urem(index, s.i64(self.items_per_leaf));

            s.if_(s.eq(target_node_number, tail_node_number), |s| {
                let tail_len = s.call(self.tail_len, &[len]);

                let new_tail = s.call(
                    self.set_tail,
                    &[s.field(array, F_ARR_TAIL), tail_len, index_in_leaf, item],
                );

                s.ret(s.make_struct(
                    self.array_t,
                    &[
                        (F_ARR_LEN, len),
                        (F_ARR_HEIGHT, height),
                        (F_ARR_TAIL, new_tail),
                        (F_ARR_BODY, s.field(array, F_ARR_BODY)),
                    ],
                ));
            });

            let new_body = s.call(
                self.set_node,
                &[
                    s.field(array, F_ARR_BODY),
                    height,
                    target_node_number,
                    index_in_leaf,
                    item,
                ],
            );

            s.ret(s.make_struct(
                self.array_t,
                &[
                    (F_ARR_LEN, len),
                    (F_ARR_HEIGHT, height),
                    (F_ARR_TAIL, s.field(array, F_ARR_TAIL)),
                    (F_ARR_BODY, new_body),
                ],
            ));
        }

        // define 'push_tail'
        {
            let s = context.scope(self.push_tail);

            let tail = s.arg(0);
            let tail_len = s.arg(1);
            let item = s.arg(2);

            let result = s.call(self.obtain_unique_tail, &[tail, tail_len]);

            s.arr_set(
                self.item_t,
                s.gep(self.leaf_t, result, F_LEAF_ITEMS),
                tail_len,
                item,
            );

            s.ret(result);
        }

        // define 'put_tail'
        {
            let s = context.scope(self.put_tail);

            let branch = s.arg(0);
            let node_height = s.arg(1);
            let node_number = s.arg(2);
            let tail = s.arg(3);

            let result = s.call(self.obtain_unique_branch, &[branch, node_height]);

            s.if_(s.eq(node_height, s.i64(1)), |s| {
                s.arr_set(
                    node_ptr_t,
                    s.gep(self.branch_t, result, F_BRANCH_CHILDREN),
                    node_number,
                    tail,
                );

                s.ret(result);
            });

            let child_info = s.call(self.set_next_path, &[node_height, node_number]);

            let child_index = s.field(child_info, F_CHILD_INDEX);
            let child_node_number = s.field(child_info, F_CHILD_NODE_NUMBER);
            let child_node_height = s.field(child_info, F_CHILD_HEIGHT);

            let children = s.gep(self.branch_t, result, F_BRANCH_CHILDREN);

            s.if_(
                s.is_null(s.arr_get(node_ptr_t, children, child_index)),
                |s| {
                    let sub_child = s.calloc(s.usize(1), self.branch_t);
                    s.arrow_set(self.branch_t, sub_child, F_BRANCH_REFCOUNT, s.i64(1));

                    s.arr_set(node_ptr_t, children, child_index, sub_child);
                },
            );

            let child_location = s.arr_get(node_ptr_t, children, child_index);

            let new_child = s.call(
                self.put_tail,
                &[child_location, child_node_height, child_node_number, tail],
            );

            s.arr_set(node_ptr_t, children, child_index, new_child);

            s.ret(result);
        }

        // define 'pop_tail'
        {
            let s = context.scope(self.pop_tail);
            let tail = s.arg(0);
            let tail_len = s.arg(1);

            let result = s.call(self.obtain_unique_tail, &[tail, tail_len]);

            let item = s.arr_get(
                self.item_t,
                s.gep(self.leaf_t, result, F_LEAF_ITEMS),
                s.sub(tail_len, s.i64(1)),
            );

            s.ret(s.make_tup(&[item, result]));
        }

        // define 'pop_node'
        {
            let s = context.scope(self.pop_node);
            let branch = s.arg(0);
            let node_height = s.arg(1);
            let node_number = s.arg(2);

            let result = s.call(self.obtain_unique_branch, &[branch, node_height]);

            s.if_(s.eq(node_height, s.i64(1)), |s| {
                let new_tail = s.arr_get(
                    node_ptr_t,
                    s.gep(self.branch_t, result, F_BRANCH_CHILDREN),
                    node_number,
                );

                s.arr_set(
                    node_ptr_t,
                    s.gep(self.branch_t, result, F_BRANCH_CHILDREN),
                    node_number,
                    s.null(),
                );

                s.if_(s.eq(node_number, s.i64(0)), |s| {
                    s.free(result);

                    s.ret(s.make_tup(&[new_tail, s.null()]));
                });

                s.ret(s.make_tup(&[new_tail, result]));
            });

            let child_info = s.call(self.set_next_path, &[node_height, node_number]);

            let child_index = s.field(child_info, F_CHILD_INDEX);
            let child_node_number = s.field(child_info, F_CHILD_NODE_NUMBER);
            let child_node_height = s.field(child_info, F_CHILD_HEIGHT);

            let child_location = s.arr_get(
                node_ptr_t,
                s.gep(self.branch_t, result, F_BRANCH_CHILDREN),
                child_index,
            );
            let popnode_ret = s.call(
                self.pop_node,
                &[child_location, child_node_height, child_node_number],
            );

            s.if_(s.eq(node_number, s.i64(0)), |s| {
                s.free(result);

                s.ret(s.make_tup(&[s.field(popnode_ret, 0), s.null()]));
            });

            s.arr_set(
                node_ptr_t,
                s.gep(self.branch_t, result, F_BRANCH_CHILDREN),
                child_index,
                s.field(popnode_ret, 1),
            );

            s.ret(s.make_tup(&[s.field(popnode_ret, 0), result]));
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
pub struct PersistentArrayIoImpl<T: Context> {
    // related types
    owned_byte_array: PersistentArrayImpl<T>,
    borrowed_byte_array: PersistentArrayImpl<T>,

    // public API
    input: T::FunctionValue,
    output: T::FunctionValue,
    output_error: T::FunctionValue,

    // helper functions
    output_tail: T::FunctionValue,
    output_node: T::FunctionValue,
    output_tail_error: T::FunctionValue,
    output_node_error: T::FunctionValue,
}

impl<T: Context> PersistentArrayIoImpl<T> {
    pub fn declare(
        globals: &Globals<T>,
        owned_byte_array: PersistentArrayImpl<T>,
        borrowed_byte_array: PersistentArrayImpl<T>,
    ) -> Self {
        let context = &globals.context;

        let input = context.declare_func(
            "builtin_pers_array_input",
            &[],
            Some(owned_byte_array.array_t),
        );

        // Used to declare both 'output' and 'output_error'
        let declare_output_with = |suffix| {
            let this_output = context.declare_func(
                &format!("builtin_pers_array_output{}", suffix),
                &[borrowed_byte_array.array_t],
                None,
            );

            let this_output_tail = context.declare_func(
                &format!("builtin_pers_array_output_tail{}", suffix),
                &[context.ptr_t(), context.i64_t()],
                None,
            );

            let this_output_node = context.declare_func(
                &format!("builtin_pers_array_output_node{}", suffix),
                &[context.ptr_t(), context.i64_t()],
                None,
            );

            (this_output, this_output_tail, this_output_node)
        };

        let (output, output_tail, output_node) = declare_output_with("");
        let (output_error, output_tail_error, output_node_error) = declare_output_with("_error");

        Self {
            // related types
            owned_byte_array,
            borrowed_byte_array,

            // public API
            input,
            output,
            output_error,

            // helper functions
            output_tail,
            output_node,
            output_tail_error,
            output_node_error,
        }
    }
}

impl<T: Context> ArrayIoImpl<T> for PersistentArrayIoImpl<T> {
    fn define(&self, globals: &Globals<T>) {
        let context = &globals.context;

        let i64_t = context.i64_t();
        let node_ptr_t = context.ptr_t();
        let array_t = self.owned_byte_array.array_t;
        let branch_t = self.owned_byte_array.branch_t;
        let leaf_t = self.owned_byte_array.leaf_t;

        // define 'input'
        {
            let s = context.scope(self.input);

            s.call(context.tal().flush(), &[]);

            let array = s.alloca(array_t);

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
                    let input_bytes = s.truncate(s.i8_t(), s.ptr_get(s.i32_t(), getchar_result));
                    let new_arr = s.call(
                        self.owned_byte_array.push,
                        &[s.ptr_get(array_t, array), input_bytes],
                    );
                    s.ptr_set(array, new_arr);
                },
            );

            s.ret(s.ptr_get(array_t, array));
        }

        // Used to define both 'output' and 'output_error'
        let define_output_with = |this_output, this_output_tail, this_output_node, tal_write| {
            // define 'output' / 'output_error'
            {
                let s = context.scope(this_output);
                let array = s.arg(0);

                let tail = s.field(array, F_ARR_TAIL);
                let body = s.field(array, F_ARR_BODY);
                let height = s.field(array, F_ARR_HEIGHT);
                let len = s.field(array, F_ARR_LEN);

                s.if_(s.not(s.is_null(body)), |s| {
                    s.call_void(this_output_node, &[body, height]);
                });

                let tail_len = s.call(self.owned_byte_array.tail_len, &[len]);

                s.if_(s.not(s.is_null(tail)), |s| {
                    s.call_void(this_output_tail, &[tail, tail_len]);
                });

                s.ret_void();
            }

            // define 'output_tail' / 'output_tail_error'
            {
                let s = context.scope(this_output_tail);
                let tail = s.arg(0);
                let tail_len = s.arg(1);

                let items = s.gep(leaf_t, tail, F_LEAF_ITEMS);
                // TODO: check bytes_written for errors
                let _bytes_written = s.call_void(
                    tal_write,
                    &[items, s.usize(1), s.int_cast(s.usize_t(), tail_len)],
                );

                s.ret_void();
            }

            // define 'output_node' / 'output_node_error'
            {
                let s = context.scope(this_output_node);
                let branch = s.arg(0);
                let height = s.arg(1);

                let i = s.alloca(i64_t);
                s.ptr_set(i, s.i64(0));

                s.if_(s.eq(height, s.i64(0)), |s| {
                    let items_per_leaf = get_items_per_leaf(1);

                    // TODO: check bytes_written for errors
                    let _bytes_written =
                        s.call_void(tal_write, &[branch, s.usize(1), s.usize(items_per_leaf)]);

                    s.ret_void();
                });

                s.while_(
                    |s| {
                        s.and_lazy(s.ult(s.ptr_get(i64_t, i), s.i64(BRANCHING_FACTOR)), |s| {
                            s.not(s.is_null(s.arr_get(
                                node_ptr_t,
                                s.gep(branch_t, branch, F_BRANCH_CHILDREN),
                                s.ptr_get(i64_t, i),
                            )))
                        })
                    },
                    |s| {
                        s.call_void(
                            this_output_node,
                            &[
                                s.arr_get(
                                    node_ptr_t,
                                    s.gep(branch_t, branch, F_BRANCH_CHILDREN),
                                    s.ptr_get(i64_t, i),
                                ),
                                s.sub(height, s.i64(1)),
                            ],
                        );
                        s.ptr_set(i, s.add(s.ptr_get(i64_t, i), s.i64(1)));
                    },
                );

                s.ret_void();
            }
        };

        define_output_with(
            self.output,
            self.output_tail,
            self.output_node,
            context.tal().write(),
        );
        define_output_with(
            self.output_error,
            self.output_tail_error,
            self.output_node_error,
            context.tal().write_error(),
        );
    }

    fn input(&self) -> <T as Context>::FunctionValue {
        self.input
    }

    fn output(&self) -> <T as Context>::FunctionValue {
        self.output
    }

    fn output_error(&self) -> <T as Context>::FunctionValue {
        self.output_error
    }
}
