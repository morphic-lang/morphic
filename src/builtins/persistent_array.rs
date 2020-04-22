use crate::builtins::array::{ArrayImpl, ArrayInterface};
use crate::builtins::fountain_pen::scope;
use crate::builtins::libc::LibC;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::TargetData;
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::FunctionValue;
use inkwell::AddressSpace;
use std::convert::TryInto;

// Performance-tuning parameters
const LOG2_BRANCHING_FACTOR: u64 = 5;
const BRANCHING_FACTOR: u64 = 1 << LOG2_BRANCHING_FACTOR;
const MIN_LEAF_BYTES: u64 = 128;

// Fields of 'branch_type'
const F_BRANCH_REFCOUNT: u32 = 0;
const F_BRANCH_CHILDREN: u32 = 1;

// Fields of 'leaf_type'
const F_LEAF_REFCOUNT: u32 = 0;
const F_LEAF_ITEMS: u32 = 1;

// Fields of 'array_type'
const F_ARR_LEN: u32 = 0;
const F_ARR_HEIGHT: u32 = 1;
const F_ARR_TAIL: u32 = 2;
const F_ARR_BODY: u32 = 3;

// Fields of 'hole_array_type'
const F_HOLE_IDX: u32 = 0;
const F_HOLE_ARRAY: u32 = 1;

// Fields of return value of set_next_path
const F_CHILD_HEIGHT: u32 = 0;
const F_CHILD_NODE_NUMBER: u32 = 1;
const F_CHILD_INDEX: u32 = 2;

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

#[derive(Clone, Copy, Debug)]
pub struct PersistentArrayImpl<'a> {
    interface: ArrayInterface<'a>,

    // related types
    branch_type: BasicTypeEnum<'a>,
    leaf_type: BasicTypeEnum<'a>,

    // helper functions
    set_next_path: FunctionValue<'a>,
    get: FunctionValue<'a>,
    retain_node: FunctionValue<'a>,
    release_node: FunctionValue<'a>,
    retain_tail: FunctionValue<'a>,
    release_tail: FunctionValue<'a>,
    tail_len: FunctionValue<'a>,
    obtain_unique_leaf: FunctionValue<'a>,
    obtain_unique_branch: FunctionValue<'a>,
    obtain_unique_tail: FunctionValue<'a>,
    set_tail: FunctionValue<'a>,
    set_node: FunctionValue<'a>,
    set: FunctionValue<'a>,
    push_tail: FunctionValue<'a>,
    put_tail: FunctionValue<'a>,
    pop_tail: FunctionValue<'a>,
    pop_node: FunctionValue<'a>,
}

impl<'a> PersistentArrayImpl<'a> {
    pub fn declare(
        context: &'a Context,
        _target: &TargetData,
        module: &Module<'a>,
        item_type: BasicTypeEnum<'a>,
    ) -> Self {
        let void_type = context.void_type();
        let i64_type = context.i64_type();
        let node_ptr_type = context.i8_type().ptr_type(AddressSpace::Generic);

        // Type declarations

        let branch_type = context.opaque_struct_type("builtin_pers_array_branch");
        let leaf_type = context.opaque_struct_type("builtin_pers_array_leaf");

        let branch_ptr_type = branch_type.ptr_type(AddressSpace::Generic);
        let leaf_ptr_type = leaf_type.ptr_type(AddressSpace::Generic);

        let array_type = context.struct_type(
            &[
                // len
                i64_type.into(),
                // height
                i64_type.into(),
                // tail
                leaf_type.ptr_type(AddressSpace::Generic).into(),
                // body
                node_ptr_type.into(),
            ],
            false,
        );

        let hole_array_type = context.struct_type(
            &[
                // idx
                i64_type.into(),
                // array
                array_type.into(),
            ],
            false,
        );

        // Convenience utilities
        let fun = |name: &str, ret: BasicTypeEnum<'a>, args: &[BasicTypeEnum<'a>]| {
            module.add_function(
                &format!("builtin_pers_array_{}", name),
                ret.fn_type(args, false),
                Some(Linkage::Internal),
            )
        };

        let void_fun = |name: &str, args: &[BasicTypeEnum<'a>]| {
            module.add_function(
                &format!("builtin_pers_array_{}", name),
                void_type.fn_type(args, false),
                Some(Linkage::Internal),
            )
        };

        // Function declarations

        let new = fun("new", array_type.into(), &[]);

        let item = fun(
            "item",
            context
                .struct_type(&[item_type, hole_array_type.into()], false)
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

        let set_next_path = fun(
            "set_next_path",
            context
                .struct_type(
                    &[
                        // child height
                        i64_type.into(),
                        // child node number
                        i64_type.into(),
                        // child index
                        i64_type.into(),
                    ],
                    false,
                )
                .into(),
            &[
                // node height
                i64_type.into(),
                // target node number
                i64_type.into(),
            ],
        );

        let get = fun(
            "get",
            item_type.into(),
            &[array_type.into(), i64_type.into()],
        );

        let retain_node = void_fun("retain_node", &[node_ptr_type.into(), i64_type.into()]);

        let release_node = void_fun("release_node", &[node_ptr_type.into(), i64_type.into()]);

        let retain_tail = void_fun("retain_tail", &[leaf_ptr_type.into()]);

        let release_tail = void_fun("release_tail", &[leaf_ptr_type.into(), i64_type.into()]);

        let tail_len = fun("tail_len", i64_type.into(), &[i64_type.into()]);

        let obtain_unique_leaf = fun(
            "obtain_unique_leaf",
            leaf_ptr_type.into(),
            &[leaf_ptr_type.into()],
        );

        let obtain_unique_branch = fun(
            "obtain_unique_branch",
            branch_ptr_type.into(),
            &[branch_ptr_type.into(), i64_type.into()],
        );

        let obtain_unique_tail = fun(
            "obtain_unique_tail",
            leaf_ptr_type.into(),
            &[leaf_ptr_type.into(), i64_type.into()],
        );

        let set_tail = fun(
            "set_tail",
            leaf_ptr_type.into(),
            &[
                leaf_ptr_type.into(),
                i64_type.into(),
                i64_type.into(),
                item_type.into(),
            ],
        );

        let set_node = fun(
            "set_node",
            node_ptr_type.into(),
            &[
                // node
                node_ptr_type.into(),
                // node height
                i64_type.into(),
                // node number
                i64_type.into(),
                // index in child
                i64_type.into(),
                // item
                item_type.into(),
            ],
        );

        let set = fun(
            "set",
            array_type.into(),
            &[array_type.into(), i64_type.into(), item_type.into()],
        );

        let push_tail = fun(
            "push_tail",
            leaf_ptr_type.into(),
            &[leaf_ptr_type.into(), i64_type.into(), item_type.into()],
        );

        let put_tail = fun(
            "put_tail",
            branch_ptr_type.into(),
            &[
                // branch
                branch_ptr_type.into(),
                // node height
                i64_type.into(),
                // node number
                i64_type.into(),
                // tail
                leaf_ptr_type.into(),
            ],
        );

        let pop_tail = fun(
            "pop_tail",
            context
                .struct_type(&[item_type.into(), leaf_ptr_type.into()], false)
                .into(),
            &[leaf_ptr_type.into(), i64_type.into()],
        );

        let pop_node = fun(
            "pop_node",
            context
                .struct_type(
                    &[
                        // new tail
                        leaf_ptr_type.into(),
                        // new branch
                        branch_ptr_type.into(),
                    ],
                    false,
                )
                .into(),
            &[
                // branch
                branch_ptr_type.into(),
                // node height
                i64_type.into(),
                // node number
                i64_type.into(),
            ],
        );

        let interface = ArrayInterface {
            item_type,
            array_type: array_type.into(),
            hole_array_type: hole_array_type.into(),

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

        Self {
            interface,

            branch_type: branch_type.into(),
            leaf_type: leaf_type.into(),

            set_next_path,
            get,
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
        }
    }
}

impl<'a> ArrayImpl<'a> for PersistentArrayImpl<'a> {
    fn define(
        &self,
        context: &'a Context,
        target: &TargetData,
        libc: &LibC<'a>,
        item_retain: Option<FunctionValue<'a>>,
        item_release: Option<FunctionValue<'a>>,
    ) {
        // Compute constants
        let items_per_leaf = get_items_per_leaf(target.get_abi_size(&self.interface.item_type));

        // Define types
        {
            let i64_type = context.i64_type();

            let node_ptr_type = context.i8_type().ptr_type(AddressSpace::Generic);

            self.branch_type.into_struct_type().set_body(
                &[
                    // refcount
                    i64_type.into(),
                    // children
                    node_ptr_type
                        .array_type(BRANCHING_FACTOR.try_into().unwrap())
                        .into(),
                ],
                false,
            );

            self.leaf_type.into_struct_type().set_body(
                &[
                    // refcount
                    i64_type.into(),
                    // items
                    self.interface
                        .item_type
                        .array_type(items_per_leaf as u32)
                        .into(),
                ],
                false,
            );
        }

        // define 'new'
        {
            let s = scope(self.interface.new, context);
            s.ret(s.make_struct(
                self.interface.array_type,
                &[
                    (F_ARR_LEN, s.i64(0)),
                    (F_ARR_HEIGHT, s.i64(-1i64 as u64)),
                    (F_ARR_TAIL, s.null(self.leaf_type.into())),
                    (F_ARR_BODY, s.null(s.i8_t())),
                ],
            ));
        }

        // define 'item'
        {
            let s = scope(self.interface.item, context);
            let arr = s.arg(0);
            let idx = s.arg(1);

            let len = s.field(arr, F_ARR_LEN);
            s.if_(s.uge(idx, len), |s| {
                s.panic(
                    "idx %d is out of bounds for persistent array of length %d",
                    &[idx, len],
                    libc,
                )
            });

            s.call_void(self.interface.retain_array, &[arr]);

            let hole_array = s.make_struct(
                self.interface.hole_array_type,
                &[(F_HOLE_IDX, idx), (F_HOLE_ARRAY, arr)],
            );

            let item = s.call(self.get, &[arr, idx]);

            let item_ptr = s.alloca(self.interface.item_type);
            s.ptr_set(item_ptr, item);

            if let Some(item_retain) = item_retain {
                s.call_void(item_retain, &[item_ptr]);
            }

            s.ret(s.make_tup(&[item, hole_array]));
        }

        // define 'len'
        {
            let s = scope(self.interface.len, context);
            let array = s.arg(0);
            s.ret(s.field(array, F_ARR_LEN));
        }

        // define 'push'
        {
            let s = scope(self.interface.push, context);
            let array = s.arg(0);
            let item = s.arg(1);

            let len = s.field(array, F_ARR_LEN);
            let height = s.field(array, F_ARR_HEIGHT);

            s.if_(s.eq(len, s.i64(0)), |s| {
                let tail = s.calloc(s.i64(1), self.leaf_type.into(), libc);
                s.arrow_set(tail, F_LEAF_REFCOUNT, s.i64(1));
                s.arr_set(s.gep(tail, F_LEAF_ITEMS), s.i32(0), item);

                s.ret(s.make_struct(
                    self.interface.array_type,
                    &[
                        (F_ARR_LEN, s.i64(1)),
                        (F_ARR_HEIGHT, s.i64(-1i64 as u64)),
                        (F_ARR_TAIL, tail),
                        (F_ARR_BODY, s.null(s.i8_t())),
                    ],
                ));
            });

            let tail_len = s.call(self.tail_len, &[len]);

            s.if_(s.ne(tail_len, s.i64(items_per_leaf)), |s| {
                let new_tail = s.call(
                    self.push_tail,
                    &[s.field(array, F_ARR_TAIL), tail_len, item],
                );

                s.ret(s.make_struct(
                    self.interface.array_type,
                    &[
                        (F_ARR_LEN, s.add(len, s.i64(1))),
                        (F_ARR_HEIGHT, height),
                        (F_ARR_TAIL, new_tail),
                        (F_ARR_BODY, s.field(array, F_ARR_BODY)),
                    ],
                ));
            });

            s.if_(s.eq(len, s.i64(items_per_leaf)), |s| {
                let new_tail = s.calloc(s.i64(1), self.leaf_type.into(), libc);

                s.arrow_set(new_tail, F_LEAF_REFCOUNT, s.i64(1));
                s.arr_set(s.gep(new_tail, F_LEAF_ITEMS), s.i64(0), item);

                s.ret(s.make_struct(
                    self.interface.array_type,
                    &[
                        (F_ARR_LEN, s.add(len, s.i64(1))),
                        (F_ARR_HEIGHT, s.i64(0)),
                        (F_ARR_TAIL, new_tail),
                        (F_ARR_BODY, s.ptr_cast(s.i8_t(), s.field(array, F_ARR_TAIL))),
                    ],
                ));
            });

            let next_missing_node_number =
                s.sll(s.i64(1), s.mul(height, s.i64(LOG2_BRANCHING_FACTOR)));
            let target_node_number =
                s.udiv(s.sub(len, s.i64(items_per_leaf)), s.i64(items_per_leaf));

            s.if_(s.eq(next_missing_node_number, target_node_number), |s| {
                let new_body = s.calloc(s.i64(1), self.branch_type.into(), libc);
                s.arrow_set(new_body, F_BRANCH_REFCOUNT, s.i64(1));
                s.arr_set(
                    s.gep(new_body, F_BRANCH_CHILDREN),
                    s.i32(0),
                    s.ptr_cast(s.i8_t(), s.field(array, F_ARR_BODY)),
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

                let new_tail = s.calloc(s.i64(1), self.leaf_type.into(), libc);
                s.arrow_set(new_tail, F_LEAF_REFCOUNT, s.i64(1));
                s.arr_set(s.gep(new_tail, F_LEAF_ITEMS), s.i64(0), item);

                s.ret(s.make_struct(
                    self.interface.array_type,
                    &[
                        (F_ARR_LEN, s.add(len, s.i64(1))),
                        (F_ARR_HEIGHT, s.add(height, s.i64(1))),
                        (F_ARR_TAIL, new_tail),
                        (F_ARR_BODY, s.ptr_cast(s.i8_t(), new_body)),
                    ],
                ));
            });

            let result = s.call(
                self.obtain_unique_branch,
                &[
                    s.ptr_cast(self.branch_type.into(), s.field(array, F_ARR_BODY)),
                    height,
                ],
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

            let new_tail = s.calloc(s.i64(1), self.leaf_type.into(), libc);
            s.arrow_set(new_tail, F_LEAF_REFCOUNT, s.i64(1));
            s.arr_set(s.gep(new_tail, F_LEAF_ITEMS), s.i64(0), item);
            s.arrow_set(new_tail, F_LEAF_REFCOUNT, s.i64(1));
            s.arr_set(s.gep(new_tail, F_LEAF_ITEMS), s.i64(0), item);

            s.ret(s.make_struct(
                self.interface.array_type,
                &[
                    (F_ARR_LEN, s.add(len, s.i64(1))),
                    (F_ARR_HEIGHT, height),
                    (F_ARR_TAIL, new_tail),
                    (F_ARR_BODY, s.ptr_cast(s.i8_t(), new_body)),
                ],
            ));
        }

        // define 'pop'
        {
            let s = scope(self.interface.pop, context);
            let array = s.arg(0);
            let len = s.field(s.arg(0), F_ARR_LEN);

            s.if_(s.eq(len, s.i64(0)), |s| {
                s.panic("pop: empty array", &[], libc)
            });

            s.if_(s.eq(len, s.i64(1)), |s| {
                let item = s.arr_get(s.gep(s.field(array, F_ARR_TAIL), F_LEAF_ITEMS), s.i64(0));

                s.free(s.field(array, F_ARR_TAIL), libc);

                let empty_arr = s.call(self.interface.new, &[]);

                s.ret(s.make_tup(&[empty_arr, item]));
            });

            let tail_len = s.call(self.tail_len, &[len]);

            s.if_(s.ne(tail_len, s.i64(1)), |s| {
                let poptail_ret = s.call(self.pop_tail, &[s.field(array, F_ARR_TAIL), tail_len]);

                let new_array = s.make_struct(
                    self.interface.array_type,
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

            let item = s.arr_get(s.gep(result_tail, F_LEAF_ITEMS), s.i64(0));

            s.free(result_tail, libc);

            s.if_(s.eq(len, s.i64(items_per_leaf + 1)), |s| {
                let new_array = s.make_struct(
                    self.interface.array_type,
                    &[
                        (F_ARR_LEN, s.sub(len, s.i64(1))),
                        (F_ARR_HEIGHT, s.i64(-1i64 as u64)),
                        (
                            F_ARR_TAIL,
                            s.ptr_cast(self.leaf_type.into(), s.field(array, F_ARR_BODY)),
                        ),
                        (F_ARR_BODY, s.null(s.i8_t())),
                    ],
                );

                s.ret(s.make_tup(&[new_array, item]));
            });

            let new_array_len = s.sub(len, s.i64(1));
            let target_node_numebr = s.udiv(s.sub(new_array_len, s.i64(1)), s.i64(items_per_leaf));

            let pop_node_ret = s.call(
                self.pop_node,
                &[
                    s.ptr_cast(self.branch_type.into(), s.field(array, F_ARR_BODY)),
                    s.field(array, F_ARR_HEIGHT),
                    target_node_numebr,
                ],
            );

            s.if_(
                s.is_null(s.arr_get(s.gep(s.field(pop_node_ret, 1), F_BRANCH_CHILDREN), s.i64(1))),
                |s| {
                    let grandchild =
                        s.arr_get(s.gep(s.field(pop_node_ret, 1), F_BRANCH_CHILDREN), s.i64(0));

                    let new_array = s.make_struct(
                        self.interface.array_type,
                        &[
                            (F_ARR_LEN, s.sub(len, s.i64(1))),
                            (F_ARR_HEIGHT, s.sub(s.field(array, F_ARR_HEIGHT), s.i64(1))),
                            (F_ARR_TAIL, s.field(pop_node_ret, 0)),
                            (F_ARR_BODY, grandchild),
                        ],
                    );

                    s.free(s.field(pop_node_ret, 1), libc);

                    s.ret(s.make_tup(&[new_array, item]));
                },
            );

            let new_array = s.make_struct(
                self.interface.array_type,
                &[
                    (F_ARR_LEN, s.sub(len, s.i64(1))),
                    (F_ARR_HEIGHT, s.field(array, F_ARR_HEIGHT)),
                    (F_ARR_TAIL, s.field(pop_node_ret, 0)),
                    (F_ARR_BODY, s.ptr_cast(s.i8_t(), s.field(pop_node_ret, 1))),
                ],
            );

            s.ret(s.make_tup(&[new_array, item]));
        }

        // define 'replace'
        {
            let s = scope(self.interface.replace, context);
            let hole = s.arg(0);
            let item = s.arg(1);

            let idx = s.field(hole, F_HOLE_IDX);
            let array = s.field(hole, F_HOLE_ARRAY);
            s.ret(s.call(self.set, &[array, idx, item]));
        }

        // define 'retain_array'
        {
            let s = scope(self.interface.retain_array, context);
            let array = s.arg(0);

            s.if_(s.not(s.eq(s.field(array, F_ARR_LEN), s.i64(0))), |s| {
                s.call_void(self.retain_tail, &[s.field(array, F_ARR_TAIL)]);
            });

            s.if_(
                s.ugt(s.field(array, F_ARR_LEN), s.i64(items_per_leaf)),
                |s| {
                    s.call_void(
                        self.retain_node,
                        &[s.field(array, F_ARR_BODY), s.field(array, F_ARR_HEIGHT)],
                    );
                },
            );

            s.ret_void();
        }

        // define 'release_array'
        {
            let s = scope(self.interface.release_array, context);
            let array = s.arg(0);

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
                s.ugt(s.field(array, F_ARR_LEN), s.i64(items_per_leaf)),
                |s| {
                    s.call_void(
                        self.release_node,
                        &[s.field(array, F_ARR_BODY), s.field(array, F_ARR_HEIGHT)],
                    );
                },
            );

            s.ret_void();
        }

        // define 'retain_hole'
        {
            let s = scope(self.interface.retain_hole, context);
            let hole = s.arg(0);

            let array = s.field(hole, F_HOLE_ARRAY);
            s.call_void(self.interface.retain_array, &[array]);
            s.ret_void();
        }

        // define 'release_hole'
        {
            let s = scope(self.interface.release_hole, context);
            let hole = s.arg(0);

            let array = s.field(hole, F_HOLE_ARRAY);
            s.call_void(self.interface.release_array, &[array]);
            s.ret_void();
        }

        // define 'set_next_path'
        {
            let s = scope(self.set_next_path, context);
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
            let s = scope(self.get, context);
            let array = s.arg(0);
            let index = s.arg(1);

            s.if_(s.uge(index, s.field(array, F_ARR_LEN)), |s| {
                s.panic(
                    "index out of bounds: attempt to access item %lld of array with length %llu",
                    &[index, s.field(array, F_ARR_LEN)],
                    libc,
                );
            });

            s.if_(
                s.eq(s.field(array, F_ARR_HEIGHT), s.i64(-1i64 as u64)),
                |s| {
                    s.ret(s.arr_get(s.gep(s.field(array, F_ARR_TAIL), F_LEAF_ITEMS), index));
                },
            );

            let target_node_number = s.udiv(index, s.i64(items_per_leaf));

            let tail_node_number = s.udiv(
                s.sub(s.field(array, F_ARR_LEN), s.i64(1)),
                s.i64(items_per_leaf),
            );

            let index_in_leaf = s.urem(index, s.i64(items_per_leaf));

            s.if_(s.eq(target_node_number, tail_node_number), |s| {
                s.ret(s.arr_get(
                    s.gep(s.field(array, F_ARR_TAIL), F_LEAF_ITEMS),
                    index_in_leaf,
                ));
            });

            let curr_node = s.alloca(context.i8_type().ptr_type(AddressSpace::Generic).into());
            s.ptr_set(curr_node, s.ptr_cast(s.i8_t(), s.field(array, F_ARR_BODY)));

            let curr_node_height = s.alloca(s.i64_t());
            s.ptr_set(curr_node_height, s.field(array, F_ARR_HEIGHT));

            let curr_node_number = s.alloca(s.i64_t());
            s.ptr_set(curr_node_number, target_node_number);

            s.while_(
                |s| s.not(s.eq(s.ptr_get(curr_node_height), s.i64(0))),
                |s| {
                    let child_info = s.call(
                        self.set_next_path,
                        &[s.ptr_get(curr_node_height), s.ptr_get(curr_node_number)],
                    );

                    s.ptr_set(curr_node_height, s.field(child_info, F_CHILD_HEIGHT));
                    s.ptr_set(curr_node_number, s.field(child_info, F_CHILD_NODE_NUMBER));

                    s.ptr_set(
                        curr_node,
                        s.arr_get(
                            s.gep(
                                s.ptr_cast(self.branch_type.into(), s.ptr_get(curr_node)),
                                F_BRANCH_CHILDREN,
                            ),
                            s.field(child_info, F_CHILD_INDEX),
                        ),
                    );
                },
            );

            let target_leaf = s.ptr_cast(self.leaf_type.into(), s.ptr_get(curr_node));

            s.ret(s.arr_get(s.gep(target_leaf, F_LEAF_ITEMS), index_in_leaf));
        }

        // define 'retain_node'
        {
            let s = scope(self.retain_node, context);
            let leaf_or_branch_ptr = s.arg(0);
            let height = s.arg(1);

            s.if_else(
                s.eq(height, s.i64(0)),
                |s| {
                    let leaf_ptr = s.ptr_cast(self.leaf_type.into(), leaf_or_branch_ptr);
                    let refcount = s.arrow(leaf_ptr, F_LEAF_REFCOUNT);
                    s.arrow_set(leaf_ptr, F_LEAF_REFCOUNT, s.add(refcount, s.i64(1)));
                },
                |s| {
                    let branch_ptr = s.ptr_cast(self.branch_type.into(), leaf_or_branch_ptr);
                    let refcount = s.arrow(branch_ptr, F_BRANCH_REFCOUNT);
                    s.arrow_set(branch_ptr, F_BRANCH_REFCOUNT, s.add(refcount, s.i64(1)));
                },
            );

            s.ret_void();
        }

        // define 'release_node'
        {
            let s = scope(self.release_node, context);
            let leaf_or_branch_ptr = s.arg(0);
            let height = s.arg(1);

            s.if_else(
                s.eq(height, s.i64(0)),
                |s| {
                    let leaf_ptr = s.ptr_cast(self.leaf_type.into(), leaf_or_branch_ptr);
                    let new_refcount = s.sub(s.arrow(leaf_ptr, F_LEAF_REFCOUNT), s.i64(1));
                    s.arrow_set(leaf_ptr, F_LEAF_REFCOUNT, new_refcount);

                    s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                        if let Some(item_release) = item_release {
                            s.for_(s.i64(items_per_leaf), |s, i| {
                                s.call_void(
                                    item_release,
                                    &[s.arr_addr(s.gep(leaf_ptr, F_LEAF_ITEMS), i)],
                                );
                            });
                        }
                        s.free(leaf_ptr, libc);
                    });
                },
                |s| {
                    let branch_ptr = s.ptr_cast(self.branch_type.into(), leaf_or_branch_ptr);
                    let new_refcount = s.sub(s.arrow(branch_ptr, F_BRANCH_REFCOUNT), s.i64(1));
                    s.arrow_set(branch_ptr, F_BRANCH_REFCOUNT, new_refcount);

                    s.if_(s.eq(new_refcount, s.i64(0)), |s| {
                        let i = s.alloca(s.i64_t());
                        s.ptr_set(i, s.i64(0));

                        s.while_(
                            |s| {
                                s.and_lazy(s.ult(s.ptr_get(i), s.i64(BRANCHING_FACTOR)), |s| {
                                    s.not(s.is_null(s.arr_get(
                                        s.gep(branch_ptr, F_BRANCH_CHILDREN),
                                        s.ptr_get(i),
                                    )))
                                })
                            },
                            |s| {
                                s.call_void(
                                    self.release_node,
                                    &[
                                        s.arr_get(
                                            s.gep(branch_ptr, F_BRANCH_CHILDREN),
                                            s.ptr_get(i),
                                        ),
                                        s.sub(height, s.i64(1)),
                                    ],
                                );
                                s.ptr_set(i, s.add(s.ptr_get(i), s.i64(1)));
                            },
                        );
                        s.free(branch_ptr, libc);
                    });
                },
            );

            s.ret_void();
        }

        // define 'retain_tail'
        {
            let s = scope(self.retain_tail, context);
            let tail = s.arg(0);

            let refcount = s.arrow(tail, F_LEAF_REFCOUNT);
            s.arrow_set(tail, F_LEAF_REFCOUNT, s.add(refcount, s.i64(1)));

            s.ret_void();
        }

        // define 'release_tail'
        {
            let s = scope(self.release_tail, context);
            let tail = s.arg(0);
            let tail_len = s.arg(1);

            let refcount = s.arrow(tail, F_LEAF_REFCOUNT);
            s.arrow_set(tail, F_LEAF_REFCOUNT, s.sub(refcount, s.i64(1)));

            s.if_(s.eq(s.arrow(tail, F_LEAF_REFCOUNT), s.i64(0)), |s| {
                if let Some(item_release) = item_release {
                    s.for_(tail_len, |s, i| {
                        s.call_void(item_release, &[s.arr_addr(s.gep(tail, F_LEAF_ITEMS), i)]);
                    })
                }
                s.free(tail, libc);
            });

            s.ret_void();
        }

        // define 'tail_len'
        {
            let s = scope(self.tail_len, context);
            let len = s.arg(0);

            s.ret(s.add(
                s.urem(s.sub(len, s.i64(1)), s.i64(items_per_leaf)),
                s.i64(1),
            ));
        }

        // define 'obtain_unique_leaf'
        {
            let s = scope(self.obtain_unique_leaf, context);
            let leaf = s.arg(0);

            s.if_(s.eq(s.arrow(leaf, F_LEAF_REFCOUNT), s.i64(1)), |s| {
                s.ret(leaf);
            });

            let result = s.calloc(s.i64(1), self.leaf_type.into(), libc);
            s.arrow_set(result, F_LEAF_REFCOUNT, s.i64(1));

            s.ptr_set(
                s.gep(result, F_LEAF_ITEMS),
                s.ptr_get(s.gep(leaf, F_LEAF_ITEMS)),
            );

            if let Some(item_retain) = item_retain {
                s.for_(s.i64(items_per_leaf), |s, i| {
                    s.call_void(item_retain, &[s.arr_addr(s.gep(leaf, F_LEAF_ITEMS), i)]);
                });
            }

            let refcount = s.arrow(leaf, F_LEAF_REFCOUNT);
            s.arrow_set(leaf, F_LEAF_REFCOUNT, s.sub(refcount, s.i64(1)));

            s.ret(result);
        }

        // define 'obtain_unique_branch'
        {
            let s = scope(self.obtain_unique_branch, context);
            let branch = s.arg(0);
            let height = s.arg(1);

            s.if_(s.eq(s.arrow(branch, F_BRANCH_REFCOUNT), s.i64(1)), |s| {
                s.ret(branch);
            });

            let result = s.calloc(s.i64(1), self.branch_type.into(), libc);
            s.arrow_set(result, F_BRANCH_REFCOUNT, s.i64(1));
            s.arrow_set(
                result,
                F_BRANCH_CHILDREN,
                s.arrow(branch, F_BRANCH_CHILDREN),
            );

            let i = s.alloca(s.i64_t());
            s.ptr_set(i, s.i64(0));
            s.while_(
                |s| {
                    s.and_lazy(s.ult(s.ptr_get(i), s.i64(BRANCHING_FACTOR)), |s| {
                        s.not(s.is_null(s.arr_get(s.gep(branch, F_BRANCH_CHILDREN), s.ptr_get(i))))
                    })
                },
                |s| {
                    s.call_void(
                        self.retain_node,
                        &[
                            s.arr_get(s.gep(branch, F_BRANCH_CHILDREN), s.ptr_get(i)),
                            s.sub(height, s.i64(1)),
                        ],
                    );
                },
            );

            s.arrow_set(
                branch,
                F_BRANCH_REFCOUNT,
                s.sub(s.arrow(branch, F_BRANCH_REFCOUNT), s.i64(1)),
            );

            s.ret(result);
        }

        // define 'obtain_unique_tail'
        {
            let s = scope(self.obtain_unique_tail, context);
            let tail = s.arg(0);
            let tail_len = s.arg(1);

            let refcount = s.arrow(tail, F_LEAF_REFCOUNT);

            s.if_(s.eq(refcount, s.i64(1)), |s| {
                s.ret(tail);
            });

            let result = s.calloc(s.i64(1), self.leaf_type.into(), libc);
            s.arrow_set(result, F_LEAF_REFCOUNT, s.i64(1));
            s.call(
                libc.memcpy,
                &[
                    s.ptr_cast(s.i8_t(), s.gep(result, F_LEAF_ITEMS)),
                    s.ptr_cast(s.i8_t(), s.gep(tail, F_LEAF_ITEMS)),
                    s.mul(s.size(self.interface.item_type), tail_len),
                ],
            );

            if let Some(item_retain) = item_retain {
                s.for_(tail_len, |s, i| {
                    s.call_void(item_retain, &[s.arr_addr(s.gep(tail, F_LEAF_ITEMS), i)]);
                });
            }

            s.arrow_set(tail, F_LEAF_REFCOUNT, s.sub(refcount, s.i64(1)));

            s.ret(result);
        }

        // define 'set_tail'
        {
            let s = scope(self.set_tail, context);
            let tail = s.arg(0);
            let tail_len = s.arg(1);
            let index_in_tail = s.arg(2);
            let item = s.arg(3);

            let result = s.call(self.obtain_unique_tail, &[tail, tail_len]);

            if let Some(item_release) = item_release {
                s.call_void(
                    item_release,
                    &[s.arr_addr(s.gep(result, F_LEAF_ITEMS), index_in_tail)],
                );
            }
            s.arr_set(s.gep(result, F_LEAF_ITEMS), index_in_tail, item);

            s.ret(result);
        }

        // define 'set_node'
        {
            let s = scope(self.set_node, context);
            let node = s.arg(0);
            let node_height = s.arg(1);
            let node_number = s.arg(2);
            let index_in_child = s.arg(3);
            let item = s.arg(4);

            s.if_(s.eq(node_height, s.i64(0)), |s| {
                let result = s.call(
                    self.obtain_unique_leaf,
                    &[s.ptr_cast(self.leaf_type.into(), node)],
                );

                if let Some(item_release) = item_release {
                    s.call_void(
                        item_release,
                        &[s.arr_addr(s.gep(result, F_LEAF_ITEMS), index_in_child)],
                    );
                };

                s.arr_set(s.gep(result, F_LEAF_ITEMS), index_in_child, item);

                s.ret(s.ptr_cast(s.i8_t(), result));
            });

            let result = s.call(
                self.obtain_unique_branch,
                &[s.ptr_cast(self.branch_type.into(), node), node_height],
            );

            let child_info = s.call(self.set_next_path, &[node_height, node_number]);

            let child_index = s.field(child_info, F_CHILD_INDEX);
            let child_node_number = s.field(child_info, F_CHILD_NODE_NUMBER);
            let child_node_height = s.field(child_info, F_CHILD_HEIGHT);

            let child_node = s.call(
                self.set_node,
                &[
                    s.arr_get(s.gep(result, F_BRANCH_CHILDREN), child_index),
                    child_node_height,
                    child_node_number,
                    index_in_child,
                    item,
                ],
            );

            s.arr_set(s.gep(result, F_BRANCH_CHILDREN), child_index, child_node);

            s.ret(s.ptr_cast(s.i8_t(), result));
        }

        // define 'set'
        {
            let s = scope(self.set, context);
            let array = s.arg(0);
            let index = s.arg(1);
            let item = s.arg(2);

            let len = s.field(array, F_ARR_LEN);
            let height = s.field(array, F_ARR_HEIGHT);

            s.if_(s.uge(index, len), |s| {
                s.panic(
                    "index out of bounds: attempt to set item %lld of array with length %llu",
                    &[index, len],
                    libc,
                );
            });

            let target_node_number = s.udiv(index, s.i64(items_per_leaf));

            let tail_node_number = s.udiv(s.sub(len, s.i64(1)), s.i64(items_per_leaf));

            let index_in_leaf = s.urem(index, s.i64(items_per_leaf));

            s.if_(s.eq(target_node_number, tail_node_number), |s| {
                let tail_len = s.call(self.tail_len, &[len]);

                let new_tail = s.call(
                    self.set_tail,
                    &[s.field(array, F_ARR_TAIL), tail_len, index_in_leaf, item],
                );

                s.ret(s.make_struct(
                    self.interface.array_type,
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
                self.interface.array_type,
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
            let s = scope(self.push_tail, context);

            let tail = s.arg(0);
            let tail_len = s.arg(1);
            let item = s.arg(2);

            let result = s.call(self.obtain_unique_tail, &[tail, tail_len]);

            s.arr_set(s.gep(result, F_LEAF_ITEMS), tail_len, item);

            s.ret(result);
        }

        // define 'put_tail'
        {
            let s = scope(self.put_tail, context);

            let branch = s.arg(0);
            let node_height = s.arg(1);
            let node_number = s.arg(2);
            let tail = s.arg(3);

            let result = s.call(self.obtain_unique_branch, &[branch, node_height]);

            s.if_(s.eq(node_height, s.i64(1)), |s| {
                s.arr_set(
                    s.gep(result, F_BRANCH_CHILDREN),
                    node_number,
                    s.ptr_cast(s.i8_t(), tail),
                );

                s.ret(result);
            });

            let child_info = s.call(self.set_next_path, &[node_height, node_number]);

            let child_index = s.field(child_info, F_CHILD_INDEX);
            let child_node_number = s.field(child_info, F_CHILD_NODE_NUMBER);
            let child_node_height = s.field(child_info, F_CHILD_HEIGHT);

            let children = s.gep(result, F_BRANCH_CHILDREN);

            s.if_(s.is_null(s.arr_get(children, child_index)), |s| {
                let sub_child = s.calloc(s.i64(1), self.branch_type.into(), libc);
                s.arrow_set(sub_child, F_BRANCH_REFCOUNT, s.i64(1));

                s.arr_set(children, child_index, s.ptr_cast(s.i8_t(), sub_child));
            });

            let child_location = s.arr_get(children, child_index);

            let new_child = s.call(
                self.put_tail,
                &[
                    s.ptr_cast(self.branch_type.into(), child_location),
                    child_node_height,
                    child_node_number,
                    tail,
                ],
            );

            s.arr_set(children, child_index, s.ptr_cast(s.i8_t(), new_child));

            s.ret(result);
        }

        // define 'pop_tail'
        {
            let s = scope(self.pop_tail, context);
            let tail = s.arg(0);
            let tail_len = s.arg(1);

            let result = s.call(self.obtain_unique_tail, &[tail, tail_len]);

            let item = s.arr_get(s.gep(result, F_LEAF_ITEMS), s.sub(tail_len, s.i64(1)));

            s.ret(s.make_tup(&[item, result]));
        }

        // define 'pop_node'
        {
            let s = scope(self.pop_node, context);
            let branch = s.arg(0);
            let node_height = s.arg(1);
            let node_number = s.arg(2);

            let result = s.call(self.obtain_unique_branch, &[branch, node_height]);

            s.if_(s.eq(node_height, s.i64(1)), |s| {
                let new_tail = s.ptr_cast(
                    self.leaf_type.into(),
                    s.arr_get(s.gep(result, F_BRANCH_CHILDREN), node_number),
                );

                s.arr_set(
                    s.gep(result, F_BRANCH_CHILDREN),
                    node_number,
                    s.null(s.i8_t()),
                );

                s.if_(s.eq(node_number, s.i64(0)), |s| {
                    s.free(result, libc);

                    s.ret(s.make_tup(&[new_tail, s.null(self.branch_type.into())]));
                });

                s.ret(s.make_tup(&[new_tail, result]));
            });

            let child_info = s.call(self.set_next_path, &[node_height, node_number]);

            let child_index = s.field(child_info, F_CHILD_INDEX);
            let child_node_number = s.field(child_info, F_CHILD_NODE_NUMBER);
            let child_node_height = s.field(child_info, F_CHILD_HEIGHT);

            let child_location = s.arr_get(s.gep(result, F_BRANCH_CHILDREN), child_index);
            let popnode_ret = s.call(
                self.pop_node,
                &[
                    s.ptr_cast(self.branch_type.into(), child_location),
                    child_node_height,
                    child_node_number,
                ],
            );

            s.if_(s.eq(node_number, s.i64(0)), |s| {
                s.free(result, libc);

                s.ret(s.make_tup(&[s.field(popnode_ret, 0), s.null(self.branch_type.into())]));
            });

            s.arr_set(
                s.gep(result, F_BRANCH_CHILDREN),
                child_index,
                s.ptr_cast(s.i8_t(), s.field(popnode_ret, 1)),
            );

            s.ret(s.make_tup(&[s.field(popnode_ret, 0), result]));
        }
    }

    fn interface(&self) -> &ArrayInterface<'a> {
        &self.interface
    }
}

#[derive(Clone, Copy, Debug)]
pub struct PersistentArrayIoImpl<'a> {
    // related types
    pub byte_array_type: PersistentArrayImpl<'a>,

    // public API
    pub input: FunctionValue<'a>,
    pub output: FunctionValue<'a>,

    // helper functions
    pub output_tail: FunctionValue<'a>,
    pub output_node: FunctionValue<'a>,
}

impl<'a> PersistentArrayIoImpl<'a> {
    pub fn declare(
        context: &'a Context,
        module: &Module<'a>,
        byte_array_type: PersistentArrayImpl<'a>,
    ) -> Self {
        let void_type = context.void_type();

        let input = module.add_function(
            "builtin_pers_array_input",
            byte_array_type.interface().array_type.fn_type(&[], false),
            Some(Linkage::Internal),
        );

        let output = module.add_function(
            "builtin_pers_array_output",
            void_type.fn_type(&[byte_array_type.interface().array_type.into()], false),
            Some(Linkage::Internal),
        );

        let output_tail = module.add_function(
            "builtin_pers_array_output_tail",
            void_type.fn_type(
                &[
                    byte_array_type
                        .leaf_type
                        .ptr_type(AddressSpace::Generic)
                        .into(),
                    context.i64_type().into(),
                ],
                false,
            ),
            Some(Linkage::Internal),
        );

        let output_node = module.add_function(
            "builtin_pers_array_output_node",
            void_type.fn_type(
                &[
                    context.i8_type().ptr_type(AddressSpace::Generic).into(),
                    context.i64_type().into(),
                ],
                false,
            ),
            Some(Linkage::Internal),
        );

        Self {
            // related types
            byte_array_type,

            // public API
            input,
            output,

            // helper functions
            output_tail,
            output_node,
        }
    }

    pub fn define(&self, context: &'a Context, libc: &LibC<'a>) {
        // define 'input'
        {
            let s = scope(self.input, context);

            s.call(libc.flush, &[]);

            let array = s.alloca(self.byte_array_type.interface().array_type.into());

            s.ptr_set(array, s.call(self.byte_array_type.interface().new, &[]));

            let getchar_result = s.alloca(s.i32_t());
            s.while_(
                |s| {
                    let getchar_result_value = s.call(libc.getchar, &[]);
                    s.ptr_set(getchar_result, getchar_result_value);
                    s.not(s.or(
                        s.eq(getchar_result_value, s.i32(-1i32 as u32)), // EOF
                        s.eq(getchar_result_value, s.i32('\n' as u32)),
                    ))
                },
                |s| {
                    let input_bytes = s.truncate(s.i8_t(), s.ptr_get(getchar_result));
                    let new_arr = s.call(
                        self.byte_array_type.interface().push,
                        &[s.ptr_get(array), input_bytes],
                    );
                    s.ptr_set(array, new_arr);
                },
            );

            s.ret(s.ptr_get(array));
        }

        // define 'output'
        {
            let s = scope(self.output, context);
            let array = s.arg(0);

            let tail = s.field(array, F_ARR_TAIL);
            let body = s.field(array, F_ARR_BODY);
            let height = s.field(array, F_ARR_HEIGHT);
            let len = s.field(array, F_ARR_LEN);

            s.if_(s.not(s.is_null(body)), |s| {
                s.call_void(self.output_node, &[body, height]);
            });

            let tail_len = s.call(self.byte_array_type.tail_len, &[len]);

            s.if_(s.not(s.is_null(tail)), |s| {
                s.call_void(self.output_tail, &[tail, tail_len]);
            });

            s.ret_void();
        }

        // define 'output_tail'
        {
            let s = scope(self.output_tail, context);
            let tail = s.arg(0);
            let tail_len = s.arg(1);

            let items = s.gep(tail, F_LEAF_ITEMS);
            // TODO: check bytes_written for errors
            let _bytes_written = s.call_void(
                libc.write,
                &[s.ptr_cast(s.i8_t(), items), s.i64(1), tail_len],
            );

            s.ret_void();
        }

        // define 'output_node'
        {
            let s = scope(self.output_node, context);
            let branch = s.arg(0);
            let height = s.arg(1);

            let i = s.alloca(s.i64_t());
            s.ptr_set(i, s.i64(0));

            s.if_(s.eq(height, s.i64(0)), |s| {
                let items_per_leaf = get_items_per_leaf(1);

                // TODO: check bytes_written for errors
                let _bytes_written = s.call_void(
                    libc.write,
                    &[
                        s.ptr_cast(s.i8_t(), branch),
                        s.i64(1),
                        s.i64(items_per_leaf),
                    ],
                );

                s.ret_void();
            });

            let branch = s.ptr_cast(self.byte_array_type.branch_type.into(), branch);

            s.while_(
                |s| {
                    s.and_lazy(s.ult(s.ptr_get(i), s.i64(BRANCHING_FACTOR)), |s| {
                        s.not(s.is_null(s.arr_get(s.gep(branch, F_BRANCH_CHILDREN), s.ptr_get(i))))
                    })
                },
                |s| {
                    s.call_void(
                        self.output_node,
                        &[
                            s.arr_get(s.gep(branch, F_BRANCH_CHILDREN), s.ptr_get(i)),
                            s.sub(height, s.i64(1)),
                        ],
                    );
                    s.ptr_set(i, s.add(s.ptr_get(i), s.i64(1)));
                },
            );

            s.ret_void();
        }
    }
}
