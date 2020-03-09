use crate::builtins::core::*;
use crate::builtins::fountain_pen::scope;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::TargetData;
use inkwell::types::{BasicType, BasicTypeEnum, StructType};
use inkwell::values::FunctionValue;
use inkwell::AddressSpace;

// Performance-tuning parameters
const LOG2_BRANCHING_FACTOR: u32 = 5;
const BRANCHING_FACTOR: u32 = 1 << LOG2_BRANCHING_FACTOR;
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

#[derive(Clone, Debug)]
pub struct PersistentArrayBuiltin<'a> {
    // related types
    pub item_type: BasicTypeEnum<'a>,
    branch_type: StructType<'a>,
    leaf_type: StructType<'a>,
    pub array_type: StructType<'a>,
    pub hole_array_type: StructType<'a>,

    // public API
    pub new: FunctionValue<'a>,
    pub item: FunctionValue<'a>,
    pub len: FunctionValue<'a>,
    pub push: FunctionValue<'a>,
    pub pop: FunctionValue<'a>,
    pub replace: FunctionValue<'a>,
    pub retain_array: FunctionValue<'a>,
    pub release_array: FunctionValue<'a>,
    pub retain_hole: FunctionValue<'a>,
    pub release_hole: FunctionValue<'a>,

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

impl<'a> PersistentArrayBuiltin<'a> {
    pub fn declare(
        context: &'a Context,
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

        let release_node = void_fun("retain_node", &[node_ptr_type.into(), i64_type.into()]);

        let retain_tail = void_fun("retain_tail", &[leaf_ptr_type.into()]);

        let release_tail = void_fun("retain_tail", &[leaf_ptr_type.into(), i64_type.into()]);

        let tail_len = fun("tail_len", i64_type.into(), &[i64_type.into()]);

        let obtain_unique_leaf = fun(
            "obtain_unique_leaf",
            leaf_ptr_type.into(),
            &[leaf_ptr_type.into()],
        );

        let obtain_unique_branch = fun(
            "obtain_unique_branch",
            branch_ptr_type.into(),
            &[branch_ptr_type.into()],
        );

        let obtain_unique_tail = fun(
            "obtain_unique_tail",
            leaf_ptr_type.into(),
            &[leaf_ptr_type.into(), i64_type.into()],
        );

        let set_tail = fun(
            "set_tail",
            leaf_ptr_type.into(),
            &[leaf_ptr_type.into(), i64_type.into()],
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

        PersistentArrayBuiltin {
            // related types
            item_type,
            branch_type,
            leaf_type,
            array_type,
            hole_array_type,

            // public API
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

            // helper functions
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

    #[allow(unreachable_code)]
    fn define(
        &self,
        context: &'a Context,
        target: &TargetData,
        libc: LibC<'a>,
        retain_item: Option<FunctionValue<'a>>,
        release_item: Option<FunctionValue<'a>>,
    ) {
        // Compute constants
        let items_per_leaf = get_items_per_leaf(target.get_abi_size(&self.item_type));

        // Define types
        {
            let i64_type = context.i64_type();

            let node_ptr_type = context.i8_type().ptr_type(AddressSpace::Generic);

            self.branch_type.set_body(
                &[
                    // refcount
                    i64_type.into(),
                    // children
                    node_ptr_type.array_type(BRANCHING_FACTOR).into(),
                ],
                false,
            );

            self.leaf_type.set_body(
                &[
                    // refcount
                    i64_type.into(),
                    // items
                    self.item_type.array_type(items_per_leaf as u32).into(),
                ],
                false,
            );
        }

        // define 'new'
        {
            let s = scope(self.new, context);
            s.ret(s.make_struct(
                self.array_type,
                &[
                    (F_ARR_LEN, s.i64(0)),
                    (F_ARR_HEIGHT, s.i64(-1)),
                    (F_ARR_TAIL, s.null(self.leaf_type.into())),
                    (F_ARR_BODY, s.null(s.i8_t())),
                ],
            ));
        }

        // define 'item'
        {
            let s = scope(self.item, context);
            let arr = s.arg(0);
            let idx = s.arg(1);

            let len = s.field(arr, F_ARR_LEN);
            s.if_(s.uge(idx, len), |s| {
                s.panic(
                    "idx %d is out of bounds for persistent array of length %d",
                    &[idx, len],
                    &libc,
                )
            });

            s.call_void(self.retain_array, &[arr]);

            s.ret(s.make_struct(
                self.hole_array_type,
                &[(F_HOLE_IDX, idx), (F_HOLE_ARRAY, arr)],
            ));
        }

        // define 'len'
        {
            let s = scope(self.len, context);
            let array = s.arg(0);
            s.ret(s.field(array, F_ARR_LEN));
        }

        // define 'push'
        {
            let s = scope(self.push, context);
            todo!();
        }

        // define 'pop'
        {
            let s = scope(self.pop, context);
            let array = s.arg(0);
            let len = s.field(s.arg(0), F_ARR_LEN);

            s.if_(s.eq(len, 0), |s| s.panic("pop: empty array", &[], &libc));

            s.if_(s.eq(len, 1), |s| {
                let item = s.arr_get(s.arrow(s.field(array, F_ARR_TAIL), F_LEAF_ITEMS), 0);

                s.free(s.field(array, F_ARR_TAIL), &libc);

                let empty_arr = s.call(self.new, &[]);

                s.ret(s.make_tup(&[empty_arr, item]));
            });

            let tail_len = s.call(self.tail_len, &[len]);

            s.if_(s.ne(tail_len, 1), |s| {
                let poptail_ret = s.call(self.pop_tail, &[s.field(array, F_ARR_TAIL), tail_len]);

                let new_array = s.make_struct(
                    self.array_type,
                    &[
                        (F_ARR_LEN, s.sub(len, 1)),
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

            s.if_(s.eq(len, items_per_leaf + 1), |s| {
                let item = s.arr_get(s.arrow(result_tail, F_LEAF_ITEMS), 0);

                s.free(result_tail, &libc);

                let new_array = s.make_struct(
                    self.array_type,
                    &[
                        (F_ARR_LEN, s.sub(len, 1)),
                        (F_ARR_HEIGHT, s.i64(-1)),
                        (
                            F_ARR_TAIL,
                            s.ptr_cast(self.leaf_type.into(), s.field(array, F_ARR_BODY)),
                        ),
                        (F_ARR_BODY, s.null(s.i8_t())),
                    ],
                );

                s.ret(s.make_tup(&[new_array, item]));
            });

            let item = s.arr_get(s.arrow(result_tail, F_LEAF_ITEMS), 0);

            s.free(result_tail, &libc);

            let new_array_len = s.sub(len, 1);
            let target_node_numebr = s.udiv(s.sub(new_array_len, 1), items_per_leaf);

            let pop_node_ret = s.call(
                self.pop_node,
                &[
                    s.ptr_cast(self.branch_type.into(), s.field(array, F_ARR_BODY)),
                    s.field(array, F_ARR_HEIGHT),
                    target_node_numebr,
                ],
            );

            s.if_(
                s.is_null(s.arr_get(s.arrow(s.field(pop_node_ret, 1), F_BRANCH_CHILDREN), 1)),
                |s| {
                    let grandchild =
                        s.arr_get(s.arrow(s.field(pop_node_ret, 0), F_BRANCH_CHILDREN), 0);

                    let new_array = s.make_struct(
                        self.array_type,
                        &[
                            (F_ARR_LEN, s.sub(len, 1)),
                            (F_ARR_HEIGHT, s.sub(s.field(array, F_ARR_HEIGHT), 1)),
                            (F_ARR_TAIL, s.field(pop_node_ret, 1)),
                            (F_ARR_BODY, grandchild),
                        ],
                    );

                    s.free(s.field(pop_node_ret, 0), &libc);

                    s.ret(s.make_tup(&[new_array, item]));
                },
            );

            let new_array = s.make_struct(
                self.array_type,
                &[
                    (F_ARR_LEN, s.sub(len, 1)),
                    (F_ARR_HEIGHT, s.field(array, F_ARR_HEIGHT)),
                    (F_ARR_TAIL, s.field(pop_node_ret, 1)),
                    (F_ARR_BODY, s.field(pop_node_ret, 0)),
                ],
            );

            s.ret(s.make_tup(&[new_array, item]));
        }

        // define 'replace'
        {
            let s = scope(self.replace, context);
            let hole = s.arg(0);
            let item = s.arg(1);

            let idx = s.field(hole, F_HOLE_IDX);
            let array = s.field(hole, F_HOLE_ARRAY);
            s.ret(s.call(self.set, &[array, idx, item]));
        }

        // define 'retain_array'
        {
            let s = scope(self.retain_array, context);
            let array = s.arg(0);

            s.if_(s.not(s.eq(s.field(array, F_ARR_LEN), 0)), |s| {
                s.call_void(self.retain_tail, &[s.field(array, F_ARR_TAIL)]);
            });

            s.if_(s.ugt(s.field(array, F_ARR_LEN), items_per_leaf), |s| {
                s.call_void(
                    self.retain_node,
                    &[s.field(array, F_ARR_BODY), s.field(array, F_ARR_HEIGHT)],
                );
            });

            s.ret_void();
        }

        // define 'release_array'
        {
            let s = scope(self.release_array, context);
            let array = s.arg(0);

            s.if_(s.not(s.eq(s.field(array, F_ARR_LEN), 0)), |s| {
                s.call_void(
                    self.release_tail,
                    &[
                        s.field(array, F_ARR_TAIL),
                        s.call(self.tail_len, &[s.field(array, F_ARR_LEN)]),
                    ],
                );
            });

            s.if_(s.ugt(s.field(array, F_ARR_LEN), items_per_leaf), |s| {
                s.call_void(
                    self.release_node,
                    &[s.field(array, F_ARR_BODY), s.field(array, F_ARR_HEIGHT)],
                );
            });

            s.ret_void();
        }

        // define 'retain_hole'
        {
            let s = scope(self.retain_hole, context);
            let hole = s.arg(0);

            let array = s.field(hole, F_HOLE_ARRAY);
            s.call_void(self.retain_array, &[array]);
            s.ret_void();
        }

        // define 'release_hole'
        {
            let s = scope(self.release_hole, context);
            let hole = s.arg(0);

            let array = s.field(hole, F_HOLE_ARRAY);
            s.call_void(self.release_array, &[array]);
            s.ret_void();
        }

        // define 'set_next_path'
        {
            let s = scope(self.set_next_path, context);
            let node_height = s.arg(0);
            let node_number = s.arg(1);

            let num_shift_bits = s.mul(s.sub(node_height, 1), LOG2_BRANCHING_FACTOR as u64);

            let child_index = s.srl(node_number, num_shift_bits);

            let child_node_number = s.sub(node_number, s.sll(child_index, num_shift_bits));

            let child_node_height = s.sub(node_height, 1);

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
                    &libc,
                );
            });

            s.if_(s.eq(s.field(array, F_ARR_HEIGHT), -1i64), |s| {
                s.ret(s.arr_get(s.gep(s.field(array, F_ARR_TAIL), F_LEAF_ITEMS), index));
            });

            let target_node_number = s.udiv(index, items_per_leaf);

            let tail_node_number = s.udiv(s.sub(s.field(array, F_ARR_LEN), 1), items_per_leaf);

            let index_in_leaf = s.urem(index, items_per_leaf);

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
                |s| s.not(s.eq(s.ptr_get(curr_node_height), 0)),
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
                s.eq(height, 0),
                |s| {
                    let leaf_ptr = s.ptr_cast(self.leaf_type.into(), leaf_or_branch_ptr);
                    let refcount = s.arrow(leaf_ptr, F_LEAF_REFCOUNT);
                    s.arrow_set(leaf_ptr, F_LEAF_REFCOUNT, s.add(refcount, 1));
                },
                |s| {
                    let branch_ptr = s.ptr_cast(self.branch_type.into(), leaf_or_branch_ptr);
                    let refcount = s.arrow(branch_ptr, F_BRANCH_REFCOUNT);
                    s.arrow_set(branch_ptr, F_BRANCH_REFCOUNT, s.add(refcount, 1));
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
                s.eq(height, 0),
                |s| {
                    let leaf_ptr = s.ptr_cast(self.leaf_type.into(), leaf_or_branch_ptr);
                    let new_refcount = s.sub(s.arrow(leaf_ptr, F_LEAF_REFCOUNT), 1);
                    s.arrow_set(leaf_ptr, F_LEAF_REFCOUNT, new_refcount);

                    s.if_(s.eq(new_refcount, 0), |s| {
                        if let Some(actual_release_item) = release_item {
                            s.for_(items_per_leaf, |s, i| {
                                s.call_void(actual_release_item, &[s.arr_addr(leaf_ptr, i)]);
                            });
                        }
                        s.free(leaf_ptr, &libc);
                    });
                },
                |s| {
                    let branch_ptr = s.ptr_cast(self.branch_type.into(), leaf_or_branch_ptr);
                    let new_refcount = s.sub(s.arrow(branch_ptr, F_BRANCH_REFCOUNT), 1);
                    s.arrow_set(branch_ptr, F_BRANCH_REFCOUNT, new_refcount);

                    s.if_(s.eq(new_refcount, 0), |s| {
                        let i = s.alloca(s.i64_t());
                        s.ptr_set(i, s.i64(0));

                        s.while_(
                            |s| {
                                s.and(
                                    s.ult(i, BRANCHING_FACTOR),
                                    s.not(s.is_null(
                                        s.arr_get(s.arrow(branch_ptr, F_BRANCH_CHILDREN), i),
                                    )),
                                )
                            },
                            |s| {
                                s.call_void(
                                    self.release_node,
                                    &[
                                        s.arr_get(s.arrow(branch_ptr, F_BRANCH_CHILDREN), i),
                                        s.sub(height, 1),
                                    ],
                                );
                                s.ptr_set(i, s.add(s.ptr_get(i), 1));
                            },
                        );
                        s.free(branch_ptr, &libc);
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
            s.arrow_set(tail, F_LEAF_REFCOUNT, s.add(refcount, 1));

            s.ret_void();
        }

        // define 'release_tail'
        {
            let s = scope(self.release_tail, context);
            let tail = s.arg(0);
            let tail_len = s.arg(1);

            let refcount = s.arrow(tail, F_LEAF_REFCOUNT);
            s.arrow_set(tail, F_LEAF_REFCOUNT, s.sub(refcount, 1));

            if let Some(release_fn) = release_item {
                s.if_(s.eq(s.arrow(tail, F_LEAF_REFCOUNT), 0), |s| {
                    s.for_(tail_len, |s, i| {
                        s.call(release_fn, &[s.arr_addr(s.arrow(tail, F_ARR_TAIL), i)]);
                    })
                });

                s.free(tail, &libc);
            }

            s.ret_void();
        }

        // define 'tail_len'
        {
            let s = scope(self.tail_len, context);
            let len = s.arg(0);

            s.ret(s.add(s.urem(s.sub(len, 1), items_per_leaf), 1));
        }

        // define 'obtain_unique_leaf'
        {
            let s = scope(self.obtain_unique_leaf, context);
            let leaf = s.arg(1);

            s.if_(s.eq(s.arrow(leaf, F_LEAF_REFCOUNT), 1), |s| {
                s.ret(leaf);
            });

            let result = s.calloc(1, self.leaf_type.into(), &libc);
            s.arrow_set(result, F_LEAF_REFCOUNT, s.i64(1));

            s.ptr_set(
                s.field(result, F_LEAF_ITEMS),
                s.ptr_get(s.field(leaf, F_LEAF_ITEMS)),
            );

            if let Some(retain_fn) = retain_item {
                s.for_(items_per_leaf, |s, i| {
                    s.call(retain_fn, &[s.arr_get(s.arrow(leaf, F_LEAF_ITEMS), i)]);
                });
            }

            let refcount = s.arrow(leaf, F_LEAF_REFCOUNT);
            s.arrow_set(leaf, F_LEAF_REFCOUNT, s.sub(refcount, 1));

            s.ret(result);
        }

        // define 'obtain_unique_branch'
        {
            let s = scope(self.obtain_unique_branch, context);
            let branch = s.arg(0);
            let height = s.arg(1);

            s.if_(s.eq(s.arrow(branch, F_BRANCH_REFCOUNT), 1), |s| {
                s.ret(branch);
            });

            let result = s.calloc(1, self.branch_type.into(), &libc);
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
                    s.and(
                        s.ult(s.ptr_get(i), BRANCHING_FACTOR as u64),
                        s.not(
                            s.is_null(s.arr_get(s.field(branch, F_BRANCH_CHILDREN), s.ptr_get(i))),
                        ),
                    )
                },
                |s| {
                    s.call_void(
                        self.retain_node,
                        &[
                            s.arr_get(s.field(branch, F_BRANCH_CHILDREN), s.ptr_get(i)),
                            s.sub(height, 1),
                        ],
                    );
                },
            );

            s.arrow_set(
                branch,
                F_BRANCH_REFCOUNT,
                s.sub(s.arrow(branch, F_BRANCH_REFCOUNT), 1),
            );

            s.ret(result);
        }

        // define 'obtain_unique_tail'
        {
            let s = scope(self.obtain_unique_tail, context);
            let tail = s.arg(0);
            let tail_len = s.arg(1);

            let refcount = s.arrow(tail, F_LEAF_REFCOUNT);

            s.if_(s.eq(refcount, 1), |s| {
                s.ret(tail);
            });

            let result = s.calloc(1, self.leaf_type.into(), &libc);
            s.arrow_set(result, F_LEAF_REFCOUNT, s.i64(1));
            s.call(
                libc.memcpy,
                &[
                    s.gep(result, F_LEAF_ITEMS),
                    s.gep(tail, F_LEAF_ITEMS),
                    s.mul(s.size(self.item_type), tail_len),
                ],
            );

            if let Some(actual_retain_item) = retain_item {
                s.for_(tail_len, |s, i| {
                    s.call_void(
                        actual_retain_item,
                        &[s.arr_addr(s.arrow(tail, F_LEAF_ITEMS), i)],
                    );
                });
            }

            s.arrow_set(tail, F_LEAF_REFCOUNT, s.sub(refcount, 1));

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

            if let Some(release_fn) = release_item {
                s.call(
                    release_fn,
                    &[s.arr_get(s.arrow(result, F_LEAF_ITEMS), index_in_tail)],
                );
            }
            s.arr_set(s.arrow(result, F_LEAF_ITEMS), index_in_tail, item);

            s.ret(result);
        }

        // define 'set_node'
        {
            let s = scope(self.set_node, context);
            todo!();
        }

        // define 'set'
        {
            let s = scope(self.set, context);
            todo!();
        }

        // define 'push_tail'
        {
            let s = scope(self.push_tail, context);
            todo!();
        }

        // define 'put_tail'
        {
            let s = scope(self.put_tail, context);
            todo!();
        }

        // define 'pop_tail'
        {
            let s = scope(self.pop_tail, context);
            todo!();
        }

        // define 'pop_node'
        {
            let s = scope(self.pop_node, context);
            todo!();
        }
    }
}
