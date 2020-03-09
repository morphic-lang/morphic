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
const MIN_LEAF_BYTES: u32 = 128;

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

fn get_items_per_leaf(item_bytes: u64) -> u32 {
    if item_bytes == 0 {
        unimplemented!("Persistent arrays of zero-sized types are not yet implemented");
    }

    let mut items_per_leaf = 1;
    while items_per_leaf * item_bytes < MIN_LEAF_BYTES as u64 {
        items_per_leaf *= 2;
    }
    items_per_leaf as u32
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
                    self.item_type.array_type(items_per_leaf).into(),
                ],
                false,
            );
        }

        // define 'new'
        {
            let s = scope(self.new, context);
            todo!();
        }

        // define 'item'
        {
            let s = scope(self.item, context);
            todo!();
        }

        // define 'len'
        {
            let s = scope(self.len, context);
            todo!();
        }

        // define 'push'
        {
            let s = scope(self.push, context);
            todo!();
        }

        // define 'pop'
        {
            let s = scope(self.pop, context);
            todo!();
        }

        // define 'replace'
        {
            let s = scope(self.replace, context);
            todo!();
        }

        // define 'retain_array'
        {
            let s = scope(self.retain_array, context);
            todo!();
        }

        // define 'release_array'
        {
            let s = scope(self.release_array, context);
            todo!();
        }

        // define 'retain_hole'
        {
            let s = scope(self.retain_hole, context);
            todo!();
        }

        // define 'release_hole'
        {
            let s = scope(self.release_hole, context);
            todo!();
        }

        // define 'set_next_path'
        {
            let s = scope(self.set_next_path, context);
            todo!();
        }

        // define 'get'
        {
            let s = scope(self.get, context);
            todo!();
        }

        // define 'retain_node'
        {
            let s = scope(self.retain_node, context);
            todo!();
        }

        // define 'release_node'
        {
            let s = scope(self.release_node, context);
            todo!();
        }

        // define 'retain_tail'
        {
            let s = scope(self.retain_tail, context);
            todo!();
        }

        // define 'release_tail'
        {
            let s = scope(self.release_tail, context);
            todo!();
        }

        // define 'tail_len'
        {
            let s = scope(self.tail_len, context);
            todo!();
        }

        // define 'obtain_unique_leaf'
        {
            let s = scope(self.obtain_unique_leaf, context);
            todo!();
        }

        // define 'obtain_unique_branch'
        {
            let s = scope(self.obtain_unique_branch, context);
            todo!();
        }

        // define 'obtain_unique_tail'
        {
            let s = scope(self.obtain_unique_tail, context);
            todo!();
        }

        // define 'set_tail'
        {
            let s = scope(self.set_tail, context);
            todo!();
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
