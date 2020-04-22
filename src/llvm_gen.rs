use crate::builtins::array::ArrayImpl;
use crate::builtins::flat_array::{FlatArrayImpl, FlatArrayIoImpl};
use crate::builtins::libc::LibC;
use crate::builtins::persistent_array::{PersistentArrayImpl, PersistentArrayIoImpl};
use crate::builtins::rc::RcBoxBuiltin;
use crate::builtins::zero_sized_array::ZeroSizedArrayImpl;
use crate::cli;
use crate::data::first_order_ast as first_ord;
use crate::data::low_ast as low;
use crate::data::repr_constrained_ast as constrain;
use crate::data::tail_rec_ast as tail;
use crate::pseudoprocess::{spawn_process, Child, Stdio};
use crate::util::graph::{self, Graph};
use crate::util::id_vec::IdVec;
use find_clang::find_clang;
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::passes::{PassManager, PassManagerBuilder};
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetData, TargetMachine,
    TargetTriple,
};
use inkwell::types::{BasicType, BasicTypeEnum, StructType};
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue};
use inkwell::AddressSpace;
use inkwell::OptimizationLevel;
use inkwell::{FloatPredicate, IntPredicate};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::convert::TryInto;
use std::path::Path;
use std::rc::Rc;

const VARIANT_DISCRIM_IDX: u32 = 0;
// we use a zero sized array to enforce proper alignment on `bytes`
const VARIANT_ALIGN_IDX: u32 = 1;
const VARIANT_BYTES_IDX: u32 = 2;

#[derive(Clone, Debug)]
struct Intrinsics<'a> {
    expect_i1: FunctionValue<'a>,
}

#[derive(Clone, Debug)]
struct Globals<'a, 'b> {
    context: &'a Context,
    module: &'b Module<'a>,
    intrinsics: Intrinsics<'a>,
    target: &'b TargetData,
    libc: LibC<'a>,
    custom_types: IdVec<low::CustomTypeId, CustomTypeDecls<'a>>,
}

#[derive(Clone, Copy, Debug)]
struct CustomTypeDecls<'a> {
    ty: StructType<'a>,
    release: FunctionValue<'a>,
    retain: FunctionValue<'a>,
}

impl<'a> CustomTypeDecls<'a> {
    fn declare(context: &'a Context, module: &Module<'a>, type_id: low::CustomTypeId) -> Self {
        let ty = context.opaque_struct_type(&format!("type_{}", type_id.0));
        let void_type = context.void_type();
        let release_func = module.add_function(
            &format!("release_{}", type_id.0),
            void_type.fn_type(&[ty.into()], false),
            Some(Linkage::Internal),
        );
        let retain_func = module.add_function(
            &format!("retain_{}", type_id.0),
            void_type.fn_type(&[ty.into()], false),
            Some(Linkage::Internal),
        );
        CustomTypeDecls {
            ty,
            release: release_func,
            retain: retain_func,
        }
    }

    fn define_type<'b>(
        &self,
        globals: &Globals<'a, 'b>,
        instances: &Instances<'a>,
        ty: &low::Type,
    ) {
        let ty = get_llvm_type(globals, instances, ty);
        self.ty.set_body(&[ty], false);
    }

    fn define<'b>(&self, globals: &Globals<'a, 'b>, instances: &Instances<'a>, ty: &low::Type) {
        let context = globals.context;
        let builder = context.create_builder();

        let retain_entry = context.append_basic_block(self.retain, "retain_entry");

        builder.position_at_end(retain_entry);
        let arg = self.retain.get_nth_param(0).unwrap().into_struct_value();
        // customs types are wrapped in one element structs
        let arg = builder.build_extract_value(arg, 0, "content").unwrap();

        gen_rc_op(
            RcOp::Retain,
            &builder,
            instances,
            globals,
            self.retain,
            ty,
            arg,
        );

        builder.build_return(None);

        let release_entry = context.append_basic_block(self.release, "release_entry");

        builder.position_at_end(release_entry);
        let arg = self.release.get_nth_param(0).unwrap().into_struct_value();
        // customs types are wrapped in one element structs
        let arg = builder.build_extract_value(arg, 0, "content").unwrap();

        gen_rc_op(
            RcOp::Release,
            &builder,
            instances,
            globals,
            self.release,
            ty,
            arg,
        );

        builder.build_return(None);
    }
}

struct Instances<'a> {
    flat_arrays: RefCell<BTreeMap<low::Type, Rc<dyn ArrayImpl<'a> + 'a>>>,
    flat_array_io: FlatArrayIoImpl<'a>,
    persistent_arrays: RefCell<BTreeMap<low::Type, Rc<dyn ArrayImpl<'a> + 'a>>>,
    persistent_array_io: PersistentArrayIoImpl<'a>,
    rcs: RefCell<BTreeMap<low::Type, RcBoxBuiltin<'a>>>,
}

impl<'a> Instances<'a> {
    fn new<'b>(globals: &Globals<'a, 'b>) -> Self {
        let mut flat_arrays = BTreeMap::new();
        let byte_flat_builtin = FlatArrayImpl::declare(
            globals.context,
            globals.target,
            globals.module,
            globals.context.i8_type().into(),
        );

        flat_arrays.insert(
            low::Type::Num(first_ord::NumType::Byte),
            Rc::new(byte_flat_builtin) as Rc<dyn ArrayImpl<'a>>,
        );
        let flat_array_io =
            FlatArrayIoImpl::declare(globals.context, globals.module, byte_flat_builtin);

        let mut persistent_arrays = BTreeMap::new();
        let byte_persistent_builtin = PersistentArrayImpl::declare(
            globals.context,
            globals.target,
            globals.module,
            globals.context.i8_type().into(),
        );

        persistent_arrays.insert(
            low::Type::Num(first_ord::NumType::Byte),
            Rc::new(byte_persistent_builtin) as Rc<dyn ArrayImpl<'a>>,
        );
        let persistent_array_io = PersistentArrayIoImpl::declare(
            globals.context,
            globals.module,
            byte_persistent_builtin,
        );

        Self {
            flat_arrays: RefCell::new(flat_arrays),
            flat_array_io,
            persistent_arrays: RefCell::new(persistent_arrays),
            persistent_array_io,
            rcs: RefCell::new(BTreeMap::new()),
        }
    }

    fn get_flat_array<'b>(
        &self,
        globals: &Globals<'a, 'b>,
        item_type: &low::Type,
    ) -> Rc<dyn ArrayImpl<'a> + 'a> {
        if let Some(existing) = self.flat_arrays.borrow().get(&item_type.clone()) {
            return existing.clone();
        }
        let ty = get_llvm_type(globals, self, item_type);
        let new_builtin = if globals.target.get_abi_size(&ty) == 0 {
            Rc::new(ZeroSizedArrayImpl::declare(
                globals.context,
                globals.target,
                globals.module,
                ty,
            )) as Rc<dyn ArrayImpl<'a>>
        } else {
            Rc::new(FlatArrayImpl::declare(
                globals.context,
                globals.target,
                globals.module,
                ty,
            )) as Rc<dyn ArrayImpl<'a>>
        };
        self.flat_arrays
            .borrow_mut()
            .insert(item_type.clone(), new_builtin.clone());
        new_builtin
    }

    fn get_persistent_array<'b>(
        &self,
        globals: &Globals<'a, 'b>,
        item_type: &low::Type,
    ) -> Rc<dyn ArrayImpl<'a> + 'a> {
        if let Some(existing) = self.persistent_arrays.borrow().get(&item_type.clone()) {
            return existing.clone();
        }
        let ty = get_llvm_type(globals, self, item_type);
        let new_builtin = if globals.target.get_abi_size(&ty) == 0 {
            Rc::new(ZeroSizedArrayImpl::declare(
                globals.context,
                globals.target,
                globals.module,
                ty,
            )) as Rc<dyn ArrayImpl<'a>>
        } else {
            Rc::new(PersistentArrayImpl::declare(
                globals.context,
                globals.target,
                globals.module,
                ty,
            )) as Rc<dyn ArrayImpl<'a>>
        };
        self.persistent_arrays
            .borrow_mut()
            .insert(item_type.clone(), new_builtin.clone());
        new_builtin
    }

    fn get_rc<'b>(&self, globals: &Globals<'a, 'b>, item_type: &low::Type) -> RcBoxBuiltin<'a> {
        if let Some(existing) = self.rcs.borrow().get(&item_type.clone()) {
            return *existing;
        }
        let new_builtin = RcBoxBuiltin::declare(
            globals.context,
            globals.module,
            get_llvm_type(globals, self, item_type),
        );
        self.rcs.borrow_mut().insert(item_type.clone(), new_builtin);
        return new_builtin;
    }

    fn define<'b>(&self, globals: &Globals<'a, 'b>) {
        let builder = globals.context.create_builder();
        let void_type = globals.context.void_type();

        // rcs
        for (i, (inner_type, rc_builtin)) in self.rcs.borrow().iter().enumerate() {
            let llvm_inner_type = get_llvm_type(globals, self, inner_type);

            let release_func = globals.module.add_function(
                &format!("rc_release_{}", i),
                void_type.fn_type(
                    &[llvm_inner_type.ptr_type(AddressSpace::Generic).into()],
                    false,
                ),
                Some(Linkage::Internal),
            );

            let release_entry = globals
                .context
                .append_basic_block(release_func, "release_entry");

            builder.position_at_end(release_entry);
            let arg = release_func.get_nth_param(0).unwrap();

            let arg = builder.build_load(arg.into_pointer_value(), "arg");

            gen_rc_op(
                RcOp::Release,
                &builder,
                self,
                globals,
                release_func,
                inner_type,
                arg,
            );

            builder.build_return(None);

            rc_builtin.define(globals.context, &globals.libc, Some(release_func));
        }

        // flat arrays
        for (i, (inner_type, flat_array_builtin)) in self.flat_arrays.borrow().iter().enumerate() {
            let llvm_inner_type = get_llvm_type(globals, self, inner_type);

            let retain_func = globals.module.add_function(
                &format!("flat_array_retain_{}", i),
                void_type.fn_type(
                    &[llvm_inner_type.ptr_type(AddressSpace::Generic).into()],
                    false,
                ),
                Some(Linkage::Internal),
            );

            let retain_entry = globals
                .context
                .append_basic_block(retain_func, "retain_entry");

            builder.position_at_end(retain_entry);
            let arg = retain_func.get_nth_param(0).unwrap();

            let arg = builder.build_load(arg.into_pointer_value(), "arg");

            gen_rc_op(
                RcOp::Retain,
                &builder,
                self,
                globals,
                retain_func,
                inner_type,
                arg,
            );

            builder.build_return(None);

            let release_func = globals.module.add_function(
                &format!("flat_array_release_{}", i),
                void_type.fn_type(
                    &[llvm_inner_type.ptr_type(AddressSpace::Generic).into()],
                    false,
                ),
                Some(Linkage::Internal),
            );

            let release_entry = globals
                .context
                .append_basic_block(release_func, "release_entry");

            builder.position_at_end(release_entry);
            let arg = release_func.get_nth_param(0).unwrap();

            let arg = builder.build_load(arg.into_pointer_value(), "arg");

            gen_rc_op(
                RcOp::Release,
                &builder,
                self,
                globals,
                release_func,
                inner_type,
                arg,
            );

            builder.build_return(None);

            // TODO: dont generate retains/releases that aren't used
            if globals.target.get_abi_size(&llvm_inner_type) == 0 {
                flat_array_builtin.define(
                    globals.context,
                    globals.target,
                    &globals.libc,
                    None,
                    None,
                );
            } else {
                flat_array_builtin.define(
                    globals.context,
                    globals.target,
                    &globals.libc,
                    Some(retain_func),
                    Some(release_func),
                );
            }
        }

        self.flat_array_io.define(globals.context, &globals.libc);

        // persistent arrays
        for (i, (inner_type, persistent_array_builtin)) in
            self.persistent_arrays.borrow().iter().enumerate()
        {
            let llvm_inner_type = get_llvm_type(globals, self, inner_type);

            let retain_func = globals.module.add_function(
                &format!("persistent_array_retain_{}", i),
                void_type.fn_type(
                    &[llvm_inner_type.ptr_type(AddressSpace::Generic).into()],
                    false,
                ),
                Some(Linkage::Internal),
            );

            let retain_entry = globals
                .context
                .append_basic_block(retain_func, "retain_entry");

            builder.position_at_end(retain_entry);
            let arg = retain_func.get_nth_param(0).unwrap();

            let arg = builder.build_load(arg.into_pointer_value(), "arg");

            gen_rc_op(
                RcOp::Retain,
                &builder,
                self,
                globals,
                retain_func,
                inner_type,
                arg,
            );

            builder.build_return(None);

            let release_func = globals.module.add_function(
                &format!("persistent_array_release_{}", i),
                void_type.fn_type(
                    &[llvm_inner_type.ptr_type(AddressSpace::Generic).into()],
                    false,
                ),
                Some(Linkage::Internal),
            );

            let release_entry = globals
                .context
                .append_basic_block(release_func, "release_entry");

            builder.position_at_end(release_entry);
            let arg = release_func.get_nth_param(0).unwrap();

            let arg = builder.build_load(arg.into_pointer_value(), "arg");

            gen_rc_op(
                RcOp::Release,
                &builder,
                self,
                globals,
                release_func,
                inner_type,
                arg,
            );

            builder.build_return(None);

            // TODO: dont generate retains/releases that aren't used
            if globals.target.get_abi_size(&llvm_inner_type) == 0 {
                persistent_array_builtin.define(
                    globals.context,
                    globals.target,
                    &globals.libc,
                    None,
                    None,
                );
            } else {
                persistent_array_builtin.define(
                    globals.context,
                    globals.target,
                    &globals.libc,
                    Some(retain_func),
                    Some(release_func),
                );
            }
        }

        self.persistent_array_io
            .define(globals.context, &globals.libc);
    }
}

fn get_llvm_variant_type<'a, 'b>(
    globals: &Globals<'a, 'b>,
    instances: &Instances<'a>,
    variants: &IdVec<low::VariantId, low::Type>,
) -> StructType<'a> {
    if variants.len() == 0 {
        return globals.context.struct_type(&[], false).into();
    }

    let discrim_type = if variants.len() <= 1 << 8 {
        globals.context.i8_type()
    } else if variants.len() <= 1 << 16 {
        globals.context.i16_type()
    } else if variants.len() <= 1 << 32 {
        globals.context.i32_type()
    } else {
        globals.context.i64_type()
    };

    let (max_alignment, max_size) = {
        let mut max_alignment = 1;
        let mut max_size = 0;
        for variant_type in &variants.items {
            let variant_type = get_llvm_type(globals, instances, &variant_type);
            debug_assert!(variant_type.is_sized());
            let alignment = globals.target.get_abi_alignment(&variant_type);
            let size = globals.target.get_abi_size(&variant_type);
            max_alignment = max_alignment.max(alignment);
            max_size = max_size.max(size);
        }
        (max_alignment, max_size)
    };

    let alignment_array = {
        let alignment_type = match max_alignment {
            1 => globals.context.i8_type(),
            2 => globals.context.i16_type(),
            4 => globals.context.i32_type(),
            8 => globals.context.i64_type(),
            _ => panic!["Unsupported alignment {}", max_alignment],
        };
        alignment_type.array_type(0)
    };

    let bytes = globals
        .context
        .i8_type()
        .array_type(max_size.try_into().unwrap());

    let field_types = &[discrim_type.into(), alignment_array.into(), bytes.into()];
    globals.context.struct_type(field_types, false)
}

fn get_llvm_type<'a, 'b>(
    globals: &Globals<'a, 'b>,
    instances: &Instances<'a>,
    type_: &low::Type,
) -> BasicTypeEnum<'a> {
    match type_ {
        low::Type::Bool => globals.context.bool_type().into(),
        low::Type::Num(first_ord::NumType::Byte) => globals.context.i8_type().into(),
        low::Type::Num(first_ord::NumType::Int) => globals.context.i64_type().into(),
        low::Type::Num(first_ord::NumType::Float) => globals.context.f64_type().into(),
        low::Type::Array(constrain::RepChoice::OptimizedMut, item_type) => instances
            .get_flat_array(globals, item_type)
            .interface()
            .array_type
            .into(),
        low::Type::Array(constrain::RepChoice::FallbackImmut, item_type) => instances
            .get_persistent_array(globals, item_type)
            .interface()
            .array_type
            .into(),
        low::Type::HoleArray(constrain::RepChoice::OptimizedMut, item_type) => instances
            .get_flat_array(globals, item_type)
            .interface()
            .hole_array_type
            .into(),
        low::Type::HoleArray(constrain::RepChoice::FallbackImmut, item_type) => instances
            .get_persistent_array(globals, item_type)
            .interface()
            .hole_array_type
            .into(),
        low::Type::Tuple(item_types) => {
            let mut field_types = vec![];
            for item_type in item_types.iter() {
                field_types.push(get_llvm_type(globals, instances, item_type));
            }
            globals.context.struct_type(&field_types[..], false).into()
        }
        low::Type::Variants(variants) => {
            get_llvm_variant_type(globals, instances, &variants).into()
        }
        low::Type::Boxed(type_) => instances
            .get_rc(globals, type_)
            .rc_type
            .ptr_type(AddressSpace::Generic)
            .into(),
        low::Type::Custom(type_id) => globals.custom_types[type_id].ty.into(),
    }
}

#[derive(Clone, Copy, Debug)]
enum RcOp {
    Retain,
    Release,
}

fn gen_rc_op<'a, 'b>(
    op: RcOp,
    builder: &Builder<'a>,
    instances: &Instances<'a>,
    globals: &Globals<'a, 'b>,
    func: FunctionValue<'a>,
    ty: &low::Type,
    arg: BasicValueEnum<'a>,
) {
    match ty {
        low::Type::Bool => {}
        low::Type::Num(_) => {}
        low::Type::Array(constrain::RepChoice::OptimizedMut, item_type) => match op {
            RcOp::Retain => {
                let retain_func = instances
                    .get_flat_array(globals, item_type)
                    .interface()
                    .retain_array;
                builder.build_call(retain_func, &[arg], "retain_flat_array");
            }
            RcOp::Release => {
                let release_func = instances
                    .get_flat_array(globals, item_type)
                    .interface()
                    .release_array;
                builder.build_call(release_func, &[arg], "release_flat_array");
            }
        },
        low::Type::Array(constrain::RepChoice::FallbackImmut, item_type) => match op {
            RcOp::Retain => {
                let retain_func = instances
                    .get_persistent_array(globals, item_type)
                    .interface()
                    .retain_array;
                builder.build_call(retain_func, &[arg], "retain_pers_array");
            }
            RcOp::Release => {
                let release_func = instances
                    .get_persistent_array(globals, item_type)
                    .interface()
                    .release_array;
                builder.build_call(release_func, &[arg], "release_pers_array");
            }
        },
        low::Type::HoleArray(constrain::RepChoice::OptimizedMut, item_type) => match op {
            RcOp::Retain => {
                let retain_func = instances
                    .get_flat_array(globals, item_type)
                    .interface()
                    .retain_hole;
                builder.build_call(retain_func, &[arg], "retain_flat_hole_array");
            }
            RcOp::Release => {
                let release_func = instances
                    .get_flat_array(globals, item_type)
                    .interface()
                    .release_hole;
                builder.build_call(release_func, &[arg], "release_flat_hole_array");
            }
        },
        low::Type::HoleArray(constrain::RepChoice::FallbackImmut, item_type) => match op {
            RcOp::Retain => {
                let retain_func = instances
                    .get_persistent_array(globals, item_type)
                    .interface()
                    .retain_hole;
                builder.build_call(retain_func, &[arg], "retain_pers_hole_array");
            }
            RcOp::Release => {
                let release_func = instances
                    .get_persistent_array(globals, item_type)
                    .interface()
                    .release_hole;
                builder.build_call(release_func, &[arg], "release_pers_hole_array");
            }
        },
        low::Type::Tuple(item_types) => {
            for i in 0..item_types.len() {
                let current_item = builder
                    .build_extract_value(
                        arg.into_struct_value(),
                        i.try_into().unwrap(),
                        "current_item",
                    )
                    .unwrap();
                gen_rc_op(
                    op,
                    builder,
                    instances,
                    globals,
                    func,
                    &item_types[i],
                    current_item,
                );
            }
        }
        low::Type::Variants(variant_types) => {
            let discrim = builder
                .build_extract_value(arg.into_struct_value(), VARIANT_DISCRIM_IDX, "discrim")
                .unwrap()
                .into_int_value();
            let undefined_block = globals.context.append_basic_block(func, "undefined");
            let mut variant_blocks = vec![];
            for _ in 0..variant_types.len() {
                variant_blocks.push(globals.context.append_basic_block(func, "variant"));
            }
            let switch_blocks = variant_blocks
                .iter()
                .enumerate()
                .map(|(i, variant_block)| {
                    (
                        discrim.get_type().const_int(i.try_into().unwrap(), false),
                        *variant_block,
                    )
                })
                .collect::<Vec<_>>();

            builder.build_switch(discrim, undefined_block, &switch_blocks[..]);

            let next_block = globals.context.append_basic_block(func, "next");

            builder.position_at_end(undefined_block);
            builder.build_unreachable();
            for (i, variant_block) in variant_blocks.iter().enumerate() {
                builder.position_at_end(*variant_block);
                let variant_id = low::VariantId(i);

                let unwrapped_variant =
                    gen_unwrap_variant(builder, instances, globals, arg, variant_types, variant_id);

                gen_rc_op(
                    op,
                    builder,
                    instances,
                    globals,
                    func,
                    &variant_types[variant_id],
                    unwrapped_variant,
                );

                builder.build_unconditional_branch(next_block);
            }

            builder.position_at_end(next_block);
        }
        low::Type::Boxed(inner_type) => match op {
            RcOp::Retain => {
                let retain_func = instances.get_rc(globals, inner_type).retain;
                builder.build_call(retain_func, &[arg], "retain_boxed");
            }
            RcOp::Release => {
                let release_func = instances.get_rc(globals, inner_type).release;
                builder.build_call(release_func, &[arg], "release_boxed");
            }
        },
        low::Type::Custom(type_id) => match op {
            RcOp::Retain => {
                let retain_func = globals.custom_types[type_id].retain;
                builder.build_call(retain_func, &[arg], "retain_boxed");
            }
            RcOp::Release => {
                let release_func = globals.custom_types[type_id].release;
                builder.build_call(release_func, &[arg], "release_boxed");
            }
        },
    }
}

fn gen_entry_alloca<'a>(
    context: &'a Context,
    builder: &Builder<'a>,
    ty: impl BasicType<'a>,
    name: &str,
) -> PointerValue<'a> {
    let curr_block = builder.get_insert_block().unwrap();
    let func = curr_block.get_parent().unwrap();
    let entry = func.get_first_basic_block().unwrap();

    let entry_builder = context.create_builder();

    if let Some(entry_inst) = entry.get_first_instruction() {
        entry_builder.position_before(&entry_inst);
    } else {
        entry_builder.position_at_end(entry);
    }

    entry_builder.build_alloca(ty, name)
}

fn gen_unwrap_variant<'a, 'b>(
    builder: &Builder<'a>,
    instances: &Instances<'a>,
    globals: &Globals<'a, 'b>,
    variant_value: BasicValueEnum<'a>,
    variants: &IdVec<low::VariantId, low::Type>,
    variant_id: low::VariantId,
) -> BasicValueEnum<'a> {
    let variant_type = get_llvm_variant_type(globals, instances, &variants);

    let byte_array_type = variant_type
        .get_field_type_at_index(VARIANT_BYTES_IDX)
        .unwrap();
    let byte_array_ptr =
        gen_entry_alloca(globals.context, builder, byte_array_type, "byte_array_ptr");

    let byte_array = builder
        .build_extract_value(
            variant_value.into_struct_value(),
            VARIANT_BYTES_IDX,
            "byte_array",
        )
        .unwrap();

    builder.build_store(byte_array_ptr, byte_array);

    let content_ptr = builder.build_bitcast(
        byte_array_ptr,
        get_llvm_type(globals, instances, &variants[variant_id]).ptr_type(AddressSpace::Generic),
        "content_ptr",
    );

    let content = builder.build_load(content_ptr.into_pointer_value(), "content");

    content
}

#[derive(Clone, Debug)]
struct TailCallTarget<'a> {
    arg_var: PointerValue<'a>,
    block: BasicBlock<'a>,
}

fn get_undef<'a>(ty: &BasicTypeEnum<'a>) -> BasicValueEnum<'a> {
    match ty {
        BasicTypeEnum::ArrayType(t) => t.get_undef().into(),
        BasicTypeEnum::FloatType(t) => t.get_undef().into(),
        BasicTypeEnum::IntType(t) => t.get_undef().into(),
        BasicTypeEnum::PointerType(t) => t.get_undef().into(),
        BasicTypeEnum::StructType(t) => t.get_undef().into(),
        BasicTypeEnum::VectorType(t) => t.get_undef().into(),
    }
}

fn build_check_divisor_nonzero<'a, 'b>(
    globals: &Globals<'a, 'b>,
    builder: &Builder<'a>,
    val: IntValue<'a>,
) {
    let is_nonzero = builder.build_int_compare(
        IntPredicate::NE,
        val,
        val.get_type().const_int(0 as u64, false),
        "is_nonzero",
    );

    builder.build_call(
        globals.intrinsics.expect_i1,
        &[
            is_nonzero.into(),
            globals
                .context
                .bool_type()
                .const_int(1 as u64, false)
                .into(),
        ],
        "expect_nonzero",
    );

    let curr_block = builder.get_insert_block().unwrap();

    let panic_if_zero = globals
        .context
        .insert_basic_block_after(curr_block, "panic_if_zero");

    let continue_if_nonzero = globals
        .context
        .insert_basic_block_after(curr_block, "continue_if_nonzero");

    builder.build_conditional_branch(is_nonzero, continue_if_nonzero, panic_if_zero);

    builder.position_at_end(panic_if_zero);

    let panic_message =
        builder.build_global_string_ptr("panicked due to division by zero\n", "panic_message");

    let stderr_val = builder.build_load(globals.libc.stderr.into_pointer_value(), "stderr");

    builder.build_call(
        globals.libc.fprintf,
        &[stderr_val, panic_message.as_pointer_value().into()],
        "fprintf_call",
    );

    builder.build_call(
        globals.libc.exit,
        &[globals.context.i32_type().const_int(1 as u64, false).into()],
        "exit_call",
    );

    builder.build_unreachable();

    builder.position_at_end(continue_if_nonzero);
}

fn gen_expr<'a, 'b>(
    builder: &Builder<'a>,
    instances: &Instances<'a>,
    globals: &Globals<'a, 'b>,
    func: FunctionValue<'a>,
    tail_targets: &IdVec<tail::TailFuncId, TailCallTarget>,
    expr: &low::Expr,
    funcs: &IdVec<low::CustomFuncId, FunctionValue<'a>>,
    locals: &mut IdVec<low::LocalId, BasicValueEnum<'a>>,
) -> BasicValueEnum<'a> {
    use low::Expr as E;
    let context = globals.context;
    match expr {
        E::Local(local_id) => locals[local_id],
        E::Call(func_id, local_id) => builder
            .build_call(funcs[func_id], &[locals[local_id]], "result")
            .try_as_basic_value()
            .left()
            .unwrap(),
        E::TailCall(tail_id, local_id) => {
            builder.build_store(tail_targets[tail_id].arg_var, locals[local_id]);
            builder.build_unconditional_branch(tail_targets[tail_id].block);
            let unreachable_block = context.append_basic_block(func, "after_tail_call");
            builder.position_at_end(unreachable_block);
            // The return type of the tail call (which is somewhat theoretical, as a tail call never
            // actually returns to its original caller) is necessarily that of the function
            // currently being generated.
            get_undef(&func.get_type().get_return_type().unwrap())
        }
        E::If(local_id, then_expr, else_expr) => {
            let then_block = context.append_basic_block(func, "then_block");
            let else_block = context.append_basic_block(func, "else_block");
            let next_block = context.append_basic_block(func, "next_block");

            let cond = locals[local_id].into_int_value();
            builder.build_conditional_branch(cond, then_block, else_block);

            builder.position_at_end(then_block);
            let result_then = gen_expr(
                builder,
                instances,
                globals,
                func,
                tail_targets,
                then_expr,
                funcs,
                locals,
            );
            let last_then_expr_block = builder.get_insert_block().unwrap();
            builder.build_unconditional_branch(next_block);

            builder.position_at_end(else_block);
            let result_else = gen_expr(
                builder,
                instances,
                globals,
                func,
                tail_targets,
                else_expr,
                funcs,
                locals,
            );
            let last_else_expr_block = builder.get_insert_block().unwrap();
            builder.build_unconditional_branch(next_block);

            builder.position_at_end(next_block);
            let phi = builder.build_phi(result_then.get_type(), "result");
            phi.add_incoming(&[
                (&result_then, last_then_expr_block),
                (&result_else, last_else_expr_block),
            ]);
            phi.as_basic_value()
        }
        E::LetMany(bindings, local_id) => {
            let len = locals.len();
            for (_, binding_expr) in bindings {
                let binding_val = gen_expr(
                    builder,
                    instances,
                    globals,
                    func,
                    tail_targets,
                    &*binding_expr,
                    funcs,
                    locals,
                );
                let _ = locals.push(binding_val);
            }
            let body = locals[local_id];
            locals.truncate(len);
            body
        }
        E::Unreachable(type_) => {
            builder.build_unreachable();
            let unreachable_block = context.append_basic_block(func, "after_unreachable");
            builder.position_at_end(unreachable_block);
            match get_llvm_type(globals, instances, type_) {
                BasicTypeEnum::ArrayType(t) => t.get_undef().into(),
                BasicTypeEnum::FloatType(t) => t.get_undef().into(),
                BasicTypeEnum::IntType(t) => t.get_undef().into(),
                BasicTypeEnum::PointerType(t) => t.get_undef().into(),
                BasicTypeEnum::StructType(t) => t.get_undef().into(),
                BasicTypeEnum::VectorType(t) => t.get_undef().into(),
            }
        }
        E::Tuple(fields) => {
            let field_types: Vec<_> = fields.iter().map(|id| locals[id].get_type()).collect();
            let tup_type = context.struct_type(&field_types[..], false);

            let mut tup = tup_type.get_undef();
            for (elem, id) in fields.iter().enumerate() {
                tup = builder
                    .build_insert_value(tup, locals[id], elem.try_into().unwrap(), "insert")
                    .unwrap()
                    .into_struct_value();
            }

            tup.into()
        }
        E::TupleField(local_id, elem) => builder
            .build_extract_value(
                locals[local_id].into_struct_value(),
                (*elem).try_into().unwrap(),
                "extract",
            )
            .unwrap(),
        E::WrapVariant(variants, variant_id, local_id) => {
            let variant_type = get_llvm_variant_type(globals, instances, &variants);
            let byte_array_type = variant_type
                .get_field_type_at_index(VARIANT_BYTES_IDX)
                .unwrap();
            let byte_array_ptr =
                gen_entry_alloca(globals.context, builder, byte_array_type, "byte_array_ptr");
            let cast_byte_array_ptr = builder.build_bitcast(
                byte_array_ptr,
                locals[local_id].get_type().ptr_type(AddressSpace::Generic),
                "cast_byte_array_ptr",
            );

            builder.build_store(cast_byte_array_ptr.into_pointer_value(), locals[local_id]);

            let byte_array = builder.build_load(byte_array_ptr, "byte_array");

            let discrim = variant_type
                .get_field_type_at_index(VARIANT_DISCRIM_IDX)
                .unwrap()
                .into_int_type()
                .const_int(variant_id.0.try_into().unwrap(), false);

            let mut variant_value = variant_type.get_undef();
            variant_value = builder
                .build_insert_value(variant_value, discrim, VARIANT_DISCRIM_IDX, "insert")
                .unwrap()
                .into_struct_value();
            variant_value = builder
                .build_insert_value(variant_value, byte_array, VARIANT_BYTES_IDX, "insert")
                .unwrap()
                .into_struct_value();
            variant_value.into()
        }
        E::UnwrapVariant(variants, variant_id, local_id) => gen_unwrap_variant(
            builder,
            instances,
            globals,
            locals[local_id],
            variants,
            *variant_id,
        ),
        E::WrapCustom(type_id, local_id) => {
            let mut custom_type_val = globals.custom_types[type_id].ty.get_undef();
            custom_type_val = builder
                .build_insert_value(custom_type_val, locals[local_id], 0, "insert")
                .unwrap()
                .into_struct_value();

            custom_type_val.into()
        }
        E::UnwrapCustom(_type_id, local_id) => {
            let custom_type_content = builder
                .build_extract_value(locals[local_id].into_struct_value(), 0, "custom_type_val")
                .unwrap();

            custom_type_content
        }
        E::CheckVariant(variant_id, local_id) => {
            let discrim = builder
                .build_extract_value(
                    locals[local_id].into_struct_value(),
                    VARIANT_DISCRIM_IDX,
                    "discrim",
                )
                .unwrap()
                .into_int_value();

            let casted_variant_id = discrim
                .get_type()
                .const_int(variant_id.0.try_into().unwrap(), false);

            builder
                .build_int_compare(
                    IntPredicate::EQ,
                    casted_variant_id,
                    discrim,
                    "check_variant",
                )
                .into()
        }
        E::WrapBoxed(local_id, inner_type) => {
            let builtin = instances.get_rc(globals, inner_type);
            builder
                .build_call(builtin.new, &[locals[local_id]], "new_box")
                .try_as_basic_value()
                .left()
                .unwrap()
        }
        E::UnwrapBoxed(local_id, inner_type) => {
            let builtin = instances.get_rc(globals, inner_type);
            let ptr = builder
                .build_call(builtin.get, &[locals[local_id]], "unbox")
                .try_as_basic_value()
                .left()
                .unwrap()
                .into_pointer_value();
            builder.build_load(ptr, "content")
        }
        E::Retain(local_id, ty) => {
            gen_rc_op(
                RcOp::Retain,
                builder,
                instances,
                globals,
                func,
                ty,
                locals[local_id],
            );
            context.struct_type(&[], false).get_undef().into()
        }
        E::Release(local_id, ty) => {
            gen_rc_op(
                RcOp::Release,
                builder,
                instances,
                globals,
                func,
                ty,
                locals[local_id],
            );
            context.struct_type(&[], false).get_undef().into()
        }
        E::ArithOp(op) => match op {
            low::ArithOp::Op(type_, bin_op, lhs, rhs) => match bin_op {
                first_ord::BinOp::Add => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_add(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "byte_add",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_add(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_add",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_add(
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_add",
                        )
                        .into(),
                },
                first_ord::BinOp::Sub => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_sub(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "byte_sub",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_sub(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_sub",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_sub(
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_sub",
                        )
                        .into(),
                },
                first_ord::BinOp::Mul => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_mul(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "byte_mul",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_mul(
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_mul",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_mul(
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_mul",
                        )
                        .into(),
                },
                first_ord::BinOp::Div => match type_ {
                    first_ord::NumType::Byte => {
                        build_check_divisor_nonzero(globals, builder, locals[rhs].into_int_value());
                        builder
                            .build_int_unsigned_div(
                                locals[lhs].into_int_value(),
                                locals[rhs].into_int_value(),
                                "byte_div",
                            )
                            .into()
                    }
                    first_ord::NumType::Int => {
                        build_check_divisor_nonzero(globals, builder, locals[rhs].into_int_value());
                        builder
                            .build_int_signed_div(
                                locals[lhs].into_int_value(),
                                locals[rhs].into_int_value(),
                                "int_div",
                            )
                            .into()
                    }
                    first_ord::NumType::Float => builder
                        .build_float_div(
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_div",
                        )
                        .into(),
                },
            },
            low::ArithOp::Cmp(type_, cmp, lhs, rhs) => match cmp {
                first_ord::Comparison::Less => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_compare(
                            IntPredicate::ULT,
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "bytes_less",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_compare(
                            IntPredicate::SLT,
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_less",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_compare(
                            FloatPredicate::OLT,
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_less",
                        )
                        .into(),
                },
                first_ord::Comparison::LessEqual => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_compare(
                            IntPredicate::ULE,
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "bytes_less_equal",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_compare(
                            IntPredicate::SLE,
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_less_equal",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_compare(
                            FloatPredicate::OLE,
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_less_equal",
                        )
                        .into(),
                },
                first_ord::Comparison::Equal => match type_ {
                    first_ord::NumType::Byte => builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "bytes_equal",
                        )
                        .into(),
                    first_ord::NumType::Int => builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            locals[lhs].into_int_value(),
                            locals[rhs].into_int_value(),
                            "int_equal",
                        )
                        .into(),
                    first_ord::NumType::Float => builder
                        .build_float_compare(
                            FloatPredicate::OEQ,
                            locals[lhs].into_float_value(),
                            locals[rhs].into_float_value(),
                            "float_equal",
                        )
                        .into(),
                },
            },
            low::ArithOp::Negate(type_, local_id) => match type_ {
                first_ord::NumType::Byte => builder
                    .build_int_neg(locals[local_id].into_int_value(), "byte_neg")
                    .into(),
                first_ord::NumType::Int => builder
                    .build_int_neg(locals[local_id].into_int_value(), "int_neg")
                    .into(),
                first_ord::NumType::Float => builder
                    .build_float_neg(locals[local_id].into_float_value(), "float_neg")
                    .into(),
            },
        },
        E::ArrayOp(rep, item_type, array_op) => match rep {
            constrain::RepChoice::OptimizedMut => {
                let builtin = instances.get_flat_array(globals, item_type);
                match array_op {
                    low::ArrayOp::New() => builder
                        .build_call(builtin.interface().new, &[], "flat_array_new")
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Item(array_id, index_id) => builder
                        .build_call(
                            builtin.interface().item,
                            &[locals[array_id], locals[index_id]],
                            "flat_array_item",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Len(array_id) => builder
                        .build_call(
                            builtin.interface().len,
                            &[locals[array_id]],
                            "flat_array_len",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Push(array_id, item_id) => builder
                        .build_call(
                            builtin.interface().push,
                            &[locals[array_id], locals[item_id]],
                            "flat_array_push",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Pop(array_id) => builder
                        .build_call(
                            builtin.interface().pop,
                            &[locals[array_id]],
                            "flat_array_pop",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Replace(array_id, item_id) => builder
                        .build_call(
                            builtin.interface().replace,
                            &[locals[array_id], locals[item_id]],
                            "flat_array_replace",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                }
            }
            constrain::RepChoice::FallbackImmut => {
                let builtin = instances.get_persistent_array(globals, item_type);
                match array_op {
                    low::ArrayOp::New() => builder
                        .build_call(builtin.interface().new, &[], "pers_array_new")
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Item(array_id, index_id) => builder
                        .build_call(
                            builtin.interface().item,
                            &[locals[array_id], locals[index_id]],
                            "pers_array_item",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Len(array_id) => builder
                        .build_call(
                            builtin.interface().len,
                            &[locals[array_id]],
                            "pers_array_len",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Push(array_id, item_id) => builder
                        .build_call(
                            builtin.interface().push,
                            &[locals[array_id], locals[item_id]],
                            "pers_array_push",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Pop(array_id) => builder
                        .build_call(
                            builtin.interface().pop,
                            &[locals[array_id]],
                            "pers_array_pop",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::ArrayOp::Replace(array_id, item_id) => builder
                        .build_call(
                            builtin.interface().replace,
                            &[locals[array_id], locals[item_id]],
                            "pers_array_replace",
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                }
            }
        },
        E::IoOp(rep, io_op) => match rep {
            constrain::RepChoice::OptimizedMut => {
                let builtin_io = instances.flat_array_io;
                match io_op {
                    low::IoOp::Input => builder
                        .build_call(builtin_io.input, &[], "flat_array_input")
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::IoOp::Output(array_id) => {
                        builder.build_call(
                            builtin_io.output,
                            &[locals[array_id]],
                            "flat_array_output",
                        );

                        context.struct_type(&[], false).get_undef().into()
                    }
                }
            }
            constrain::RepChoice::FallbackImmut => {
                let builtin_io = instances.persistent_array_io;
                match io_op {
                    low::IoOp::Input => builder
                        .build_call(builtin_io.input, &[], "pers_array_input")
                        .try_as_basic_value()
                        .left()
                        .unwrap(),
                    low::IoOp::Output(array_id) => {
                        builder.build_call(
                            builtin_io.output,
                            &[locals[array_id]],
                            "pers_array_output",
                        );

                        context.struct_type(&[], false).get_undef().into()
                    }
                }
            }
        },
        E::BoolLit(val) => {
            BasicValueEnum::from(context.bool_type().const_int(*val as u64, false)).into()
        }

        E::ByteLit(val) => {
            BasicValueEnum::from(context.i8_type().const_int(*val as u64, false)).into()
        }

        E::IntLit(val) => {
            BasicValueEnum::from(context.i64_type().const_int(*val as u64, true)).into()
        }
        E::FloatLit(val) => BasicValueEnum::from(context.f64_type().const_float(*val)).into(),
    }
}

fn gen_function<'a, 'b>(
    context: &'a Context,
    instances: &Instances<'a>,
    globals: &Globals<'a, 'b>,
    func_decl: FunctionValue<'a>,
    funcs: &IdVec<low::CustomFuncId, FunctionValue<'a>>,
    func: &low::FuncDef,
) {
    let builder = context.create_builder();

    let entry = context.append_basic_block(func_decl, "entry");

    // Declare tail call targets, but don't populate their bodies yet. Tail functions are
    // implemented via blocks which may be jumped to, and their arguments are implemented as mutable
    // variables.
    builder.position_at_end(entry);
    let tail_targets = func.tail_funcs.map(|tail_id, tail_func| {
        let arg_var = builder.build_alloca(
            get_llvm_type(globals, instances, &tail_func.arg_type),
            &format!("tail_{}_arg", tail_id.0),
        );

        let block = context.append_basic_block(func_decl, &format!("tail_{}", tail_id.0));

        TailCallTarget { arg_var, block }
    });

    // Generate main body
    {
        let mut locals = IdVec::from_items(vec![func_decl.get_nth_param(0).unwrap()]);
        let ret_value = gen_expr(
            &builder,
            instances,
            globals,
            func_decl,
            &tail_targets,
            &func.body,
            funcs,
            &mut locals,
        );
        builder.build_return(Some(&ret_value));
    }

    // Generate tail function bodies
    for (tail_id, tail_target) in &tail_targets {
        builder.position_at_end(tail_target.block);
        let tail_arg_val = builder.build_load(tail_target.arg_var, "tail_arg_val");
        let mut locals = IdVec::from_items(vec![tail_arg_val]);
        let ret_value = gen_expr(
            &builder,
            instances,
            globals,
            func_decl,
            &tail_targets,
            &func.tail_funcs[tail_id].body,
            funcs,
            &mut locals,
        );
        builder.build_return(Some(&ret_value));
    }
}

fn get_target_machine(target: &cli::TargetConfig, opt_level: OptimizationLevel) -> TargetMachine {
    Target::initialize_all(&InitializationConfig::default());
    let llvm_target = Target::from_triple(&target.target).unwrap();

    // RelocMode and CodeModel can affect the options we need to pass cc::Build in get_cc
    llvm_target
        .create_target_machine(
            &target.target,
            &target.target_cpu,
            &target.target_features,
            opt_level,
            RelocMode::PIC,
            // https://stackoverflow.com/questions/40493448/what-does-the-codemodel-in-clang-llvm-refer-to
            CodeModel::Small,
        )
        .unwrap()
}

fn add_size_deps(type_: &low::Type, deps: &mut BTreeSet<low::CustomTypeId>) {
    match type_ {
        low::Type::Bool | low::Type::Num(_) => {}

        low::Type::Array(_, _) | low::Type::HoleArray(_, _) | low::Type::Boxed(_) => {}

        low::Type::Tuple(items) => {
            for item in items {
                add_size_deps(item, deps)
            }
        }

        low::Type::Variants(variants) => {
            for (_, variant) in variants {
                add_size_deps(variant, deps)
            }
        }

        low::Type::Custom(custom) => {
            deps.insert(*custom);
        }
    }
}

fn custom_type_dep_order(typedefs: &IdVec<low::CustomTypeId, low::Type>) -> Vec<low::CustomTypeId> {
    let size_deps = Graph {
        edges_out: typedefs.map(|_, def| {
            let mut deps = BTreeSet::new();
            add_size_deps(def, &mut deps);
            deps.into_iter().collect()
        }),
    };

    let sccs = graph::strongly_connected(&size_deps);

    sccs.into_iter()
        .map(|scc| {
            debug_assert_eq!(scc.len(), 1);
            scc[0]
        })
        .collect()
}

fn get_intrinsics<'a>(context: &'a Context, module: &Module<'a>) -> Intrinsics<'a> {
    Intrinsics {
        expect_i1: module.add_function(
            "llvm.expect.i1",
            context.bool_type().fn_type(
                &[context.bool_type().into(), context.bool_type().into()],
                false,
            ),
            Some(Linkage::External),
        ),
    }
}

fn gen_program<'a>(
    program: low::Program,
    target_machine: &TargetMachine,
    context: &'a Context,
) -> Module<'a> {
    let module = context.create_module("module");
    module.set_triple(&target_machine.get_triple());
    module.set_data_layout(&target_machine.get_target_data().get_data_layout());

    let intrinsics = get_intrinsics(context, &module);

    let libc = LibC::declare(&context, &module);

    let custom_types = program
        .custom_types
        .map(|type_id, _type| CustomTypeDecls::declare(&context, &module, type_id));

    let globals = Globals {
        context: &context,
        module: &module,
        intrinsics,
        target: &target_machine.get_target_data(),
        libc,
        custom_types,
    };

    let instances = Instances::new(&globals);

    for type_id in custom_type_dep_order(&program.custom_types) {
        let type_decls = &globals.custom_types[type_id];
        type_decls.define_type(&globals, &instances, &program.custom_types[type_id]);
    }

    let funcs = program.funcs.map(|func_id, func_def| {
        let return_type = get_llvm_type(&globals, &instances, &func_def.ret_type);
        let arg_type = get_llvm_type(&globals, &instances, &func_def.arg_type);

        module.add_function(
            &format!("func_{}", func_id.0),
            return_type.fn_type(&[arg_type], false),
            Some(Linkage::Internal),
        )
    });

    for (func_id, func) in &funcs {
        gen_function(
            context,
            &instances,
            &globals,
            *func,
            &funcs,
            &program.funcs[func_id],
        );
    }

    instances.define(&globals);

    for (type_id, type_decls) in &globals.custom_types {
        type_decls.define(&globals, &instances, &program.custom_types[type_id]);
    }

    libc.define(&context);

    let i32_type = context.i32_type();
    let unit_type = context.struct_type(&[], false);
    let i8_ptr_ptr_type = context
        .i8_type()
        .ptr_type(AddressSpace::Generic)
        .ptr_type(AddressSpace::Generic);
    let main = module.add_function(
        "main",
        i32_type.fn_type(&[i32_type.into(), i8_ptr_ptr_type.into()], false),
        Some(Linkage::External),
    );

    let builder = context.create_builder();
    let main_block = context.append_basic_block(main, "main_block");

    builder.position_at_end(main_block);
    builder.build_call(libc.initialize, &[], "libc_initialize");

    builder.build_call(
        funcs[program.main],
        &[unit_type.get_undef().into()],
        "main_result",
    );

    builder.build_call(libc.cleanup, &[], "libc_cleanup");
    builder.build_return(Some(&i32_type.const_int(0, false)));

    return module;
}

fn run_cc(_target_triple: &TargetTriple, obj_path: &Path, exe_path: &Path) {
    // TODO: handle different platforms!!!
    let clang = find_clang(10).unwrap();
    std::process::Command::new(clang.path)
        .arg("-O3")
        .arg("-ffunction-sections")
        .arg("-fdata-sections")
        .arg("-fPIC")
        .arg("-m64")
        .arg("-Wl,--gc-sections")
        .arg("-o")
        .arg(exe_path)
        .arg(obj_path)
        .status()
        .unwrap();
}

fn verify_llvm(module: &Module) {
    if let Err(err) = module.verify() {
        panic!("LLVM verification failed:\n{}", err.to_string());
    }
}

#[derive(Clone, Copy, Debug)]
struct ArtifactPaths<'a> {
    ll: Option<&'a Path>,
    opt_ll: Option<&'a Path>,
    asm: Option<&'a Path>,
    obj: &'a Path,
    exe: &'a Path,
}

fn compile_to_executable(
    program: low::Program,
    target: &cli::TargetConfig,
    opt_level: OptimizationLevel,
    artifact_paths: ArtifactPaths,
) {
    let target_machine = get_target_machine(&target, opt_level);
    let context = Context::create();

    let module = gen_program(program, &target_machine, &context);

    // We output the ll file before verifying so that it can be inspected even if verification
    // fails.
    if let Some(ll_path) = artifact_paths.ll {
        module.print_to_file(ll_path).unwrap();
    }

    verify_llvm(&module);

    let pass_manager_builder = PassManagerBuilder::create();
    pass_manager_builder.set_optimization_level(opt_level);
    let pass_manager = PassManager::create(());
    pass_manager_builder.populate_module_pass_manager(&pass_manager);
    pass_manager.run_on(&module);

    if let Some(opt_ll_path) = artifact_paths.opt_ll {
        module.print_to_file(opt_ll_path).unwrap();
    }

    // Optimization should produce a well-formed module, but if it doesn't, we want to know about
    // it!
    verify_llvm(&module);

    if let Some(asm_path) = artifact_paths.asm {
        target_machine
            .write_to_file(&module, FileType::Assembly, &asm_path)
            .unwrap();
    }

    target_machine
        .write_to_file(&module, FileType::Object, artifact_paths.obj)
        .unwrap();

    run_cc(&target.target, artifact_paths.obj, artifact_paths.exe);
}

pub fn run(stdio: Stdio, program: low::Program, use_valgrind: bool) -> Child {
    let target = cli::native_target_config();
    let opt_level = cli::default_llvm_opt_level();

    let obj_path = tempfile::Builder::new()
        .suffix(".o")
        .tempfile_in("")
        .unwrap()
        .into_temp_path();

    let output_path = tempfile::Builder::new()
        .prefix(".tmp-exe-")
        .tempfile_in("")
        .unwrap()
        .into_temp_path();

    compile_to_executable(
        program,
        &target,
        opt_level,
        ArtifactPaths {
            ll: None,
            opt_ll: None,
            asm: None,
            obj: &obj_path,
            exe: &output_path,
        },
    );

    std::mem::drop(obj_path);

    spawn_process(stdio, output_path, use_valgrind).unwrap()
}

pub fn build(program: low::Program, config: &cli::BuildConfig) {
    if let Some(artifact_dir) = &config.artifact_dir {
        compile_to_executable(
            program,
            &config.target,
            config.llvm_opt_level,
            ArtifactPaths {
                ll: Some(&artifact_dir.artifact_path("ll")),
                opt_ll: Some(&artifact_dir.artifact_path("opt.ll")),
                asm: Some(&artifact_dir.artifact_path("s")),
                obj: &artifact_dir.artifact_path("o"),
                exe: &config.output_path,
            },
        );
    } else {
        let obj_path = tempfile::Builder::new()
            .suffix(".o")
            .tempfile_in("")
            .unwrap()
            .into_temp_path();

        compile_to_executable(
            program,
            &config.target,
            config.llvm_opt_level,
            ArtifactPaths {
                ll: None,
                opt_ll: None,
                asm: None,
                obj: &obj_path,
                exe: &config.output_path,
            },
        )
    }
}
