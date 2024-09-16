#![allow(dead_code)]

mod array;
mod cow_array;
mod fountain_pen;
mod prof_report;
mod rc;
mod tal;
mod zero_sized_array;

use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::low_ast as low;
use crate::data::mode_annot_ast2::Mode;
use crate::data::profile as prof;
use crate::data::rc_specialized_ast2::ModeScheme;
use crate::data::tail_rec_ast as tail;
use crate::llvm_gen::array::ArrayImpl;
use crate::llvm_gen::cow_array::{CowArrayImpl, CowArrayIoImpl};
use crate::llvm_gen::prof_report::{
    define_prof_report_fn, ProfilePointCounters, ProfilePointDecls,
};
use crate::llvm_gen::rc::RcBoxBuiltin;
use crate::llvm_gen::tal::{ProfileRc, Tal};
use crate::llvm_gen::zero_sized_array::ZeroSizedArrayImpl;
use crate::pseudoprocess::{spawn_process, Child, Stdio, ValgrindConfig};
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use crate::{cli, progress_ui};
use find_clang::find_default_clang;
use id_collections::IdVec;
use id_graph_sccs::{SccKind, Sccs};
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::passes::{PassManager, PassManagerBuilder};
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetData, TargetMachine,
    TargetTriple,
};
use inkwell::types::{BasicType, BasicTypeEnum, IntType, StructType};
use inkwell::values::{
    BasicValue, BasicValueEnum, CallSiteValue, FloatValue, FunctionValue, GlobalValue, IntValue,
    PointerValue, StructValue,
};
use inkwell::AddressSpace;
use inkwell::OptimizationLevel;
use inkwell::{FloatPredicate, IntPredicate};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::convert::TryInto;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::rc::Rc;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("directory {0:?} does not exist")]
    DirectoryDoesNotExist(PathBuf),
    #[error("expected a file but was provided directory {0:?} instead")]
    GivenDirExpectedFile(PathBuf),
    #[error("expected a directory but was provided file {0:?} instead")]
    GivenFileExpectedDir(PathBuf),
    #[error("could not create directory, IO error: {0}")]
    CouldNotCreateOutputDir(std::io::Error),
    #[error("could not create temporary file, IO error: {0}")]
    CouldNotCreateTempFile(std::io::Error),
    #[error("could not create object file, IO error: {0}")]
    CouldNotWriteObjFile(std::io::Error),
    #[error("could not create output file, {0}")]
    CouldNotWriteOutputFile(std::io::Error),
    #[error("could not locate valid clang install: {0}")]
    CouldNotFindClang(String),
    #[error("clang exited unsuccessfully, IO error: {0}")]
    ClangFailed(std::io::Error),
    #[error("selected LLVM target triple is not supported on your system, {0}")]
    TargetTripleNotSupported(inkwell::support::LLVMString),
    #[error("could not configure LLVM for target")]
    CouldNotCreateTargetMachine,
    #[error("compilation of generated LLVM-IR failed, {0}")]
    LlvmCompilationFailed(inkwell::support::LLVMString),
    #[error("could not dump IR from LLVM, {0}")]
    CouldNotDumpIrFromLlvm(inkwell::support::LLVMString),
    #[error("could not spawn child process, IO error: {0}")]
    CouldNotSpawnChild(std::io::Error),
}

type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug)]
struct VariantsType<'a, 'b> {
    type_: StructType<'a>,
    variants: &'b IdVec<first_ord::VariantId, low::Type>,
}

impl<'a, 'b> VariantsType<'a, 'b> {
    const DISCRIM_IDX: u32 = 0;
    // we use a zero sized array to enforce proper alignment on `bytes`
    const ALIGN_IDX: u32 = 1;
    const BYTES_IDX: u32 = 2;

    fn is_zero_sized_with(
        _variants: &IdVec<first_ord::VariantId, low::Type>,
        _custom_is_zero_sized: &impl Fn(low::CustomTypeId) -> IsZeroSized,
    ) -> bool {
        // All variants have a non-zero-sized discriminant
        false
    }

    fn into_raw(self) -> BasicTypeEnum<'a> {
        self.type_.into()
    }

    fn new(
        globals: &Globals<'a, '_>,
        instances: &Instances<'a>,
        variants: &'b IdVec<first_ord::VariantId, low::Type>,
    ) -> VariantsType<'a, 'b> {
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
            for variant_type in variants.values() {
                let variant_type = get_llvm_type(globals, instances, &variant_type);
                debug_assert!(variant_type.is_sized());
                let alignment = globals.target.get_abi_alignment(&variant_type);
                let size = globals.target.get_abi_size(&variant_type);
                max_alignment = max_alignment.max(alignment);
                max_size = max_size.max(size);
            }
            (max_alignment, max_size)
        };

        let alignment_type = match max_alignment {
            1 => globals.context.i8_type(),
            2 => globals.context.i16_type(),
            4 => globals.context.i32_type(),
            8 => globals.context.i64_type(),
            _ => panic!["Unsupported alignment {}", max_alignment],
        };

        let alignment_array = alignment_type.array_type(0);

        // The payload is represented by an array of "chunks", each an integer.
        //
        // Originally we always used an array of 'i8's here (i.e. the chunk size was always 1 byte), but
        // it turns out that when trying to bitcast byte arrays stored in SSA registers into other
        // types, LLVM generates huge sequences of bit operations to assemble the resulting structure
        // byte-by-byte.  Constructing our payload array out of larger chunks mitigates this problem
        // somewhat.
        //
        // Currently, we use the maximum alignment to determine the chunk size (which, incidentally,
        // makes the zero-size alignment array redundant). This is only a heuristic, and we may want to
        // change it later, or even use a heterogenous struct of chunks.  Other code in this module
        // should *not* rely on assumptions about the particular chunking strategy used here.
        let num_chunks: u32 = ceil_div(max_size as i64, max_alignment as i64)
            .try_into()
            .unwrap();
        let bytes = alignment_type.array_type(num_chunks);

        let field_types = &[discrim_type.into(), alignment_array.into(), bytes.into()];
        let type_ = globals.context.struct_type(field_types, false);

        Self { type_, variants }
    }

    fn discrim_type(&self) -> IntType<'a> {
        self.type_
            .get_field_type_at_index(Self::DISCRIM_IDX)
            .unwrap()
            .into_int_type()
    }

    fn bytes_type(&self) -> BasicTypeEnum<'a> {
        self.type_.get_field_type_at_index(Self::BYTES_IDX).unwrap()
    }

    fn content_type<'c>(
        &self,
        globals: &Globals<'a, 'c>,
        instances: &Instances<'a>,
        variant_id: first_ord::VariantId,
    ) -> BasicTypeEnum<'a> {
        get_llvm_type(globals, instances, &self.variants[variant_id])
    }

    fn discrim_const(&self, id: first_ord::VariantId) -> IntValue<'a> {
        self.discrim_type()
            .const_int(id.0.try_into().unwrap(), false)
            .into()
    }

    fn build_bytes(
        &self,
        builder: &Builder<'a>,
        globals: &Globals<'a, '_>,
        content: BasicValueEnum<'a>,
    ) -> BasicValueEnum<'a> {
        let byte_array_type = self.bytes_type();
        let byte_array_ptr =
            gen_entry_alloca(globals.context, builder, byte_array_type, "byte_array_ptr");

        let content_ptr_type = content.get_type().ptr_type(AddressSpace::default());
        let content_ptr = builder
            .build_bitcast(byte_array_ptr, content_ptr_type, "cast_byte_array_ptr")
            .unwrap();

        builder
            .build_store(content_ptr.into_pointer_value(), content)
            .unwrap();

        builder
            .build_load(byte_array_type, byte_array_ptr, "byte_array")
            .unwrap()
    }

    fn build_value(
        &self,
        builder: &Builder<'a>,
        discrim: impl BasicValue<'a>,
        byte_array: impl BasicValue<'a>,
    ) -> VariantsValue<'a> {
        let mut value = self.type_.get_undef();
        value = builder
            .build_insert_value(value, discrim, Self::DISCRIM_IDX, "insert")
            .unwrap()
            .into_struct_value();
        value = builder
            .build_insert_value(value, byte_array, Self::BYTES_IDX, "insert")
            .unwrap()
            .into_struct_value();
        VariantsValue { inner: value }
    }
}

#[derive(Clone, Debug)]
struct VariantsValue<'a> {
    inner: StructValue<'a>,
}

impl<'a> VariantsValue<'a> {
    fn from_raw(value: BasicValueEnum<'a>) -> Self {
        Self {
            inner: value.into_struct_value(),
        }
    }

    fn into_raw(self) -> BasicValueEnum<'a> {
        self.inner.into()
    }

    fn build_get_discrim(&self, builder: &Builder<'a>) -> IntValue<'a> {
        builder
            .build_extract_value(self.inner, VariantsType::DISCRIM_IDX, "discrim")
            .unwrap()
            .into_int_value()
    }

    fn build_get_content(
        &self,
        builder: &Builder<'a>,
        globals: &Globals<'a, '_>,
        instances: &Instances<'a>,
        type_: &VariantsType<'a, '_>,
        id: first_ord::VariantId,
    ) -> BasicValueEnum<'a> {
        let byte_array_ptr = gen_entry_alloca(
            globals.context,
            builder,
            type_.bytes_type(),
            "byte_array_ptr",
        );
        let byte_array = builder
            .build_extract_value(self.inner, VariantsType::BYTES_IDX, "byte_array")
            .unwrap();
        builder.build_store(byte_array_ptr, byte_array).unwrap();

        let content_type = type_.content_type(globals, instances, id);
        let content_ptr = builder
            .build_bitcast(
                byte_array_ptr,
                content_type.ptr_type(AddressSpace::default()),
                "content_ptr",
            )
            .unwrap();
        let content = builder
            .build_load(content_type, content_ptr.into_pointer_value(), "content")
            .unwrap();

        content
    }

    /// This function handles the bookkeeping needed to build a switch statement over variants. It
    /// will position the builder correctly each time before calling `build_case` and after the
    /// switch is done.
    fn build_switch(
        &self,
        builder: &Builder<'a>,
        globals: &Globals<'a, '_>,
        func: FunctionValue<'a>,
        type_: &VariantsType<'a, '_>,
        mut build_case: impl FnMut(first_ord::VariantId),
    ) {
        let discrim = self.build_get_discrim(builder);
        let undefined_block = globals.context.append_basic_block(func, "undefined");
        let mut variant_blocks = IdVec::new();
        for _ in 0..type_.variants.len() {
            let _ = variant_blocks.push(globals.context.append_basic_block(func, "variant"));
        }
        let switch_blocks = variant_blocks
            .iter()
            .map(|(i, variant_block)| (type_.discrim_const(i), *variant_block))
            .collect::<Vec<_>>();
        builder
            .build_switch(discrim, undefined_block, &switch_blocks[..])
            .unwrap();

        let next_block = globals.context.append_basic_block(func, "next");

        builder.position_at_end(undefined_block);
        builder.build_unreachable().unwrap();

        for (i, variant_block) in variant_blocks.iter() {
            builder.position_at_end(*variant_block);
            build_case(i);
            builder.build_unconditional_branch(next_block).unwrap();
        }

        builder.position_at_end(next_block);
    }
}

#[derive(Clone, Debug)]
struct TupleType<'a> {
    inner: StructType<'a>,
}

impl<'a> TupleType<'a> {
    fn is_zero_sized_with(
        fields: &Vec<low::Type>,
        custom_is_zero_sized: &impl Fn(low::CustomTypeId) -> IsZeroSized,
    ) -> bool {
        fields
            .iter()
            .all(|field| is_zero_sized_with(field, custom_is_zero_sized))
    }

    fn from_raw(
        globals: &Globals<'a, '_>,
        fields: impl Iterator<Item = BasicTypeEnum<'a>>,
    ) -> Self {
        let fields = fields.collect::<Vec<_>>();
        let type_ = globals.context.struct_type(&fields[..], false);
        Self { inner: type_ }
    }

    fn into_raw(self) -> BasicTypeEnum<'a> {
        self.inner.into()
    }

    fn new(globals: &Globals<'a, '_>, instances: &Instances<'a>, fields: &Vec<low::Type>) -> Self {
        let fields = fields
            .iter()
            .map(|field| get_llvm_type(globals, instances, field))
            .collect::<Vec<_>>();
        let type_ = globals.context.struct_type(&fields[..], false);
        Self { inner: type_ }
    }

    fn build_value(
        &self,
        builder: &Builder<'a>,
        fields: impl Iterator<Item = BasicValueEnum<'a>>,
    ) -> TupleValue<'a> {
        let mut value = self.inner.get_undef();
        for (i, field) in fields.enumerate() {
            value = builder
                .build_insert_value(value, field, i.try_into().unwrap(), "insert")
                .unwrap()
                .into_struct_value();
        }
        TupleValue { inner: value }
    }
}

struct TupleValue<'a> {
    inner: StructValue<'a>,
}

impl<'a> TupleValue<'a> {
    fn from_raw(value: BasicValueEnum<'a>) -> Self {
        Self {
            inner: value.into_struct_value(),
        }
    }

    fn into_raw(self) -> BasicValueEnum<'a> {
        self.inner.into()
    }

    fn build_get_field(&self, builder: &Builder<'a>, i: usize) -> BasicValueEnum<'a> {
        builder
            .build_extract_value(self.inner, i.try_into().unwrap(), "field")
            .unwrap()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum IsZeroSized {
    NonZeroSized,
    ZeroSized,
}

#[derive(Clone, Debug)]
struct Globals<'a, 'b> {
    context: &'a Context,
    module: &'b Module<'a>,
    target: &'b TargetData,
    tal: Tal<'a>,
    custom_types_zero_sized: IdVec<low::CustomTypeId, IsZeroSized>,
    custom_types: IdVec<low::CustomTypeId, CustomTypeDecls<'a>>,
    profile_points: IdVec<prof::ProfilePointId, ProfilePointDecls<'a>>,
}

#[derive(Clone, Copy, Debug)]
struct CustomTypeDecls<'a> {
    type_: StructType<'a>,
    release: BTreeMap<ModeScheme, FunctionValue<'a>>,
    retain: FunctionValue<'a>,
}

impl<'a> CustomTypeDecls<'a> {
    fn declare_type(context: &'a Context, id: first_ord::CustomTypeId) -> Self {
        Self {
            type_: context.opaque_struct_type(&format!("type_{}", id.0)),
            release: BTreeMap::new(),
            retain: BTreeMap::new(),
        }
    }

    fn declare(
        context: &'a Context,
        module: &Module<'a>,
        first_ord_id: first_ord::CustomTypeId,
        ty: StructType<'a>,
    ) -> Self {
        let void_type = context.void_type();
        let release_func = module.add_function(
            &format!("release_{}_{}", first_ord_id.0, low_id.0),
            void_type.fn_type(&[ty.into()], false),
            Some(Linkage::Internal),
        );
        let retain_func = module.add_function(
            &format!("retain_{}_{}", first_ord_id.0, low_id.0),
            void_type.fn_type(&[ty.into()], false),
            Some(Linkage::Internal),
        );
        CustomTypeDecls {
            type_: ty,
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
        self.type_.set_body(&[ty], false);
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

        builder.build_return(None).unwrap();

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

        builder.build_return(None).unwrap();
    }
}

fn declare_profile_points<'a>(
    context: &'a Context,
    module: &Module<'a>,
    program: &low::Program,
) -> IdVec<prof::ProfilePointId, ProfilePointDecls<'a>> {
    let mut decls = program.profile_points.map_refs(|_, _| ProfilePointDecls {
        counters: BTreeMap::new(),
        skipped_tail_rec: BTreeSet::new(),
    });

    for (func_id, def) in &program.funcs {
        if let Some(prof_id) = def.profile_point {
            let total_calls = module.add_global(
                context.i64_type(),
                None, // TODO: Is this the correct address space annotation?
                &format!("total_calls_{}", func_id.0),
            );
            total_calls.set_initializer(&context.i64_type().const_zero());

            let total_clock_nanos = module.add_global(
                context.i64_type(),
                None, // TODO: Is this the correct address space annotation?
                &format!("total_clock_nanos_{}", func_id.0),
            );
            total_clock_nanos.set_initializer(&context.i64_type().const_zero());

            let (total_retain_count, total_release_count) =
                if program.profile_points[prof_id].record_rc {
                    let total_retain_count = module.add_global(
                        context.i64_type(),
                        None, // TODO: Is this the correct address space annotation?
                        &format!("total_retain_count_{}", func_id.0),
                    );
                    total_retain_count.set_initializer(&context.i64_type().const_zero());

                    let total_release_count = module.add_global(
                        context.i64_type(),
                        None, // TODO: Is this the correct address space annotation?
                        &format!("total_release_count_{}", func_id.0),
                    );
                    total_release_count.set_initializer(&context.i64_type().const_zero());

                    (Some(total_retain_count), Some(total_release_count))
                } else {
                    (None, None)
                };

            let existing = decls[prof_id].counters.insert(
                func_id,
                ProfilePointCounters {
                    total_calls,
                    total_clock_nanos,
                    total_retain_count,
                    total_release_count,
                },
            );
            debug_assert!(existing.is_none());
        }

        for (tail_id, tail_def) in &def.tail_funcs {
            // We don't currently attempt to profile tail-recursive functions
            if let Some(prof_id) = tail_def.profile_point {
                let is_new = decls[prof_id].skipped_tail_rec.insert((func_id, tail_id));
                debug_assert!(is_new);
            }
        }
    }

    decls
}

struct Instances<'a> {
    cow_arrays: RefCell<BTreeMap<low::Type, Rc<dyn ArrayImpl<'a> + 'a>>>,
    cow_array_io: CowArrayIoImpl<'a>,
    rcs: RefCell<BTreeMap<low::Type, RcBoxBuiltin<'a>>>,
}

impl<'a> Instances<'a> {
    fn new<'b>(globals: &Globals<'a, 'b>) -> Self {
        let mut cow_arrays = BTreeMap::new();
        let byte_cow_builtin = CowArrayImpl::declare(
            globals.context,
            globals.target,
            globals.module,
            globals.context.i8_type().into(),
        );

        cow_arrays.insert(
            low::Type::Num(first_ord::NumType::Byte),
            Rc::new(byte_cow_builtin) as Rc<dyn ArrayImpl<'a>>,
        );
        let cow_array_io =
            CowArrayIoImpl::declare(globals.context, globals.module, byte_cow_builtin);

        Self {
            cow_arrays: RefCell::new(cow_arrays),
            cow_array_io: cow_array_io,
            rcs: RefCell::new(BTreeMap::new()),
        }
    }

    fn get_cow_array<'b>(
        &self,
        globals: &Globals<'a, 'b>,
        item_type: &low::Type,
    ) -> Rc<dyn ArrayImpl<'a> + 'a> {
        if let Some(existing) = self.cow_arrays.borrow().get(&item_type.clone()) {
            return existing.clone();
        }
        let ty = get_llvm_type(globals, self, item_type);
        let new_builtin = if is_zero_sized(globals, item_type) {
            Rc::new(ZeroSizedArrayImpl::declare(
                globals.context,
                globals.target,
                globals.module,
                ty,
            )) as Rc<dyn ArrayImpl<'a>>
        } else {
            Rc::new(CowArrayImpl::declare(
                globals.context,
                globals.target,
                globals.module,
                ty,
            )) as Rc<dyn ArrayImpl<'a>>
        };
        self.cow_arrays
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

    fn define<'b>(
        &self,
        globals: &Globals<'a, 'b>,
        rc_progress: impl ProgressLogger,
        cow_progress: impl ProgressLogger,
    ) {
        let builder = globals.context.create_builder();
        let void_type = globals.context.void_type();

        // rcs
        let mut rc_progress = rc_progress.start_session(Some(self.rcs.borrow().len()));
        for (i, (inner_type, rc_builtin)) in self.rcs.borrow().iter().enumerate() {
            let llvm_inner_type = get_llvm_type(globals, self, inner_type);

            let release_func = globals.module.add_function(
                &format!("rc_release_{}", i),
                void_type.fn_type(
                    &[llvm_inner_type.ptr_type(AddressSpace::default()).into()],
                    false,
                ),
                Some(Linkage::Internal),
            );

            let release_entry = globals
                .context
                .append_basic_block(release_func, "release_entry");

            builder.position_at_end(release_entry);
            let arg = release_func.get_nth_param(0).unwrap();

            let arg = builder
                .build_load(llvm_inner_type, arg.into_pointer_value(), "arg")
                .unwrap();

            gen_rc_op(
                RcOp::Release,
                &builder,
                self,
                globals,
                release_func,
                inner_type,
                arg,
            );

            builder.build_return(None).unwrap();

            rc_builtin.define(
                globals.context,
                globals.target,
                &globals.tal,
                Some(release_func),
            );

            rc_progress.update(1);
        }
        rc_progress.finish();

        // cow arrays
        let mut cow_progress = cow_progress.start_session(Some(self.cow_arrays.borrow().len() + 1));
        for (i, (inner_type, cow_array_builtin)) in self.cow_arrays.borrow().iter().enumerate() {
            let llvm_inner_type = get_llvm_type(globals, self, inner_type);

            let retain_func = globals.module.add_function(
                &format!("cow_array_retain_{}", i),
                void_type.fn_type(
                    &[llvm_inner_type.ptr_type(AddressSpace::default()).into()],
                    false,
                ),
                Some(Linkage::Internal),
            );

            let retain_entry = globals
                .context
                .append_basic_block(retain_func, "retain_entry");

            builder.position_at_end(retain_entry);
            let arg = retain_func.get_nth_param(0).unwrap();

            let arg = builder
                .build_load(llvm_inner_type, arg.into_pointer_value(), "arg")
                .unwrap();

            gen_rc_op(
                RcOp::Retain,
                &builder,
                self,
                globals,
                retain_func,
                inner_type,
                arg,
            );

            builder.build_return(None).unwrap();

            let release_func = globals.module.add_function(
                &format!("cow_array_release_{}", i),
                void_type.fn_type(
                    &[llvm_inner_type.ptr_type(AddressSpace::default()).into()],
                    false,
                ),
                Some(Linkage::Internal),
            );

            let release_entry = globals
                .context
                .append_basic_block(release_func, "release_entry");

            builder.position_at_end(release_entry);
            let arg = release_func.get_nth_param(0).unwrap();

            let arg = builder
                .build_load(llvm_inner_type, arg.into_pointer_value(), "arg")
                .unwrap();

            gen_rc_op(
                RcOp::Release,
                &builder,
                self,
                globals,
                release_func,
                inner_type,
                arg,
            );

            builder.build_return(None).unwrap();

            // TODO: dont generate retains/releases that aren't used
            if is_zero_sized(globals, inner_type) {
                cow_array_builtin.define(globals.context, globals.target, &globals.tal, None, None);
            } else {
                cow_array_builtin.define(
                    globals.context,
                    globals.target,
                    &globals.tal,
                    Some(retain_func),
                    Some(release_func),
                );
            }

            cow_progress.update(1);
        }

        self.cow_array_io
            .define(globals.context, globals.target, &globals.tal);
        cow_progress.update(1);

        cow_progress.finish();
    }
}

fn ceil_div(num: i64, den: i64) -> i64 {
    // When num == 0, we need to round towards +infinity
    (num - 1).div_euclid(den) + 1
}

// Fiddly arithmetic may be the hardest part of programming.
// There's no harm in a simple correctness check.
#[test]
fn ceil_div_test() {
    assert_eq!(ceil_div(0, 3), 0);
    assert_eq!(ceil_div(1, 3), 1);
    assert_eq!(ceil_div(2, 3), 1);
    assert_eq!(ceil_div(3, 3), 1);
    assert_eq!(ceil_div(4, 3), 2);
    assert_eq!(ceil_div(9, 3), 3);
}

// This function MUST NOT depend on any mode annotations.
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
        low::Type::Tuple(item_types) => TupleType::new(globals, instances, item_types).into_raw(),
        low::Type::Variants(variants) => VariantsType::new(globals, instances, variants).into_raw(),
        low::Type::Custom(type_id) => globals.custom_types[type_id].type_.into(),
        low::Type::Array(item_type) => instances
            .get_cow_array(globals, item_type)
            .array_type()
            .into(),
        low::Type::HoleArray(item_type) => instances
            .get_cow_array(globals, item_type)
            .hole_array_type()
            .into(),
        low::Type::Boxed(type_) => instances
            .get_rc(globals, type_)
            .rc_type
            .ptr_type(AddressSpace::default())
            .into(),
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
    scheme: &ModeScheme,
    arg: BasicValueEnum<'a>,
) {
    match scheme {
        ModeScheme::Bool => {}
        ModeScheme::Num(_) => {}
        ModeScheme::Array(mode, item_scheme) => match op {
            RcOp::Retain => {
                let retain_func = instances
                    .get_cow_array(globals, &item_scheme.as_type())
                    .retain_array();
                builder
                    .build_call(retain_func, &[arg.into()], "retain_cow_array")
                    .unwrap();
            }
            RcOp::Release => {
                if *mode == Mode::Owned {
                    let release_func = instances
                        .get_cow_array(globals, &item_scheme.as_type())
                        .release_array();
                    builder
                        .build_call(release_func, &[arg.into()], "release_cow_array")
                        .unwrap();
                }
            }
        },
        ModeScheme::HoleArray(mode, item_type) => match op {
            RcOp::Retain => {
                let retain_func = instances.get_cow_array(globals, item_type).retain_hole();
                builder
                    .build_call(retain_func, &[arg.into()], "retain_cow_hole_array")
                    .unwrap();
            }
            RcOp::Release => {
                if *mode == Mode::Owned {
                    let release_func = instances.get_cow_array(globals, item_type).release_hole();
                    builder
                        .build_call(release_func, &[arg.into()], "release_cow_hole_array")
                        .unwrap();
                }
            }
        },
        ModeScheme::Tuple(item_types) => {
            let arg = TupleValue::from_raw(arg);
            for i in 0..item_types.len() {
                let current_item = arg.build_get_field(builder, i);
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
        ModeScheme::Variants(variant_types) => {
            let type_ = VariantsType::new(globals, instances, &variant_types);
            let arg = VariantsValue::from_raw(arg);
            arg.build_switch(builder, globals, func, &type_, |id| {
                let content = arg.build_get_content(builder, globals, instances, &type_, id);
                gen_rc_op(
                    op,
                    builder,
                    instances,
                    globals,
                    func,
                    &variant_types[id],
                    content,
                );
            });
        }
        ModeScheme::Boxed(mode, inner_type) => match op {
            RcOp::Retain => {
                let retain_func = instances.get_rc(globals, inner_type).retain;
                builder
                    .build_call(retain_func, &[arg.into()], "retain_boxed")
                    .unwrap();
            }
            RcOp::Release => {
                if *mode == Mode::Owned {
                    let release_func = instances.get_rc(globals, inner_type).release;
                    builder
                        .build_call(release_func, &[arg.into()], "release_boxed")
                        .unwrap();
                }
            }
        },
        ModeScheme::Custom(type_id) => match op {
            RcOp::Retain => {
                let retain_func = globals.custom_types[type_id].retain;
                builder
                    .build_call(retain_func, &[arg.into()], "retain_boxed")
                    .unwrap();
            }
            RcOp::Release => {
                let release_func = globals.custom_types[type_id].release;
                builder
                    .build_call(release_func, &[arg.into()], "release_boxed")
                    .unwrap();
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

    entry_builder.build_alloca(ty, name).unwrap()
}

#[derive(Clone, Debug)]
struct TailCallTarget<'a> {
    arg_ty: BasicTypeEnum<'a>,
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
    let is_nonzero = builder
        .build_int_compare(
            IntPredicate::NE,
            val,
            val.get_type().const_int(0 as u64, false),
            "is_nonzero",
        )
        .unwrap();

    builder
        .build_call(
            globals.tal.expect_i1,
            &[
                is_nonzero.into(),
                globals
                    .context
                    .bool_type()
                    .const_int(1 as u64, false)
                    .into(),
            ],
            "expect_nonzero",
        )
        .unwrap();

    let curr_block = builder.get_insert_block().unwrap();

    let panic_if_zero = globals
        .context
        .insert_basic_block_after(curr_block, "panic_if_zero");

    let continue_if_nonzero = globals
        .context
        .insert_basic_block_after(curr_block, "continue_if_nonzero");

    builder
        .build_conditional_branch(is_nonzero, continue_if_nonzero, panic_if_zero)
        .unwrap();

    builder.position_at_end(panic_if_zero);

    let panic_message = builder
        .build_global_string_ptr("panicked due to division by zero\n", "panic_message")
        .unwrap();

    builder
        .build_call(
            globals.tal.print_error,
            &[panic_message.as_pointer_value().into()],
            "print_error__call",
        )
        .unwrap();

    builder
        .build_call(
            globals.tal.exit,
            &[globals.context.i32_type().const_int(1 as u64, false).into()],
            "exit_call",
        )
        .unwrap();

    builder.build_unreachable().unwrap();

    builder.position_at_end(continue_if_nonzero);
}

fn build_binop_int_args<'a>(
    builder: &Builder<'a>,
    args: BasicValueEnum<'a>,
) -> (IntValue<'a>, IntValue<'a>) {
    let args_struct = args.into_struct_value();
    debug_assert_eq!(args_struct.get_type().count_fields(), 2);
    let lhs = builder
        .build_extract_value(args_struct, 0, "binop_lhs")
        .unwrap()
        .into_int_value();
    let rhs = builder
        .build_extract_value(args_struct, 1, "binop_rhs")
        .unwrap()
        .into_int_value();
    (lhs, rhs)
}

fn build_binop_float_args<'a>(
    builder: &Builder<'a>,
    args: BasicValueEnum<'a>,
) -> (FloatValue<'a>, FloatValue<'a>) {
    let args_struct = args.into_struct_value();
    debug_assert_eq!(args_struct.get_type().count_fields(), 2);
    let lhs = builder
        .build_extract_value(args_struct, 0, "binop_lhs")
        .unwrap()
        .into_float_value();
    let rhs = builder
        .build_extract_value(args_struct, 1, "binop_rhs")
        .unwrap()
        .into_float_value();
    (lhs, rhs)
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
        E::Local(local_id) => locals[local_id].into(),
        E::Call(func_id, local_id) => builder
            .build_call(funcs[func_id], &[locals[local_id].into()], "result")
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap(),
        E::TailCall(tail_id, local_id) => {
            builder
                .build_store(tail_targets[tail_id].arg_var, locals[local_id])
                .unwrap();
            builder
                .build_unconditional_branch(tail_targets[tail_id].block)
                .unwrap();
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
            builder
                .build_conditional_branch(cond, then_block, else_block)
                .unwrap();

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
            builder.build_unconditional_branch(next_block).unwrap();

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
            builder.build_unconditional_branch(next_block).unwrap();

            builder.position_at_end(next_block);
            let phi = builder.build_phi(result_then.get_type(), "result").unwrap();
            phi.add_incoming(&[
                (&result_then, last_then_expr_block),
                (&result_else, last_else_expr_block),
            ]);
            phi.as_basic_value()
        }
        E::LetMany(bindings, local_id) => {
            let count = locals.count();
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
            locals.truncate(count);
            body
        }
        E::Unreachable(type_) => {
            builder.build_unreachable().unwrap();
            let unreachable_block = context.append_basic_block(func, "after_unreachable");
            builder.position_at_end(unreachable_block);
            get_undef(&get_llvm_type(globals, instances, type_))
        }
        E::Tuple(fields) => {
            let type_ = TupleType::from_raw(globals, fields.iter().map(|id| locals[id].get_type()));
            type_
                .build_value(builder, fields.iter().map(|id| locals[id]))
                .into_raw()
        }
        E::TupleField(local_id, elem) => {
            TupleValue::from_raw(locals[local_id]).build_get_field(builder, *elem)
        }
        E::WrapVariant(variants, variant_id, local_id) => {
            let variant_type = VariantsType::new(globals, instances, &variants);
            let discrim = variant_type.discrim_const(*variant_id);
            let byte_array = variant_type.build_bytes(builder, globals, locals[local_id]);
            variant_type
                .build_value(builder, discrim, byte_array)
                .into_raw()
        }
        E::UnwrapVariant(variants, variant_id, local_id) => {
            let variant_type = VariantsType::new(globals, instances, variants);
            let variant_value = VariantsValue::from_raw(locals[local_id]);
            variant_value.build_get_content(builder, globals, instances, &variant_type, *variant_id)
        }
        E::WrapCustom(type_id, local_id) => {
            let mut custom_type_val = globals.custom_types[type_id].type_.get_undef();
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
            let discrim = VariantsValue::from_raw(locals[local_id]).build_get_discrim(builder);

            let expected_value = discrim
                .get_type()
                .const_int(variant_id.0.try_into().unwrap(), false);

            builder
                .build_int_compare(IntPredicate::EQ, expected_value, discrim, "check_variant")
                .unwrap()
                .into()
        }
        E::WrapBoxed(local_id, inner_type) => {
            let builtin = instances.get_rc(globals, inner_type);
            builder
                .build_call(builtin.new, &[locals[local_id].into()], "new_box")
                .unwrap()
                .try_as_basic_value()
                .left()
                .unwrap()
        }
        E::UnwrapBoxed(local_id, inner_type) => {
            let builtin = instances.get_rc(globals, inner_type);
            let ptr = builder
                .build_call(builtin.get, &[locals[local_id].into()], "unbox")
                .unwrap()
                .try_as_basic_value()
                .left()
                .unwrap()
                .into_pointer_value();
            builder
                .build_load(
                    get_llvm_type(globals, instances, inner_type),
                    ptr,
                    "content",
                )
                .unwrap()
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
        E::Intrinsic(intr, local_id) => match intr {
            Intrinsic::Not => builder
                .build_not(locals[local_id].into_int_value(), "not_expr")
                .unwrap()
                .into(),
            Intrinsic::AddByte => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder.build_int_add(lhs, rhs, "add_byte").unwrap().into()
            }
            Intrinsic::AddInt => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder.build_int_add(lhs, rhs, "add_int").unwrap().into()
            }
            Intrinsic::AddFloat => {
                let (lhs, rhs) = build_binop_float_args(builder, locals[local_id]);
                builder
                    .build_float_add(lhs, rhs, "add_float")
                    .unwrap()
                    .into()
            }
            Intrinsic::SubByte => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder.build_int_sub(lhs, rhs, "sub_byte").unwrap().into()
            }
            Intrinsic::SubInt => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder.build_int_sub(lhs, rhs, "sub_int").unwrap().into()
            }
            Intrinsic::SubFloat => {
                let (lhs, rhs) = build_binop_float_args(builder, locals[local_id]);
                builder
                    .build_float_sub(lhs, rhs, "sub_float")
                    .unwrap()
                    .into()
            }
            Intrinsic::MulByte => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder.build_int_mul(lhs, rhs, "mul_byte").unwrap().into()
            }
            Intrinsic::MulInt => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder.build_int_mul(lhs, rhs, "mul_int").unwrap().into()
            }
            Intrinsic::MulFloat => {
                let (lhs, rhs) = build_binop_float_args(builder, locals[local_id]);
                builder
                    .build_float_mul(lhs, rhs, "mul_float")
                    .unwrap()
                    .into()
            }
            Intrinsic::DivByte => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                build_check_divisor_nonzero(globals, builder, rhs);
                builder
                    .build_int_unsigned_div(lhs, rhs, "div_byte")
                    .unwrap()
                    .into()
            }
            Intrinsic::DivInt => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                build_check_divisor_nonzero(globals, builder, rhs);
                builder
                    .build_int_signed_div(lhs, rhs, "div_int")
                    .unwrap()
                    .into()
            }
            Intrinsic::DivFloat => {
                let (lhs, rhs) = build_binop_float_args(builder, locals[local_id]);
                builder
                    .build_float_div(lhs, rhs, "div_float")
                    .unwrap()
                    .into()
            }
            Intrinsic::LtByte => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder
                    .build_int_compare(IntPredicate::ULT, lhs, rhs, "lt_byte")
                    .unwrap()
                    .into()
            }
            Intrinsic::LtInt => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder
                    .build_int_compare(IntPredicate::SLT, lhs, rhs, "lt_int")
                    .unwrap()
                    .into()
            }
            Intrinsic::LtFloat => {
                let (lhs, rhs) = build_binop_float_args(builder, locals[local_id]);
                builder
                    .build_float_compare(FloatPredicate::OLT, lhs, rhs, "lt_float")
                    .unwrap()
                    .into()
            }
            Intrinsic::LteByte => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder
                    .build_int_compare(IntPredicate::ULE, lhs, rhs, "lte_byte")
                    .unwrap()
                    .into()
            }
            Intrinsic::LteInt => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder
                    .build_int_compare(IntPredicate::SLE, lhs, rhs, "lte_int")
                    .unwrap()
                    .into()
            }
            Intrinsic::LteFloat => {
                let (lhs, rhs) = build_binop_float_args(builder, locals[local_id]);
                builder
                    .build_float_compare(FloatPredicate::OLE, lhs, rhs, "lte_float")
                    .unwrap()
                    .into()
            }
            Intrinsic::GtByte => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder
                    .build_int_compare(IntPredicate::UGT, lhs, rhs, "gt_byte")
                    .unwrap()
                    .into()
            }
            Intrinsic::GtInt => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder
                    .build_int_compare(IntPredicate::SGT, lhs, rhs, "gt_int")
                    .unwrap()
                    .into()
            }
            Intrinsic::GtFloat => {
                let (lhs, rhs) = build_binop_float_args(builder, locals[local_id]);
                builder
                    .build_float_compare(FloatPredicate::OGT, lhs, rhs, "gt_float")
                    .unwrap()
                    .into()
            }
            Intrinsic::GteByte => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder
                    .build_int_compare(IntPredicate::UGE, lhs, rhs, "gte_byte")
                    .unwrap()
                    .into()
            }
            Intrinsic::GteInt => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder
                    .build_int_compare(IntPredicate::SGE, lhs, rhs, "gte_int")
                    .unwrap()
                    .into()
            }
            Intrinsic::GteFloat => {
                let (lhs, rhs) = build_binop_float_args(builder, locals[local_id]);
                builder
                    .build_float_compare(FloatPredicate::OGE, lhs, rhs, "gte_float")
                    .unwrap()
                    .into()
            }
            Intrinsic::EqByte => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder
                    .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq_byte")
                    .unwrap()
                    .into()
            }
            Intrinsic::EqInt => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder
                    .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq_int")
                    .unwrap()
                    .into()
            }
            Intrinsic::EqFloat => {
                let (lhs, rhs) = build_binop_float_args(builder, locals[local_id]);
                builder
                    .build_float_compare(FloatPredicate::OEQ, lhs, rhs, "eq_float")
                    .unwrap()
                    .into()
            }
            Intrinsic::NegByte => builder
                .build_int_neg(locals[local_id].into_int_value(), "neg_byte")
                .unwrap()
                .into(),
            Intrinsic::NegInt => builder
                .build_int_neg(locals[local_id].into_int_value(), "neg_int")
                .unwrap()
                .into(),
            Intrinsic::NegFloat => builder
                .build_float_neg(locals[local_id].into_float_value(), "neg_float")
                .unwrap()
                .into(),
            Intrinsic::ByteToInt => builder
                .build_int_z_extend(
                    locals[local_id].into_int_value(),
                    context.i64_type(),
                    "byte_to_int",
                )
                .unwrap()
                .into(),
            Intrinsic::ByteToIntSigned => builder
                .build_int_s_extend(
                    locals[local_id].into_int_value(),
                    context.i64_type(),
                    "byte_to_int_signed",
                )
                .unwrap()
                .into(),
            Intrinsic::IntToByte => builder
                .build_int_truncate(
                    locals[local_id].into_int_value(),
                    context.i8_type(),
                    "int_to_byte",
                )
                .unwrap()
                .into(),
            Intrinsic::IntShiftLeft => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                // Shifting an i64 by >= 64 bits produces a poison value, so we mask the rhs by 64 -
                // 1 (which is the same as taking the rhs mod 64). This appears to be what rustc
                // does.
                builder
                    .build_left_shift(
                        lhs,
                        builder
                            .build_and(
                                rhs,
                                context.i64_type().const_int(64 - 1, false),
                                "int_shift_left_rhs_mask",
                            )
                            .unwrap(),
                        "int_shift_left",
                    )
                    .unwrap()
                    .into()
            }
            Intrinsic::IntShiftRight => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                // Shifting an i64 by >= 64 bits produces a poison value, so we mask the rhs by 64 -
                // 1 (which is the same as taking the rhs mod 64). This appears to be what rustc
                // does.
                builder
                    .build_right_shift(
                        lhs,
                        builder
                            .build_and(
                                rhs,
                                context.i64_type().const_int(64 - 1, false),
                                "int_shift_right_rhs_mask",
                            )
                            .unwrap(),
                        false, // this is a logical shift
                        "int_shift_right",
                    )
                    .unwrap()
                    .into()
            }
            Intrinsic::IntBitAnd => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder.build_and(lhs, rhs, "int_bit_and").unwrap().into()
            }
            Intrinsic::IntBitOr => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder.build_or(lhs, rhs, "int_bit_or").unwrap().into()
            }
            Intrinsic::IntBitXor => {
                let (lhs, rhs) = build_binop_int_args(builder, locals[local_id]);
                builder.build_xor(lhs, rhs, "int_bit_xor").unwrap().into()
            }
            Intrinsic::IntCtpop => {
                let val = locals[local_id].into_int_value();
                builder
                    .build_call(globals.tal.ctpop_i64, &[val.into()], "int_ctpop")
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }
            Intrinsic::IntCtlz => {
                let val = locals[local_id].into_int_value();
                let zero_is_poison = globals.context.bool_type().const_int(0, false);
                builder
                    .build_call(
                        globals.tal.ctlz_i64,
                        &[val.into(), zero_is_poison.into()],
                        "int_ctlz",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }
            Intrinsic::IntCttz => {
                let val = locals[local_id].into_int_value();
                let zero_is_poison = globals.context.bool_type().const_int(0, false);
                builder
                    .build_call(
                        globals.tal.cttz_i64,
                        &[val.into(), zero_is_poison.into()],
                        "int_cttz",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }
        },
        E::ArrayOp(item_type, array_op) => {
            let builtin = instances.get_cow_array(globals, item_type);
            match array_op {
                low::ArrayOp::New(_) => builder
                    .build_call(builtin.new(), &[], "cow_array_new")
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap(),
                low::ArrayOp::Get(array_id, index_id) => builder
                    .build_call(
                        builtin.get(),
                        &[locals[array_id].into(), locals[index_id].into()],
                        "cow_array_get",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap(),
                low::ArrayOp::Extract(array_id, index_id) => builder
                    .build_call(
                        builtin.extract(),
                        &[locals[array_id].into(), locals[index_id].into()],
                        "cow_array_extract",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap(),
                low::ArrayOp::Len(array_id) => builder
                    .build_call(builtin.len(), &[locals[array_id].into()], "cow_array_len")
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap(),
                low::ArrayOp::Push(array_id, item_id) => builder
                    .build_call(
                        builtin.push(),
                        &[locals[array_id].into(), locals[item_id].into()],
                        "cow_array_push",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap(),
                low::ArrayOp::Pop(array_id) => builder
                    .build_call(builtin.pop(), &[locals[array_id].into()], "cow_array_pop")
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap(),
                low::ArrayOp::Replace(array_id, item_id) => builder
                    .build_call(
                        builtin.replace(),
                        &[locals[array_id].into(), locals[item_id].into()],
                        "cow_array_replace",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap(),
                low::ArrayOp::Reserve(array_id, capacity_id) => builder
                    .build_call(
                        builtin.reserve(),
                        &[locals[array_id].into(), locals[capacity_id].into()],
                        "cow_array_reserve",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap(),
            }
        }
        E::IoOp(io_op) => {
            let builtin_io = instances.cow_array_io;
            match io_op {
                low::IoOp::Input => builder
                    .build_call(builtin_io.input, &[], "cow_array_input")
                    .unwrap()
                    .try_as_basic_value()
                    .left()
                    .unwrap(),
                low::IoOp::Output(array_id) => {
                    builder
                        .build_call(
                            builtin_io.output,
                            &[locals[array_id].into()],
                            "cow_array_output",
                        )
                        .unwrap();

                    context.struct_type(&[], false).get_undef().into()
                }
            }
        }
        E::Panic(ret_type, message_id) => {
            let builtin_io = instances.cow_array_io;
            builder
                .build_call(
                    builtin_io.output_error,
                    &[locals[message_id].into()],
                    "cow_array_panic",
                )
                .unwrap();

            builder
                .build_call(
                    globals.tal.exit,
                    &[globals.context.i32_type().const_int(1 as u64, false).into()],
                    "exit_call",
                )
                .unwrap();

            builder.build_unreachable().unwrap();
            let unreachable_block = context.append_basic_block(func, "after_panic");
            builder.position_at_end(unreachable_block);
            get_undef(&get_llvm_type(globals, instances, ret_type))
        }
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
    func_id: low::CustomFuncId,
    func: &low::FuncDef,
) {
    let builder = context.create_builder();
    let entry = context.append_basic_block(func_decl, "entry");
    builder.position_at_end(entry);

    let i64_t = context.i64_type();

    let (start_clock_nanos, start_retain_count, start_release_count) =
        if let Some(prof_id) = func.profile_point {
            let start_clock_nanos = builder
                .build_call(globals.tal.prof_clock_nanos, &[], "start_clock_nanos")
                .unwrap()
                .try_as_basic_value()
                .left()
                .unwrap()
                .into_int_value();

            let counters = &globals.profile_points[prof_id].counters[&func_id];
            let start_retain_count = if counters.total_retain_count.is_some() {
                let start_retain_count = builder
                    .build_call(
                        globals.tal.prof_rc.unwrap().get_retain_count,
                        &[],
                        "start_retain_count",
                    )
                    .unwrap();
                Some(start_retain_count)
            } else {
                None
            };
            let start_release_count = if counters.total_release_count.is_some() {
                let start_release_count = builder
                    .build_call(
                        globals.tal.prof_rc.unwrap().get_release_count,
                        &[],
                        "start_release_count",
                    )
                    .unwrap();
                Some(start_release_count)
            } else {
                None
            };

            (
                Some(start_clock_nanos),
                start_retain_count,
                start_release_count,
            )
        } else {
            (None, None, None)
        };

    // Declare tail call targets, but don't populate their bodies yet. Tail functions are
    // implemented via blocks which may be jumped to, and their arguments are implemented as mutable
    // variables.
    let tail_targets = func.tail_funcs.map_refs(|tail_id, tail_func| {
        let arg_ty = get_llvm_type(globals, instances, &tail_func.arg_type);
        let arg_var = builder
            .build_alloca(arg_ty, &format!("tail_{}_arg", tail_id.0))
            .unwrap();

        let block = context.append_basic_block(func_decl, &format!("tail_{}", tail_id.0));

        TailCallTarget {
            arg_ty,
            arg_var,
            block,
        }
    });

    let gen_prof_epilogue = || {
        if let Some(prof_id) = func.profile_point {
            let end_clock_nanos = builder
                .build_call(globals.tal.prof_clock_nanos, &[], "end_clock_nanos")
                .unwrap()
                .try_as_basic_value()
                .left()
                .unwrap()
                .into_int_value();

            let diff_clock_nanos = builder
                .build_int_sub(
                    end_clock_nanos,
                    start_clock_nanos.unwrap(),
                    "diff_clock_nanos",
                )
                .unwrap();

            let counters = &globals.profile_points[prof_id].counters[&func_id];

            let old_clock_nanos = builder
                .build_load(
                    i64_t,
                    counters.total_clock_nanos.as_pointer_value(),
                    "old_clock_nanos",
                )
                .unwrap()
                .into_int_value();

            let new_clock_nanos = builder
                .build_int_add(old_clock_nanos, diff_clock_nanos, "new_clock_nanos")
                .unwrap();

            builder
                .build_store(
                    counters.total_clock_nanos.as_pointer_value(),
                    new_clock_nanos,
                )
                .unwrap();

            let gen_rc_count_update =
                |start_rc_count: Option<CallSiteValue<'_>>,
                 total_rc_count: Option<GlobalValue<'_>>,
                 tal_fn: fn(ProfileRc) -> FunctionValue<'_>| match (
                    start_rc_count,
                    total_rc_count,
                ) {
                    (Some(start_rc_count), Some(total_rc_count)) => {
                        let end_rc_count = builder
                            .build_call(tal_fn(globals.tal.prof_rc.unwrap()), &[], "end_rc_count")
                            .unwrap();

                        let diff_rc_count = builder
                            .build_int_sub(
                                end_rc_count
                                    .try_as_basic_value()
                                    .left()
                                    .unwrap()
                                    .into_int_value(),
                                start_rc_count
                                    .try_as_basic_value()
                                    .left()
                                    .unwrap()
                                    .into_int_value(),
                                "diff_rc_count",
                            )
                            .unwrap();

                        let old_rc_count = builder
                            .build_load(i64_t, total_rc_count.as_pointer_value(), "old_rc_count")
                            .unwrap()
                            .into_int_value();

                        let new_rc_count = builder
                            .build_int_add(old_rc_count, diff_rc_count, "new_rc_count")
                            .unwrap();

                        builder
                            .build_store(total_rc_count.as_pointer_value(), new_rc_count)
                            .unwrap();
                    }
                    (None, None) => {}
                    _ => unreachable!(),
                };

            gen_rc_count_update(start_retain_count, counters.total_retain_count, |prof_rc| {
                prof_rc.get_retain_count
            });
            gen_rc_count_update(
                start_release_count,
                counters.total_release_count,
                |prof_rc| prof_rc.get_release_count,
            );

            let old_calls = builder
                .build_load(i64_t, counters.total_calls.as_pointer_value(), "old_calls")
                .unwrap()
                .into_int_value();

            let new_calls = builder
                .build_int_add(
                    old_calls,
                    context.i64_type().const_int(1, false),
                    "new_calls",
                )
                .unwrap();

            builder
                .build_store(counters.total_calls.as_pointer_value(), new_calls)
                .unwrap();
        }
    };

    // Generate main body
    {
        let mut locals = IdVec::from_vec(vec![func_decl.get_nth_param(0).unwrap()]);
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
        gen_prof_epilogue();
        builder.build_return(Some(&ret_value)).unwrap();
    }

    // Generate tail function bodies
    for (tail_id, tail_target) in &tail_targets {
        builder.position_at_end(tail_target.block);
        let tail_arg_val = builder
            .build_load(tail_target.arg_ty, tail_target.arg_var, "tail_arg_val")
            .unwrap();
        let mut locals = IdVec::from_vec(vec![tail_arg_val]);
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
        gen_prof_epilogue();
        builder.build_return(Some(&ret_value)).unwrap();
    }
}

fn get_target_machine(
    target: cli::LlvmConfig,
    opt_level: OptimizationLevel,
) -> Result<TargetMachine> {
    Target::initialize_all(&InitializationConfig::default());

    let (target_triple, target_cpu, target_features) = match target {
        cli::LlvmConfig::Native => (
            TargetMachine::get_default_triple(),
            TargetMachine::get_host_cpu_name().to_string(),
            TargetMachine::get_host_cpu_features().to_string(),
        ),
        cli::LlvmConfig::Wasm => (
            TargetTriple::create("wasm32-unknown-unknown"),
            "".to_owned(),
            "".to_owned(),
        ),
    };

    let llvm_target =
        Target::from_triple(&target_triple).map_err(Error::TargetTripleNotSupported)?;

    // RelocMode and CodeModel can affect the options we need to pass clang in run_cc
    llvm_target
        .create_target_machine(
            &target_triple,
            &target_cpu,
            &target_features,
            opt_level,
            RelocMode::PIC,
            // https://stackoverflow.com/questions/40493448/what-does-the-codemodel-in-clang-llvm-refer-to
            CodeModel::Small,
        )
        .ok_or_else(|| Error::CouldNotCreateTargetMachine)
}

fn add_size_deps(type_: &low::Type, deps: &mut BTreeSet<low::CustomTypeId>) {
    match type_ {
        low::Type::Bool | low::Type::Num(_) => {}

        low::Type::Array(_) | low::Type::HoleArray(_) | low::Type::Boxed(_) => {}

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
    let sccs: Sccs<usize, _> = id_graph_sccs::find_components(typedefs.count(), |id| {
        let mut deps = BTreeSet::new();
        add_size_deps(&typedefs[id], &mut deps);
        deps
    });

    sccs.into_iter()
        .map(|(_, scc)| {
            debug_assert_eq!(scc.kind, SccKind::Acyclic);
            scc.nodes[0]
        })
        .collect()
}

// We use this function both when computing initial zero-sizedness flags, and when processing types
// during the main phase of code generation.  These cases use different underlying data structures
// to store the zero-sizedness of custom types (in particular, during initial flag computation,
// flags not yet computed are `None`), so we abstract over the particular data structure with a
// closure.
fn is_zero_sized_with(
    type_: &low::Type,
    custom_is_zero_sized: &impl Fn(low::CustomTypeId) -> IsZeroSized,
) -> bool {
    match type_ {
        low::Type::Bool
        | low::Type::Num(_)
        | low::Type::Array(_)
        | low::Type::HoleArray(_)
        | low::Type::Boxed(_) => false,
        low::Type::Tuple(items) => TupleType::is_zero_sized_with(items, custom_is_zero_sized),
        low::Type::Variants(variants) => {
            VariantsType::is_zero_sized_with(variants, custom_is_zero_sized)
        }
        &low::Type::Custom(custom) => custom_is_zero_sized(custom) == IsZeroSized::ZeroSized,
    }
}

fn is_zero_sized(globals: &Globals, type_: &low::Type) -> bool {
    is_zero_sized_with(type_, &|custom| globals.custom_types_zero_sized[custom])
}

fn find_zero_sized(
    custom_types: &IdVec<low::CustomTypeId, low::Type>,
    type_dep_order: &[low::CustomTypeId],
) -> IdVec<low::CustomTypeId, IsZeroSized> {
    // We only pass `type_dep_order` as an argument because the caller will need to use it again
    // later.  Otherwise we would compute it inside this function; it is fully determined by
    // `custom_types`.
    debug_assert_eq!(type_dep_order, &custom_type_dep_order(custom_types) as &[_]);

    let mut custom_types_zero_sized = IdVec::from_vec(vec![None; custom_types.len()]);

    for &type_id in type_dep_order {
        debug_assert!(custom_types_zero_sized[type_id].is_none());

        let zero_sized = is_zero_sized_with(&custom_types[type_id], &|other| {
            custom_types_zero_sized[other].expect(
                "the zero-sizedness of custom types should be determined in dependency order",
            )
        });

        custom_types_zero_sized[type_id] = Some(if zero_sized {
            IsZeroSized::ZeroSized
        } else {
            IsZeroSized::NonZeroSized
        });
    }

    custom_types_zero_sized.map(|_, zero_sized| zero_sized.unwrap())
}

fn declare_customs<'a>(
    context: &'a Context,
    module: &Module<'a>,
    types: &IdVec<low::CustomTypeId, low::Type>,
) -> IdVec<low::CustomTypeId, CustomTypeDecls<'a>> {
    types.map_refs(|type_id, type_def| {
        let type_ = CustomTypeDecls::declare_type(context, type_id);
        CustomTypeDecls::declare(context, module, type_id, type_id, type_)
    })
}

fn gen_program<'a>(
    program: low::Program,
    target_machine: &TargetMachine,
    context: &'a Context,
    func_progress: impl ProgressLogger,
    rc_progress: impl ProgressLogger,
    cow_progress: impl ProgressLogger,
    type_progress: impl ProgressLogger,
) -> Module<'a> {
    let module = context.create_module("module");
    module.set_triple(&target_machine.get_triple());
    module.set_data_layout(&target_machine.get_target_data().get_data_layout());

    let profile_record_rc = program
        .profile_points
        .iter()
        .any(|(_, prof_point)| prof_point.record_rc);

    let tal = Tal::declare(
        context,
        &module,
        &target_machine.get_target_data(),
        profile_record_rc,
    );

    let custom_types = declare_customs(context, &module, &program.custom_types.types);

    let profile_points = declare_profile_points(&context, &module, &program);

    let type_dep_order = custom_type_dep_order(&program.custom_types.types);

    // TODO: we are doing unnecessary work here because `low_ast` types with the same provenance
    // have the same LLVM type.
    let custom_types_zero_sized = find_zero_sized(&program.custom_types.types, &type_dep_order);

    let globals = Globals {
        context,
        module: &module,
        target: &target_machine.get_target_data(),
        tal,
        custom_types_zero_sized,
        custom_types,
        profile_points,
    };

    let instances = Instances::new(&globals);

    for type_id in type_dep_order {
        let type_decls = &globals.custom_types[type_id];
        type_decls.define_type(&globals, &instances, &program.custom_types.types[type_id]);

        debug_assert!(type_decls.type_.is_sized());

        // Note: the following assertion is checking an *equality of booleans* to check that types
        // have zero size iff they are marked as having zero size.  We're not asserting that all
        // types have zero size!
        debug_assert_eq!(
            globals.target.get_abi_size(&type_decls.type_) == 0,
            globals.custom_types_zero_sized[type_id] == IsZeroSized::ZeroSized
        );
    }

    let mut func_progress = func_progress.start_session(Some(program.funcs.len()));

    let funcs = program.funcs.map_refs(|func_id, func_def| {
        let return_type = get_llvm_type(&globals, &instances, &func_def.ret_type);
        let arg_type = get_llvm_type(&globals, &instances, &func_def.arg_type);

        module.add_function(
            &format!("func_{}", func_id.0),
            return_type.fn_type(&[arg_type.into()], false),
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
            func_id,
            &program.funcs[func_id],
        );
        func_progress.update(1);
    }

    func_progress.finish();

    instances.define(&globals, rc_progress, cow_progress);

    let mut type_progress = type_progress.start_session(Some(program.custom_types.types.len()));
    for (type_id, type_decls) in &globals.custom_types {
        type_decls.define(&globals, &instances, &program.custom_types.types[type_id]);
        type_progress.update(1);
    }
    type_progress.finish();

    let i32_type = context.i32_type();
    let unit_type = context.struct_type(&[], false);
    let i8_ptr_ptr_type = context
        .i8_type()
        .ptr_type(AddressSpace::default())
        .ptr_type(AddressSpace::default());
    let main = module.add_function(
        "main",
        i32_type.fn_type(&[i32_type.into(), i8_ptr_ptr_type.into()], false),
        Some(Linkage::External),
    );

    let builder = context.create_builder();
    let main_block = context.append_basic_block(main, "main_block");
    builder.position_at_end(main_block);

    builder
        .build_call(
            funcs[program.main],
            &[unit_type.get_undef().into()],
            "main_result",
        )
        .unwrap();

    if program.profile_points.len() > 0 {
        let prof_report_fn = define_prof_report_fn(
            context,
            &target_machine.get_target_data(),
            &module,
            &tal,
            &program.profile_points,
            &globals.profile_points,
        );

        builder
            .build_call(prof_report_fn, &[], "prof_report_call")
            .unwrap();
    }

    builder
        .build_return(Some(&i32_type.const_int(0, false)))
        .unwrap();

    return module;
}

fn check_valid_file_path(path: &Path) -> Result<()> {
    if path.is_dir() {
        return Err(Error::GivenDirExpectedFile(path.to_owned()));
    }

    match path.parent() {
        None => return Err(Error::GivenDirExpectedFile(path.to_owned())),
        Some(parent) => {
            if !parent.exists() {
                return Err(Error::DirectoryDoesNotExist(parent.to_owned()));
            }
        }
    }

    Ok(())
}

fn check_valid_dir_path(path: &Path) -> Result<()> {
    if path.is_file() {
        return Err(Error::GivenFileExpectedDir(path.to_owned()));
    }

    match path.parent() {
        None => {}
        Some(parent) => {
            if !parent.exists() {
                return Err(Error::DirectoryDoesNotExist(parent.to_owned()));
            }
        }
    }

    Ok(())
}

fn run_cc(target: cli::LlvmConfig, obj_path: &Path, exe_path: &Path) -> Result<()> {
    match target {
        cli::LlvmConfig::Native => {
            check_valid_file_path(obj_path)?;
            check_valid_file_path(exe_path)?;

            // materialize files to link with
            let mut tal_file = tempfile::Builder::new()
                .suffix(".o")
                .tempfile_in("")
                .map_err(Error::CouldNotCreateTempFile)?;
            tal_file
                .write_all(tal::native::TAL_O)
                .map_err(Error::CouldNotWriteObjFile)?;

            let clang = find_default_clang().map_err(Error::CouldNotFindClang)?;
            std::process::Command::new(clang.path)
                .arg("-O3")
                .arg("-ffunction-sections")
                .arg("-fdata-sections")
                .arg("-fPIC")
                .arg("-Wl,--gc-sections")
                .arg("-o")
                .arg(exe_path)
                .arg(obj_path)
                .arg(tal_file.path())
                .status()
                .map_err(Error::ClangFailed)?;
        }
        cli::LlvmConfig::Wasm => {
            // materialize files to link with
            let mut tal_file = tempfile::Builder::new()
                .suffix(".o")
                .tempfile_in("")
                .map_err(Error::CouldNotCreateTempFile)?;
            tal_file
                .write_all(tal::wasm::TAL_O)
                .map_err(Error::CouldNotWriteObjFile)?;
            let mut malloc_file = tempfile::Builder::new()
                .suffix(".o")
                .tempfile_in("")
                .map_err(Error::CouldNotCreateTempFile)?;
            malloc_file
                .write_all(tal::wasm::MALLOC_O)
                .map_err(Error::CouldNotWriteObjFile)?;

            check_valid_dir_path(exe_path)?;
            if !exe_path.exists() {
                std::fs::create_dir(exe_path).map_err(Error::CouldNotCreateOutputDir)?;
            }

            let index_path = exe_path.join("index.html");
            let mut index_file =
                std::fs::File::create(index_path).map_err(Error::CouldNotWriteOutputFile)?;
            index_file
                .write_all(tal::wasm::INDEX_HTML)
                .map_err(Error::CouldNotWriteOutputFile)?;

            let wasm_loader_path = exe_path.join("wasm_loader.js");
            let mut wasm_loader_file =
                std::fs::File::create(wasm_loader_path).map_err(Error::CouldNotWriteOutputFile)?;
            wasm_loader_file
                .write_all(tal::wasm::WASM_LOADER_JS)
                .map_err(Error::CouldNotWriteOutputFile)?;

            let clang = find_default_clang().map_err(Error::CouldNotFindClang)?;
            std::process::Command::new(clang.path)
                .arg("-O3")
                .arg("-ffunction-sections")
                .arg("-fdata-sections")
                .arg("-fPIC")
                .arg("-Wl,--gc-sections")
                // WASM only options:
                .arg("--target=wasm32")
                .arg("-nostdlib")
                .arg("-Wl,--allow-undefined")
                /////////////////////
                .arg("-o")
                .arg(exe_path.join("a.wasm"))
                .arg(obj_path)
                .arg(tal_file.path())
                .arg(malloc_file.path())
                .status()
                .map_err(Error::ClangFailed)?;
        }
    }
    Ok(())
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
    target: cli::LlvmConfig,
    opt_level: OptimizationLevel,
    artifact_paths: ArtifactPaths,
    progress: progress_ui::ProgressMode,
) -> Result<()> {
    let target_machine = get_target_machine(target, opt_level)?;
    let context = Context::create();

    let module = gen_program(
        program,
        &target_machine,
        &context,
        progress_ui::bar(progress, "gen_program: functions"),
        progress_ui::bar(progress, "gen_program: rc boxes"),
        progress_ui::bar(progress, "gen_program: cow arrays"),
        progress_ui::bar(progress, "gen_program: custom types"),
    );

    // We output the ll file before verifying so that it can be inspected even if verification
    // fails.
    if let Some(ll_path) = artifact_paths.ll {
        module
            .print_to_file(ll_path)
            .map_err(Error::CouldNotDumpIrFromLlvm)?;
    }

    verify_llvm(&module);

    let pass_manager_builder = PassManagerBuilder::create();
    pass_manager_builder.set_optimization_level(opt_level);
    // These inliner thresholds are based on those used by rustc (at the time of this writing).
    // See https://doc.rust-lang.org/rustc/codegen-options/index.html#inline-threshold
    match opt_level {
        OptimizationLevel::None | OptimizationLevel::Less => {}
        OptimizationLevel::Default => {
            pass_manager_builder.set_inliner_with_threshold(225);
        }
        OptimizationLevel::Aggressive => {
            pass_manager_builder.set_inliner_with_threshold(275);
        }
    }

    let pass_manager = PassManager::create(());
    pass_manager_builder.populate_module_pass_manager(&pass_manager);

    let opt_progress = progress_ui::bar(progress, "llvm opt").start_session(None);
    pass_manager.run_on(&module);
    opt_progress.finish();

    if let Some(opt_ll_path) = artifact_paths.opt_ll {
        module
            .print_to_file(opt_ll_path)
            .map_err(Error::CouldNotDumpIrFromLlvm)?;
    }

    // Optimization should produce a well-formed module, but if it doesn't, we want to know about
    // it!
    verify_llvm(&module);

    let codegen_progress = progress_ui::bar(progress, "llvm codegen").start_session(None);

    if let Some(asm_path) = artifact_paths.asm {
        target_machine
            .write_to_file(&module, FileType::Assembly, &asm_path)
            .map_err(Error::LlvmCompilationFailed)?;
    }

    target_machine
        .write_to_file(&module, FileType::Object, artifact_paths.obj)
        .map_err(Error::LlvmCompilationFailed)?;

    codegen_progress.finish();

    run_cc(target, artifact_paths.obj, artifact_paths.exe)
}

pub fn run(stdio: Stdio, program: low::Program, valgrind: Option<ValgrindConfig>) -> Result<Child> {
    let target = cli::LlvmConfig::Native;
    let opt_level = cli::default_llvm_opt_level();

    let obj_path = tempfile::Builder::new()
        .suffix(".o")
        .tempfile_in("")
        .map_err(Error::CouldNotCreateTempFile)?
        .into_temp_path();

    let output_path = tempfile::Builder::new()
        .prefix(".tmp-exe-")
        .tempfile_in("")
        .map_err(Error::CouldNotCreateTempFile)?
        .into_temp_path();

    compile_to_executable(
        program,
        target,
        opt_level,
        ArtifactPaths {
            ll: None,
            opt_ll: None,
            asm: None,
            obj: &obj_path,
            exe: &output_path,
        },
        progress_ui::ProgressMode::Hidden,
    )?;

    std::mem::drop(obj_path);

    spawn_process(stdio, output_path, valgrind).map_err(Error::CouldNotSpawnChild)
}

pub fn build(program: low::Program, config: &cli::BuildConfig) -> Result<()> {
    let target = if let cli::TargetConfig::Llvm(target) = config.target {
        target
    } else {
        unreachable!("not an llvm target")
    };

    if let Some(artifact_dir) = &config.artifact_dir {
        compile_to_executable(
            program,
            target,
            config.llvm_opt_level,
            ArtifactPaths {
                ll: Some(&artifact_dir.artifact_path("ll")),
                opt_ll: Some(&artifact_dir.artifact_path("opt.ll")),
                asm: Some(&artifact_dir.artifact_path("s")),
                obj: &artifact_dir.artifact_path("o"),
                exe: &config.output_path,
            },
            config.progress,
        )
    } else {
        let obj_path = tempfile::Builder::new()
            .suffix(".o")
            .tempfile_in("")
            .map_err(Error::CouldNotCreateTempFile)?
            .into_temp_path();

        compile_to_executable(
            program,
            target,
            config.llvm_opt_level,
            ArtifactPaths {
                ll: None,
                opt_ll: None,
                asm: None,
                obj: &obj_path,
                exe: &config.output_path,
            },
            config.progress,
        )
    }
}
