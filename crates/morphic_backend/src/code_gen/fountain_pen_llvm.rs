use crate::code_gen::fountain_pen::{self, Scope as ScopeTrait};
use crate::code_gen::{gen_program, Error};
use find_tool::finders::{find_default_clang, ClangKind};
use id_collections::{id_type, IdVec};
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::module::{Linkage, Module};
use inkwell::passes::{PassManager, PassManagerBuilder};
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetData, TargetMachine,
    TargetTriple,
};
use inkwell::types::{BasicType, BasicTypeEnum, IntType};
use inkwell::values::{self, BasicValue, InstructionOpcode};
use inkwell::OptimizationLevel;
use inkwell::{AddressSpace, FloatPredicate, IntPredicate};
use morphic_common::config::{self as cfg, ArrayKind, GcKind};
use morphic_common::data::low_ast as low;
use morphic_common::progress_ui;
use morphic_common::util::progress_logger::{ProgressLogger, ProgressSession};
use std::cell::RefCell;
use std::collections::HashMap;
use std::io::Write;
use std::path::Path;
use std::rc::Rc;

mod native {
    pub const TAL_O: &'static [u8] = include_bytes!(concat!(env!("OUT_DIR"), "/native/tal.o"));
    pub const GC_A: &'static [u8] = include_bytes!(concat!(env!("OUT_DIR"), "/native/gc/libgc.a"));
}

mod wasm {
    pub const MALLOC_O: &'static [u8] = include_bytes!(concat!(env!("OUT_DIR"), "/wasm/malloc.o"));
    pub const TAL_O: &'static [u8] = include_bytes!(concat!(env!("OUT_DIR"), "/wasm/tal.o"));
    pub const INDEX_HTML: &'static [u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tal/wasm/dist/index.html"
    ));
    pub const WASM_LOADER_JS: &'static [u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tal/wasm/dist/wasm_loader.js"
    ));
}

#[derive(Clone, Copy, Debug)]
pub struct Type<'a>(BasicTypeEnum<'a>);

impl<'a> std::fmt::Display for Type<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone)]
pub struct VariantsType<'a> {
    inner: inkwell::types::StructType<'a>,
    variants: Rc<[BasicTypeEnum<'a>]>,
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

fn gen_entry_alloca<'a>(
    context: &'a inkwell::context::Context,
    builder: &Builder<'a>,
    ty: impl BasicType<'a>,
    name: &str,
) -> inkwell::values::PointerValue<'a> {
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

impl<'a> VariantsType<'a> {
    const DISCRIM_IDX: u32 = 0;
    // we use a zero sized array to enforce proper alignment on `bytes`
    const ALIGN_IDX: u32 = 1;
    const BYTES_IDX: u32 = 2;

    fn new(
        context: &'a inkwell::context::Context,
        target: &TargetData,
        variants: Vec<BasicTypeEnum<'a>>,
    ) -> Self {
        let discrim_type = if variants.len() <= 1 << 8 {
            context.i8_type()
        } else if variants.len() <= 1 << 16 {
            context.i16_type()
        } else if variants.len() <= 1 << 32 {
            context.i32_type()
        } else {
            context.i64_type()
        };

        let (max_alignment, max_size) = {
            let mut max_alignment = 1;
            let mut max_size = 0;
            for variant_type in variants.iter() {
                debug_assert!(variant_type.is_sized());
                let alignment = target.get_abi_alignment(variant_type);
                let size = target.get_abi_size(variant_type);
                max_alignment = max_alignment.max(alignment);
                max_size = max_size.max(size);
            }
            (max_alignment, max_size)
        };

        let alignment_type = match max_alignment {
            1 => context.i8_type(),
            2 => context.i16_type(),
            4 => context.i32_type(),
            8 => context.i64_type(),
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
        let inner = context.struct_type(field_types, false);

        Self {
            inner,
            variants: Rc::from(variants),
        }
    }

    // Can be called without knowing the full `VariantsType`
    fn discrim_t(inner: &inkwell::types::StructType<'a>) -> IntType<'a> {
        inner
            .get_field_type_at_index(Self::DISCRIM_IDX)
            .unwrap()
            .into_int_type()
    }

    fn bytes_t(&self) -> BasicTypeEnum<'a> {
        self.inner.get_field_type_at_index(Self::BYTES_IDX).unwrap()
    }

    fn variant_t(&self, idx: u32) -> BasicTypeEnum<'a> {
        self.variants[idx as usize]
    }

    // Can be called without knowing the full `VariantsType`
    fn discrim_const(inner: &inkwell::types::StructType<'a>, idx: u32) -> values::IntValue<'a> {
        Self::discrim_t(inner)
            .const_int(idx.try_into().unwrap(), false)
            .into()
    }

    fn build_bytes(
        &self,
        context: &'a inkwell::context::Context,
        builder: &Builder<'a>,
        content: values::BasicValueEnum<'a>,
    ) -> values::BasicValueEnum<'a> {
        let bytes_t = self.bytes_t();
        let bytes_ptr = gen_entry_alloca(context, builder, bytes_t, "bytes_ptr");
        builder.build_store(bytes_ptr, content).unwrap();
        builder.build_load(bytes_t, bytes_ptr, "bytes").unwrap()
    }

    fn build_value(
        &self,
        builder: &Builder<'a>,
        discrim: impl values::BasicValue<'a>,
        bytes: impl values::BasicValue<'a>,
    ) -> values::BasicValueEnum<'a> {
        let mut value = self.inner.get_undef();
        value = builder
            .build_insert_value(value, discrim, Self::DISCRIM_IDX, "insert")
            .unwrap()
            .into_struct_value();
        value = builder
            .build_insert_value(value, bytes, Self::BYTES_IDX, "insert")
            .unwrap()
            .into_struct_value();
        value.into()
    }

    fn build_get_discrim(
        builder: &Builder<'a>,
        val: values::BasicValueEnum<'a>,
    ) -> values::IntValue<'a> {
        builder
            .build_extract_value(val.into_struct_value(), Self::DISCRIM_IDX, "discrim")
            .unwrap()
            .into_int_value()
    }

    fn build_get_variant(
        &self,
        context: &'a inkwell::context::Context,
        builder: &Builder<'a>,
        val: values::BasicValueEnum<'a>,
        idx: u32,
    ) -> values::BasicValueEnum<'a> {
        let bytes_ptr = gen_entry_alloca(context, builder, self.bytes_t(), "bytes_ptr");
        let bytes = builder
            .build_extract_value(val.into_struct_value(), Self::BYTES_IDX, "bytes")
            .unwrap();
        builder.build_store(bytes_ptr, bytes).unwrap();

        let content_t = self.variant_t(idx);
        let content = builder.build_load(content_t, bytes_ptr, "content").unwrap();
        content
    }
}

#[derive(Clone, Copy)]
pub struct GlobalValue<'a>(inkwell::values::GlobalValue<'a>);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunctionValue<'a>(inkwell::values::FunctionValue<'a>);

impl<'a> FunctionValue<'a> {
    fn has_name(&self, name: &str) -> bool {
        self.0
            .get_name()
            .to_str()
            .map(|s| s == name)
            .unwrap_or(false)
    }
}

#[derive(Clone, Copy)]
pub struct Value<'a>(values::BasicValueEnum<'a>);

#[derive(Clone)]
pub struct ProfileRc<'a> {
    record_retain: FunctionValue<'a>,
    record_release: FunctionValue<'a>,
    record_rc1: FunctionValue<'a>,
    get_retain_count: FunctionValue<'a>,
    get_release_count: FunctionValue<'a>,
    get_rc1_count: FunctionValue<'a>,
}

impl<'a> fountain_pen::ProfileRc for ProfileRc<'a> {
    type FunctionValue = FunctionValue<'a>;

    fn record_retain(&self) -> Self::FunctionValue {
        self.record_retain
    }

    fn record_release(&self) -> Self::FunctionValue {
        self.record_release
    }

    fn record_rc1(&self) -> Self::FunctionValue {
        self.record_rc1
    }

    fn get_retain_count(&self) -> Self::FunctionValue {
        self.get_retain_count
    }

    fn get_release_count(&self) -> Self::FunctionValue {
        self.get_release_count
    }

    fn get_rc1_count(&self) -> Self::FunctionValue {
        self.get_rc1_count
    }
}

#[derive(Clone)]
pub struct Tal<'a> {
    memcpy: FunctionValue<'a>,
    exit: FunctionValue<'a>,
    getchar: FunctionValue<'a>,

    init_gc: Option<FunctionValue<'a>>,
    malloc: FunctionValue<'a>,
    calloc: FunctionValue<'a>,
    realloc: FunctionValue<'a>,
    free: FunctionValue<'a>,

    print: FunctionValue<'a>,
    print_error: FunctionValue<'a>,
    write: FunctionValue<'a>,
    write_error: FunctionValue<'a>,
    flush: FunctionValue<'a>,

    prof_clock_res_nanos: FunctionValue<'a>,
    prof_clock_nanos: FunctionValue<'a>,
    prof_report_init: FunctionValue<'a>,
    prof_report_write_string: FunctionValue<'a>,
    prof_report_write_u64: FunctionValue<'a>,
    prof_report_done: FunctionValue<'a>,
    prof_rc: Option<ProfileRc<'a>>,

    expect_i1: FunctionValue<'a>,
    umul_with_overflow_i64: FunctionValue<'a>,

    /// (i64) -> i64
    ctpop_i64: FunctionValue<'a>,

    /// The second argument is a bool indicating whether the output is poison if the input is 0.
    ///
    /// (i64, i1) -> i64
    ctlz_i64: FunctionValue<'a>,

    /// The second argument is a bool indicating whether the output is poison if the input is 0.
    ///
    /// (i64, i1) -> i64
    cttz_i64: FunctionValue<'a>,
}

impl<'a> fountain_pen::Tal for Tal<'a> {
    type FunctionValue = FunctionValue<'a>;
    type ProfileRc = ProfileRc<'a>;

    fn memcpy(&self) -> Self::FunctionValue {
        self.memcpy
    }

    fn exit(&self) -> Self::FunctionValue {
        self.exit
    }

    fn getchar(&self) -> Self::FunctionValue {
        self.getchar
    }

    fn malloc(&self) -> Self::FunctionValue {
        self.malloc
    }

    fn calloc(&self) -> Self::FunctionValue {
        self.calloc
    }

    fn realloc(&self) -> Self::FunctionValue {
        self.realloc
    }

    fn free(&self) -> Self::FunctionValue {
        self.free
    }

    fn print(&self) -> Self::FunctionValue {
        self.print
    }

    fn print_error(&self) -> Self::FunctionValue {
        self.print_error
    }

    fn write(&self) -> Self::FunctionValue {
        self.write
    }

    fn write_error(&self) -> Self::FunctionValue {
        self.write_error
    }

    fn flush(&self) -> Self::FunctionValue {
        self.flush
    }

    fn prof_clock_res_nanos(&self) -> Self::FunctionValue {
        self.prof_clock_res_nanos
    }

    fn prof_clock_nanos(&self) -> Self::FunctionValue {
        self.prof_clock_nanos
    }

    fn prof_report_init(&self) -> Self::FunctionValue {
        self.prof_report_init
    }

    fn prof_report_write_string(&self) -> Self::FunctionValue {
        self.prof_report_write_string
    }

    fn prof_report_write_u64(&self) -> Self::FunctionValue {
        self.prof_report_write_u64
    }

    fn prof_report_done(&self) -> Self::FunctionValue {
        self.prof_report_done
    }

    fn prof_rc(&self) -> Option<&Self::ProfileRc> {
        self.prof_rc.as_ref()
    }

    fn expect_i1(&self) -> Self::FunctionValue {
        self.expect_i1
    }

    fn umul_with_overflow_i64(&self) -> Self::FunctionValue {
        self.umul_with_overflow_i64
    }

    fn ctpop_i64(&self) -> Self::FunctionValue {
        self.ctpop_i64
    }

    fn ctlz_i64(&self) -> Self::FunctionValue {
        self.ctlz_i64
    }

    fn cttz_i64(&self) -> Self::FunctionValue {
        self.cttz_i64
    }
}

impl<'a> ProfileRc<'a> {
    fn declare(context: &'a inkwell::context::Context, module: &Module<'a>) -> ProfileRc<'a> {
        let void_t = context.void_type();
        let i64_t = context.i64_type();

        let record_retain = module.add_function(
            "morphic_prof_rc_record_retain",
            void_t.fn_type(&[], false),
            Some(Linkage::External),
        );
        let record_release = module.add_function(
            "morphic_prof_rc_record_release",
            void_t.fn_type(&[], false),
            Some(Linkage::External),
        );
        let record_rc1 = module.add_function(
            "morphic_prof_rc_record_rc1",
            void_t.fn_type(&[], false),
            Some(Linkage::External),
        );
        let get_retain_count = module.add_function(
            "morphic_prof_rc_get_retain_count",
            i64_t.fn_type(&[], false),
            Some(Linkage::External),
        );
        let get_release_count = module.add_function(
            "morphic_prof_rc_get_release_count",
            i64_t.fn_type(&[], false),
            Some(Linkage::External),
        );
        let get_rc1_count = module.add_function(
            "morphic_prof_rc_get_rc1_count",
            i64_t.fn_type(&[], false),
            Some(Linkage::External),
        );

        ProfileRc {
            record_retain: FunctionValue(record_retain),
            record_release: FunctionValue(record_release),
            record_rc1: FunctionValue(record_rc1),
            get_retain_count: FunctionValue(get_retain_count),
            get_release_count: FunctionValue(get_release_count),
            get_rc1_count: FunctionValue(get_rc1_count),
        }
    }
}

impl<'a> Tal<'a> {
    fn declare(
        context: &'a inkwell::context::Context,
        module: &Module<'a>,
        target: &TargetData,
        gc: GcKind,
        profile_record_rc: bool,
    ) -> Tal<'a> {
        let usize_t = usize_t(context, target);
        let void_t = context.void_type();
        let i1_t = context.bool_type();
        let i8_ptr_t = context.ptr_type(AddressSpace::default());
        let i32_t = context.i32_type();
        let i64_t = context.i64_type();

        let memcpy = module.add_function(
            "memcpy",
            i8_ptr_t.fn_type(&[i8_ptr_t.into(), i8_ptr_t.into(), usize_t.into()], false),
            Some(Linkage::External),
        );
        let exit = module.add_function(
            "exit",
            void_t.fn_type(&[i32_t.into()], false),
            Some(Linkage::External),
        );
        let getchar = module.add_function(
            "getchar",
            i32_t.fn_type(&[], false),
            Some(Linkage::External),
        );

        let init_gc = match gc {
            GcKind::Bdw => Some(module.add_function(
                "morphic_GC_init",
                void_t.fn_type(&[], false),
                Some(Linkage::External),
            )),
            GcKind::None => None,
        };
        let malloc = module.add_function(
            match gc {
                GcKind::Bdw => "GC_malloc",
                GcKind::None => "malloc",
            },
            i8_ptr_t.fn_type(&[usize_t.into()], false),
            Some(Linkage::External),
        );
        let calloc = module.add_function(
            match gc {
                GcKind::Bdw => "morphic_GC_calloc",
                GcKind::None => "calloc",
            },
            i8_ptr_t.fn_type(&[usize_t.into(), usize_t.into()], false),
            Some(Linkage::External),
        );
        let realloc = module.add_function(
            match gc {
                GcKind::Bdw => "GC_realloc",
                GcKind::None => "realloc",
            },
            i8_ptr_t.fn_type(&[i8_ptr_t.into(), usize_t.into()], false),
            Some(Linkage::External),
        );
        let free = module.add_function(
            match gc {
                GcKind::Bdw => "GC_free",
                GcKind::None => "free",
            },
            void_t.fn_type(&[i8_ptr_t.into()], false),
            Some(Linkage::External),
        );

        let print = module.add_function(
            "morphic_print",
            void_t.fn_type(&[i8_ptr_t.into()], true),
            Some(Linkage::External),
        );
        let print_error = module.add_function(
            "morphic_print_error",
            void_t.fn_type(&[i8_ptr_t.into()], true),
            Some(Linkage::External),
        );
        let write = module.add_function(
            "morphic_write",
            void_t.fn_type(&[i8_ptr_t.into(), usize_t.into(), usize_t.into()], false),
            Some(Linkage::External),
        );
        let write_error = module.add_function(
            "morphic_write_error",
            void_t.fn_type(&[i8_ptr_t.into(), usize_t.into(), usize_t.into()], false),
            Some(Linkage::External),
        );
        let flush = module.add_function(
            "morphic_flush",
            i32_t.fn_type(&[], false),
            Some(Linkage::External),
        );

        // Profiling primitives:

        let prof_clock_res_nanos = module.add_function(
            "morphic_prof_clock_res_nanos",
            i64_t.fn_type(&[], false),
            Some(Linkage::External),
        );
        let prof_clock_nanos = module.add_function(
            "morphic_prof_clock_nanos",
            i64_t.fn_type(&[], false),
            Some(Linkage::External),
        );
        let prof_report_init = module.add_function(
            "morphic_prof_report_init",
            void_t.fn_type(&[], false),
            Some(Linkage::External),
        );
        let prof_report_write_string = module.add_function(
            "morphic_prof_report_write_string",
            void_t.fn_type(&[i8_ptr_t.into()], false),
            Some(Linkage::External),
        );
        let prof_report_write_u64 = module.add_function(
            "morphic_prof_report_write_u64",
            void_t.fn_type(&[i64_t.into()], false),
            Some(Linkage::External),
        );
        let prof_report_done = module.add_function(
            "morphic_prof_report_done",
            void_t.fn_type(&[], false),
            Some(Linkage::External),
        );

        // LLVM Intrinsics:

        let expect_i1 = module.add_function(
            "llvm.expect.i1",
            context.bool_type().fn_type(
                &[context.bool_type().into(), context.bool_type().into()],
                false,
            ),
            Some(Linkage::External),
        );
        let umul_with_overflow_i64 = module.add_function(
            "llvm.umul.with.overflow.i64",
            context
                .struct_type(&[i64_t.into(), context.bool_type().into()], false)
                .fn_type(&[i64_t.into(), i64_t.into()], false),
            Some(Linkage::External),
        );
        let ctpop_i64 = module.add_function(
            "llvm.ctpop.i64",
            i64_t.fn_type(&[i64_t.into()], false),
            Some(Linkage::External),
        );
        let ctlz_i64 = module.add_function(
            "llvm.ctlz.i64",
            i64_t.fn_type(&[i64_t.into(), i1_t.into()], false),
            Some(Linkage::External),
        );
        let cttz_i64 = module.add_function(
            "llvm.cttz.i64",
            i64_t.fn_type(&[i64_t.into(), i1_t.into()], false),
            Some(Linkage::External),
        );

        let prof_rc = if profile_record_rc {
            Some(ProfileRc::declare(context, module))
        } else {
            None
        };

        Tal {
            memcpy: FunctionValue(memcpy),
            exit: FunctionValue(exit),
            getchar: FunctionValue(getchar),

            init_gc: init_gc.map(FunctionValue),
            malloc: FunctionValue(malloc),
            calloc: FunctionValue(calloc),
            realloc: FunctionValue(realloc),
            free: FunctionValue(free),

            print: FunctionValue(print),
            print_error: FunctionValue(print_error),
            write: FunctionValue(write),
            write_error: FunctionValue(write_error),
            flush: FunctionValue(flush),

            prof_clock_res_nanos: FunctionValue(prof_clock_res_nanos),
            prof_clock_nanos: FunctionValue(prof_clock_nanos),
            prof_report_init: FunctionValue(prof_report_init),
            prof_report_write_string: FunctionValue(prof_report_write_string),
            prof_report_write_u64: FunctionValue(prof_report_write_u64),
            prof_report_done: FunctionValue(prof_report_done),
            prof_rc,

            expect_i1: FunctionValue(expect_i1),
            umul_with_overflow_i64: FunctionValue(umul_with_overflow_i64),
            ctpop_i64: FunctionValue(ctpop_i64),
            ctlz_i64: FunctionValue(ctlz_i64),
            cttz_i64: FunctionValue(cttz_i64),
        }
    }
}

pub struct Scope<'a, 'b> {
    context: Context<'a, 'b>,
    builder: Builder<'a>,
    func: FunctionValue<'a>,
    tail_arg: Option<(Type<'a>, inkwell::values::PointerValue<'a>)>,
}

impl<'a, 'b> Scope<'a, 'b> {
    fn new(
        context: Context<'a, 'b>,
        func: FunctionValue<'a>,
        block: BasicBlock<'a>,
        tail_arg: Option<(Type<'a>, inkwell::values::PointerValue<'a>)>,
    ) -> Scope<'a, 'b> {
        let builder = context.context.create_builder();
        builder.position_at_end(block);

        Scope {
            context,
            builder,
            func,
            tail_arg,
        }
    }
}

#[id_type]
pub struct TailTarget(usize);

#[derive(Clone)]
struct TailTargetData<'a> {
    arg_ty: Type<'a>,
    arg_ptr: inkwell::values::PointerValue<'a>,
    func: FunctionValue<'a>,
    block: BasicBlock<'a>,
}

#[derive(Clone)]
pub struct Context<'a, 'b> {
    gc: GcKind,
    context: &'a inkwell::context::Context,
    module: &'b Module<'a>,
    target: &'b TargetData,
    tal: Tal<'a>,
    tail_funcs: Rc<RefCell<HashMap<FunctionValue<'a>, BasicBlock<'a>>>>,
    tail_targets: Rc<RefCell<IdVec<TailTarget, TailTargetData<'a>>>>,
}

fn usize_t<'a>(context: &'a inkwell::context::Context, target: &TargetData) -> IntType<'a> {
    let bits_per_byte = 8;
    let ptr_size = target.get_pointer_byte_size(Some(AddressSpace::default())) * bits_per_byte;
    return context.custom_width_int_type(ptr_size);
}

macro_rules! impl_int_cmp {
    ($(($name:ident, $predicate:ident)),* $(,)?) => {
        $(
            fn $name(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
                Value(
                    self.builder
                        .build_int_compare(
                            IntPredicate::$predicate,
                            arg1.0.into_int_value(),
                            arg2.0.into_int_value(),
                            stringify!($name),
                        )
                        .unwrap()
                        .into(),
                )
            }
        )*
    };
}

macro_rules! impl_float_cmp {
    ($(($name:ident, $predicate:ident)),* $(,)?) => {
        $(
            fn $name(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
            Value(
                self.builder
                    .build_float_compare(
                        FloatPredicate::$predicate,
                        arg1.0.into_float_value(),
                        arg2.0.into_float_value(),
                        stringify!($name),
                    )
                    .unwrap()
                    .into(),
                )
            }
        )*
    };
}

impl<'a, 'b> fountain_pen::Context for Context<'a, 'b> {
    type Scope = Scope<'a, 'b>;

    type TailTarget = TailTarget;
    type VariantsType = VariantsType<'a>;
    type Type = Type<'a>;
    type GlobalValue = GlobalValue<'a>;
    type FunctionValue = FunctionValue<'a>;
    type Value = Value<'a>;

    type ProfileRc = ProfileRc<'a>;
    type Tal = Tal<'a>;

    fn is_gc_on(&self) -> bool {
        self.gc != GcKind::None
    }

    fn tal(&self) -> &Self::Tal {
        &self.tal
    }

    fn declare_main_func(&self) -> Self::FunctionValue {
        let i32_t = self.context.i32_type();
        let ptr_t = self.context.ptr_type(AddressSpace::default());
        let fn_ty = i32_t.fn_type(&[i32_t.into(), ptr_t.into()], false);
        FunctionValue(
            self.module
                .add_function("main", fn_ty, Some(Linkage::External)),
        )
    }

    fn declare_func(
        &self,
        name: &str,
        arg_tys: &[Self::Type],
        ret_ty: Option<Self::Type>,
    ) -> Self::FunctionValue {
        let arg_tys = arg_tys.iter().map(|ty| ty.0.into()).collect::<Vec<_>>();
        let fn_ty = ret_ty
            .map(|ty| ty.0.fn_type(&arg_tys, false))
            .unwrap_or_else(|| self.context.void_type().fn_type(&arg_tys, false));
        FunctionValue(
            self.module
                .add_function(name, fn_ty, Some(Linkage::Internal)),
        )
    }

    fn declare_tail_func(
        &self,
        name: &str,
        arg_tys: &[Self::Type],
        ret_ty: Option<Self::Type>,
        tail_arg_tys: &[Self::Type],
    ) -> (Self::FunctionValue, Vec<Self::TailTarget>) {
        let func = self.declare_func(name, arg_tys, ret_ty);

        let entry_block = self.context.append_basic_block(func.0, "entry");
        let entry_builder = self.context.create_builder();
        entry_builder.position_at_end(entry_block);

        let mut tail_targets = Vec::new();
        for (i, &arg_ty) in tail_arg_tys.iter().enumerate() {
            let arg_ptr = entry_builder
                .build_alloca(arg_ty.0, &format!("tail_{}_arg", i))
                .unwrap();

            let block = self
                .context
                .append_basic_block(func.0, &format!("tail_{}", i));

            let id = self.tail_targets.borrow_mut().push(TailTargetData {
                arg_ty,
                arg_ptr,
                func,
                block,
            });

            tail_targets.push(id);
        }

        let body_block = self.context.append_basic_block(func.0, "body");
        entry_builder
            .build_unconditional_branch(body_block)
            .unwrap();
        self.tail_funcs.borrow_mut().insert(func, body_block);

        return (func, tail_targets);
    }

    fn declare_global(
        &self,
        name: &str,
        ty: Self::Type,
        init: Option<Self::Value>,
    ) -> Self::GlobalValue {
        let global = self
            .module
            .add_global(ty.0, Some(AddressSpace::default()), name);
        if let Some(init) = init {
            global.set_initializer(&init.0);
        }
        GlobalValue(global)
    }

    fn scope(&self, func: Self::FunctionValue) -> Self::Scope {
        if let Some(&body_block) = self.tail_funcs.borrow().get(&func) {
            assert_eq!(body_block.get_instructions().count(), 0);
            return Scope::new(self.clone(), func, body_block, None);
        }

        assert_eq!(func.0.count_basic_blocks(), 0);
        let entry_block = self.context.append_basic_block(func.0, "entry");
        let scope = Scope::new(self.clone(), func, entry_block, None);

        if self.gc == GcKind::Bdw && func.has_name("main") {
            scope.call_void(self.tal.init_gc.unwrap(), &[])
        }

        scope
    }

    fn tail_scope(&self, tail_target: Self::TailTarget) -> Self::Scope {
        let tail_targets = self.tail_targets.borrow();
        let data = tail_targets.get(tail_target).unwrap();
        Scope::new(
            self.clone(),
            data.func,
            data.block,
            Some((data.arg_ty, data.arg_ptr)),
        )
    }

    fn global_value_as_pointer(&self, global_value: Self::GlobalValue) -> Self::Value {
        Value(global_value.0.as_pointer_value().into())
    }

    fn variants_type_as_type(&self, variants_type: &Self::VariantsType) -> Self::Type {
        Type(variants_type.inner.into())
    }

    fn get_type(&self, val: Self::Value) -> Self::Type {
        Type(val.0.get_type().into())
    }

    fn get_abi_size(&self, ty: Self::Type) -> u64 {
        self.target.get_abi_size(&ty.0)
    }

    fn i1_t(&self) -> Self::Type {
        Type(self.context.bool_type().into())
    }

    fn i8_t(&self) -> Self::Type {
        Type(self.context.i8_type().into())
    }

    fn i32_t(&self) -> Self::Type {
        Type(self.context.i32_type().into())
    }

    fn i64_t(&self) -> Self::Type {
        Type(self.context.i64_type().into())
    }

    fn usize_t(&self) -> Self::Type {
        Type(usize_t(self.context, self.target).into())
    }

    fn f32_t(&self) -> Self::Type {
        Type(self.context.f32_type().into())
    }

    fn f64_t(&self) -> Self::Type {
        Type(self.context.f64_type().into())
    }

    fn ptr_t(&self) -> Self::Type {
        Type(self.context.ptr_type(AddressSpace::default()).into())
    }

    fn array_t(&self, item_ty: Self::Type, len: u32) -> Self::Type {
        Type(item_ty.0.array_type(len).into())
    }

    fn struct_t(&self, fields: &[Self::Type]) -> Self::Type {
        let fields = fields.iter().map(|ty| ty.0.into()).collect::<Vec<_>>();
        Type(self.context.struct_type(&fields, false).into())
    }

    fn variants_t(&self, variants: &[Self::Type]) -> Self::VariantsType {
        VariantsType::new(
            self.context,
            self.target,
            variants.iter().map(|ty| ty.0.into()).collect::<Vec<_>>(),
        )
    }

    fn undef(&self, ty: Self::Type) -> Self::Value {
        Value(match ty.0 {
            BasicTypeEnum::ArrayType(t) => t.get_undef().into(),
            BasicTypeEnum::FloatType(t) => t.get_undef().into(),
            BasicTypeEnum::IntType(t) => t.get_undef().into(),
            BasicTypeEnum::PointerType(t) => t.get_undef().into(),
            BasicTypeEnum::StructType(t) => t.get_undef().into(),
            BasicTypeEnum::VectorType(t) => t.get_undef().into(),
            BasicTypeEnum::ScalableVectorType(t) => t.get_undef().into(),
        })
    }

    fn i1(&self, val: bool) -> Value<'a> {
        Value(self.context.bool_type().const_int(val as u64, false).into())
    }

    fn i8(&self, val: u8) -> Value<'a> {
        Value(self.context.i8_type().const_int(val as u64, false).into())
    }

    fn i32(&self, val: u32) -> Value<'a> {
        Value(self.context.i32_type().const_int(val as u64, false).into())
    }

    fn i64(&self, val: u64) -> Value<'a> {
        Value(self.context.i64_type().const_int(val as u64, false).into())
    }

    fn usize(&self, val: u64) -> Value<'a> {
        Value(
            usize_t(self.context, self.target)
                .const_int(val as u64, false)
                .into(),
        )
    }

    fn f32(&self, val: f32) -> Value<'a> {
        Value(self.context.f32_type().const_float(val as f64).into())
    }

    fn f64(&self, val: f64) -> Value<'a> {
        Value(self.context.f64_type().const_float(val as f64).into())
    }

    fn null(&self) -> Value<'a> {
        Value(
            self.context
                .ptr_type(AddressSpace::default())
                .const_null()
                .into(),
        )
    }
}

impl<'a, 'b> fountain_pen::Scope for Scope<'a, 'b> {
    type Context = Context<'a, 'b>;

    type TailTarget = TailTarget;
    type VariantsType = VariantsType<'a>;
    type Type = Type<'a>;
    type GlobalValue = GlobalValue<'a>;
    type FunctionValue = FunctionValue<'a>;
    type Value = Value<'a>;

    fn context(&self) -> &Context<'a, 'b> {
        &self.context
    }

    fn func(&self) -> FunctionValue<'a> {
        self.func
    }

    fn str(&self, s: &str) -> Value<'a> {
        Value(
            self.builder
                .build_global_string_ptr(s, "global_str")
                .unwrap()
                .as_basic_value_enum()
                .into(),
        )
    }

    fn arg(&self, idx: u32) -> Value<'a> {
        Value(self.func.0.get_nth_param(idx).unwrap())
    }

    fn tail_arg(&self) -> Value<'a> {
        let (arg_ty, arg_ptr) = self.tail_arg.unwrap();
        Value(
            self.builder
                .build_load(arg_ty.0, arg_ptr, "tail_arg")
                .unwrap(),
        )
    }

    fn call(&self, called: FunctionValue<'a>, args: &[Value<'a>]) -> Value<'a> {
        Value(
            self.builder
                .build_call(
                    called.0,
                    &args
                        .iter()
                        .map(|x| Into::<values::BasicMetadataValueEnum>::into(x.0))
                        .collect::<Vec<_>>(),
                    "call",
                )
                .unwrap()
                .try_as_basic_value()
                .left()
                .expect("Cannot use 'call' to call a function without a return value")
                .into(),
        )
    }

    fn call_void(&self, called: FunctionValue<'a>, args: &[Value<'a>]) {
        self.builder
            .build_call(
                called.0,
                &args
                    .iter()
                    .map(|x| Into::<values::BasicMetadataValueEnum>::into(x.0))
                    .collect::<Vec<_>>(),
                "call",
            )
            .unwrap()
            .try_as_basic_value()
            .right()
            .expect("Cannot use 'call_void' to call a function with a return value");
    }

    fn tail_call(&self, called: TailTarget, arg: Value<'a>) -> Value<'a> {
        let tail_targets = self.context.tail_targets.borrow();
        let data = tail_targets.get(called).unwrap();

        self.builder.build_store(data.arg_ptr, arg.0).unwrap();
        self.builder.build_unconditional_branch(data.block).unwrap();

        let unreachable_block = self
            .context
            .context
            .append_basic_block(self.func.0, "after_tail_call");
        self.builder.position_at_end(unreachable_block);

        // The return type of the tail call (which is somewhat theoretical, as a tail call never
        // actually returns to its original caller) is necessarily that of the function
        // currently being generated.
        self.undef(Type(self.func.0.get_type().get_return_type().unwrap()))
    }

    fn gep(&self, struct_ty: Type<'a>, struct_ptr: Value<'a>, idx: u32) -> Value<'a> {
        let x: values::BasicValueEnum<'a> = self
            .builder
            .build_struct_gep(struct_ty.0, struct_ptr.0.into_pointer_value(), idx, "gep")
            .unwrap()
            .into();

        Value(x)
    }

    fn arrow(
        &self,
        struct_ty: Type<'a>,
        field_ty: Type<'a>,
        struct_ptr: Value<'a>,
        idx: u32,
    ) -> Value<'a> {
        Value(
            self.builder
                .build_load(
                    field_ty.0,
                    self.gep(struct_ty, struct_ptr, idx).0.into_pointer_value(),
                    "arrow",
                )
                .unwrap(),
        )
    }

    fn field(&self, struct_val: Value<'a>, idx: u32) -> Value<'a> {
        Value(
            self.builder
                .build_extract_value(struct_val.0.into_struct_value(), idx, "field")
                .unwrap(),
        )
    }

    fn arrow_set(&self, struct_ty: Type<'a>, struct_ptr: Value<'a>, idx: u32, new_data: Value<'a>) {
        self.builder
            .build_store(
                self.builder
                    .build_struct_gep(struct_ty.0, struct_ptr.0.into_pointer_value(), idx, "gep")
                    .unwrap(),
                new_data.0,
            )
            .unwrap();
    }

    fn if_(&self, cond: Value<'a>, body: impl FnOnce(&Scope<'a, 'b>) -> ()) {
        let cond_int = cond.0.into_int_value();
        let then_block = self
            .context
            .context
            .append_basic_block(self.func.0, "then_block");
        let next_block = self
            .context
            .context
            .append_basic_block(self.func.0, "next_block");

        self.builder
            .build_conditional_branch(cond_int, then_block, next_block)
            .unwrap();
        let new_scope = Scope::new(self.context.clone(), self.func, then_block, self.tail_arg);

        body(&new_scope);

        let final_child_block = new_scope.builder.get_insert_block().unwrap();

        if final_child_block.get_terminator().is_none() {
            new_scope
                .builder
                .build_unconditional_branch(next_block)
                .unwrap();
        }

        self.builder.position_at_end(next_block);
    }

    fn if_else(&self, cond: Value<'a>, mut body: impl FnMut(&Scope<'a, 'b>, bool)) {
        let cond_int = cond.0.into_int_value();
        let then_block = self
            .context
            .context
            .append_basic_block(self.func.0, "then_block");
        let else_block = self
            .context
            .context
            .append_basic_block(self.func.0, "else_block");
        let next_block = self
            .context
            .context
            .append_basic_block(self.func.0, "next_block");

        self.builder
            .build_conditional_branch(cond_int, then_block, else_block)
            .unwrap();
        let then_scope = Scope::new(self.context.clone(), self.func, then_block, self.tail_arg);

        body(&then_scope, true);

        let final_then_block = then_scope.builder.get_insert_block().unwrap();

        if final_then_block.get_terminator().is_none() {
            then_scope
                .builder
                .build_unconditional_branch(next_block)
                .unwrap();
        }

        let else_scope = Scope::new(self.context.clone(), self.func, else_block, self.tail_arg);

        body(&else_scope, false);

        let final_else_block = else_scope.builder.get_insert_block().unwrap();

        if final_else_block.get_terminator().is_none() {
            else_scope
                .builder
                .build_unconditional_branch(next_block)
                .unwrap();
        }

        self.builder.position_at_end(next_block);
    }

    fn if_expr(
        &self,
        cond: Value<'a>,
        mut body: impl FnMut(&Scope<'a, 'b>, bool) -> Value<'a>,
    ) -> Value<'a> {
        let cond_int = cond.0.into_int_value();
        let then_block = self
            .context
            .context
            .append_basic_block(self.func.0, "then_block");
        let else_block = self
            .context
            .context
            .append_basic_block(self.func.0, "else_block");
        let next_block = self
            .context
            .context
            .append_basic_block(self.func.0, "next_block");

        self.builder
            .build_conditional_branch(cond_int, then_block, else_block)
            .unwrap();

        let then_scope = Scope::new(self.context.clone(), self.func, then_block, self.tail_arg);
        let then_value = body(&then_scope, true);
        let final_then_block = then_scope.builder.get_insert_block().unwrap();
        then_scope
            .builder
            .build_unconditional_branch(next_block)
            .unwrap();

        let else_scope = Scope::new(self.context.clone(), self.func, else_block, self.tail_arg);
        let else_value = body(&else_scope, false);
        let final_else_block = else_scope.builder.get_insert_block().unwrap();
        else_scope
            .builder
            .build_unconditional_branch(next_block)
            .unwrap();

        assert![then_value.0.get_type() == else_value.0.get_type()];

        self.builder.position_at_end(next_block);

        let phi = self
            .builder
            .build_phi(then_value.0.get_type(), "result")
            .unwrap();
        phi.add_incoming(&[
            (&then_value.0, final_then_block),
            (&else_value.0, final_else_block),
        ]);

        Value(phi.as_basic_value())
    }

    fn ternary(&self, cond: Value<'a>, then_value: Value<'a>, else_value: Value<'a>) -> Value<'a> {
        let cond_int = cond.0.into_int_value();
        Value(
            self.builder
                .build_select(cond_int, then_value.0, else_value.0, "ternary")
                .unwrap(),
        )
    }

    fn int_cast(&self, result_type: Type<'a>, int: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_int_cast(
                    int.0.into_int_value(),
                    result_type.0.into_int_type(),
                    "int_cast",
                )
                .unwrap()
                .into(),
        )
    }

    fn make_struct(&self, ty: Self::Type, fields: &[(u32, Self::Value)]) -> Self::Value {
        let mut sorted = fields.to_vec();
        sorted.sort_by_key(|(idx, _)| *idx);

        let struct_ty = ty.0.into_struct_type();
        let field_tys = struct_ty.get_field_types();
        let expected_len = field_tys.len();
        let actual_len = sorted.len();

        if expected_len != actual_len {
            panic!(
                "make_struct: struct has {expected_len} fields, but {actual_len} fields were provided",
            );
        }

        for (i, (j, value)) in sorted.iter().enumerate() {
            if i as u32 != *j {
                panic!("make_struct: fields must be consecutive numbers starting from 0, but field {i} is missing");
            }

            let field_ty = field_tys[i];
            let value_ty = value.0.get_type();

            if field_ty != value_ty {
                panic!(
                    "make_struct: field {i} has type {field_ty}, but provided value has type {value_ty}",
                );
            }
        }

        self.make_tup(&sorted.into_iter().map(|(_, val)| val).collect::<Vec<_>>())
    }

    fn make_tup(&self, fields: &[Value<'a>]) -> Value<'a> {
        let field_types: Vec<_> = fields.iter().map(|field| field.0.get_type()).collect();
        let tup_type = self.context.context.struct_type(&field_types[..], false);

        let mut tup = tup_type.get_undef();
        for (elem, value) in fields.iter().enumerate() {
            tup = self
                .builder
                .build_insert_value(tup, value.0, elem.try_into().unwrap(), "insert")
                .unwrap()
                .into_struct_value();
        }

        Value(tup.into())
    }

    fn buf_addr(&self, pointee_ty: Type<'a>, arr: Value<'a>, idx: Value<'a>) -> Value<'a> {
        unsafe {
            Value(
                self.builder
                    .build_in_bounds_gep(
                        pointee_ty.0,
                        arr.0.into_pointer_value().into(),
                        &[idx.0.into_int_value()],
                        "arr_addr",
                    )
                    .unwrap()
                    .into(),
            )
        }
    }

    /// 'buf_addr' out of bounds (OOB) -- i.e., without the "in-bounds" requirement.
    fn buf_addr_oob(&self, pointee_ty: Type<'a>, arr: Value<'a>, idx: Value<'a>) -> Value<'a> {
        unsafe {
            Value(
                self.builder
                    .build_gep(
                        pointee_ty.0,
                        arr.0.into_pointer_value().into(),
                        &[idx.0.into_int_value()],
                        "arr_addr",
                    )
                    .unwrap()
                    .into(),
            )
        }
    }

    fn buf_set(&self, pointee_ty: Type<'a>, arr: Value<'a>, idx: Value<'a>, val: Value<'a>) {
        let addr = self.buf_addr(pointee_ty, arr, idx).0.into_pointer_value();

        self.builder.build_store(addr, val.0).unwrap();
    }

    fn buf_get(&self, pointee_ty: Type<'a>, arr: Value<'a>, idx: Value<'a>) -> Value<'a> {
        let addr = self.buf_addr(pointee_ty, arr, idx).0.into_pointer_value();

        Value(self.builder.build_load(pointee_ty.0, addr, "get").unwrap())
    }

    fn arr_addr(&self, pointee_ty: Type<'a>, arr: Value<'a>, idx: Value<'a>) -> Value<'a> {
        self.buf_addr(pointee_ty, arr, idx)
    }

    fn arr_set(&self, pointee_ty: Type<'a>, arr: Value<'a>, idx: Value<'a>, val: Value<'a>) {
        let addr = self.arr_addr(pointee_ty, arr, idx).0.into_pointer_value();

        self.builder.build_store(addr, val.0).unwrap();
    }

    fn arr_get(&self, pointee_ty: Type<'a>, arr: Value<'a>, idx: Value<'a>) -> Value<'a> {
        let addr = self.arr_addr(pointee_ty, arr, idx).0.into_pointer_value();

        Value(self.builder.build_load(pointee_ty.0, addr, "get").unwrap())
    }

    fn for_(&self, bound: Value<'a>, body: impl FnOnce(&Scope<'a, 'b>, Value<'a>)) {
        let i_ptr = self.alloca(self.i64_t());
        self.ptr_set(i_ptr, self.i64(0));
        self.while_(
            |s| s.ult(s.ptr_get(self.i64_t(), i_ptr), bound),
            |s| {
                body(s, s.ptr_get(self.i64_t(), i_ptr));
                s.ptr_set(i_ptr, s.add(s.ptr_get(self.i64_t(), i_ptr), s.i64(1)));
            },
        );
    }

    fn ptr_set(&self, ptr: Value<'a>, val: Value<'a>) {
        self.builder
            .build_store(ptr.0.into_pointer_value(), val.0)
            .unwrap();
    }

    fn ptr_get(&self, pointee_ty: Type<'a>, ptr: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_load(pointee_ty.0, ptr.0.into_pointer_value(), "get")
                .unwrap(),
        )
    }

    fn global_set(&self, ptr: GlobalValue<'a>, val: Value<'a>) {
        self.builder
            .build_store(ptr.0.as_pointer_value(), val.0)
            .unwrap();
    }

    fn global_get(&self, pointee_ty: Type<'a>, ptr: GlobalValue<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_load(pointee_ty.0, ptr.0.as_pointer_value(), "get")
                .unwrap(),
        )
    }

    fn panic(&self, panic_string: &str, panic_args: &[Value<'a>]) {
        let i32_type = self.context.context.i32_type();

        let panic_global = self
            .builder
            .build_global_string_ptr(panic_string, "panic_str")
            .unwrap();

        let mut print_error_args = vec![panic_global.as_pointer_value().into()];
        print_error_args.extend_from_slice(
            &panic_args
                .iter()
                .map(|x| Into::<values::BasicMetadataValueEnum>::into(x.0))
                .collect::<Vec<_>>(),
        );

        self.builder
            .build_call(
                self.context.tal.print_error.0,
                &print_error_args,
                "print_error_output",
            )
            .unwrap();

        self.builder
            .build_call(
                self.context.tal.exit.0,
                &[i32_type.const_int(1, true).into()],
                "",
            )
            .unwrap();

        self.builder.build_unreachable().unwrap();

        let unreachable_block = self
            .context
            .context
            .append_basic_block(self.func.0, "after_unreachable");
        self.builder.position_at_end(unreachable_block);
    }

    fn print(&self, message: &str, message_args: &[Value<'a>]) {
        let message_global = self
            .builder
            .build_global_string_ptr(message, "print_str")
            .unwrap();

        let mut print_args = vec![message_global.as_pointer_value().into()];
        print_args.extend_from_slice(
            &message_args
                .iter()
                .map(|x| Into::<values::BasicMetadataValueEnum>::into(x.0))
                .collect::<Vec<_>>(),
        );

        self.builder
            .build_call(self.context.tal.print.0, &print_args, "print_output")
            .unwrap();
    }

    fn debug(&self, message: &str, message_args: &[Value<'a>]) {
        let message_global = self
            .builder
            .build_global_string_ptr(message, "debug_str")
            .unwrap();

        let mut print_error_args = vec![message_global.as_pointer_value().into()];
        print_error_args.extend_from_slice(
            &message_args
                .iter()
                .map(|x| Into::<values::BasicMetadataValueEnum>::into(x.0))
                .collect::<Vec<_>>(),
        );

        self.builder
            .build_call(
                self.context.tal.print_error.0,
                &print_error_args,
                "print_error__output",
            )
            .unwrap();
    }

    fn malloc(&self, num: Value<'a>, ty: Type<'a>) -> Value<'a> {
        let size = self.size(ty);

        let alloc_size_umul_result = self.call(
            self.context.tal.umul_with_overflow_i64,
            &[num, self.int_cast(self.usize_t(), size)],
        );

        let is_overflow = self.field(alloc_size_umul_result, 1);
        self.if_(is_overflow, |s| {
            s.panic("malloc: requested size overflows 64-bit integer type", &[]);
        });

        // TODO: Check for truncation overflow on 32-bit platforms
        let ptr = self.call(
            self.context.tal.malloc,
            &[self.field(alloc_size_umul_result, 0)],
        );
        self.if_(self.is_null(ptr), |s| {
            s.panic("malloc failed", &[]);
        });

        return ptr;
    }

    fn calloc(&self, num: Value<'a>, ty: Type<'a>) -> Value<'a> {
        let ptr = self.call(
            self.context.tal.calloc,
            &[
                Value(num.0.into_int_value().into()),
                self.int_cast(self.usize_t(), self.size(ty)),
            ],
        );
        self.if_(self.is_null(ptr), |s| {
            s.panic("calloc failed", &[]);
        });

        return ptr;
    }

    fn free(&self, ptr: Value<'a>) {
        self.call_void(self.context.tal.free, &[ptr]);
    }

    fn is_null(&self, ptr: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_is_null(ptr.0.into_pointer_value(), "is_null")
                .unwrap()
                .into(),
        )
    }

    fn struct_t(&self, fields: &[Self::Type]) -> Self::Type {
        let fields = fields.iter().map(|ty| ty.0.into()).collect::<Vec<_>>();
        Type(self.context.context.struct_type(&fields, false).into())
    }

    fn variants_t(&self, variants: &[Self::Type]) -> Self::VariantsType {
        VariantsType::new(
            self.context.context,
            self.context.target,
            variants.iter().map(|ty| ty.0.into()).collect::<Vec<_>>(),
        )
    }

    fn variants_new_discrim(&self, ty: Self::Type, idx: u32) -> Self::Value {
        let discrim = VariantsType::discrim_const(&ty.0.into_struct_type(), idx);
        Value(discrim.into())
    }

    fn variants_get_discrim(&self, val: Self::Value) -> Self::Value {
        let discrim = VariantsType::build_get_discrim(&self.builder, val.0);
        Value(discrim.into())
    }

    fn variants_new(&self, ty: &Self::VariantsType, val: Self::Value, idx: u32) -> Self::Value {
        let discrim = VariantsType::discrim_const(&ty.inner, idx);
        let bytes = ty.build_bytes(self.context.context, &self.builder, val.0);
        Value(ty.build_value(&self.builder, discrim, bytes))
    }

    fn variants_get(&self, ty: &Self::VariantsType, val: Self::Value, idx: u32) -> Self::Value {
        Value(ty.build_get_variant(self.context.context, &self.builder, val.0, idx))
    }

    fn variants_switch(
        &self,
        ty: &Self::VariantsType,
        val: Self::Value,
        mut cases: impl FnMut(&Self, u32, Self::Value),
    ) {
        // Note: in this funciton we must position the builder correctly each time before calling
        // one of `cases` and after the switch is done.

        let context = self.context.context;

        let discrim = VariantsType::build_get_discrim(&self.builder, val.0);
        let undefined_block = context.append_basic_block(self.func.0, "undefined");
        let mut variant_blocks = Vec::new();
        for _ in 0..ty.variants.len() {
            let _ = variant_blocks.push(context.append_basic_block(self.func.0, "variant"));
        }
        let switch_blocks: Vec<(values::IntValue<'a>, BasicBlock<'a>)> = variant_blocks
            .iter()
            .enumerate()
            .map(|(i, variant_block)| {
                let discrim = VariantsType::discrim_const(&ty.inner, i.try_into().unwrap());
                (discrim, *variant_block)
            })
            .collect::<Vec<_>>();
        self.builder
            .build_switch(discrim, undefined_block, &switch_blocks[..])
            .unwrap();

        let next_block = context.append_basic_block(self.func.0, "next");

        self.builder.position_at_end(undefined_block);
        self.builder.build_unreachable().unwrap();

        for (i, variant_block) in variant_blocks.iter().enumerate() {
            self.builder.position_at_end(*variant_block);
            let variant_val =
                ty.build_get_variant(context, &self.builder, val.0, i.try_into().unwrap());
            cases(self, i.try_into().unwrap(), Value(variant_val.into()));
            self.builder.build_unconditional_branch(next_block).unwrap();
        }

        self.builder.position_at_end(next_block);
    }

    fn ret_void(&self) {
        self.builder.build_return(None).unwrap();
    }

    fn ret(&self, ret_val: Value<'a>) {
        self.builder.build_return(Some(&ret_val.0)).unwrap();
    }

    fn size(&self, ty: Type<'a>) -> Value<'a> {
        Value(ty.0.size_of().unwrap().into())
    }

    fn unreachable(&self) {
        self.builder.build_unreachable().unwrap();

        let unreachable_block = self
            .context
            .context
            .append_basic_block(self.func.0, "after_unreachable");
        self.builder.position_at_end(unreachable_block);
    }

    fn alloca(&self, ty: Type<'a>) -> Value<'a> {
        let entry = self.func.0.get_first_basic_block().unwrap();

        let entry_builder = self.context.context.create_builder();

        if let Some(entry_inst) = entry.get_first_instruction() {
            entry_builder.position_before(&entry_inst);
        } else {
            entry_builder.position_at_end(entry);
        }

        Value(entry_builder.build_alloca(ty.0, "alloca").unwrap().into())
    }

    fn while_(
        &self,
        cond: impl FnOnce(&Scope<'a, 'b>) -> Value<'a>,
        body: impl FnOnce(&Scope<'a, 'b>),
    ) {
        let cond_block = self
            .context
            .context
            .append_basic_block(self.func.0, "cond_block");
        let loop_block = self
            .context
            .context
            .append_basic_block(self.func.0, "loop_block");
        let next_block = self
            .context
            .context
            .append_basic_block(self.func.0, "next_block");

        self.builder.build_unconditional_branch(cond_block).unwrap();

        let cond_scope = Scope::new(self.context.clone(), self.func, cond_block, self.tail_arg);
        let cond_val = cond(&cond_scope);
        cond_scope
            .builder
            .build_conditional_branch(cond_val.0.into_int_value(), loop_block, next_block)
            .unwrap();

        let loop_scope = Scope::new(self.context.clone(), self.func, loop_block, self.tail_arg);
        body(&loop_scope);
        loop_scope
            .builder
            .build_unconditional_branch(cond_block)
            .unwrap();

        self.builder.position_at_end(next_block);
    }

    impl_int_cmp!(
        (eq, EQ),
        (ne, NE),
        (slt, SLT),
        (sle, SLE),
        (sgt, SGT),
        (sge, SGE),
        (ult, ULT),
        (ule, ULE),
        (ugt, UGT),
        (uge, UGE),
    );

    fn sdiv(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_int_signed_div(arg1.0.into_int_value(), arg2.0.into_int_value(), "sdiv")
                .unwrap()
                .into(),
        )
    }

    fn srem(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_int_signed_rem(arg1.0.into_int_value(), arg2.0.into_int_value(), "srem")
                .unwrap()
                .into(),
        )
    }

    fn udiv(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_int_unsigned_div(arg1.0.into_int_value(), arg2.0.into_int_value(), "udiv")
                .unwrap()
                .into(),
        )
    }

    fn urem(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_int_unsigned_rem(arg1.0.into_int_value(), arg2.0.into_int_value(), "urem")
                .unwrap()
                .into(),
        )
    }

    fn neg(&self, arg: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_int_neg(arg.0.into_int_value(), "neg")
                .unwrap()
                .into(),
        )
    }

    fn add(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_int_add(arg1.0.into_int_value(), arg2.0.into_int_value(), "add")
                .unwrap()
                .into(),
        )
    }

    fn sub(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_int_sub(arg1.0.into_int_value(), arg2.0.into_int_value(), "sub")
                .unwrap()
                .into(),
        )
    }

    fn mul(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_int_mul(arg1.0.into_int_value(), arg2.0.into_int_value(), "mul")
                .unwrap()
                .into(),
        )
    }

    impl_float_cmp!(
        (oeq, OEQ),
        (one, ONE),
        (olt, OLT),
        (ole, OLE),
        (ogt, OGT),
        (oge, OGE),
    );

    fn fneg(&self, arg: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_float_neg(arg.0.into_float_value(), "fneg")
                .unwrap()
                .into(),
        )
    }

    fn fadd(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_float_add(arg1.0.into_float_value(), arg2.0.into_float_value(), "fadd")
                .unwrap()
                .into(),
        )
    }

    fn fsub(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_float_sub(arg1.0.into_float_value(), arg2.0.into_float_value(), "fsub")
                .unwrap()
                .into(),
        )
    }

    fn fmul(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_float_mul(arg1.0.into_float_value(), arg2.0.into_float_value(), "fmul")
                .unwrap()
                .into(),
        )
    }

    fn fdiv(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_float_div(arg1.0.into_float_value(), arg2.0.into_float_value(), "fdiv")
                .unwrap()
                .into(),
        )
    }

    fn sll(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_left_shift(arg1.0.into_int_value(), arg2.0.into_int_value(), "sll")
                .unwrap()
                .into(),
        )
    }

    fn srl(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_right_shift(
                    arg1.0.into_int_value(),
                    arg2.0.into_int_value(),
                    false,
                    "srl",
                )
                .unwrap()
                .into(),
        )
    }

    fn and(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_and(arg1.0.into_int_value(), arg2.0.into_int_value(), "and")
                .unwrap()
                .into(),
        )
    }

    fn or(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_or(arg1.0.into_int_value(), arg2.0.into_int_value(), "and")
                .unwrap()
                .into(),
        )
    }

    fn not(&self, arg: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_not(arg.0.into_int_value(), "not")
                .unwrap()
                .into(),
        )
    }

    fn xor(&self, arg1: Value<'a>, arg2: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_xor(arg1.0.into_int_value(), arg2.0.into_int_value(), "xor")
                .unwrap()
                .into(),
        )
    }

    fn z_extend(&self, result_type: Type<'a>, value: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_int_z_extend(
                    value.0.into_int_value(),
                    result_type.0.into_int_type(),
                    "z_extend",
                )
                .unwrap()
                .into(),
        )
    }

    fn s_extend(&self, result_type: Type<'a>, value: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_int_s_extend(
                    value.0.into_int_value(),
                    result_type.0.into_int_type(),
                    "s_extend",
                )
                .unwrap()
                .into(),
        )
    }

    fn truncate(&self, result_type: Type<'a>, value: Value<'a>) -> Value<'a> {
        Value(
            self.builder
                .build_int_truncate(
                    value.0.into_int_value(),
                    result_type.0.into_int_type(),
                    "truncate",
                )
                .unwrap()
                .into(),
        )
    }

    fn ctpop(&self, arg: Value<'a>) -> Value<'a> {
        self.call(self.context.tal.ctpop_i64, &[arg])
    }

    fn ctlz(&self, arg: Value<'a>) -> Value<'a> {
        let zero_is_poison = self.i1(false);
        self.call(self.context.tal.ctlz_i64, &[arg, zero_is_poison])
    }

    fn cttz(&self, arg: Value<'a>) -> Value<'a> {
        let zero_is_poison = self.i1(false);
        self.call(self.context.tal.cttz_i64, &[arg, zero_is_poison])
    }
}

fn get_target_machine(
    target: cfg::LlvmConfig,
    opt_level: OptimizationLevel,
) -> Result<TargetMachine, Error> {
    Target::initialize_all(&InitializationConfig::default());

    let (target_triple, target_cpu, target_features) = match target {
        cfg::LlvmConfig::Native => (
            TargetMachine::get_default_triple(),
            TargetMachine::get_host_cpu_name().to_string(),
            TargetMachine::get_host_cpu_features().to_string(),
        ),
        cfg::LlvmConfig::Wasm => (
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

#[derive(Clone, Copy, Debug)]
pub struct ArtifactPaths<'a> {
    pub ll: Option<&'a Path>,
    pub opt_ll: Option<&'a Path>,
    pub asm: Option<&'a Path>,
    pub obj: &'a Path,
    pub exe: &'a Path,
}

fn check_valid_file_path(path: &Path) -> Result<(), Error> {
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

fn check_valid_dir_path(path: &Path) -> Result<(), Error> {
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

fn run_cc(
    _gc: GcKind,
    target: cfg::LlvmConfig,
    obj_path: &Path,
    exe_path: &Path,
) -> Result<(), Error> {
    check_valid_file_path(obj_path)?;
    check_valid_file_path(exe_path)?;

    match target {
        cfg::LlvmConfig::Native => {
            let clang = find_default_clang(ClangKind::C).map_err(Error::CouldNotFindClang)?;

            let mut tal_file = tempfile::Builder::new()
                .suffix(".o")
                .tempfile_in("")
                .map_err(Error::CouldNotCreateTempFile)?;
            tal_file
                .write_all(native::TAL_O)
                .map_err(Error::CouldNotWriteObjFile)?;
            let mut gc_file = tempfile::Builder::new()
                .suffix(".a")
                .tempfile_in("")
                .map_err(Error::CouldNotCreateTempFile)?;
            gc_file
                .write_all(native::GC_A)
                .map_err(Error::CouldNotWriteObjFile)?;

            let mut cmd = std::process::Command::new(clang.path());
            // cmd.arg("-g")
            //     .arg("-O0")
            //     .arg("-fno-omit-frame-pointer")
            //     .arg("-fPIC")
            //     .arg("-o")
            //     .arg(exe_path)
            //     .arg(obj_path)
            //     .arg(tal_file.path())
            //     .arg(gc_file.path());
            cmd.arg("-O3")
                .arg("-ffunction-sections")
                .arg("-fdata-sections")
                .arg("-fPIC")
                .arg(if cfg!(target_os = "macos") {
                    "-Wl,-dead_strip"
                } else {
                    "-Wl,--gc-sections"
                })
                .arg("-o")
                .arg(exe_path)
                .arg(obj_path)
                .arg(tal_file.path())
                .arg(gc_file.path());
            cmd.status().map_err(Error::ClangFailed)?;
        }
        cfg::LlvmConfig::Wasm => {
            // materialize files to link with
            let mut tal_file = tempfile::Builder::new()
                .suffix(".o")
                .tempfile_in("")
                .map_err(Error::CouldNotCreateTempFile)?;
            tal_file
                .write_all(wasm::TAL_O)
                .map_err(Error::CouldNotWriteObjFile)?;
            let mut malloc_file = tempfile::Builder::new()
                .suffix(".o")
                .tempfile_in("")
                .map_err(Error::CouldNotCreateTempFile)?;
            malloc_file
                .write_all(wasm::MALLOC_O)
                .map_err(Error::CouldNotWriteObjFile)?;

            check_valid_dir_path(exe_path)?;
            if !exe_path.exists() {
                std::fs::create_dir(exe_path).map_err(Error::CouldNotCreateOutputDir)?;
            }

            let index_path = exe_path.join("index.html");
            let mut index_file =
                std::fs::File::create(index_path).map_err(Error::CouldNotWriteOutputFile)?;
            index_file
                .write_all(wasm::INDEX_HTML)
                .map_err(Error::CouldNotWriteOutputFile)?;

            let wasm_loader_path = exe_path.join("wasm_loader.js");
            let mut wasm_loader_file =
                std::fs::File::create(wasm_loader_path).map_err(Error::CouldNotWriteOutputFile)?;
            wasm_loader_file
                .write_all(wasm::WASM_LOADER_JS)
                .map_err(Error::CouldNotWriteOutputFile)?;

            let clang = find_default_clang(ClangKind::C).map_err(Error::CouldNotFindClang)?;
            std::process::Command::new(clang.path())
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
        let module_tmp_file: tempfile::NamedTempFile = tempfile::Builder::new()
            .suffix(".ll")
            .tempfile_in("")
            .unwrap();

        let (_file, path) = module_tmp_file.keep().unwrap();

        module.print_to_file(&path).unwrap();
        panic!(
            "LLVM verification failed (module written to {}):\n{}",
            &path.display(),
            err.to_string()
        );
    }
}

struct FunctionValueIter<'a>(Option<values::FunctionValue<'a>>);

impl<'a> Iterator for FunctionValueIter<'a> {
    type Item = values::FunctionValue<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(fun) = self.0 {
            self.0 = fun.get_next_function();
            Some(fun)
        } else {
            None
        }
    }
}

trait ModuleExt<'a> {
    fn get_functions(&self) -> FunctionValueIter<'a>;
}

impl<'a> ModuleExt<'a> for Module<'a> {
    fn get_functions(&self) -> FunctionValueIter<'a> {
        FunctionValueIter(self.get_first_function())
    }
}

struct AllocaSizeReport {
    sizes: Vec<(String, u64)>,
}

impl std::fmt::Display for AllocaSizeReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Stack frame sizes:")?;
        writeln!(f, "----------------------------------------")?;
        for (name, size) in &self.sizes {
            writeln!(f, "{}:\n    {} bytes", name, size)?;
        }
        Ok(())
    }
}

fn analyze_alloca_sizes<'a>(target: &TargetData, module: &Module<'a>) -> AllocaSizeReport {
    let mut sizes = Vec::new();
    for fun in module.get_functions() {
        let mut size = 0;
        for bb in fun.get_basic_block_iter() {
            for instr in bb.get_instructions() {
                if instr.get_opcode() == InstructionOpcode::Alloca {
                    let type_ = instr.get_allocated_type().unwrap();
                    size += target.get_abi_size(&type_);
                }
            }
        }
        sizes.push((fun.get_name().to_string_lossy().into_owned(), size));
    }
    sizes.sort_by_key(|(_, size)| std::cmp::Reverse(*size));
    AllocaSizeReport { sizes }
}

pub fn compile_to_executable(
    gc: GcKind,
    array_kind: ArrayKind,
    program: low::Program,
    target: cfg::LlvmConfig,
    opt_level: OptimizationLevel,
    artifact_paths: ArtifactPaths,
    progress: progress_ui::ProgressMode,
) -> Result<(), Error> {
    let profile_record_rc = program
        .profile_points
        .iter()
        .any(|(_, prof_point)| prof_point.record_rc);

    let target_machine = get_target_machine(target, opt_level)?;
    let target_data = target_machine.get_target_data();
    let llvm_context = inkwell::context::Context::create();

    let module = llvm_context.create_module("module");
    module.set_triple(&target_machine.get_triple());
    module.set_data_layout(&target_machine.get_target_data().get_data_layout());

    let tal = Tal::declare(&llvm_context, &module, &target_data, gc, profile_record_rc);

    let context = Context {
        gc,
        context: &llvm_context,
        module: &module,
        target: &target_data,
        tal,
        tail_funcs: Default::default(),
        tail_targets: Default::default(),
    };

    gen_program(
        array_kind,
        program,
        context,
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

    // let alloca_sizes = analyze_alloca_sizes(&target_data, &module);
    // let mut file = std::fs::File::create("alloca_sizes.txt").unwrap();
    // writeln!(file, "{}", alloca_sizes).unwrap();

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

    run_cc(gc, target, artifact_paths.obj, artifact_paths.exe)
}
