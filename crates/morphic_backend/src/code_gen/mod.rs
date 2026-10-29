#![allow(dead_code)]

mod array;
mod cow_array;
mod fountain_pen;
mod fountain_pen_llvm;
mod persistent_array;
mod prof_report;
mod rc;
mod zero_sized_array;

#[cfg(test)]
mod test;

use crate::code_gen::array::{ArrayImpl, ArrayIoImpl};
use crate::code_gen::cow_array::{cow_array_t, cow_hole_array_t, CowArrayImpl, CowArrayIoImpl};
use crate::code_gen::fountain_pen::{Context, ProfileRc, Scope, Tal};
use crate::code_gen::fountain_pen_llvm::{compile_to_executable, ArtifactPaths};
use crate::code_gen::persistent_array::{
    persistent_array_t, persistent_hole_array_t, PersistentArrayImpl, PersistentArrayIoImpl,
};
use crate::code_gen::prof_report::{
    define_prof_report_fn, ProfilePointCounters, ProfilePointDecls,
};
use crate::code_gen::rc::{rc_ptr_t, RcBuiltin, RcBuiltinImpl};
use crate::code_gen::zero_sized_array::{
    zero_sized_array_t, zero_sized_hole_array_t, ZeroSizedArrayImpl,
};
use crate::error::Error as CrateError;
use crate::pretty_print::utils::TailFuncRenderer;
use id_collections::{IdMap, IdVec};
use id_graph_sccs::{SccKind, Sccs};
use morphic_common::config::ArrayKind;
use morphic_common::data::first_order_ast as first_ord;
use morphic_common::data::intrinsics::Intrinsic;
use morphic_common::data::low_ast as low;
use morphic_common::data::mode_annot_ast::Mode;
use morphic_common::data::num_type::{IntType, NumKind, NumLit, Signedness};
use morphic_common::data::profile as prof;
use morphic_common::data::rc_specialized_ast::{ModeScheme, ModeSchemeId, RcOp};
use morphic_common::data::tail_rec_ast::TailFuncId;
use morphic_common::pseudoprocess::{spawn_process, Child, Stdio, ValgrindConfig};
use morphic_common::util::progress_logger::{ProgressLogger, ProgressSession};
use morphic_common::{config as cfg, progress_ui};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::convert::TryInto;
use std::path::{Path, PathBuf};
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum IsZeroSized {
    NonZeroSized,
    ZeroSized,
}

#[derive(Clone)]
struct Globals<T: Context> {
    array_kind: ArrayKind,
    context: T,
    custom_raw_types: IdVec<low::CustomTypeId, low::Type>,
    custom_sizes: IdVec<low::CustomTypeId, IsZeroSized>,
    custom_schemes: IdVec<ModeSchemeId, ModeScheme>,
    profile_points: IdVec<prof::ProfilePointId, ProfilePointDecls<T>>,
}

impl<T: Context> Globals<T> {
    fn is_zero_sized(&self, type_: &low::Type) -> bool {
        is_zero_sized(type_, &|custom| self.custom_sizes[custom])
    }
}

#[derive(Clone, Debug)]
struct CustomTypeInterface<T: Context> {
    type_: T::Type,
    retain: T::FunctionValue,
    derived_retain: T::FunctionValue,
    release: T::FunctionValue,
}

impl<T: Context> CustomTypeInterface<T> {
    fn declare(globals: &Globals<T>, mode_scheme_id: ModeSchemeId, type_: &low::Type) -> Self {
        let type_ = low_type_in_context(globals, type_);
        let release =
            globals
                .context
                .declare_func(&format!("release_{}", mode_scheme_id.0), &[type_], None);
        let retain =
            globals
                .context
                .declare_func(&format!("retain_{}", mode_scheme_id.0), &[type_], None);
        let derived_retain = globals.context.declare_func(
            &format!("derived_retain_{}", mode_scheme_id.0),
            &[type_],
            None,
        );
        CustomTypeInterface {
            type_,
            release,
            retain,
            derived_retain,
        }
    }

    fn define(&self, instances: &mut Instances<T>, globals: &Globals<T>, scheme: &ModeScheme) {
        let context = &globals.context;

        // define 'retain'
        {
            let s = context.scope(self.retain);
            let arg = s.arg(0);
            gen_rc_op(DerivedRcOp::Retain, &s, instances, globals, scheme, arg);
            s.ret_void();
        }

        // define 'derived_retain'
        {
            let s = context.scope(self.derived_retain);
            let arg = s.arg(0);
            gen_rc_op(
                DerivedRcOp::DerivedRetain,
                &s,
                instances,
                globals,
                scheme,
                arg,
            );
            s.ret_void();
        }

        // define 'release'
        {
            let s = context.scope(self.release);
            let arg = s.arg(0);
            gen_rc_op(DerivedRcOp::Release, &s, instances, globals, scheme, arg);
            s.ret_void();
        }
    }
}

fn declare_profile_points<T: Context>(
    context: &T,
    program: &low::Program,
) -> IdVec<prof::ProfilePointId, ProfilePointDecls<T>> {
    let mut decls = program.profile_points.map_refs(|_, _| ProfilePointDecls {
        counters: BTreeMap::new(),
        skipped_tail_rec: BTreeSet::new(),
    });

    for (func_id, def) in &program.funcs {
        if let Some(prof_id) = def.profile_point {
            let total_calls = context.declare_global(
                &format!("total_calls_{}", func_id.0),
                context.i64_t(),
                Some(context.i64(0)),
            );

            let total_clock_nanos = context.declare_global(
                &format!("total_clock_nanos_{}", func_id.0),
                context.i64_t(),
                Some(context.i64(0)),
            );

            let (total_retain_count, total_release_count, total_rc1_count) =
                if program.profile_points[prof_id].record_rc {
                    let total_retain_count = context.declare_global(
                        &format!("total_retain_count_{}", func_id.0),
                        context.i64_t(),
                        Some(context.i64(0)),
                    );

                    let total_release_count = context.declare_global(
                        &format!("total_release_count_{}", func_id.0),
                        context.i64_t(),
                        Some(context.i64(0)),
                    );

                    let total_rc1_count = context.declare_global(
                        &format!("total_rc1_count_{}", func_id.0),
                        context.i64_t(),
                        Some(context.i64(0)),
                    );

                    (
                        Some(total_retain_count),
                        Some(total_release_count),
                        Some(total_rc1_count),
                    )
                } else {
                    (None, None, None)
                };

            let existing = decls[prof_id].counters.insert(
                func_id,
                ProfilePointCounters {
                    total_calls,
                    total_clock_nanos,
                    total_retain_count,
                    total_release_count,
                    total_rc1_count,
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

#[derive(Clone, Debug)]
enum PendingDefine {
    Rc(ModeScheme),
    Array(ModeScheme),
}

struct Instances<'a, T: Context + 'a> {
    array_io: Rc<dyn ArrayIoImpl<T> + 'a>,
    rcs: BTreeMap<ModeScheme, RcBuiltinImpl<T>>,
    arrays: BTreeMap<ModeScheme, Rc<dyn ArrayImpl<T> + 'a>>,
    pending: Vec<PendingDefine>,
}

impl<'a, T: Context + 'a> Instances<'a, T> {
    fn new(globals: &Globals<T>) -> Self {
        let mut arrays = BTreeMap::new();

        let owned_string = ModeScheme::Array(
            Mode::Owned,
            Box::new(ModeScheme::Num(first_ord::NumType::U8)),
        );
        let borrowed_string = ModeScheme::Array(
            Mode::Borrowed,
            Box::new(ModeScheme::Num(first_ord::NumType::U8)),
        );

        let (owned_string_builtin, borrowed_string_builtin, array_io) = match globals.array_kind {
            ArrayKind::Cow => {
                let owned_string_builtin = CowArrayImpl::declare(globals, &owned_string);
                let borrowed_string_builtin = CowArrayImpl::declare(globals, &borrowed_string);
                let array_io = CowArrayIoImpl::declare(
                    globals,
                    owned_string_builtin.clone(),
                    borrowed_string_builtin.clone(),
                );
                (
                    Rc::new(owned_string_builtin) as Rc<dyn ArrayImpl<T> + 'a>,
                    Rc::new(borrowed_string_builtin) as Rc<dyn ArrayImpl<T> + 'a>,
                    Rc::new(array_io) as Rc<dyn ArrayIoImpl<T> + 'a>,
                )
            }
            ArrayKind::Persistent => {
                let owned_string_builtin = PersistentArrayImpl::declare(globals, &owned_string);
                let borrowed_string_builtin =
                    PersistentArrayImpl::declare(globals, &borrowed_string);
                let array_io = PersistentArrayIoImpl::declare(
                    globals,
                    owned_string_builtin.clone(),
                    borrowed_string_builtin.clone(),
                );
                (
                    Rc::new(owned_string_builtin) as Rc<dyn ArrayImpl<T> + 'a>,
                    Rc::new(borrowed_string_builtin) as Rc<dyn ArrayImpl<T> + 'a>,
                    Rc::new(array_io) as Rc<dyn ArrayIoImpl<T> + 'a>,
                )
            }
        };

        arrays.insert(owned_string.clone(), owned_string_builtin);
        arrays.insert(borrowed_string.clone(), borrowed_string_builtin);

        Self {
            array_io,
            rcs: BTreeMap::new(),
            arrays,
            pending: vec![
                PendingDefine::Array(owned_string),
                PendingDefine::Array(borrowed_string),
            ],
        }
    }

    fn get_array(
        &mut self,
        globals: &Globals<T>,
        mode_scheme: &ModeScheme,
    ) -> Rc<dyn ArrayImpl<T> + 'a> {
        if let Some(existing) = self.arrays.get(mode_scheme) {
            return existing.clone();
        }

        let zst = match mode_scheme {
            ModeScheme::Array(_, item_scheme) | ModeScheme::HoleArray(_, item_scheme) => {
                globals.is_zero_sized(&item_scheme.as_type())
            }
            _ => unreachable!(),
        };

        let new_builtin: Rc<dyn ArrayImpl<T> + 'a> = if zst {
            Rc::new(ZeroSizedArrayImpl::declare(globals, self, &mode_scheme))
        } else {
            match globals.array_kind {
                ArrayKind::Cow => Rc::new(CowArrayImpl::declare(globals, &mode_scheme)),
                ArrayKind::Persistent => {
                    Rc::new(PersistentArrayImpl::declare(globals, &mode_scheme))
                }
            }
        };

        self.arrays.insert(mode_scheme.clone(), new_builtin.clone());

        self.pending.push(PendingDefine::Array(mode_scheme.clone()));

        new_builtin
    }

    fn get_rc(&mut self, globals: &Globals<T>, mode_scheme: &ModeScheme) -> RcBuiltinImpl<T> {
        if let Some(existing) = self.rcs.get(&mode_scheme) {
            return existing.clone();
        }

        let new_builtin = RcBuiltinImpl::declare(globals, &mode_scheme);
        self.rcs.insert(mode_scheme.clone(), new_builtin.clone());
        self.pending.push(PendingDefine::Rc(mode_scheme.clone()));
        return new_builtin;
    }

    fn define(
        &mut self,
        globals: &Globals<T>,
        // TODO: fix progress tracker someday?
        _rc_progress: impl ProgressLogger,
        _array_progress: impl ProgressLogger,
    ) {
        self.array_io.define(globals);

        while let Some(pending_op) = self.pending.pop() {
            match pending_op {
                PendingDefine::Rc(scheme) => {
                    let rc_builtin = self.rcs.get(&scheme).unwrap().clone();
                    rc_builtin.define(globals, self);
                }
                PendingDefine::Array(scheme) => {
                    let array_builtin = self.arrays.get(&scheme).unwrap().clone();
                    array_builtin.define(globals, self);
                }
            }
        }
    }
}

fn low_type_in_context<T: Context>(globals: &Globals<T>, type_: &low::Type) -> T::Type {
    match type_ {
        low::Type::Bool => globals.context.i1_t(),
        low::Type::Num(num) => globals.context.num_t(*num),
        low::Type::Tuple(item_types) => globals.context.struct_t(
            &item_types
                .iter()
                .map(|t| low_type_in_context(globals, t))
                .collect::<Vec<_>>(),
        ),
        low::Type::Variants(variants) => globals.context.variants_type_as_type(
            &globals.context.variants_t(
                &variants
                    .values()
                    .map(|t| low_type_in_context(globals, t))
                    .collect::<Vec<_>>(),
            ),
        ),
        low::Type::Custom(type_id) => {
            low_type_in_context(globals, &globals.custom_raw_types[type_id])
        }
        low::Type::Array(item_type) => {
            if globals.is_zero_sized(item_type) {
                zero_sized_array_t(&globals.context)
            } else {
                match globals.array_kind {
                    ArrayKind::Cow => cow_array_t(&globals.context),
                    ArrayKind::Persistent => persistent_array_t(&globals.context),
                }
            }
        }
        low::Type::HoleArray(item_type) => {
            if globals.is_zero_sized(item_type) {
                zero_sized_hole_array_t(&globals.context)
            } else {
                match globals.array_kind {
                    ArrayKind::Cow => cow_hole_array_t(&globals.context),
                    ArrayKind::Persistent => persistent_hole_array_t(&globals.context),
                }
            }
        }
        low::Type::Boxed(_) => rc_ptr_t(&globals.context),
    }
}

#[derive(Copy, Clone, Debug)]
pub enum DerivedRcOp {
    DerivedRetain,
    Retain,
    Release,
}

fn gen_rc_op<T: Context>(
    op: DerivedRcOp,
    s: &T::Scope,
    instances: &mut Instances<T>,
    globals: &Globals<T>,
    scheme: &ModeScheme,
    arg: T::Value,
) {
    if s.is_gc_on() {
        s.panic(
            "gen_rc_op: cannot use rc operations in garbage collected mode\n",
            &[],
        );
        return;
    }

    match scheme {
        ModeScheme::Bool => {}
        ModeScheme::Num(_) => {}
        ModeScheme::Array(_, _) => match op {
            DerivedRcOp::Retain => {
                let retain_func = instances.get_array(globals, scheme).retain_array();
                s.call_void(retain_func, &[arg]);
            }
            DerivedRcOp::DerivedRetain => {
                let derived_retain_func =
                    instances.get_array(globals, scheme).derived_retain_array();
                s.call_void(derived_retain_func, &[arg]);
            }
            DerivedRcOp::Release => {
                let release_func = instances.get_array(globals, scheme).release_array();
                s.call_void(release_func, &[arg]);
            }
        },
        ModeScheme::HoleArray(_, _) => match op {
            DerivedRcOp::Retain => {
                let retain_func = instances.get_array(globals, scheme).retain_hole();
                s.call_void(retain_func, &[arg]);
            }
            DerivedRcOp::DerivedRetain => {
                let derived_retain_func =
                    instances.get_array(globals, scheme).derived_retain_hole();
                s.call_void(derived_retain_func, &[arg]);
            }
            DerivedRcOp::Release => {
                let release_func = instances.get_array(globals, scheme).release_hole();
                s.call_void(release_func, &[arg]);
            }
        },
        ModeScheme::Boxed(_, _) => match op {
            DerivedRcOp::Retain => {
                let retain_func = instances.get_rc(globals, scheme).retain();
                s.call_void(retain_func, &[arg]);
            }
            DerivedRcOp::DerivedRetain => {
                let derived_retain_func = instances.get_rc(globals, scheme).derived_retain();
                s.call_void(derived_retain_func, &[arg]);
            }
            DerivedRcOp::Release => {
                let release_func = instances.get_rc(globals, scheme).release();
                s.call_void(release_func, &[arg]);
            }
        },
        ModeScheme::Tuple(item_types) => {
            for i in 0..item_types.len() {
                let current_item = s.field(arg, i.try_into().unwrap());
                gen_rc_op(op, s, instances, globals, &item_types[i], current_item);
            }
        }
        ModeScheme::Variants(variant_schemes) => {
            // TODO: optimize this (or maybe refactor previous passes to get rid of mode schemes...)
            let variants = variant_schemes
                .values()
                .map(|s| low_type_in_context(globals, &s.as_type()))
                .collect::<Vec<_>>();
            let type_ = s.variants_t(&variants);
            s.variants_switch(&type_, arg, |s, id, content| {
                gen_rc_op(
                    op,
                    s,
                    instances,
                    globals,
                    &variant_schemes[&first_ord::VariantId(id as usize)],
                    content,
                );
            });
        }
        ModeScheme::Custom(mode_scheme_id, _type_id) => {
            gen_rc_op(
                op,
                s,
                instances,
                globals,
                &globals.custom_schemes[mode_scheme_id],
                arg,
            );
        }
    }
}

// Helper function to check divisor for non-zero using s._ API. `zero` must be a zero constant of
// the divisor's type.
fn check_divisor_nonzero<T: Scope>(s: &T, divisor: T::Value, zero: T::Value) {
    s.if_(s.eq(divisor, zero), |s| {
        s.panic("panicked due to division by zero\n", &[]);
    });
}

// Helper function to extract binary operation arguments using s._ API
fn extract_binop_args<T: Scope>(s: &T, args: T::Value) -> (T::Value, T::Value) {
    let lhs = s.field(args, 0);
    let rhs = s.field(args, 1);
    (lhs, rhs)
}

/// Reduces a shift amount mod the operand's width, as the shift intrinsics require.  Shifting by
/// at least the width produces a poison value, so we mask the amount by `width - 1`.  This appears
/// to be what rustc does.
fn mask_shift_amount<T: Scope>(s: &T, int: IntType, amount: T::Value) -> T::Value {
    let mask = s.int(int, u64::from(int.bits() - 1));
    s.and(amount, mask)
}

fn gen_expr<T: Context>(
    s: &T::Scope,
    instances: &mut Instances<T>,
    globals: &Globals<T>,
    tail_targets: &IdVec<TailFuncId, T::TailTarget>,
    expr: &low::Expr,
    funcs: &IdVec<low::CustomFuncId, T::FunctionValue>,
    locals: &mut IdVec<low::LocalId, T::Value>,
) -> T::Value {
    use low::Expr as E;
    match expr {
        E::Local(local_id) => locals[local_id].into(),
        E::Call(func_id, local_id) => s.call(funcs[func_id], &[locals[local_id]]),
        E::TailCall(tail_id, local_id) => s.tail_call(tail_targets[tail_id], locals[local_id]),
        E::If(local_id, then_expr, else_expr) => s.if_expr(locals[local_id], |s, cond| {
            gen_expr(
                s,
                instances,
                globals,
                tail_targets,
                if cond { then_expr } else { else_expr },
                funcs,
                locals,
            )
        }),

        E::LetMany(bindings, local_id) => {
            let count = locals.count();
            for (_, binding_expr, _metadata) in bindings {
                let binding_val = gen_expr(
                    s,
                    instances,
                    globals,
                    tail_targets,
                    binding_expr,
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
            s.unreachable();
            s.undef(low_type_in_context(globals, type_))
        }
        E::Tuple(fields) => s.make_tup(&fields.into_iter().map(|x| locals[x]).collect::<Vec<_>>()),
        E::TupleField(local_id, elem) => s.field(locals[local_id], (*elem).try_into().unwrap()),
        E::WrapVariant(variants, variant_id, local_id) => {
            let variants = variants
                .values()
                .map(|v| low_type_in_context(globals, v))
                .collect::<Vec<_>>();
            let ty = s.variants_t(&variants[..]);
            let local = locals[local_id];
            s.variants_new(&ty, local, variant_id.0.try_into().unwrap())
        }
        E::UnwrapVariant(variants, variant_id, local_id) => {
            let variants = variants
                .values()
                .map(|v| low_type_in_context(globals, v))
                .collect::<Vec<_>>();
            let ty = s.variants_t(&variants[..]);
            let local = locals[local_id];
            s.variants_get(&ty, local, variant_id.0.try_into().unwrap())
        }
        E::WrapCustom(_type_id, local_id) => locals[local_id].into(),
        E::UnwrapCustom(_type_id, local_id) => locals[local_id].into(),
        E::CheckVariant(variant_id, local_id) => {
            let local = locals[local_id];
            let discrim = s.variants_get_discrim(locals[local_id]);
            let variant = variant_id.0.try_into().unwrap();
            let expected_value = s.variants_new_discrim(s.get_type(local), variant);
            s.eq(expected_value, discrim)
        }
        E::WrapBoxed(local_id, inner_type) => {
            let builtin = instances.get_rc(globals, inner_type);
            s.call(builtin.new(), &[locals[local_id]])
        }
        E::UnwrapBoxed(local_id, input_scheme, output_scheme) => {
            let builtin = instances.get_rc(globals, input_scheme);
            let ptr = s.call(builtin.get(), &[locals[local_id]]);
            let result = s.ptr_get(low_type_in_context(globals, &output_scheme.as_type()), ptr);
            result
        }
        E::RcOp(mode_scheme, rc_op, local_id) => {
            if !s.is_gc_on() {
                gen_rc_op(
                    match rc_op {
                        RcOp::Retain => DerivedRcOp::Retain,
                        RcOp::Release => DerivedRcOp::Release,
                    },
                    s,
                    instances,
                    globals,
                    mode_scheme,
                    locals[local_id],
                );
            }
            s.make_tup(&[])
        }
        E::Intrinsic(intr, local_id) => {
            let arg = locals[local_id];
            match *intr {
                Intrinsic::Add(num) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    match num.kind() {
                        NumKind::Int(_) => s.add(lhs, rhs),
                        NumKind::Float(_) => s.fadd(lhs, rhs),
                    }
                }
                Intrinsic::Sub(num) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    match num.kind() {
                        NumKind::Int(_) => s.sub(lhs, rhs),
                        NumKind::Float(_) => s.fsub(lhs, rhs),
                    }
                }
                Intrinsic::Mul(num) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    match num.kind() {
                        NumKind::Int(_) => s.mul(lhs, rhs),
                        NumKind::Float(_) => s.fmul(lhs, rhs),
                    }
                }
                Intrinsic::Div(num) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    match num.kind() {
                        NumKind::Int(int) => {
                            check_divisor_nonzero(s, rhs, s.int(int, 0));
                            match int.signedness() {
                                Signedness::Unsigned => s.udiv(lhs, rhs),
                                Signedness::Signed => s.sdiv(lhs, rhs),
                            }
                        }
                        NumKind::Float(_) => s.fdiv(lhs, rhs),
                    }
                }
                Intrinsic::Neg(num) => match num.kind() {
                    NumKind::Int(_) => s.neg(arg),
                    NumKind::Float(_) => s.fneg(arg),
                },
                Intrinsic::Eq(num) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    match num.kind() {
                        NumKind::Int(_) => s.eq(lhs, rhs),
                        NumKind::Float(_) => s.oeq(lhs, rhs),
                    }
                }
                Intrinsic::Lt(num) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    match num.kind() {
                        NumKind::Int(int) => match int.signedness() {
                            Signedness::Unsigned => s.ult(lhs, rhs),
                            Signedness::Signed => s.slt(lhs, rhs),
                        },
                        NumKind::Float(_) => s.olt(lhs, rhs),
                    }
                }
                Intrinsic::Lte(num) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    match num.kind() {
                        NumKind::Int(int) => match int.signedness() {
                            Signedness::Unsigned => s.ule(lhs, rhs),
                            Signedness::Signed => s.sle(lhs, rhs),
                        },
                        NumKind::Float(_) => s.ole(lhs, rhs),
                    }
                }
                Intrinsic::Gt(num) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    match num.kind() {
                        NumKind::Int(int) => match int.signedness() {
                            Signedness::Unsigned => s.ugt(lhs, rhs),
                            Signedness::Signed => s.sgt(lhs, rhs),
                        },
                        NumKind::Float(_) => s.ogt(lhs, rhs),
                    }
                }
                Intrinsic::Gte(num) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    match num.kind() {
                        NumKind::Int(int) => match int.signedness() {
                            Signedness::Unsigned => s.uge(lhs, rhs),
                            Signedness::Signed => s.sge(lhs, rhs),
                        },
                        NumKind::Float(_) => s.oge(lhs, rhs),
                    }
                }
                Intrinsic::EqBool => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    s.eq(lhs, rhs)
                }
                Intrinsic::Not => s.not(arg),
                Intrinsic::BitAnd(_) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    s.and(lhs, rhs)
                }
                Intrinsic::BitOr(_) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    s.or(lhs, rhs)
                }
                Intrinsic::BitXor(_) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    s.xor(lhs, rhs)
                }
                Intrinsic::BitNot(_) => s.not(arg),
                Intrinsic::ShiftLeft(int) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    s.sll(lhs, mask_shift_amount(s, int, rhs))
                }
                Intrinsic::ShiftRight(int) => {
                    let (lhs, rhs) = extract_binop_args(s, arg);
                    s.srl(lhs, mask_shift_amount(s, int, rhs))
                }
                Intrinsic::Ctpop(int) => s.ctpop(int, arg),
                Intrinsic::Ctlz(int) => s.ctlz(int, arg),
                Intrinsic::Cttz(int) => s.cttz(int, arg),
                Intrinsic::Convert(from, to) => match (from.kind(), to.kind()) {
                    (NumKind::Int(from), NumKind::Int(to)) => match to.bits().cmp(&from.bits()) {
                        Ordering::Greater => match from.signedness() {
                            Signedness::Unsigned => s.z_extend(s.int_t(to), arg),
                            Signedness::Signed => s.s_extend(s.int_t(to), arg),
                        },
                        Ordering::Less => s.truncate(s.int_t(to), arg),
                        // The types differ only in signedness, which LLVM integers don't carry,
                        // so the value already has the target type.
                        Ordering::Equal => arg,
                    },
                    (NumKind::Int(from), NumKind::Float(to)) => match from.signedness() {
                        Signedness::Unsigned => s.ui_to_fp(s.float_t(to), arg),
                        Signedness::Signed => s.si_to_fp(s.float_t(to), arg),
                    },
                    (NumKind::Float(from), NumKind::Int(to)) => s.fp_to_int_sat(from, to, arg),
                    (NumKind::Float(from), NumKind::Float(to)) => {
                        match to.bits().cmp(&from.bits()) {
                            Ordering::Greater => s.fp_extend(s.float_t(to), arg),
                            Ordering::Less => s.fp_truncate(s.float_t(to), arg),
                            // The two float types have different widths.
                            Ordering::Equal => unreachable!(),
                        }
                    }
                },
            }
        }
        E::ArrayOp(mode_scheme, array_op) => {
            let builtin = instances.get_array(globals, mode_scheme);
            match array_op {
                low::ArrayOp::New => s.call(builtin.new(), &[]),
                low::ArrayOp::Get(array_id, index_id) => {
                    s.call(builtin.get(), &[locals[array_id], locals[index_id]])
                }
                low::ArrayOp::Extract(array_id, index_id) => {
                    s.call(builtin.extract(), &[locals[array_id], locals[index_id]])
                }
                low::ArrayOp::Len(array_id) => s.call(builtin.len(), &[locals[array_id]]),
                low::ArrayOp::Push(array_id, item_id) => {
                    s.call(builtin.push(), &[locals[array_id], locals[item_id]])
                }
                low::ArrayOp::Pop(array_id) => s.call(builtin.pop(), &[locals[array_id]]),
                low::ArrayOp::Replace(array_id, item_id) => {
                    s.call(builtin.replace(), &[locals[array_id], locals[item_id]])
                }
                low::ArrayOp::Reserve(array_id, capacity_id) => {
                    s.call(builtin.reserve(), &[locals[array_id], locals[capacity_id]])
                }
            }
        }
        E::IoOp(io_op) => {
            let builtin_io = &instances.array_io;
            match io_op {
                low::IoOp::Input => s.call(builtin_io.input(), &[]),
                low::IoOp::Output(_input_type, array_id) => {
                    s.call_void(builtin_io.output(), &[locals[array_id]]);
                    s.undef(s.struct_t(&[]))
                }
            }
        }
        E::Panic(ret_type, _input_type, message_id) => {
            let builtin_io = &instances.array_io;
            s.call_void(builtin_io.output_error(), &[locals[message_id]]);
            s.call_void(globals.context.tal().exit(), &[s.i32(1)]);
            s.unreachable();
            s.undef(low_type_in_context(globals, ret_type))
        }
        E::BoolLit(val) => s.i1(*val),
        E::NumLit(lit) => match lit {
            NumLit::I8(val) => s.i8(*val as u8),
            NumLit::I16(val) => s.i16(*val as u16),
            NumLit::I32(val) => s.i32(*val as u32),
            NumLit::I64(val) => s.i64(*val as u64),
            NumLit::U8(val) => s.i8(*val),
            NumLit::U16(val) => s.i16(*val),
            NumLit::U32(val) => s.i32(*val),
            NumLit::U64(val) => s.i64(*val),
            NumLit::F32(val) => s.f32(*val),
            NumLit::F64(val) => s.f64(*val),
        },
    }
}

fn gen_function<T: Context>(
    globals: &Globals<T>,
    instances: &mut Instances<T>,
    funcs: &IdVec<low::CustomFuncId, T::FunctionValue>,
    func_id: low::CustomFuncId,
    low_func: &low::FuncDef,
    func_decl: T::FunctionValue,
    tail_targets: &IdVec<TailFuncId, T::TailTarget>,
) {
    let s = globals.context.scope(func_decl);

    let (start_clock_nanos, start_retain_count, start_release_count, start_rc1_count) =
        if let Some(prof_id) = low_func.profile_point {
            let start_clock_nanos = s.call(globals.context.tal().prof_clock_nanos(), &[]);

            let counters = &globals.profile_points[prof_id].counters[&func_id];
            let start_retain_count = if counters.total_retain_count.is_some() {
                let start_retain_count = s.call(
                    globals.context.tal().prof_rc().unwrap().get_retain_count(),
                    &[],
                );
                Some(start_retain_count)
            } else {
                None
            };
            let start_release_count = if counters.total_release_count.is_some() {
                let start_release_count = s.call(
                    globals.context.tal().prof_rc().unwrap().get_release_count(),
                    &[],
                );
                Some(start_release_count)
            } else {
                None
            };
            let start_rc1_count = if counters.total_rc1_count.is_some() {
                let start_rc1_count = s.call(
                    globals.context.tal().prof_rc().unwrap().get_rc1_count(),
                    &[],
                );
                Some(start_rc1_count)
            } else {
                None
            };

            (
                Some(start_clock_nanos),
                start_retain_count,
                start_release_count,
                start_rc1_count,
            )
        } else {
            (None, None, None, None)
        };

    let gen_prof_epilogue = || {
        if let Some(prof_id) = low_func.profile_point {
            let end_clock_nanos = s.call(globals.context.tal().prof_clock_nanos(), &[]);
            let diff_clock_nanos = s.sub(end_clock_nanos, start_clock_nanos.unwrap());

            let counters = &globals.profile_points[prof_id].counters[&func_id];

            let old_clock_nanos = s.global_get(s.i64_t(), counters.total_clock_nanos);
            let new_clock_nanos = s.add(old_clock_nanos, diff_clock_nanos);
            s.global_set(counters.total_clock_nanos, new_clock_nanos);

            let gen_rc_count_update =
                |start_rc_count: Option<T::Value>,
                 total_rc_count: Option<T::GlobalValue>,
                 tal_fn: fn(&T::ProfileRc) -> T::FunctionValue| match (
                    start_rc_count,
                    total_rc_count,
                ) {
                    (Some(start_rc_count), Some(total_rc_count)) => {
                        let end_rc_count =
                            s.call(tal_fn(globals.context.tal().prof_rc().unwrap()), &[]);
                        let old_rc_count = s.global_get(s.i64_t(), total_rc_count);
                        s.global_set(
                            total_rc_count,
                            s.add(old_rc_count, s.sub(end_rc_count, start_rc_count)),
                        )
                    }
                    (None, None) => {}
                    _ => unreachable!(),
                };

            gen_rc_count_update(start_retain_count, counters.total_retain_count, |prof_rc| {
                prof_rc.get_retain_count()
            });

            gen_rc_count_update(
                start_release_count,
                counters.total_release_count,
                |prof_rc| prof_rc.get_release_count(),
            );

            gen_rc_count_update(start_rc1_count, counters.total_rc1_count, |prof_rc| {
                prof_rc.get_rc1_count()
            });

            let old_rc_count = s.global_get(s.i64_t(), counters.total_calls);
            s.global_set(counters.total_calls, s.add(old_rc_count, s.i64(1)))
        }
    };

    // Generate main body
    {
        let mut locals = IdVec::from_vec(vec![s.arg(0)]);
        let ret_value = gen_expr(
            &s,
            instances,
            globals,
            &tail_targets,
            &low_func.body,
            funcs,
            &mut locals,
        );
        gen_prof_epilogue();
        s.ret(ret_value)
    }

    // Generate tail function bodies
    for (tail_id, tail_target) in tail_targets {
        let s = globals.context.tail_scope(*tail_target);
        let mut locals = IdVec::from_vec(vec![s.tail_arg()]);
        let ret_value = gen_expr(
            &s,
            instances,
            globals,
            &tail_targets,
            &low_func.tail_funcs[tail_id].body,
            funcs,
            &mut locals,
        );
        gen_prof_epilogue();
        s.ret(ret_value)
    }
}

fn declare_customs<T: Context>(
    globals: &Globals<T>,
) -> IdVec<ModeSchemeId, CustomTypeInterface<T>> {
    globals.custom_schemes.map_refs(|scheme_id, scheme| {
        CustomTypeInterface::declare(globals, scheme_id, &scheme.as_type())
    })
}

fn is_zero_sized(type_: &low::Type, zsts: &impl Fn(low::CustomTypeId) -> IsZeroSized) -> bool {
    match type_ {
        low::Type::Bool
        | low::Type::Num(_)
        | low::Type::Array(_)
        | low::Type::HoleArray(_)
        | low::Type::Boxed(_)
        | low::Type::Variants(_) => false, // always has a (non-zero-sized) discriminant
        low::Type::Tuple(items) => items.iter().all(|item| is_zero_sized(item, zsts)),
        low::Type::Custom(custom) => zsts(*custom) == IsZeroSized::ZeroSized,
    }
}

// We need to know zero-sizedness *before* we can decide on an appropriate backend representation
// for a given type because we need to decide whether to use a `ZeroSizedArray`. We can't just rely
// on e.g. LLVM's `get_abi_size`.
fn find_zero_sized(
    custom_types: &IdVec<low::CustomTypeId, low::Type>,
) -> IdVec<low::CustomTypeId, IsZeroSized> {
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

    let sccs: Sccs<usize, _> = id_graph_sccs::find_components(custom_types.count(), |id| {
        let mut deps = BTreeSet::new();
        add_size_deps(&custom_types[id], &mut deps);
        deps
    });

    let dep_order: Vec<_> = sccs
        .into_iter()
        .map(|(_, scc)| {
            debug_assert_eq!(scc.kind, SccKind::Acyclic);
            scc.nodes[0]
        })
        .collect();

    let mut zsts: IdMap<low::CustomTypeId, IsZeroSized> = IdMap::new();
    for &type_id in &dep_order {
        let zero_sized = is_zero_sized(&custom_types[type_id], &|other| {
            *zsts.get(other).expect(
                "the zero-sizedness of custom types should be determined in dependency order",
            )
        });
        zsts.insert(
            type_id,
            if zero_sized {
                IsZeroSized::ZeroSized
            } else {
                IsZeroSized::NonZeroSized
            },
        );
    }
    zsts.to_id_vec(custom_types.count())
}

pub fn gen_program<T: Context>(
    array_kind: ArrayKind,
    program: low::Program,
    context: T,
    func_progress: impl ProgressLogger,
    rc_progress: impl ProgressLogger,
    array_progress: impl ProgressLogger,
    type_progress: impl ProgressLogger,
) {
    let profile_points = declare_profile_points(&context, &program);

    let custom_sizes = find_zero_sized(&program.custom_types.types);

    let globals = Globals {
        array_kind,
        context,
        custom_schemes: program.schemes,
        custom_sizes,
        custom_raw_types: program.custom_types.types,
        profile_points,
    };

    let context = &globals.context;

    let custom_types = declare_customs(&globals);

    let mut instances = Instances::new(&globals);

    let mut func_progress = func_progress.start_session(Some(program.funcs.len()));

    let func_renderer = TailFuncRenderer::from_symbols(&program.func_symbols);

    let mut func_decls = IdVec::new();
    let mut tail_targets = IdVec::new();
    for (func_id, func_def) in &program.funcs {
        let name = format!("{}_{}", func_renderer.render(&func_id), func_id.0);
        let ret_ty = low_type_in_context(&globals, &func_def.ret_type);
        let arg_ty = low_type_in_context(&globals, &func_def.arg_type);

        if func_def.tail_funcs.len() > 0 {
            let tail_arg_tys = func_def
                .tail_funcs
                .iter()
                .map(|(_, tail_func)| low_type_in_context(&globals, &tail_func.arg_type))
                .collect::<Vec<_>>();

            let (func, tails) =
                context.declare_tail_func(&name, &[arg_ty], Some(ret_ty), &tail_arg_tys);
            let _ = func_decls.push(func);
            let _ = tail_targets.push(IdVec::from_vec(tails));
        } else {
            let func = context.declare_func(&name, &[arg_ty], Some(ret_ty));
            let _ = func_decls.push(func);
            let _ = tail_targets.push(IdVec::new());
        }
    }

    for (func_id, low_func) in &program.funcs {
        gen_function(
            &globals,
            &mut instances,
            &func_decls,
            func_id,
            low_func,
            func_decls[func_id],
            &tail_targets[func_id],
        );
        func_progress.update(1);
    }

    func_progress.finish();

    let mut type_progress = type_progress.start_session(Some(custom_types.len()));
    for (type_id, type_decls) in &custom_types {
        type_decls.define(&mut instances, &globals, &globals.custom_schemes[type_id]);
        type_progress.update(1);
    }
    type_progress.finish();

    instances.define(&globals, rc_progress, array_progress);

    let main = context.declare_main_func();
    let s = context.scope(main);
    let unit_type = context.struct_t(&[]);
    s.call(func_decls[program.main], &[s.undef(unit_type)]);

    if program.profile_points.len() > 0 {
        let prof_report_fn =
            define_prof_report_fn(context, &program.profile_points, &globals.profile_points);

        s.call_void(prof_report_fn, &[]);
    }

    s.ret(s.i32(0));
}

pub fn run(
    stdio: Stdio,
    program: low::Program,
    config: &cfg::LlvmConfig,
    valgrind: Option<ValgrindConfig>,
) -> std::result::Result<Child, CrateError> {
    let target = cfg::TargetConfig::Native;
    let opt_level = cfg::default_llvm_opt_level();

    let obj_path = tempfile::Builder::new()
        .suffix(".o")
        .tempfile_in("")
        .map_err(|err| CrateError::CodeGenFailed(Error::CouldNotCreateTempFile(err)))?
        .into_temp_path();

    let output_path = tempfile::Builder::new()
        .prefix(".tmp-exe-")
        .tempfile_in("")
        .map_err(|err| CrateError::CodeGenFailed(Error::CouldNotCreateTempFile(err)))?
        .into_temp_path();

    compile_to_executable(
        config.gc_kind,
        config.array_kind,
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
    )
    .map_err(CrateError::CodeGenFailed)?;

    std::mem::drop(obj_path);

    spawn_process(stdio, output_path, valgrind)
        .map_err(|err| CrateError::CodeGenFailed(Error::CouldNotSpawnChild(err)))
}

pub fn build(
    program: low::Program,
    artifact_dir: Option<&cfg::ArtifactDir>,
    output_path: &Path,
    progress: progress_ui::ProgressMode,
    config: &cfg::LlvmConfig,
) -> std::result::Result<(), CrateError> {
    if let Some(artifact_dir) = artifact_dir {
        compile_to_executable(
            config.gc_kind,
            config.array_kind,
            program,
            config.target,
            config.opt_level,
            ArtifactPaths {
                ll: Some(&artifact_dir.artifact_path("ll")),
                opt_ll: Some(&artifact_dir.artifact_path("opt.ll")),
                asm: Some(&artifact_dir.artifact_path("s")),
                obj: &artifact_dir.artifact_path("o"),
                exe: output_path,
            },
            progress,
        )
        .map_err(CrateError::CodeGenFailed)
    } else {
        let obj_path = tempfile::Builder::new()
            .suffix(".o")
            .tempfile_in("")
            .map_err(|err| CrateError::CodeGenFailed(Error::CouldNotCreateTempFile(err)))?
            .into_temp_path();

        compile_to_executable(
            config.gc_kind,
            config.array_kind,
            program,
            config.target,
            config.opt_level,
            ArtifactPaths {
                ll: None,
                opt_ll: None,
                asm: None,
                obj: &obj_path,
                exe: output_path,
            },
            progress,
        )
        .map_err(CrateError::CodeGenFailed)
    }
}
