#![allow(dead_code)]

mod array;
mod cow_array;
mod fountain_pen;
mod fountain_pen_java;
mod fountain_pen_llvm;
mod java_builder;
mod prof_report;
mod rc;
mod zero_sized_array;

#[cfg(test)]
mod test;

use crate::code_gen::array::ArrayImpl;
use crate::code_gen::cow_array::{cow_array_t, cow_hole_array_t, CowArrayImpl, CowArrayIoImpl};
use crate::code_gen::fountain_pen::{Context, ProfileRc, Scope, Tal};
use crate::code_gen::fountain_pen_llvm::{compile_to_executable, ArtifactPaths};
use crate::code_gen::prof_report::{
    define_prof_report_fn, ProfilePointCounters, ProfilePointDecls,
};
use crate::code_gen::rc::{rc_ptr_t, RcBuiltin, RcBuiltinImpl};
use crate::code_gen::zero_sized_array::ZeroSizedArrayImpl;
use crate::error::Error as CrateError;
use crate::pretty_print::utils::TailFuncRenderer;
use crate::BuildConfig;
use id_collections::IdVec;
use morphic_common::data::first_order_ast as first_ord;
use morphic_common::data::intrinsics::Intrinsic;
use morphic_common::data::low_ast as low;
use morphic_common::data::mode_annot_ast::Mode;
use morphic_common::data::profile as prof;
use morphic_common::data::rc_specialized_ast::{ModeScheme, ModeSchemeId, RcOp};
use morphic_common::data::tail_rec_ast::TailFuncId;
use morphic_common::pseudoprocess::{spawn_process, Child, Stdio, ValgrindConfig};
use morphic_common::util::progress_logger::{ProgressLogger, ProgressSession};
use morphic_common::{config as cfg, progress_ui};
use std::collections::{BTreeMap, BTreeSet};
use std::convert::TryInto;
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum IsZeroSized {
    NonZeroSized,
    ZeroSized,
}

#[derive(Clone)]
struct Globals<T: Context> {
    context: T,
    custom_raw_types: IdVec<low::CustomTypeId, low::Type>,
    custom_schemes: IdVec<ModeSchemeId, ModeScheme>,
    profile_points: IdVec<prof::ProfilePointId, ProfilePointDecls<T>>,
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
    CowArray(ModeScheme),
}

struct Instances<'a, T: Context + 'a> {
    cow_array_io: CowArrayIoImpl<T>,
    rcs: BTreeMap<ModeScheme, RcBuiltinImpl<T>>,
    cow_arrays: BTreeMap<ModeScheme, Rc<dyn ArrayImpl<T> + 'a>>,
    pending: Vec<PendingDefine>,
}

impl<'a, T: Context + 'a> Instances<'a, T> {
    fn new(globals: &Globals<T>) -> Self {
        let mut cow_arrays = BTreeMap::new();

        let owned_string = ModeScheme::Array(
            Mode::Owned,
            Box::new(ModeScheme::Num(first_ord::NumType::Byte)),
        );
        let borrowed_string = ModeScheme::Array(
            Mode::Borrowed,
            Box::new(ModeScheme::Num(first_ord::NumType::Byte)),
        );

        let owned_string_cow_builtin = CowArrayImpl::declare(globals, &owned_string);

        let borrowed_string_cow_builtin = CowArrayImpl::declare(globals, &borrowed_string);

        cow_arrays.insert(
            owned_string.clone(),
            Rc::new(owned_string_cow_builtin.clone()) as Rc<dyn ArrayImpl<T> + 'a>,
        );
        cow_arrays.insert(
            borrowed_string.clone(),
            Rc::new(borrowed_string_cow_builtin.clone()) as Rc<dyn ArrayImpl<T> + 'a>,
        );

        let cow_array_io: CowArrayIoImpl<T> = CowArrayIoImpl::declare(
            &globals.context,
            owned_string_cow_builtin,
            borrowed_string_cow_builtin,
        );

        Self {
            cow_array_io: cow_array_io,
            rcs: BTreeMap::new(),
            cow_arrays: cow_arrays,
            pending: vec![
                PendingDefine::CowArray(owned_string),
                PendingDefine::CowArray(borrowed_string),
            ],
        }
    }

    fn get_cow_array(
        &mut self,
        globals: &Globals<T>,
        mode_scheme: &ModeScheme,
    ) -> Rc<dyn ArrayImpl<T> + 'a> {
        if let Some(existing) = self.cow_arrays.get(mode_scheme) {
            return existing.clone();
        }

        let trivial = globals
            .context
            .is_iso_to_unit(low_type_in_context(globals, &mode_scheme.as_type()));

        let new_builtin: Rc<dyn ArrayImpl<T> + 'a> = if trivial {
            Rc::new(ZeroSizedArrayImpl::declare(globals, self, &mode_scheme))
        } else {
            Rc::new(CowArrayImpl::declare(globals, &mode_scheme))
        };

        self.cow_arrays
            .insert(mode_scheme.clone(), new_builtin.clone());

        self.pending
            .push(PendingDefine::CowArray(mode_scheme.clone()));

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
        _cow_progress: impl ProgressLogger,
    ) {
        self.cow_array_io.define(&globals.context);

        while let Some(pending_op) = self.pending.pop() {
            match pending_op {
                PendingDefine::Rc(scheme) => {
                    let rc_builtin = self.rcs.get(&scheme).unwrap().clone();
                    rc_builtin.define(globals, self);
                }
                PendingDefine::CowArray(scheme) => {
                    let cow_builtin = self.cow_arrays.get(&scheme).unwrap().clone();
                    cow_builtin.define(globals, self);
                }
            }
        }
    }
}

fn low_type_in_context<T: Context>(globals: &Globals<T>, type_: &low::Type) -> T::Type {
    match type_ {
        low::Type::Bool => globals.context.i1_t(),
        low::Type::Num(first_ord::NumType::Byte) => globals.context.i8_t(),
        low::Type::Num(first_ord::NumType::Int) => globals.context.i64_t(),
        low::Type::Num(first_ord::NumType::Float) => globals.context.f64_t(),
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
        low::Type::Array(_) => cow_array_t(&globals.context),
        low::Type::HoleArray(_) => cow_hole_array_t(&globals.context),
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
    match scheme {
        ModeScheme::Bool => {}
        ModeScheme::Num(_) => {}
        ModeScheme::Array(_, _) => match op {
            DerivedRcOp::Retain => {
                let retain_func = instances.get_cow_array(globals, scheme).retain_array();
                s.call_void(retain_func, &[arg]);
            }
            DerivedRcOp::DerivedRetain => {
                let derived_retain_func = instances
                    .get_cow_array(globals, scheme)
                    .derived_retain_array();
                s.call_void(derived_retain_func, &[arg]);
            }
            DerivedRcOp::Release => {
                let release_func = instances.get_cow_array(globals, scheme).release_array();
                s.call_void(release_func, &[arg]);
            }
        },
        ModeScheme::HoleArray(_, _) => match op {
            DerivedRcOp::Retain => {
                let retain_func = instances.get_cow_array(globals, scheme).retain_hole();
                s.call_void(retain_func, &[arg]);
            }
            DerivedRcOp::DerivedRetain => {
                let derived_retain_func = instances
                    .get_cow_array(globals, scheme)
                    .derived_retain_hole();
                s.call_void(derived_retain_func, &[arg]);
            }
            DerivedRcOp::Release => {
                let release_func = instances.get_cow_array(globals, scheme).release_hole();
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

// Helper function to check divisor for non-zero using s._ API
fn check_divisor_nonzero<T: Scope>(s: &T, divisor: T::Value) {
    s.if_(s.eq(divisor, s.i64(0)), |s| {
        s.panic("panicked due to division by zero\n", &[]);
    });
}

// Helper function to extract binary operation arguments using s._ API
fn extract_binop_args<T: Scope>(s: &T, args: T::Value) -> (T::Value, T::Value) {
    let lhs = s.field(args, 0);
    let rhs = s.field(args, 1);
    (lhs, rhs)
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
            gen_rc_op(
                match rc_op {
                    RcOp::Retain => DerivedRcOp::Retain,
                    RcOp::Release => DerivedRcOp::Release,
                },
                s,
                // &builder,
                instances,
                globals,
                mode_scheme,
                locals[local_id],
            );
            s.make_tup(&[])
        }
        E::Intrinsic(intr, local_id) => match intr {
            Intrinsic::Not => s.not(locals[local_id]),
            Intrinsic::AddByte => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.add(lhs, rhs)
            }
            Intrinsic::AddInt => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.add(lhs, rhs)
            }
            Intrinsic::AddFloat => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.fadd(lhs, rhs)
            }
            Intrinsic::SubByte => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.sub(lhs, rhs)
            }
            Intrinsic::SubInt => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.sub(lhs, rhs)
            }
            Intrinsic::SubFloat => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.fsub(lhs, rhs)
            }
            Intrinsic::MulByte => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.mul(lhs, rhs)
            }
            Intrinsic::MulInt => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.mul(lhs, rhs)
            }
            Intrinsic::MulFloat => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.fmul(lhs, rhs)
            }
            Intrinsic::DivByte => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                check_divisor_nonzero(s, rhs);
                s.udiv(lhs, rhs)
            }
            Intrinsic::DivInt => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                check_divisor_nonzero(s, rhs);
                s.sdiv(lhs, rhs)
            }
            Intrinsic::DivFloat => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.fdiv(lhs, rhs)
            }
            Intrinsic::LtByte => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.ult(lhs, rhs)
            }
            Intrinsic::LtInt => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.slt(lhs, rhs)
            }
            Intrinsic::LtFloat => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.olt(lhs, rhs)
            }
            Intrinsic::LteByte => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.ule(lhs, rhs)
            }
            Intrinsic::LteInt => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.sle(lhs, rhs)
            }
            Intrinsic::LteFloat => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.ole(lhs, rhs)
            }
            Intrinsic::GtByte => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.ugt(lhs, rhs)
            }
            Intrinsic::GtInt => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.sgt(lhs, rhs)
            }
            Intrinsic::GtFloat => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.ogt(lhs, rhs)
            }
            Intrinsic::GteByte => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.uge(lhs, rhs)
            }
            Intrinsic::GteInt => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.sge(lhs, rhs)
            }
            Intrinsic::GteFloat => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.oge(lhs, rhs)
            }
            Intrinsic::EqByte => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.eq(lhs, rhs)
            }
            Intrinsic::EqInt => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.eq(lhs, rhs)
            }
            Intrinsic::EqFloat => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.oeq(lhs, rhs)
            }
            Intrinsic::NegByte => s.neg(locals[local_id]),
            Intrinsic::NegInt => s.neg(locals[local_id]),
            Intrinsic::NegFloat => s.fneg(locals[local_id]),
            Intrinsic::ByteToInt => s.z_extend(s.i64_t(), locals[local_id]),
            Intrinsic::ByteToIntSigned => s.s_extend(s.i64_t(), locals[local_id]),
            Intrinsic::IntToByte => s.truncate(s.i8_t(), locals[local_id]),
            Intrinsic::IntShiftLeft => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                // Shifting an i64 by >= 64 bits produces a poison value, so we mask the rhs by 64 -
                // 1 (which is the same as taking the rhs mod 64). This appears to be what rustc
                // does.
                let mask = s.i64(63);
                let masked_rhs = s.and(rhs, mask);
                s.sll(lhs, masked_rhs)
            }
            Intrinsic::IntShiftRight => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                // Shifting an i64 by >= 64 bits produces a poison value, so we mask the rhs by 64 -
                // 1 (which is the same as taking the rhs mod 64). This appears to be what rustc
                // does.
                let mask = s.i64(63);
                let masked_rhs = s.and(rhs, mask);
                s.srl(lhs, masked_rhs)
            }
            Intrinsic::IntBitAnd => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.and(lhs, rhs)
            }
            Intrinsic::IntBitOr => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.or(lhs, rhs)
            }
            Intrinsic::IntBitXor => {
                let (lhs, rhs) = extract_binop_args(s, locals[local_id]);
                s.xor(lhs, rhs)
            }
            Intrinsic::IntCtpop => s.ctpop(locals[local_id]),
            Intrinsic::IntCtlz => s.ctlz(locals[local_id]),
            Intrinsic::IntCttz => s.cttz(locals[local_id]),
        },
        E::ArrayOp(mode_scheme, array_op) => {
            let builtin = instances.get_cow_array(globals, mode_scheme);
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
            let builtin_io = &instances.cow_array_io;
            match io_op {
                low::IoOp::Input => s.call(builtin_io.input, &[]),
                low::IoOp::Output(_input_type, array_id) => {
                    s.call_void(builtin_io.output, &[locals[array_id]]);
                    s.undef(s.struct_t(&[]))
                }
            }
        }
        E::Panic(ret_type, _input_type, message_id) => {
            let builtin_io = &instances.cow_array_io;
            s.call_void(builtin_io.output_error, &[locals[message_id]]);
            s.call_void(globals.context.tal().exit(), &[s.i32(1)]);
            s.unreachable();
            s.undef(low_type_in_context(globals, ret_type))
        }
        E::BoolLit(val) => s.i1(*val),
        E::ByteLit(val) => s.i8(*val),
        E::IntLit(val) => s.i64(*val as u64),
        E::FloatLit(val) => s.f64(*val),
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

pub fn gen_program<T: Context>(
    program: low::Program,
    context: T,
    func_progress: impl ProgressLogger,
    rc_progress: impl ProgressLogger,
    cow_progress: impl ProgressLogger,
    type_progress: impl ProgressLogger,
) {
    let profile_points = declare_profile_points(&context, &program);

    let globals = Globals {
        context,
        custom_schemes: program.schemes,
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

    instances.define(&globals, rc_progress, cow_progress);

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
    valgrind: Option<ValgrindConfig>,
) -> std::result::Result<Child, CrateError> {
    let target = cfg::LlvmConfig::Native;
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

pub fn build(program: low::Program, config: &BuildConfig) -> std::result::Result<(), CrateError> {
    let target = if let cfg::TargetConfig::Llvm(target) = config.target {
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
        .map_err(CrateError::CodeGenFailed)
    } else {
        let obj_path = tempfile::Builder::new()
            .suffix(".o")
            .tempfile_in("")
            .map_err(|err| CrateError::CodeGenFailed(Error::CouldNotCreateTempFile(err)))?
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
        .map_err(CrateError::CodeGenFailed)
    }
}
