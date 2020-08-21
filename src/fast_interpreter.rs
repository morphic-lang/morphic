use crate::data::first_order_ast::{BinOp, Comparison, NumType};
use crate::data::low_ast::{
    ArithOp, ArrayOp, CustomFuncId, CustomTypeId, Expr, IoOp, LocalId, Program, Type, VariantId,
};
use crate::data::repr_constrained_ast::RepChoice;
use crate::data::tail_rec_ast as tail;
use crate::{
    pseudoprocess::{spawn_thread, Child, ExitStatus, Stdio},
    util::id_vec::IdVec,
};
use generational_arena::{Arena, Index as ArenaIndex};
use im_rc::Vector;
use smallvec::{Array, SmallVec};
use stacker;
use std::borrow::Borrow;
use std::convert::TryFrom;
use std::fmt;
use std::io::BufRead;
use std::io::Write;
use std::num::Wrapping;
use std::ops::{Index, IndexMut};
use std::rc::Rc;

// This "red zone" value depends on the maximum stack space required by `interpret_expr`, which is
// determined experimentally. If you make a change to `interpret_expr and` `cargo test` starts
// segfaulting, bump this value until it works.
const STACK_RED_ZONE_BYTES: usize = 256 * 1024;
const STACK_GROW_BYTES: usize = 1024 * 1024;

// only meaningful for flat arrays
#[derive(Debug, Clone, PartialEq, Eq)]
enum ArrayStatus {
    Invalid,
    Valid,
}

#[derive(Debug, Clone, Copy)]
struct RefCount(usize);

impl fmt::Display for RefCount {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, Copy)]
struct HoleIdx(i64);

impl fmt::Display for HoleIdx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// A `Value::Variant` is 24 bytes, and a tuple size of 2 yields a 24 byte `SmallVec` (if you look
// at the implementation, it's only "extra" field is a capacity). Therefore, this is the biggest
// `Tuple` size that will not increase the size of the `Value` enum.
type Tuple = SmallVec<[Pointer; 2]>;

#[derive(Debug, Clone)]
enum Value {
    Bool(bool),
    Byte(Wrapping<u8>),
    Int(Wrapping<i64>),
    Float(f64),
    Pointer(Pointer),
    Tuple(Tuple),
    Variant(VariantId, Pointer),
    Custom(CustomTypeId, Pointer),
}

#[derive(Debug, Clone)]
enum BoxedValue {
    Array(RepChoice, ArrayStatus, RefCount, Vector<Value>),
    HoleArray(RepChoice, ArrayStatus, RefCount, HoleIdx, Vector<Value>),
    Box(RefCount, Value),
}

impl BoxedValue {
    fn assert_valid(&self, trace: &mut StackTrace) {
        match self {
            BoxedValue::Array(RepChoice::OptimizedMut, status, _, _)
            | BoxedValue::HoleArray(RepChoice::OptimizedMut, status, _, _, _) => {
                if *status != ArrayStatus::Valid {
                    trace.panic(StackTraceEntry::String(format!(
                        "accessing invalid flat array {:?}",
                        self
                    )));
                }
            }
            _ => {}
        }
    }

    fn maybe_invalidate(&mut self, trace: &mut StackTrace) {
        if let BoxedValue::Array(rep, status, _, _) | BoxedValue::HoleArray(rep, status, _, _, _) =
            self
        {
            if *rep == RepChoice::OptimizedMut {
                *status = ArrayStatus::Invalid;
            }
        } else {
            trace.panic(StackTraceEntry::String(format!(
                "attempting to invalidate non-array type {:?}",
                self
            )));
        }
    }
}

#[derive(Debug, Clone)]
enum StackTraceEntry {
    Str(&'static str),
    String(String),
}

impl fmt::Display for StackTraceEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        type E = StackTraceEntry;
        match self {
            E::Str(s) => write!(f, "{}", s),
            E::String(s) => write!(f, "{}", s),
        }
    }
}

#[derive(Debug, Clone)]
struct StackTrace(Vec<StackTraceEntry>);

impl StackTrace {
    fn new() -> Self {
        Self(vec![StackTraceEntry::Str("Stacktrace:")])
    }

    fn panic(&self, entry: StackTraceEntry) -> ! {
        for item in &self.0 {
            println!("{}", item);
        }
        println!("{}", entry);
        panic!();
    }

    fn run_frame<F, R>(&mut self, entry: StackTraceEntry, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        self.0.push(entry);
        let ret = f(self);
        self.0.pop();
        ret
    }
}

#[derive(Debug, Clone)]
struct Stack {
    frames: Vec<usize>,
    values: Vec<Pointer>,
}

impl Stack {
    fn new() -> Self {
        Self {
            frames: vec![0],
            values: Vec::new(),
        }
    }

    fn get(&self, local_id: LocalId) -> &Pointer {
        let idx = local_id.0 + self.frames.last().unwrap();
        if idx >= self.values.len() {
            panic!("accessing undefined local variable");
        }
        &self.values[idx]
    }

    fn push(&mut self, heap_id: Pointer) {
        self.values.push(heap_id);
    }

    fn run_frame<F, R>(&mut self, arg_id: Pointer, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        self.frames.push(self.values.len());
        self.values.push(arg_id);
        let ret = f(self);
        let idx = self.frames.pop().unwrap();
        self.values.truncate(idx);
        ret
    }
}

fn run_frame<F, R>(
    trace: &mut StackTrace,
    stack: &mut Stack,
    entry: StackTraceEntry,
    arg_id: Pointer,
    f: F,
) -> R
where
    F: FnOnce(&mut StackTrace, &mut Stack) -> R,
{
    trace.run_frame(entry, |trace| {
        stack.run_frame(arg_id, |stack| f(trace, stack))
    })
}

#[derive(Debug, Clone, Copy)]
struct Pointer(ArenaIndex);

#[derive(Debug, Clone)]
struct Heap(Arena<BoxedValue>);

impl Heap {
    fn new() -> Self {
        Self(Arena::new())
    }

    fn len(&self) -> usize {
        return self.0.len();
    }

    fn insert(&mut self, val: BoxedValue) -> Pointer {
        Pointer(self.0.insert(val))
    }

    fn remove(&mut self, ptr: Pointer) {
        self.0.remove(ptr.0);
    }

    fn get(&self, ptr: Pointer, trace: &mut StackTrace) -> &BoxedValue {
        if let Some(val) = self.0.get(ptr.0) {
            val.assert_valid(trace);
            return val;
        }
        trace.panic(StackTraceEntry::Str("accessing freed memory"));
    }

    fn get_mut(&mut self, ptr: Pointer, trace: &mut StackTrace) -> &mut BoxedValue {
        if let Some(val) = self.0.get_mut(ptr.0) {
            val.assert_valid(trace);
            return val;
        }
        trace.panic(StackTraceEntry::Str("accessing freed memory"));
    }
}

fn ptr_to_string(ptr: Pointer, heap: &Heap, trace: &mut StackTrace) -> String {
    match heap.get(ptr, trace) {
        BoxedValue::Array(rep, status, rc, content) => {
            let rep_str = match rep {
                RepChoice::OptimizedMut => "flat",
                RepChoice::FallbackImmut => "persistent",
            };
            let status_str = match status {
                ArrayStatus::Valid => "valid",
                ArrayStatus::Invalid => "invalid",
            };
            let content_str = content
                .iter()
                .map(|item| val_to_string(item, heap, trace))
                .collect::<Vec<String>>()
                .join(",");
            format!(
                "{} {} rc:{} array [{}]",
                status_str, rep_str, rc, content_str
            )
        }
        BoxedValue::HoleArray(rep, status, rc, hole, content) => {
            let rep_str = match rep {
                RepChoice::OptimizedMut => "flat",
                RepChoice::FallbackImmut => "persistent",
            };
            let status_str = match status {
                ArrayStatus::Valid => "valid",
                ArrayStatus::Invalid => "invalid",
            };
            let content_str = content
                .iter()
                .enumerate()
                .map(|(i, item)| {
                    if i as i64 == hole.0 {
                        "_".into()
                    } else {
                        val_to_string(item, heap, trace)
                    }
                })
                .collect::<Vec<String>>()
                .join(",");
            format!(
                "{} {} rc:{} hole array [{}]",
                status_str, rep_str, rc, content_str
            )
        }
        BoxedValue::Box(rc, content) => {
            format!("box rc:{} ({})", rc, val_to_string(content, heap, trace))
        }
    }
}

fn val_to_string(val: &Value, heap: &Heap, trace: &mut StackTrace) -> String {
    match val {
        Value::Bool(val) => val.to_string(),
        Value::Byte(Wrapping(val)) => (*val as char).to_string(),
        Value::Int(val) => val.to_string(),
        Value::Float(val) => val.to_string(),
        Value::Pointer(ptr) => ptr_to_string(*ptr, heap, trace),
        Value::Tuple(content) => {
            let content_str = content
                .iter()
                .map(|ptr| ptr_to_string(*ptr, heap, trace))
                .collect::<Vec<String>>()
                .join(",");
            format!("tuple({})", content_str)
        }
        Value::Variant(variant_id, ptr) => format!(
            "variant #{} ({})",
            variant_id.0,
            ptr_to_string(*ptr, heap, trace)
        ),
        Value::Custom(type_id, ptr) => format!(
            "custom #{} ({})",
            type_id.0,
            ptr_to_string(*ptr, heap, trace)
        ),
    }
}

fn retain_ptr(ptr: Pointer, heap: &mut Heap, trace: &mut StackTrace) {
    match heap.get_mut(ptr, trace) {
        BoxedValue::Array(_, _, rc, _)
        | BoxedValue::HoleArray(_, _, rc, _, _)
        | BoxedValue::Box(rc, _) => {
            rc.0 += 1;
        }
    }
}

fn retain_val(val: &Value, heap: &mut Heap, trace: &mut StackTrace) {
    match val {
        Value::Bool(_) | Value::Byte(_) | Value::Int(_) | Value::Float(_) => {}
        Value::Pointer(ptr) => retain_ptr(*ptr, heap, trace),
        Value::Tuple(content) => {
            let content = content.clone();
            for ptr in content.iter() {
                trace.run_frame(StackTraceEntry::Str("retaining tuple item"), |trace| {
                    retain_ptr(*ptr, heap, trace);
                });
            }
        }
        Value::Variant(_, ptr) => {
            let ptr = ptr.clone();
            trace.run_frame(StackTraceEntry::Str("retaining variant content"), |trace| {
                retain_ptr(ptr, heap, trace);
            });
        }
        Value::Custom(_, ptr) => {
            let ptr = ptr.clone();
            trace.run_frame(StackTraceEntry::Str("retaining custom content"), |trace| {
                retain_ptr(ptr, heap, trace);
            });
        }
    }
}

fn release_ptr(ptr: Pointer, heap: &mut Heap, trace: &mut StackTrace) {
    let val = heap.get_mut(ptr, trace);
    match val {
        BoxedValue::Array(_, _, rc, content) | BoxedValue::HoleArray(_, _, rc, _, content) => {
            if rc.0 == 0 {
                trace.panic(StackTraceEntry::String(format!(
                    "releasing with rc 0, {:?}",
                    val
                )))
            }
            rc.0 -= 1;
            if rc.0 == 0 {
                let content = content.clone();
                for item in content.iter() {
                    trace.run_frame(StackTraceEntry::Str("releasing array item"), |trace| {
                        release_val(item, heap, trace);
                    });
                }
                heap.remove(ptr);
            }
        }
        BoxedValue::Box(rc, content) => {
            if rc.0 == 0 {
                trace.panic(StackTraceEntry::String(format!(
                    "releasing with rc 0, {:?}",
                    val
                )))
            }
            rc.0 -= 1;
            if rc.0 == 0 {
                let content = content.clone();
                trace.run_frame(StackTraceEntry::Str("releasing box content"), |trace| {
                    release_val(&content, heap, trace);
                });
            }
        }
    }
}

fn release_val(val: &Value, heap: &mut Heap, trace: &mut StackTrace) {
    match val {
        Value::Bool(_) | Value::Byte(_) | Value::Int(_) | Value::Float(_) => {}
        Value::Pointer(ptr) => release_ptr(*ptr, heap, trace),
        Value::Tuple(content) => {
            let content = content.clone();
            for ptr in content.iter() {
                trace.run_frame(StackTraceEntry::Str("releasing tuple item"), |trace| {
                    release_ptr(*ptr, heap, trace);
                });
            }
        }
        Value::Variant(_, ptr) | Value::Custom(_, ptr) => {
            let ptr = ptr.clone();
            trace.run_frame(StackTraceEntry::Str("releasing variant content"), |trace| {
                release_ptr(ptr, heap, trace);
            });
        }
    }
}

// only the first item in an array is type checked
fn typecheck_ptr(
    ptr: Pointer,
    ty: &Type,
    heap: &Heap,
    custom_types: &IdVec<CustomTypeId, Type>,
    trace: &mut StackTrace,
) {
    match ty {
        Type::Array(rep, item_type) => {
            let array_type = match rep {
                RepChoice::OptimizedMut => "flat array",
                RepChoice::FallbackImmut => "persistent array",
            };

            if let Value::Array(_, _, _, values) = val {
                if let Some(item_heap_id) = values.front() {
                    typecheck(heap, custom_types, *item_heap_id, item_type, trace);
                }
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected {}, received {:?}",
                    array_type, val
                )));
            }
        }

        Type::HoleArray(rep, item_type) => {
            let array_type = match rep {
                RepChoice::OptimizedMut => "flat hole array",
                RepChoice::FallbackImmut => "persistent hole array",
            };

            if let Value::HoleArray(_, _, _, _, values) = val {
                if let Some(item_heap_id) = values.front() {
                    typecheck(heap, custom_types, *item_heap_id, item_type, trace);
                }
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected a {} received {:?}",
                    array_type, val
                )));
            }
        }

        Type::Boxed(boxed_type) => {
            if let Value::Box(_rc, heap_id) = val {
                trace.run_frame(StackTraceEntry::Str("typechecking box interior"), |trace| {
                    typecheck(heap, custom_types, *heap_id, &*boxed_type, trace);
                });
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected a box received {:?}",
                    val
                )));
            }
        }
    }
}

fn typecheck_val(
    val: &Value,
    ty: &Type,
    heap: &Heap,
    custom_types: &IdVec<CustomTypeId, Type>,
    trace: &mut StackTrace,
) {
    match ty {
        Type::Bool => {
            if let Value::Bool(_) = val {
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected a bool received {:?}",
                    val
                )));
            }
        }

        Type::Num(NumType::Byte) => {
            if let Value::Byte(_) = val {
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected a byte received {:?}",
                    val
                )));
            };
        }

        Type::Num(NumType::Int) => {
            if let Value::Int(_) = val {
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected an int received {:?}",
                    val
                )));
            };
        }

        Type::Num(NumType::Float) => {
            if let Value::Float(_) = val {
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected an float received {:?}",
                    val
                )));
            };
        }

        Type::Tuple(item_types) => {
            if let Value::Tuple(values) = val {
                if item_types.len() != values.len() {
                    trace.panic(StackTraceEntry::String(format!(
                        "tuple type runtime length does not match expected: expected {}, got {:?}",
                        item_types.len(),
                        val
                    )));
                }

                for (item_type, ptr) in item_types.iter().zip(values.iter()) {
                    trace.run_frame(StackTraceEntry::Str("typechecking tuple items"), |trace| {
                        typecheck_ptr(*ptr, &*item_type, heap, custom_types, trace);
                    })
                }
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected a tuple received {:?}",
                    val
                )));
            }
        }

        Type::Variants(variants) => {
            if let Value::Variant(variant_id, ptr) = val {
                if variant_id.0 >= variants.len() {
                    trace.panic(StackTraceEntry::String(format!(
                        "variant id out of bounds, {} >= {}",
                        variant_id.0,
                        variants.len()
                    )));
                }
                trace.run_frame(
                    StackTraceEntry::Str("typechecking variant content"),
                    |trace| {
                        typecheck_ptr(*ptr, &variants[variant_id], heap, custom_types, trace);
                    },
                );
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected a variant received {:?}",
                    val
                )));
            }
        }

        Type::Custom(custom_type_id) => {
            if let Value::Custom(custom_id, ptr) = val {
                if *custom_type_id != *custom_id {
                    trace.panic(StackTraceEntry::String(format!(
                        "differing custom type ids {:?} != {:?}",
                        *custom_type_id, *custom_id
                    )));
                }

                trace.run_frame(
                    StackTraceEntry::Str("typechecking custom interior"),
                    |trace| {
                        typecheck_ptr(
                            *ptr,
                            &custom_types[custom_type_id],
                            heap,
                            custom_types,
                            trace,
                        );
                    },
                )
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected a custom received {:?}",
                    val
                )));
            }
        }

        Type::Array()

        Type::Array(rep, item_type) => {
            let array_type = match rep {
                RepChoice::OptimizedMut => "flat array",
                RepChoice::FallbackImmut => "persistent array",
            };

            if let Value::Array(_, _, _, values) = val {
                if let Some(item_heap_id) = values.front() {
                    typecheck(heap, custom_types, *item_heap_id, item_type, trace);
                }
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected {}, received {:?}",
                    array_type, val
                )));
            }
        }

        Type::HoleArray(rep, item_type) => {
            let array_type = match rep {
                RepChoice::OptimizedMut => "flat hole array",
                RepChoice::FallbackImmut => "persistent hole array",
            };

            if let Value::HoleArray(_, _, _, _, values) = val {
                if let Some(item_heap_id) = values.front() {
                    typecheck(heap, custom_types, *item_heap_id, item_type, trace);
                }
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected a {} received {:?}",
                    array_type, val
                )));
            }
        }

        Type::Boxed(boxed_type) => {
            if let Value::Box(_rc, heap_id) = val {
                trace.run_frame(StackTraceEntry::Str("typechecking box interior"), |trace| {
                    typecheck(heap, custom_types, *heap_id, &*boxed_type, trace);
                });
            } else {
                trace.panic(StackTraceEntry::String(format!(
                    "expected a box received {:?}",
                    val
                )));
            }
        }
    }
}

fn unwrap_bool(val: &Value, trace: &mut StackTrace) -> bool {
    trace.run_frame(StackTraceEntry::Str("unwrap bool"), |trace| {
        if let Value::Bool(val) = val {
            *val
        } else {
            trace.panic(StackTraceEntry::String(format!(
                "expected a bool received {:?}",
                val
            )));
        }
    })
}

fn unwrap_byte(val: &Value, trace: &mut StackTrace) -> Wrapping<u8> {
    trace.run_frame(StackTraceEntry::Str("unwrap byte"), |trace| {
        if let Value::Byte(val) = val {
            *val
        } else {
            trace.panic(StackTraceEntry::String(format!(
                "expected a byte received {:?}",
                val
            )));
        }
    })
}

fn unwrap_int(val: &Value, trace: &mut StackTrace) -> Wrapping<i64> {
    trace.run_frame(StackTraceEntry::Str("unwrap int"), |trace| {
        if let Value::Int(val) = val {
            *val
        } else {
            trace.panic(StackTraceEntry::String(format!(
                "expected an int received {:?}",
                val
            )));
        }
    })
}

fn unwrap_float(val: &Value, trace: &mut StackTrace) -> f64 {
    trace.run_frame(StackTraceEntry::Str("unwrap float"), |trace| {
        if let Value::Float(val) = val {
            *val
        } else {
            trace.panic(StackTraceEntry::String(format!(
                "expected a float received {:?}",
                val
            )));
        }
    })
}

// fn unwrap_array(
//     heap: &Heap,
//     heap_id: HeapId,
//     rep: RepChoice,
//     trace: &mut StackTrace,
// ) -> Vec<HeapId> {
//     let val = heap.get(heap_id, trace);
//     let kind = &heap[heap_id].assert_live(trace.add_frame("unwrap array".into()));
//     if let Value::Array(runtime_rep, _status, _rc, values) = kind {
//         if *runtime_rep != rep {
//             trace.panic(format![
//                 "expceted an array of different type, received {:?}",
//                 *kind
//             ]);
//         }
//         values.clone()
//     } else {
//         trace.panic(StackTraceEntry::String(format!(
//             "expected an array received {:?}",
//             val
//         )));
//     }
// }
//
// fn unwrap_array_retain(
//     heap: &mut Heap,
//     heap_id: HeapId,
//     rep: RepChoice,
//     trace: StackTrace,
// ) -> Vec<HeapId> {
//     let result = unwrap_array(heap, heap_id, rep, trace.clone());
//     for &item_id in &result {
//         retain(
//             heap,
//             item_id,
//             trace.add_frame("unwrap array retain".into()),
//         );
//     }
//     result
// }
//
// fn unwrap_hole_array(
//     heap: &Heap,
//     heap_id: HeapId,
//     rep: RepChoice,
//     trace: StackTrace,
// ) -> (i64, Vec<HeapId>) {
//     let val = heap.get(heap_id, trace);
//     let kind = &heap[heap_id].assert_live(trace.add_frame("unwrap hole array".into()));
//     if let Value::HoleArray(runtime_rep, _status, _rc, index, values) = kind {
//         if *runtime_rep != rep {
//             trace.panic(format![
//                 "expceted an array of different type, received {:?}",
//                 *kind
//             ]);
//         }
//         (*index, values.clone())
//     } else {
//         trace.panic(format!["expected a hole array received {:?}", kind]);
//     }
// }
//
// fn unwrap_hole_array_retain(
//     heap: &mut Heap,
//     heap_id: HeapId,
//     rep: RepChoice,
//     trace: StackTrace,
// ) -> (i64, Vec<HeapId>) {
//     let (idx, result) = unwrap_hole_array(heap, heap_id, rep, trace.clone());
//     for &item_id in &result {
//         retain(
//             heap,
//             item_id,
//             trace.add_frame("unwrap hole array retain".into()),
//         );
//     }
//     (idx, result)
// }

fn unwrap_tuple<'a>(value: &'a Value, trace: &mut StackTrace) -> &'a Tuple {
    trace.run_frame(StackTraceEntry::Str("unwrap tuple"), |trace| {
        if let Value::Tuple(content) = val {
            content
        } else {
            trace.panic(StackTraceEntry::String(format!(
                "expected a tuple received {:?}",
                val
            )));
        }
    })
}

fn unwrap_variant(heap: &Heap, heap_id: Pointer, trace: &mut StackTrace) -> (VariantId, Pointer) {
    trace.run_frame(StackTraceEntry::Str("unwrap variant"), |trace| {
        let val = heap.get(heap_id, trace);
        if let Value::Variant(variant_id, heap_id) = val {
            (*variant_id, *heap_id)
        } else {
            trace.panic(StackTraceEntry::String(format!(
                "expected a variant received {:?}",
                val
            )));
        }
    })
}

fn unwrap_box(heap: &Heap, heap_id: Pointer, trace: &mut StackTrace) -> Pointer {
    trace.run_frame(StackTraceEntry::Str("unwrap boxed"), |trace| {
        let val = heap.get(heap_id, trace);
        if let Value::Box(_, heap_id) = val {
            *heap_id
        } else {
            trace.panic(StackTraceEntry::String(format!(
                "expected a box received {:?}",
                val
            )));
        }
    })
}

fn unwrap_custom(heap: &Heap, heap_id: Pointer, trace: &mut StackTrace) -> (CustomTypeId, Pointer) {
    trace.run_frame(StackTraceEntry::Str("unwrap custom"), |trace| {
        let val = heap.get(heap_id, trace);
        if let Value::Custom(type_id, heap_id) = val {
            (*type_id, *heap_id)
        } else {
            trace.panic(StackTraceEntry::String(format!(
                "expected a custom received {:?}",
                val
            )));
        }
    })
}

fn bounds_check(stderr: &mut dyn Write, len: usize, index: i64) -> Result<(), ExitStatus> {
    let maybe_index = usize::try_from(index);
    match maybe_index {
        Ok(actual_index) if actual_index < len => Ok(()),
        _ => {
            writeln!(
                stderr,
                "index out of bounds: attempt to access item {} of array with length {}",
                index, len,
            )
            .unwrap();
            Err(ExitStatus::Failure(Some(1)))
        }
    }
}

#[derive(Clone, Debug)]
enum Interruption {
    Exit(ExitStatus),
    TailCall(tail::TailFuncId, Pointer),
}

impl From<ExitStatus> for Interruption {
    fn from(status: ExitStatus) -> Interruption {
        Interruption::Exit(status)
    }
}

fn interpret_call(
    func_id: CustomFuncId,
    arg_id: Pointer,
    stdin: &mut dyn BufRead,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
    program: &Program,
    stack: &mut Stack,
    heap: &mut Heap,
    trace: &mut StackTrace,
) -> Result<Pointer, ExitStatus> {
    let func = &program.funcs[func_id];

    trace.run_frame(
        StackTraceEntry::String(format!("typecheck function argument {:?}", func_id)),
        |trace| {
            typecheck(heap, &program.custom_types, arg_id, &func.arg_type, trace);
        },
    );

    let mut result = run_frame(
        trace,
        stack,
        StackTraceEntry::String(format!("func: {:?} arg: {:?}", func_id, arg_id)),
        arg_id,
        |trace, stack| {
            interpret_expr(
                &func.body, stdin, stdout, stderr, program, stack, heap, trace,
            )
        },
    );

    while let Err(Interruption::TailCall(tail_id, tail_arg)) = result {
        let tail_func = &func.tail_funcs[tail_id];

        trace.run_frame(
            StackTraceEntry::String(format!(
                "typecheck tail function argument {:?} {:?}",
                func_id, tail_id
            )),
            |trace| {
                typecheck(
                    heap,
                    &program.custom_types,
                    tail_arg,
                    &tail_func.arg_type,
                    trace,
                );
            },
        );

        result = run_frame(
            trace,
            stack,
            StackTraceEntry::String(format!(
                "tail func: {:?} {:?} arg: {:?}",
                func_id, tail_id, arg_id
            )),
            tail_arg,
            |trace, stack| {
                interpret_expr(
                    &tail_func.body,
                    stdin,
                    stdout,
                    stderr,
                    program,
                    stack,
                    heap,
                    trace,
                )
            },
        );
    }

    match result {
        Ok(ret_id) => {
            trace.run_frame(
                StackTraceEntry::String(format!("typecheck function return: {:?}", func_id)),
                |trace| {
                    typecheck(heap, &program.custom_types, ret_id, &func.ret_type, trace);
                },
            );

            Ok(ret_id)
        }
        Err(Interruption::Exit(status)) => Err(status),
        Err(Interruption::TailCall(_, _)) => unreachable!(),
    }
}

fn interpret_expr(
    expr: &Expr,
    stdin: &mut dyn BufRead,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
    program: &Program,
    stack: &Stack,
    heap: &mut Heap,
    stacktrace: &mut StackTrace,
) -> Result<Pointer, Interruption> {
    unimplemented!()
}
