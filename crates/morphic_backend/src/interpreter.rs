use crate::data::first_order_ast::{NumType, VariantId};
use crate::data::intrinsics::Intrinsic;
use crate::data::low_ast::{ArrayOp, CustomFuncId, Expr, IoOp, LocalId, Program, Type};
use crate::data::mode_annot_ast::Mode;
use crate::data::rc_specialized_ast::{ModeScheme, ModeSchemeId, RcOp};
use crate::data::tail_rec_ast as tail;
use crate::pretty_print::utils::{FuncRenderer, TailFuncRenderer};
use id_collections::IdVec;
use im_rc::Vector;
use morphic_common::pseudoprocess::{spawn_thread, Child, ExitStatus, Stdio};
use morphic_common::util::iter::IterExt;
use stacker;
use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::convert::TryFrom;
use std::fmt::Display;
use std::io::{BufRead, Write};
use std::num::Wrapping;
use std::ops::{Index, IndexMut};
use std::rc::Rc;

type RefCount = usize;

#[derive(Debug, Clone, Copy)]
enum NumValue {
    Byte(Wrapping<u8>),
    Int(Wrapping<i64>),
    Float(f64),
}

#[derive(Debug, Clone)]
enum Value {
    Bool(bool),
    Num(NumValue),
    Array(usize, Option<HeapId>),
    HoleArray(usize, i64, HeapId),
    ArrayContent(RefCount, Vec<HeapId>),
    Tuple(Vec<HeapId>),
    Variant(VariantId, HeapId),
    Box(RefCount, HeapId),
    // Because of our type 'guarding' pass, customs must be treated transparently in the dynamics
    // Custom(CustomTypeId, HeapId),
}

fn assert_live<'a>(heap: &'a Heap, id: HeapId, stacktrace: StackTrace) -> &'a Value {
    match &heap[id] {
        Value::Box(rc, _) | Value::ArrayContent(rc, _) => {
            if *rc == 0 {
                stacktrace.panic(format!["accessing rc 0 value {:?}", &heap[id]]);
            }
            &heap[id]
        }
        Value::Array(_, None) => &heap[id],
        Value::Array(_, Some(ptr)) | Value::HoleArray(_, _, ptr) => {
            assert_live(heap, *ptr, stacktrace);
            &heap[id]
        }
        _ => &heap[id],
    }
}

#[derive(Debug, Clone)]
struct StackTrace(Vector<Rc<String>>);

impl Display for StackTrace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, line) in self.0.iter().enumerate() {
            write![f, "{}", line.as_str()]?;
            if i != self.0.len() - 1 {
                write![f, "\n"]?
            }
        }
        Ok(())
    }
}

impl StackTrace {
    fn new() -> StackTrace {
        StackTrace({
            let mut v = Vector::new();
            v.push_front(Rc::new("Stacktrace:".into()));
            v
        })
    }

    fn add_frame(&self, s: impl AsRef<str>) -> StackTrace {
        StackTrace({
            let mut v = self.0.clone();
            v.push_back(Rc::new(s.as_ref().lines().collect::<Vec<&str>>().join(" ")));
            v
        })
    }

    fn panic(&self, s: impl Display) -> ! {
        println!["{}", self];
        println!["{}", s];
        panic![];
    }
}

#[derive(Debug, Clone)]
struct Locals {
    values: Vec<HeapId>,
}

impl Locals {
    fn new(value: HeapId) -> Locals {
        Locals {
            values: vec![value],
        }
    }

    fn add(&mut self, heap_id: HeapId) {
        self.values.push(heap_id)
    }
}

impl<T: Borrow<LocalId>> Index<T> for Locals {
    type Output = HeapId;

    fn index(&self, index: T) -> &Self::Output {
        if index.borrow().0 >= self.values.len() {
            // this shouldn't happen
            panic!["Accessing undefined local variable"];
        }

        &self.values[index.borrow().0]
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Copy)]
struct HeapId(usize);

#[derive(Clone, Debug)]
struct Heap<'a> {
    values: Vec<Value>,
    program: &'a Program,
}

impl Index<HeapId> for Heap<'_> {
    type Output = Value;

    fn index(&self, index: HeapId) -> &Self::Output {
        if index.0 >= self.values.len() {
            // this shouldn't happen
            panic!["accessing undefined heap variable"];
        }

        &self.values[index.0]
    }
}

impl IndexMut<HeapId> for Heap<'_> {
    fn index_mut(&mut self, index: HeapId) -> &mut Self::Output {
        if index.0 >= self.values.len() {
            // this shouldn't happen
            panic!["accessing undefined heap variable"];
        }

        &mut self.values[index.0]
    }
}

impl Heap<'_> {
    fn new<'a>(program: &'a Program) -> Heap<'a> {
        let mut heap = Heap {
            program,
            values: vec![],
        };
        heap.add(Value::Tuple(vec![]));
        heap
    }

    fn add(&mut self, kind: Value) -> HeapId {
        self.values.push(kind);
        HeapId(self.values.len() - 1)
    }

    fn value_to_str(&self, kind: HeapId) -> String {
        match &self[kind] {
            Value::Bool(val) => val.to_string(),
            Value::Num(NumValue::Byte(Wrapping(val))) => format!("{:?}", *val as char),
            Value::Num(NumValue::Int(Wrapping(val))) => val.to_string(),
            Value::Num(NumValue::Float(val)) => val.to_string(),
            Value::ArrayContent(rc, contents) => {
                let contents_str = contents
                    .iter()
                    .map(|heap_id| self.value_to_str(*heap_id))
                    .collect::<Vec<String>>()
                    .join(",");
                format!["rc:{} [{}]", rc, contents_str]
            }
            Value::Array(_len, None) => {
                format!["empty array on stack"]
            }
            Value::Array(_len, Some(ptr)) => {
                let Value::ArrayContent(rc, contents) = &self[*ptr] else {
                    panic!("expected array content")
                };
                let contents_str = contents
                    .iter()
                    .map(|heap_id| self.value_to_str(*heap_id))
                    .collect::<Vec<String>>()
                    .join(",");
                format!["array rc:{} [{}]", rc, contents_str]
            }
            Value::HoleArray(_len, hole, ptr) => {
                let Value::ArrayContent(rc, contents) = &self[*ptr] else {
                    panic!("expected array content")
                };
                let contents_str = contents
                    .iter()
                    .enumerate()
                    .map(|(i, heap_id)| {
                        if i as i64 == *hole {
                            "_".into()
                        } else {
                            self.value_to_str(*heap_id)
                        }
                    })
                    .collect::<Vec<String>>()
                    .join(",");
                format!["hole array rc:{} [{}]", rc, contents_str]
            }
            Value::Tuple(contents) => {
                let contents_str = contents
                    .iter()
                    .map(|heap_id| self.value_to_str(*heap_id))
                    .collect::<Vec<String>>()
                    .join(",");
                format!["tuple({})", contents_str]
            }
            Value::Variant(variant_id, heap_id) => format![
                "variant #{} ({})",
                variant_id.0,
                self.value_to_str(*heap_id)
            ],
            Value::Box(rc, heap_id) => {
                format!["box rc:{} ({})", rc, self.value_to_str(*heap_id)]
            }
        }
    }

    fn to_str(&self) -> String {
        (0..self.values.len())
            .filter(|i| {
                matches!(
                    self.values[*i],
                    Value::Array(_, _) | Value::HoleArray(_, _, _) | Value::Box(_, _)
                )
            })
            .map(|i| format!["{}", self.value_to_str(HeapId(i))])
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn assert_everything_else_deallocated(&self) {
        let mut not_freed_values = vec![];
        for (index, value) in self.values.iter().enumerate() {
            match value {
                Value::Box(rc, _) | Value::ArrayContent(rc, _) => {
                    if *rc != 0 {
                        not_freed_values.push(index);
                    }
                }
                _ => {}
            }
        }
        for value in &not_freed_values {
            println![
                "NONZERO RC: HeapId({}), {}",
                value,
                self.value_to_str(HeapId(*value))
            ]
        }

        if not_freed_values.len() != 0 {
            panic!["rc != 0 at end of main"];
        }
    }
}

fn retain(heap: &mut Heap, scheme: &ModeScheme, heap_id: HeapId, stacktrace: StackTrace) {
    let kind = &mut heap[heap_id];

    match kind {
        Value::Bool(_) | Value::Num(_) => {}
        Value::Tuple(content) => {
            let content = content.clone();
            for sub_heap_id in content {
                retain(
                    heap,
                    scheme,
                    sub_heap_id,
                    stacktrace.add_frame("retain subtuple"),
                );
            }
        }
        Value::Variant(_idx, content) => {
            let content = content.clone();
            retain(
                heap,
                scheme,
                content,
                stacktrace.add_frame("retain subthing"),
            );
        }
        Value::Array(_, None) => {}
        Value::Array(_, Some(ptr)) | Value::HoleArray(_, _, ptr) => {
            let ptr = *ptr;
            retain(heap, scheme, ptr, stacktrace);
        }
        Value::ArrayContent(rc, _) | Value::Box(rc, _) => {
            *rc += 1;
        }
    }
}

fn derived_retain(
    custom_schemes: &IdVec<ModeSchemeId, ModeScheme>,
    heap: &mut Heap,
    heap_id: HeapId,
    scheme: &ModeScheme,
    stacktrace: StackTrace,
) {
    let kind = &mut heap[heap_id];

    match (kind, scheme) {
        (Value::Bool(_), ModeScheme::Bool) => {}
        (Value::Num(_), ModeScheme::Num(_)) => {}
        (Value::Tuple(content), ModeScheme::Tuple(schemes)) => {
            let content = content.clone();
            for (sub_heap_id, scheme) in content.iter().zip_eq(schemes) {
                derived_retain(
                    custom_schemes,
                    heap,
                    *sub_heap_id,
                    scheme,
                    stacktrace.add_frame("derived retain subtuple"),
                );
            }
        }
        (Value::Variant(idx, content), ModeScheme::Variants(schemes)) => {
            let idx = *idx;
            let content = content.clone();
            derived_retain(
                custom_schemes,
                heap,
                content,
                &schemes[idx],
                stacktrace.add_frame("derived retain subthing"),
            );
        }
        (_, ModeScheme::Custom(scheme_id, _)) => {
            derived_retain(
                custom_schemes,
                heap,
                heap_id,
                &custom_schemes[*scheme_id],
                stacktrace.add_frame("derived retain subthing"),
            );
        }
        (Value::Array(_, None), ModeScheme::Array(_, _)) => {}
        (Value::Array(_, Some(ptr)), ModeScheme::Array(_, _))
        | (Value::HoleArray(_, _, ptr), ModeScheme::HoleArray(_, _)) => {
            let ptr = *ptr;
            derived_retain(custom_schemes, heap, ptr, scheme, stacktrace)
        }

        (Value::ArrayContent(rc, _), ModeScheme::Array(mode, _))
        | (Value::ArrayContent(rc, _), ModeScheme::HoleArray(mode, _))
        | (Value::Box(rc, _), ModeScheme::Boxed(mode, _)) => {
            if *mode == Mode::Owned {
                *rc += 1;
            }
        }
        _ => stacktrace.panic("mismatched value and scheme"),
    }
}

fn release(
    custom_schemes: &IdVec<ModeSchemeId, ModeScheme>,
    heap: &mut Heap,
    heap_id: HeapId,
    scheme: &ModeScheme,
    stacktrace: StackTrace,
) {
    let kind = &mut heap[heap_id];
    match (kind, scheme) {
        (Value::Bool(_), ModeScheme::Bool) => {}
        (Value::Num(_), ModeScheme::Num(_)) => {}
        (Value::Tuple(content), ModeScheme::Tuple(schemes)) => {
            let content = content.clone();
            for (sub_heap_id, scheme) in content.iter().zip_eq(schemes) {
                release(
                    custom_schemes,
                    heap,
                    *sub_heap_id,
                    scheme,
                    stacktrace.add_frame("releasing subtuple"),
                );
            }
        }
        (Value::Variant(idx, content), ModeScheme::Variants(schemes)) => {
            let idx = *idx;
            let content = content.clone();
            release(
                custom_schemes,
                heap,
                content,
                &schemes[idx],
                stacktrace.add_frame("release subthing"),
            );
        }
        (_, ModeScheme::Custom(scheme_id, _)) => {
            release(
                custom_schemes,
                heap,
                heap_id,
                &custom_schemes[*scheme_id],
                stacktrace.add_frame("release subthing"),
            );
        }
        (Value::Array(_, None), ModeScheme::Array(_, _)) => {}

        (Value::Array(_, Some(ptr)), ModeScheme::Array(mode, item_scheme)) => {
            let ptr = *ptr;
            let Value::ArrayContent(rc, content) = &mut heap[ptr] else {
                panic!()
            };
            if *mode == Mode::Owned {
                if *rc == 0 {
                    stacktrace.panic(format!["releasing with rc 0, array {:?}", content]);
                }
                *rc -= 1;

                if *rc == 0 {
                    for sub_heap_id in content.clone() {
                        release(
                            custom_schemes,
                            heap,
                            sub_heap_id,
                            item_scheme,
                            stacktrace.add_frame("releasing subthings"),
                        );
                    }
                }
            }
        }
        (Value::HoleArray(_, hole_idx, ptr), ModeScheme::HoleArray(mode, item_scheme)) => {
            let hole_idx = *hole_idx;
            let ptr = *ptr;
            let Value::ArrayContent(rc, content) = &mut heap[ptr] else {
                panic!();
            };
            if *mode == Mode::Owned {
                if *rc == 0 {
                    stacktrace.panic(format!["releasing with rc 0, array {:?}", content]);
                }
                *rc -= 1;

                if *rc == 0 {
                    for (i, sub_heap_id) in content.clone().iter().enumerate() {
                        if i as i64 != hole_idx {
                            release(
                                custom_schemes,
                                heap,
                                *sub_heap_id,
                                item_scheme,
                                stacktrace.add_frame("releasing subthings"),
                            );
                        }
                    }
                }
            }
        }
        (Value::ArrayContent(_rc, _content), ModeScheme::Array(_mode, _scheme))
        | (Value::ArrayContent(_rc, _content), ModeScheme::HoleArray(_mode, _scheme)) => {
            panic!()
        }
        (Value::Box(rc, content), ModeScheme::Boxed(mode, scheme)) => {
            if *mode == Mode::Owned {
                if *rc == 0 {
                    stacktrace.panic(format![
                        "releasing with rc 0, box {:?} {}",
                        content, heap_id.0
                    ]);
                }
                *rc -= 1;
                let content = *content;
                if *rc == 0 {
                    release(
                        custom_schemes,
                        heap,
                        content,
                        scheme,
                        stacktrace.add_frame("releasing subthing"),
                    );
                }
            }
        }
        (kind, scheme) => {
            stacktrace.panic(format![
                "value is not compatible with scheme:\n  - value: {:?}\n  - scheme: {:?}",
                kind, scheme
            ]);
        }
    }
}

fn typecheck_many(
    heap: &Heap,
    heap_ids: &[HeapId],
    type_: &Type,
    seen: &BTreeSet<HeapId>,
    stacktrace: StackTrace,
) {
    for heap_id in heap_ids {
        typecheck_rec(
            heap,
            *heap_id,
            type_,
            &seen,
            stacktrace.add_frame("checking array contents"),
        );
    }
}

fn typecheck(heap: &Heap, heap_id: HeapId, type_: &Type, stacktrace: StackTrace) {
    typecheck_rec(heap, heap_id, type_, &BTreeSet::new(), stacktrace)
}

fn typecheck_rec(
    heap: &Heap,
    heap_id: HeapId,
    type_: &Type,
    seen: &BTreeSet<HeapId>,
    stacktrace: StackTrace,
) {
    if seen.contains(&heap_id) {
        stacktrace.panic("encountered recursive data structure")
    }

    let original_seen = seen.clone();
    let mut seen = seen.clone();

    seen.insert(heap_id);
    let kind = &heap[heap_id];

    match type_ {
        Type::Bool => {
            if let Value::Bool(_) = kind {
            } else {
                stacktrace.panic(format!["expected a bool received {:?}", kind]);
            }
        }

        Type::Num(NumType::Byte) => {
            if let Value::Num(NumValue::Byte(_)) = kind {
            } else {
                stacktrace.panic(format!["expected a byte received {:?}", kind]);
            };
        }

        Type::Num(NumType::Int) => {
            if let Value::Num(NumValue::Int(_)) = kind {
            } else {
                stacktrace.panic(format!["expected an int received {:?}", kind]);
            };
        }

        Type::Num(NumType::Float) => {
            if let Value::Num(NumValue::Float(_)) = kind {
            } else {
                stacktrace.panic(format!["expected an float received {:?}", kind]);
            };
        }

        Type::Array(item_type) => {
            if let Value::Array(_, ptr) = kind {
                match ptr {
                    Some(ptr) => {
                        if let Value::ArrayContent(_, values) = &heap[*ptr] {
                            typecheck_many(
                                heap,
                                &values,
                                item_type,
                                &seen,
                                stacktrace.add_frame("typechecking array interior"),
                            );
                        } else {
                            stacktrace
                                .panic(format!["expected array content received {:?}", heap[*ptr]]);
                        }
                    }
                    None => {
                        // pass
                    }
                }
            } else {
                stacktrace.panic(format!["expected an array received {:?}", kind]);
            }
        }

        Type::HoleArray(item_type) => {
            if let Value::HoleArray(_, _, ptr) = kind {
                if let Value::ArrayContent(_, values) = &heap[*ptr] {
                    typecheck_many(
                        heap,
                        &values,
                        item_type,
                        &seen,
                        stacktrace.add_frame("typechecking array interior"),
                    );
                } else {
                    stacktrace.panic(format!["expected array content received {:?}", heap[*ptr]]);
                }
            } else {
                stacktrace.panic(format!["expected an array received {:?}", kind]);
            }
        }

        Type::Tuple(item_types) => {
            if let Value::Tuple(values) = kind {
                if item_types.len() != values.len() {
                    stacktrace.panic(format![
                        "tuple type does not match runtime length, expected {}, got {:?}",
                        item_types.len(),
                        kind
                    ]);
                }

                for (item_type, value) in item_types.iter().zip(values.iter()) {
                    typecheck_rec(
                        heap,
                        *value,
                        &*item_type,
                        &seen,
                        stacktrace.add_frame("typechecking tuple interior"),
                    );
                }
            } else {
                stacktrace.panic(format!["expected a tuple received {:?}", kind]);
            }
        }

        Type::Variants(variants) => {
            if let Value::Variant(variant_id, heap_id) = kind {
                if variant_id.0 >= variants.len() {
                    stacktrace.panic(format![
                        "variant id is out of bounds, {} >= {}",
                        variant_id.0,
                        variants.len()
                    ])
                }

                typecheck_rec(
                    heap,
                    *heap_id,
                    &variants[variant_id],
                    &seen,
                    stacktrace.add_frame("typechecking variant interior"),
                );
            } else {
                stacktrace.panic(format!["expected a variant received {:?}", kind]);
            }
        }

        Type::Boxed(boxed_type) => {
            if let Value::Box(_rc, heap_id) = kind {
                typecheck_rec(
                    heap,
                    *heap_id,
                    &*boxed_type,
                    &seen,
                    stacktrace.add_frame("typechecking box interior"),
                );
            } else {
                stacktrace.panic(format!["expected a box received {:?}", kind]);
            }
        }

        Type::Custom(custom_type_id) => {
            let customs = &heap.program.custom_types.types;
            typecheck_rec(
                heap,
                heap_id,
                &customs[*custom_type_id],
                &original_seen,
                stacktrace.add_frame("typechecking custom interior"),
            );
        }
    }
}

fn unwrap_bool(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> bool {
    let kind = assert_live(heap, heap_id, stacktrace.add_frame("unwrap bool"));
    if let Value::Bool(val) = kind {
        *val
    } else {
        stacktrace.panic(format!["expected a bool received {:?}", kind]);
    }
}

fn unwrap_byte(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> Wrapping<u8> {
    let kind = assert_live(heap, heap_id, stacktrace.add_frame("unwrap byte"));
    if let Value::Num(NumValue::Byte(val)) = kind {
        *val
    } else {
        stacktrace.panic(format!["expected a byte received {:?}", kind]);
    }
}

fn unwrap_int(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> Wrapping<i64> {
    let kind = assert_live(heap, heap_id, stacktrace.add_frame("unwrap int"));
    if let Value::Num(NumValue::Int(val)) = kind {
        *val
    } else {
        stacktrace.panic(format!["expected an int received {:?}", kind]);
    }
}

fn unwrap_float(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> f64 {
    let kind = assert_live(heap, heap_id, stacktrace.add_frame("unwrap float"));
    if let Value::Num(NumValue::Float(val)) = kind {
        *val
    } else {
        stacktrace.panic(format!["expected a float received {:?}", kind]);
    }
}

fn unwrap_pair(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> (HeapId, HeapId) {
    let pair = unwrap_tuple(heap, heap_id, stacktrace.add_frame("unwrap pair"));
    if pair.len() != 2 {
        stacktrace.panic(format!["expected a pair, received {:?}", pair]);
    }
    (pair[0], pair[1])
}

fn unwrap_binop_bytes(
    heap: &Heap,
    heap_id: HeapId,
    stacktrace: StackTrace,
) -> (Wrapping<u8>, Wrapping<u8>) {
    let (lhs_id, rhs_id) = unwrap_pair(heap, heap_id, stacktrace.add_frame("unwrap binop bytes"));
    (
        unwrap_byte(heap, lhs_id, stacktrace.add_frame("unwrap binop bytes")),
        unwrap_byte(heap, rhs_id, stacktrace.add_frame("unwrap binop bytes")),
    )
}

fn unwrap_binop_ints(
    heap: &Heap,
    heap_id: HeapId,
    stacktrace: StackTrace,
) -> (Wrapping<i64>, Wrapping<i64>) {
    let (lhs_id, rhs_id) = unwrap_pair(heap, heap_id, stacktrace.add_frame("unwrap binop ints"));
    (
        unwrap_int(heap, lhs_id, stacktrace.add_frame("unwrap binop ints")),
        unwrap_int(heap, rhs_id, stacktrace.add_frame("unwrap binop ints")),
    )
}

fn unwrap_binop_floats(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> (f64, f64) {
    let (lhs_id, rhs_id) = unwrap_pair(heap, heap_id, stacktrace.add_frame("unwrap binop floats"));
    (
        unwrap_float(heap, lhs_id, stacktrace.add_frame("unwrap binop floats")),
        unwrap_float(heap, rhs_id, stacktrace.add_frame("unwrap binop floats")),
    )
}

fn unwrap_array_content<'a>(
    heap: &'a mut Heap,
    ptr: HeapId,
    stacktrace: StackTrace,
) -> &'a mut Vec<HeapId> {
    match &mut heap[ptr] {
        Value::ArrayContent(rc, content) => {
            if *rc <= 0 {
                stacktrace.panic(format!["accessing rc {rc} array"]);
            } else {
                content
            }
        }
        kind => {
            stacktrace.panic(format!["expected array content received {:?}", kind]);
        }
    }
}

fn unwrap_tuple(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> Vec<HeapId> {
    let kind = assert_live(heap, heap_id, stacktrace.add_frame("unwrap tuple"));
    if let Value::Tuple(values) = kind {
        values.clone()
    } else {
        stacktrace.panic(format!["expected a tuple received {:?}", kind]);
    }
}

fn unwrap_variant(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> (VariantId, HeapId) {
    let kind = assert_live(heap, heap_id, stacktrace.add_frame("unwrap variant"));
    if let Value::Variant(variant_id, heap_id) = kind {
        (*variant_id, *heap_id)
    } else {
        stacktrace.panic(format!["expected a variant received {:?}", kind]);
    }
}

fn unwrap_boxed(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> HeapId {
    let kind = assert_live(heap, heap_id, stacktrace.add_frame("unwrap boxed"));
    if let Value::Box(_rc, heap_id) = kind {
        *heap_id
    } else {
        stacktrace.panic(format!["expected a box received {:?}", kind]);
    }
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

fn obtain_unique<'a>(
    custom_schemes: &IdVec<ModeSchemeId, ModeScheme>,
    ptr: HeapId,
    scheme: &ModeScheme,
    heap: &'a mut Heap,
    stacktrace: StackTrace,
) -> HeapId {
    assert_live(&heap, ptr, stacktrace.add_frame("obtain unique"));

    let Value::ArrayContent(rc, values) = &mut heap[ptr] else {
        stacktrace.panic(format!["expected array content received {:?}", heap[ptr]]);
    };

    if *rc == 1 {
        return ptr;
    } else {
        let values = values.clone();
        *rc -= 1;

        let (ModeScheme::Array(mode, item_scheme) | ModeScheme::HoleArray(mode, item_scheme)) =
            scheme
        else {
            stacktrace.panic(format!["expected an array scheme, got {:?}", scheme]);
        };
        if *mode != Mode::Owned {
            stacktrace.panic(format!["expected an owned array"]);
        }
        for &item_id in &values {
            derived_retain(
                custom_schemes,
                heap,
                item_id,
                item_scheme,
                stacktrace.add_frame("obtain unique"),
            );
        }

        heap.add(Value::ArrayContent(1, values.clone()))
    }
}

fn new_array(heap: &mut Heap, values: Vec<HeapId>) -> HeapId {
    let content_id = heap.add(Value::ArrayContent(1, values.clone()));
    let heap_id = heap.add(Value::Array(values.len(), Some(content_id)));
    heap_id
}

// This "red zone" value depends on the maximum stack space required by `interpret_expr`, which is
// determined experimentally.  If you make a change to `interpret_expr and` `cargo test` starts
// segfaulting, bump this value until it works.
const STACK_RED_ZONE_BYTES: usize = 256 * 1024;
const STACK_GROW_BYTES: usize = 1024 * 1024;

#[derive(Clone, Debug)]
enum Interruption {
    Exit(ExitStatus),
    TailCall(tail::TailFuncId, HeapId),
}

impl From<ExitStatus> for Interruption {
    fn from(status: ExitStatus) -> Interruption {
        Interruption::Exit(status)
    }
}

fn interpret_call(
    tail_renderer: &TailFuncRenderer<CustomFuncId>,
    func_id: CustomFuncId,
    arg_id: HeapId,
    stdin: &mut dyn BufRead,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
    program: &Program,
    heap: &mut Heap,
    stacktrace: StackTrace,
) -> Result<HeapId, ExitStatus> {
    let func = &program.funcs[func_id];
    let func_renderer = FuncRenderer::from_symbols(&func.tail_func_symbols);

    typecheck(
        heap,
        arg_id,
        &func.arg_type,
        stacktrace.add_frame(format![
            "typecheck function argument {}",
            tail_renderer.render(func_id)
        ]),
    );

    let mut result = interpret_expr(
        tail_renderer,
        &func.body,
        stdin,
        stdout,
        stderr,
        program,
        &Locals::new(arg_id),
        heap,
        stacktrace.add_frame(format![
            "func: {} arg: {:?}",
            tail_renderer.render(func_id),
            arg_id
        ]),
    );

    while let Err(Interruption::TailCall(tail_id, tail_arg)) = result {
        let tail_func = &func.tail_funcs[tail_id];

        typecheck(
            heap,
            tail_arg,
            &tail_func.arg_type,
            stacktrace.add_frame(format![
                "typecheck tail function argument {} {}",
                tail_renderer.render(func_id),
                func_renderer.render(tail_id)
            ]),
        );

        result = interpret_expr(
            tail_renderer,
            &tail_func.body,
            stdin,
            stdout,
            stderr,
            program,
            &Locals::new(tail_arg),
            heap,
            stacktrace.add_frame(format![
                "tail func: {} {} arg: {:?}",
                tail_renderer.render(func_id),
                func_renderer.render(tail_id),
                arg_id
            ]),
        );
    }

    match result {
        Ok(ret_id) => {
            typecheck(
                heap,
                ret_id,
                &func.ret_type,
                stacktrace.add_frame(format![
                    "typecheck function return: {}",
                    tail_renderer.render(func_id)
                ]),
            );

            Ok(ret_id)
        }
        Err(Interruption::Exit(status)) => Err(status),
        Err(Interruption::TailCall(_, _)) => unreachable!(),
    }
}

// We call this function when implementing built-ins that always take borrowed arguments under the
// normal rc elision, but owned arguments under Perceus. This is equivalent to calling `release`,
// but better expresses the intent of the caller.
fn discard_owned_input(
    custom_schemes: &IdVec<ModeSchemeId, ModeScheme>,
    heap: &mut Heap,
    heap_id: HeapId,
    scheme: &ModeScheme,
    stacktrace: StackTrace,
) {
    match scheme {
        ModeScheme::Array(_, _) | ModeScheme::HoleArray(_, _) | ModeScheme::Boxed(_, _) => {}
        _ => stacktrace.panic("expected an array or box type"),
    };
    // println!["RELEASING {}", heap.value_to_str(heap_id)];
    release(custom_schemes, heap, heap_id, scheme, stacktrace);
}

fn interpret_expr(
    func_renderer: &TailFuncRenderer<CustomFuncId>,
    expr: &Expr,
    stdin: &mut dyn BufRead,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
    program: &Program,
    locals: &Locals,
    heap: &mut Heap,
    stacktrace: StackTrace,
) -> Result<HeapId, Interruption> {
    stacker::maybe_grow(STACK_RED_ZONE_BYTES, STACK_GROW_BYTES, move || {
        Ok(match expr {
            Expr::Local(local_id) => locals[local_id],

            Expr::Call(func_id, arg_id) => interpret_call(
                func_renderer,
                *func_id,
                locals[arg_id],
                stdin,
                stdout,
                stderr,
                program,
                heap,
                stacktrace,
            )?,

            Expr::TailCall(tail_func_id, arg_id) => {
                return Err(Interruption::TailCall(*tail_func_id, locals[*arg_id]));
            }

            Expr::If(discrim_id, then_branch, else_branch) => {
                let discrim_value = unwrap_bool(
                    heap,
                    locals[discrim_id],
                    stacktrace.add_frame("computing discriminant of if"),
                );

                if discrim_value {
                    interpret_expr(
                        func_renderer,
                        then_branch,
                        stdin,
                        stdout,
                        stderr,
                        program,
                        locals,
                        heap,
                        stacktrace.add_frame("going into if branch"),
                    )?
                } else {
                    interpret_expr(
                        func_renderer,
                        else_branch,
                        stdin,
                        stdout,
                        stderr,
                        program,
                        locals,
                        heap,
                        stacktrace.add_frame("going into else branch"),
                    )?
                }
            }

            Expr::LetMany(bindings, final_local_id) => {
                let mut new_locals = locals.clone();

                for (expected_type, let_expr, _) in bindings {
                    let local_heap_id = interpret_expr(
                        func_renderer,
                        let_expr,
                        stdin,
                        stdout,
                        stderr,
                        program,
                        &new_locals,
                        heap,
                        stacktrace
                            .add_frame(format!["evaluating let expr {}", new_locals.values.len()]),
                    )?;

                    typecheck(
                        heap,
                        local_heap_id,
                        &expected_type,
                        stacktrace.add_frame(format![
                            "typechecking let return value {}",
                            new_locals.values.len()
                        ]),
                    );

                    new_locals.add(local_heap_id);
                }

                new_locals[final_local_id]
            }

            Expr::Unreachable(_) => stacktrace.panic("encountered unreachable code"),

            Expr::Tuple(elem_ids) => heap.add(Value::Tuple(
                elem_ids.iter().map(|elem_id| locals[*elem_id]).collect(),
            )),

            Expr::TupleField(tuple_id, index) => {
                let tuple =
                    unwrap_tuple(heap, locals[tuple_id], stacktrace.add_frame("tuple_field"));
                match tuple.get(*index) {
                    Some(heap_id) => *heap_id,
                    None => {
                        stacktrace.panic(format![
                            "tuple fields out of bound: {}, got {:?}",
                            index, tuple
                        ]);
                    }
                }
            }

            Expr::WrapVariant(variants, variant_id, local_id) => {
                let heap_id = locals[local_id];
                typecheck(
                    heap,
                    heap_id,
                    &variants[variant_id],
                    stacktrace.add_frame("wrap variant"),
                );

                heap.add(Value::Variant(*variant_id, heap_id))
            }

            Expr::UnwrapVariant(variants, variant_id, local_id) => {
                let heap_id = locals[local_id];
                typecheck(
                    heap,
                    heap_id,
                    &Type::Variants(variants.clone()),
                    stacktrace.add_frame("unwrap variant"),
                );
                let (runtime_variant_id, local_variant_id) =
                    unwrap_variant(heap, heap_id, stacktrace.add_frame("unwrap variant"));

                if *variant_id != runtime_variant_id {
                    stacktrace.panic(format![
                        "unwrap variant ids not equal {:?} != {:?}",
                        variant_id, runtime_variant_id
                    ]);
                }

                local_variant_id
            }

            // Customs don't exist in the dynamics; there is nothing to do operationally
            Expr::WrapCustom(_, local_id) => locals[local_id],
            Expr::UnwrapCustom(_, local_id) => locals[local_id],

            Expr::WrapBoxed(local_id, output_scheme) => {
                let Type::Boxed(item_type) = output_scheme.as_type() else {
                    stacktrace.panic(format!["expected a boxed type, got {:?}", output_scheme]);
                };
                typecheck(
                    heap,
                    locals[local_id],
                    &item_type,
                    stacktrace.add_frame("wrap boxed typecheck"),
                );

                let heap_id = locals[local_id];
                heap.add(Value::Box(1, heap_id))
            }

            Expr::UnwrapBoxed(local_id, input_scheme, output_scheme) => {
                let heap_id = locals[local_id];
                let local_heap_id =
                    unwrap_boxed(heap, heap_id, stacktrace.add_frame("unwrap boxed"));

                typecheck(
                    heap,
                    local_heap_id,
                    &output_scheme.as_type(),
                    stacktrace.add_frame("unwrap boxed typecheck"),
                );

                discard_owned_input(&program.schemes, heap, heap_id, input_scheme, stacktrace);
                local_heap_id
            }

            Expr::RcOp(scheme, RcOp::Retain, local_id) => {
                typecheck(
                    heap,
                    locals[local_id],
                    &scheme.as_type(),
                    stacktrace.add_frame("retain typecheck"),
                );

                retain(heap, scheme, locals[local_id], stacktrace);

                HeapId(0)
            }

            Expr::RcOp(scheme, RcOp::Release, local_id) => {
                typecheck(
                    heap,
                    locals[local_id],
                    &scheme.as_type(),
                    stacktrace.add_frame("retain typecheck"),
                );
                release(&program.schemes, heap, locals[local_id], scheme, stacktrace);

                HeapId(0)
            }

            Expr::CheckVariant(variant_id, local_id) => {
                let heap_id = locals[local_id];

                let (local_variant_id, _local_heap_id) =
                    unwrap_variant(heap, heap_id, stacktrace.add_frame("check variant"));

                heap.add(Value::Bool(*variant_id == local_variant_id))
            }

            Expr::Intrinsic(Intrinsic::Not, local_id) => {
                let heap_id = locals[local_id];

                let value = !unwrap_bool(heap, heap_id, stacktrace.add_frame("check bool"));

                heap.add(Value::Bool(value))
            }

            Expr::Intrinsic(Intrinsic::AddByte, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_bytes(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Num(NumValue::Byte(lhs + rhs)))
            }

            Expr::Intrinsic(Intrinsic::AddInt, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_ints(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Num(NumValue::Int(lhs + rhs)))
            }

            Expr::Intrinsic(Intrinsic::AddFloat, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_floats(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Num(NumValue::Float(lhs + rhs)))
            }

            Expr::Intrinsic(Intrinsic::SubByte, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_bytes(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Num(NumValue::Byte(lhs - rhs)))
            }

            Expr::Intrinsic(Intrinsic::SubInt, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_ints(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Num(NumValue::Int(lhs - rhs)))
            }

            Expr::Intrinsic(Intrinsic::SubFloat, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_floats(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Num(NumValue::Float(lhs - rhs)))
            }

            Expr::Intrinsic(Intrinsic::MulByte, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_bytes(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Num(NumValue::Byte(lhs * rhs)))
            }

            Expr::Intrinsic(Intrinsic::MulInt, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_ints(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Num(NumValue::Int(lhs * rhs)))
            }

            Expr::Intrinsic(Intrinsic::MulFloat, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_floats(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Num(NumValue::Float(lhs * rhs)))
            }

            Expr::Intrinsic(Intrinsic::DivByte, local_id) => {
                let (numerator, divisor) =
                    unwrap_binop_bytes(heap, locals[local_id], stacktrace.add_frame("arith"));

                if divisor.0 == 0 {
                    writeln!(stderr, "panicked due to division by zero").unwrap();
                    return Err(Interruption::Exit(ExitStatus::Failure(Some(1))));
                }

                heap.add(Value::Num(NumValue::Byte(numerator / divisor)))
            }

            Expr::Intrinsic(Intrinsic::DivInt, local_id) => {
                let (numerator, divisor) =
                    unwrap_binop_ints(heap, locals[local_id], stacktrace.add_frame("arith"));

                if divisor.0 == 0 {
                    writeln!(stderr, "panicked due to division by zero").unwrap();
                    return Err(Interruption::Exit(ExitStatus::Failure(Some(1))));
                }

                heap.add(Value::Num(NumValue::Int(numerator / divisor)))
            }

            Expr::Intrinsic(Intrinsic::DivFloat, local_id) => {
                let (numerator, divisor) =
                    unwrap_binop_floats(heap, locals[local_id], stacktrace.add_frame("arith"));

                heap.add(Value::Num(NumValue::Float(numerator / divisor)))
            }

            Expr::Intrinsic(Intrinsic::LtByte, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_bytes(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs < rhs))
            }

            Expr::Intrinsic(Intrinsic::LtInt, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_ints(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs < rhs))
            }

            Expr::Intrinsic(Intrinsic::LtFloat, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_floats(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs < rhs))
            }

            Expr::Intrinsic(Intrinsic::LteByte, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_bytes(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs <= rhs))
            }

            Expr::Intrinsic(Intrinsic::LteInt, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_ints(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs <= rhs))
            }

            Expr::Intrinsic(Intrinsic::LteFloat, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_floats(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs <= rhs))
            }

            Expr::Intrinsic(Intrinsic::GtByte, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_bytes(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs > rhs))
            }

            Expr::Intrinsic(Intrinsic::GtInt, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_ints(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs > rhs))
            }

            Expr::Intrinsic(Intrinsic::GtFloat, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_floats(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs > rhs))
            }

            Expr::Intrinsic(Intrinsic::GteByte, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_bytes(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs >= rhs))
            }

            Expr::Intrinsic(Intrinsic::GteInt, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_ints(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs >= rhs))
            }

            Expr::Intrinsic(Intrinsic::GteFloat, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_floats(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs >= rhs))
            }

            Expr::Intrinsic(Intrinsic::EqByte, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_bytes(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs == rhs))
            }

            Expr::Intrinsic(Intrinsic::EqInt, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_ints(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs == rhs))
            }

            Expr::Intrinsic(Intrinsic::EqFloat, local_id) => {
                let (lhs, rhs) =
                    unwrap_binop_floats(heap, locals[local_id], stacktrace.add_frame("arith"));
                heap.add(Value::Bool(lhs == rhs))
            }

            // Don't negate a byte u dummy
            Expr::Intrinsic(Intrinsic::NegByte, local_id) => heap.add(Value::Num(NumValue::Byte(
                -unwrap_byte(heap, locals[local_id], stacktrace.add_frame("arith")),
            ))),

            Expr::Intrinsic(Intrinsic::NegInt, local_id) => heap.add(Value::Num(NumValue::Int(
                -unwrap_int(heap, locals[local_id], stacktrace.add_frame("arith")),
            ))),

            Expr::Intrinsic(Intrinsic::NegFloat, local_id) => {
                heap.add(Value::Num(NumValue::Float(-unwrap_float(
                    heap,
                    locals[local_id],
                    stacktrace.add_frame("arith"),
                ))))
            }

            Expr::Intrinsic(Intrinsic::ByteToInt, local_id) => {
                heap.add(Value::Num(NumValue::Int(Wrapping(
                    unwrap_byte(heap, locals[local_id], stacktrace.add_frame("byte_to_int")).0
                        as i64,
                ))))
            }

            Expr::Intrinsic(Intrinsic::ByteToIntSigned, local_id) => {
                heap.add(Value::Num(NumValue::Int(Wrapping(
                    unwrap_byte(heap, locals[local_id], stacktrace.add_frame("byte_to_int")).0 as i8
                        as i64,
                ))))
            }

            Expr::Intrinsic(Intrinsic::IntToByte, local_id) => {
                heap.add(Value::Num(NumValue::Byte(Wrapping(
                    unwrap_int(heap, locals[local_id], stacktrace.add_frame("int_to_byte")).0 as u8,
                ))))
            }

            Expr::Intrinsic(Intrinsic::IntShiftLeft, local_id) => {
                let args = unwrap_tuple(
                    heap,
                    locals[local_id],
                    stacktrace.add_frame("int_shift_left"),
                );
                assert_eq!(args.len(), 2);
                let left = unwrap_int(heap, args[0], stacktrace.add_frame("int_shift_left"));
                let right = unwrap_int(heap, args[1], stacktrace.add_frame("int_shift_left"));
                heap.add(Value::Num(NumValue::Int(Wrapping(
                    left.0 << (right.0 as u64 % 64),
                ))))
            }

            Expr::Intrinsic(Intrinsic::IntShiftRight, local_id) => {
                let args = unwrap_tuple(
                    heap,
                    locals[local_id],
                    stacktrace.add_frame("int_shift_right"),
                );
                assert_eq!(args.len(), 2);
                let left = unwrap_int(heap, args[0], stacktrace.add_frame("int_shift_right"));
                let right = unwrap_int(heap, args[1], stacktrace.add_frame("int_shift_right"));
                heap.add(Value::Num(NumValue::Int(Wrapping(
                    ((left.0 as u64) >> (right.0 as u64 % 64)) as i64,
                ))))
            }

            Expr::Intrinsic(Intrinsic::IntBitAnd, local_id) => {
                let args =
                    unwrap_tuple(heap, locals[local_id], stacktrace.add_frame("int_bit_and"));
                assert_eq!(args.len(), 2);
                let left = unwrap_int(heap, args[0], stacktrace.add_frame("int_bit_and"));
                let right = unwrap_int(heap, args[1], stacktrace.add_frame("int_bit_and"));
                heap.add(Value::Num(NumValue::Int(left & right)))
            }

            Expr::Intrinsic(Intrinsic::IntBitOr, local_id) => {
                let args = unwrap_tuple(heap, locals[local_id], stacktrace.add_frame("int_bit_or"));
                assert_eq!(args.len(), 2);
                let left = unwrap_int(heap, args[0], stacktrace.add_frame("int_bit_or"));
                let right = unwrap_int(heap, args[1], stacktrace.add_frame("int_bit_or"));
                heap.add(Value::Num(NumValue::Int(left | right)))
            }

            Expr::Intrinsic(Intrinsic::IntBitXor, local_id) => {
                let args =
                    unwrap_tuple(heap, locals[local_id], stacktrace.add_frame("int_bit_xor"));
                assert_eq!(args.len(), 2);
                let left = unwrap_int(heap, args[0], stacktrace.add_frame("int_bit_xor"));
                let right = unwrap_int(heap, args[1], stacktrace.add_frame("int_bit_xor"));
                heap.add(Value::Num(NumValue::Int(left ^ right)))
            }

            Expr::Intrinsic(Intrinsic::IntCtpop, local_id) => {
                let value = unwrap_int(heap, locals[local_id], stacktrace.add_frame("int_ctpop"));
                heap.add(Value::Num(NumValue::Int(Wrapping(
                    value.0.count_ones() as i64
                ))))
            }

            Expr::Intrinsic(Intrinsic::IntCtlz, local_id) => {
                let value = unwrap_int(heap, locals[local_id], stacktrace.add_frame("int_ctlz"));
                heap.add(Value::Num(NumValue::Int(Wrapping(
                    value.0.leading_zeros() as i64
                ))))
            }

            Expr::Intrinsic(Intrinsic::IntCttz, local_id) => {
                let value = unwrap_int(heap, locals[local_id], stacktrace.add_frame("int_cttz"));
                heap.add(Value::Num(NumValue::Int(Wrapping(
                    value.0.trailing_zeros() as i64,
                ))))
            }

            Expr::ArrayOp(_scheme, ArrayOp::New) => heap.add(Value::Array(0, None)),

            Expr::ArrayOp(scheme, ArrayOp::Len(array_id)) => {
                let array_id = locals[array_id];

                // We *intentionally* avoid asserting that the array is live here. It needn't be
                // since `len` does not access the heap under the LLVM backend.
                let kind = &heap[array_id];
                let result = match kind {
                    Value::Array(len, _) => {
                        heap.add(Value::Num(NumValue::Int(Wrapping(*len as i64))))
                    }
                    _ => {
                        stacktrace.panic(format!["expected an array received {:?}", kind]);
                    }
                };

                discard_owned_input(&program.schemes, heap, array_id, scheme, stacktrace);
                result
            }

            Expr::ArrayOp(scheme, ArrayOp::Push(array_id, item_id)) => {
                let array_id = locals[array_id];
                let item_heap_id = locals[item_id];
                match &heap[array_id] {
                    Value::Array(_, None) => new_array(heap, vec![item_heap_id]),
                    Value::Array(len, Some(ptr)) => {
                        let len = *len;
                        let ptr = obtain_unique(
                            &program.schemes,
                            *ptr,
                            scheme,
                            heap,
                            stacktrace.add_frame("array push"),
                        );
                        let array =
                            unwrap_array_content(heap, ptr, stacktrace.add_frame("array push"));
                        array.push(item_heap_id);
                        heap.add(Value::Array(len + 1, Some(ptr)))
                    }
                    kind => {
                        stacktrace.panic(format!["expected an array received {:?}", kind]);
                    }
                }
            }

            Expr::ArrayOp(scheme, ArrayOp::Pop(array_id)) => {
                let array_id = locals[array_id];

                match &heap[array_id] {
                    Value::Array(_len, None) => {
                        writeln!(stderr, "pop: empty array").unwrap();
                        return Err(Interruption::Exit(ExitStatus::Failure(Some(1))));
                    }
                    Value::Array(len, Some(ptr)) => {
                        let len = *len;
                        if len == 0 {
                            writeln!(stderr, "pop: empty array").unwrap();
                            return Err(Interruption::Exit(ExitStatus::Failure(Some(1))));
                        } else {
                            let ptr = obtain_unique(
                                &program.schemes,
                                *ptr,
                                scheme,
                                heap,
                                stacktrace.add_frame("array pop"),
                            );

                            let array =
                                unwrap_array_content(heap, ptr, stacktrace.add_frame("array pop"));
                            let item_heap_id = array.pop().unwrap();
                            let array_id = heap.add(Value::Array(len - 1, Some(ptr)));
                            heap.add(Value::Tuple(vec![array_id, item_heap_id]))
                        }
                    }
                    kind => {
                        stacktrace.panic(format!["expected an array received {:?}", kind]);
                    }
                }
            }

            Expr::ArrayOp(scheme, ArrayOp::Get(array_id, index_id)) => {
                let array_heap_id = locals[array_id];
                let index_heap_id = locals[index_id];

                let index = unwrap_int(heap, index_heap_id, stacktrace.add_frame("get index"));

                let result = match &heap[array_heap_id] {
                    Value::Array(_, None) => {
                        bounds_check(stderr, 0, index.0)?;
                        unreachable!()
                    }
                    Value::Array(_, Some(ptr)) => {
                        let array = unwrap_array_content(heap, *ptr, stacktrace.add_frame("get"));
                        bounds_check(stderr, array.len(), index.0)?;

                        array[index.0 as usize]
                    }
                    kind => {
                        stacktrace.panic(format!["expected an array received {:?}", kind]);
                    }
                };

                discard_owned_input(&program.schemes, heap, array_heap_id, scheme, stacktrace);
                result
            }

            Expr::ArrayOp(scheme, ArrayOp::Extract(array_id, index_id)) => {
                let array_id = locals[array_id];
                let index_heap_id = locals[index_id];

                let index = unwrap_int(heap, index_heap_id, stacktrace.add_frame("extract index"));

                match &heap[array_id] {
                    Value::Array(_, None) => {
                        bounds_check(stderr, 0, index.0)?;
                        unreachable!()
                    }
                    Value::Array(len, Some(ptr)) => {
                        let len = *len;
                        let ptr = obtain_unique(
                            &program.schemes,
                            *ptr,
                            scheme,
                            heap,
                            stacktrace.add_frame("array pop"),
                        );

                        let array =
                            unwrap_array_content(heap, ptr, stacktrace.add_frame("array pop"));

                        bounds_check(stderr, array.len(), index.0)?;

                        let get_item = array[index.0 as usize];

                        let hole_array_id = heap.add(Value::HoleArray(len, index.0, ptr));
                        heap.add(Value::Tuple(vec![get_item, hole_array_id]))
                    }
                    kind => {
                        stacktrace.panic(format!["expected an array received {:?}", kind]);
                    }
                }
            }

            Expr::ArrayOp(scheme, ArrayOp::Replace(array_id, item_id)) => {
                let array_heap_id = locals[array_id];
                let item_heap_id = locals[item_id];
                match &heap[array_heap_id] {
                    Value::HoleArray(len, idx, ptr) => {
                        let len = *len;
                        let idx = *idx;
                        let ptr = obtain_unique(
                            &program.schemes,
                            *ptr,
                            scheme,
                            heap,
                            stacktrace.add_frame("array replace"),
                        );

                        let array =
                            unwrap_array_content(heap, ptr, stacktrace.add_frame("array replace"));

                        array[idx as usize] = item_heap_id;

                        heap.add(Value::Array(len, Some(ptr)))
                    }

                    kind => {
                        stacktrace.panic(format!["expected a hole array received {:?}", kind]);
                    }
                }
            }

            Expr::ArrayOp(_scheme, ArrayOp::Reserve(array_id, capacity_id)) => {
                let array_heap_id = locals[array_id];
                let index = unwrap_int(
                    heap,
                    locals[capacity_id],
                    stacktrace.add_frame("reserve capacity"),
                );

                match &mut heap[array_heap_id] {
                    Value::Array(_len, None) => {
                        if index.0 > 0 {
                            new_array(heap, vec![])
                        } else {
                            array_heap_id
                        }
                    }
                    Value::Array(_rc, _array) => array_heap_id,
                    kind => {
                        stacktrace.panic(format!["expected an array received {:?}", kind]);
                    }
                }
            }

            Expr::IoOp(IoOp::Input) => {
                let mut input = String::new();
                stdin
                    .read_line(&mut input)
                    .ok()
                    .expect("failed reading stdin");
                if input.ends_with('\n') {
                    input.pop();
                }

                let mut heap_ids = vec![];
                for byte in input.into_bytes().into_iter() {
                    heap_ids.push(heap.add(Value::Num(NumValue::Byte(Wrapping(byte)))));
                }

                new_array(heap, heap_ids)
            }

            Expr::IoOp(IoOp::Output(input_scheme, array_id)) => {
                let array_heap_id = locals[array_id];

                let Value::Array(_, ptr) = heap[array_heap_id] else {
                    stacktrace.add_frame("output").panic(format!(
                        "expected an array received {:?}",
                        heap[array_heap_id]
                    ));
                };

                let result = match ptr {
                    None => HeapId(0),

                    Some(ptr) => {
                        let array =
                            unwrap_array_content(heap, ptr, stacktrace.add_frame("output")).clone();

                        let mut bytes = vec![];
                        for heap_id in array {
                            bytes.push(unwrap_byte(
                                heap,
                                heap_id,
                                stacktrace.add_frame("output byte"),
                            ));
                        }

                        write!(
                            stdout,
                            "{}",
                            String::from_utf8(bytes.iter().map(|&Wrapping(byte)| byte).collect())
                                .expect("UTF-8 output error")
                        )
                        .expect("write failed");

                        HeapId(0)
                    }
                };

                // println!["DISCARDING {:?}", heap.value_to_str(array_heap_id)];
                // println!["scheme {:?}", input_scheme];
                discard_owned_input(
                    &program.schemes,
                    heap,
                    array_heap_id,
                    input_scheme,
                    stacktrace,
                );
                result
            }

            Expr::Panic(_ret_type, input_scheme, array_id) => {
                let array_heap_id = locals[array_id];

                let Value::Array(_, ptr) = heap[array_heap_id] else {
                    stacktrace.add_frame("panic").panic(format!(
                        "expected an array received {:?}",
                        heap[array_heap_id]
                    ));
                };

                let result = match ptr {
                    None => HeapId(0),

                    Some(ptr) => {
                        let array =
                            unwrap_array_content(heap, ptr, stacktrace.add_frame("panic")).clone();

                        let mut bytes = vec![];
                        for heap_id in array {
                            bytes.push(unwrap_byte(
                                heap,
                                heap_id,
                                stacktrace.add_frame("panic byte"),
                            ));
                        }

                        write!(
                            stderr,
                            "{}",
                            String::from_utf8(bytes.iter().map(|&Wrapping(byte)| byte).collect())
                                .expect("UTF-8 output error")
                        )
                        .expect("write failed");

                        return Err(Interruption::Exit(ExitStatus::Failure(Some(1))));
                    }
                };

                discard_owned_input(
                    &program.schemes,
                    heap,
                    array_heap_id,
                    input_scheme,
                    stacktrace,
                );
                result
            }

            Expr::BoolLit(val) => heap.add(Value::Bool(*val)),

            Expr::ByteLit(val) => heap.add(Value::Num(NumValue::Byte(Wrapping(*val)))),

            Expr::IntLit(val) => heap.add(Value::Num(NumValue::Int(Wrapping(*val)))),

            Expr::FloatLit(val) => heap.add(Value::Num(NumValue::Float(*val))),
        })
    })
}

pub fn interpret(stdio: Stdio, program: Program) -> Child {
    spawn_thread(stdio, move |stdin, stdout, stderr| {
        let func_renderer = TailFuncRenderer::from_symbols(&program.func_symbols);
        let mut heap = Heap::new(&program);
        match interpret_call(
            &func_renderer,
            program.main,
            HeapId(0),
            stdin,
            stdout,
            stderr,
            &program,
            &mut heap,
            StackTrace::new(),
        ) {
            Ok(final_heap_id) => {
                typecheck(
                    &heap,
                    final_heap_id,
                    &Type::Tuple(vec![]),
                    StackTrace::new(),
                );
                heap.assert_everything_else_deallocated();
                Ok(ExitStatus::Success)
            }
            Err(status) => Ok(status),
        }
    })
}
