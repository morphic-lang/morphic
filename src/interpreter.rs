use crate::data::first_order_ast::{BinOp, Comparison, NumType};
use crate::data::intrinsics::Intrinsic;
use crate::data::low_ast::{
    ArithOp, ArrayOp, CustomFuncId, CustomTypeId, Expr, IoOp, LocalId, Program, Type, VariantId,
};
use crate::data::repr_constrained_ast::RepChoice;
use crate::data::tail_rec_ast as tail;
use crate::pseudoprocess::{spawn_thread, Child, ExitStatus, Stdio};
use im_rc::Vector;
use stacker;
use std::borrow::Borrow;
use std::convert::TryFrom;
use std::io::BufRead;
use std::io::Write;
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

// only meaningful for flat arrays
#[derive(Debug, Clone, PartialEq, Eq)]
enum ArrayStatus {
    Invalid,
    Valid,
}

#[derive(Debug, Clone)]
enum Value {
    Bool(bool),
    Num(NumValue),
    Array(RepChoice, ArrayStatus, RefCount, Vec<HeapId>),
    HoleArray(RepChoice, ArrayStatus, RefCount, i64, Vec<HeapId>),
    Tuple(Vec<HeapId>),
    Variant(VariantId, HeapId),
    Box(RefCount, HeapId),
    Custom(CustomTypeId, HeapId),
}

impl Value {
    fn assert_live(&self, stacktrace: StackTrace) -> &Value {
        match self {
            Value::Array(_, _, rc, _) | Value::HoleArray(_, _, rc, _, _) | Value::Box(rc, _) => {
                if *rc == 0 {
                    stacktrace.panic(format!["accessing rc 0 value {:?}", &self]);
                }
            }
            _ => {}
        };

        match &self {
            Value::Array(RepChoice::OptimizedMut, status, _rc, _values)
            | Value::HoleArray(RepChoice::OptimizedMut, status, _rc, _, _values) => {
                if *status != ArrayStatus::Valid {
                    stacktrace.panic(format!["accessing invalid flat array {:?}", self]);
                }
            }
            _ => {}
        }

        self
    }
}

#[derive(Debug, Clone)]
struct StackTrace(Vector<Rc<String>>);

impl StackTrace {
    fn new() -> StackTrace {
        StackTrace({
            let mut v = Vector::new();
            v.push_front(Rc::new("Stacktrace:".into()));
            v
        })
    }

    fn add_frame(&self, s: String) -> StackTrace {
        StackTrace({
            let mut v = self.0.clone();
            v.push_back(Rc::new(s.lines().collect::<Vec<&str>>().join(" ")));
            v
        })
    }

    fn panic(&self, s: String) -> ! {
        println![
            "{}",
            self.0
                .iter()
                .map(|x| (**x).clone())
                .collect::<Vec<String>>()
                .join("\n")
        ];
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

#[derive(Clone, Debug, Copy)]
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
            Value::Num(NumValue::Byte(Wrapping(val))) => (*val as char).to_string(),
            Value::Num(NumValue::Int(Wrapping(val))) => val.to_string(),
            Value::Num(NumValue::Float(val)) => val.to_string(),
            Value::Array(rep, status, rc, contents) => {
                let rep_str = match rep {
                    RepChoice::OptimizedMut => "flat",
                    RepChoice::FallbackImmut => "persistent",
                };
                let status_str = match status {
                    ArrayStatus::Valid => "",
                    ArrayStatus::Invalid => "invalid ",
                };
                let contents_str = contents
                    .iter()
                    .map(|heap_id| self.value_to_str(*heap_id))
                    .collect::<Vec<String>>()
                    .join(",");
                format![
                    "{}{} rc:{} array [{}]",
                    status_str, rep_str, rc, contents_str
                ]
            }
            Value::HoleArray(rep, status, rc, hole, contents) => {
                let rep_str = match rep {
                    RepChoice::OptimizedMut => "flat",
                    RepChoice::FallbackImmut => "persistent",
                };
                let status_str = match status {
                    ArrayStatus::Valid => "",
                    ArrayStatus::Invalid => "invalid ",
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
                format![
                    "{}{} hole array rc:{} [{}]",
                    status_str, rep_str, rc, contents_str
                ]
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
            Value::Box(rc, heap_id) => format!["box rc:{} ({})", rc, self.value_to_str(*heap_id)],
            Value::Custom(type_id, heap_id) => {
                format!["custom #{} ({})", type_id.0, self.value_to_str(*heap_id)]
            }
        }
    }

    fn assert_everything_else_deallocated(&self) {
        let mut not_freed_values = vec![];
        for (index, value) in self.values.iter().enumerate() {
            match value {
                Value::Box(rc, _)
                | Value::Array(_, _, rc, _)
                | Value::HoleArray(_, _, rc, _, _) => {
                    if *rc != 0 {
                        not_freed_values.push(index);
                    }
                }
                _ => {}
            }
        }
        for value in &not_freed_values {
            println!["{}", self.value_to_str(HeapId(*value))]
        }

        if not_freed_values.len() != 0 {
            panic!["rc != 0 at end of main"];
        }
    }

    fn maybe_invalidate(&mut self, heap_id: HeapId) {
        let kind = &mut self[heap_id];
        if let Value::Array(rep, status, _rc, _values)
        | Value::HoleArray(rep, status, _rc, _, _values) = kind
        {
            if *rep == RepChoice::OptimizedMut {
                *status = ArrayStatus::Invalid;
            }
        } else {
            unreachable![];
        }
    }
}

fn retain(heap: &mut Heap, heap_id: HeapId, stacktrace: StackTrace) {
    let kind = &mut heap[heap_id];

    match kind {
        Value::Bool(_) | Value::Num(_) => {}
        Value::Tuple(contents) => {
            for sub_heap_id in contents.clone() {
                retain(
                    heap,
                    sub_heap_id,
                    stacktrace.add_frame("retaining subtuple".into()),
                );
            }
        }
        Value::Array(_, _, rc, _) | Value::HoleArray(_, _, rc, _, _) | Value::Box(rc, _) => {
            *rc += 1;
        }
        Value::Variant(_, content) | Value::Custom(_, content) => {
            let content = content.clone();
            retain(
                heap,
                content,
                stacktrace.add_frame("retaining subthing".into()),
            );
        }
    }
}

fn release(heap: &mut Heap, heap_id: HeapId, stacktrace: StackTrace) {
    let kind = &mut heap[heap_id];

    match kind {
        Value::Bool(_) | Value::Num(_) => {}
        Value::Tuple(contents) => {
            for sub_heap_id in contents.clone() {
                release(
                    heap,
                    sub_heap_id,
                    stacktrace.add_frame("releasing subtuple".into()),
                );
            }
        }
        Value::Array(_, _, rc, contents) | Value::HoleArray(_, _, rc, _, contents) => {
            if *rc == 0 {
                stacktrace.panic(format!("releasing with rc 0, {:?}", kind));
            }
            *rc -= 1;
            if *rc == 0 {
                for sub_heap_id in contents.clone() {
                    release(
                        heap,
                        sub_heap_id,
                        stacktrace.add_frame("releasing subthings".into()),
                    );
                }
            }
        }
        Value::Box(rc, content) => {
            let content = content.clone();
            if *rc == 0 {
                stacktrace.panic(format!("releasing with rc 0, {:?}", kind));
            }
            *rc -= 1;
            if *rc == 0 {
                release(
                    heap,
                    content,
                    stacktrace.add_frame("releasing subthing".into()),
                );
            }
        }
        Value::Variant(_, content) | Value::Custom(_, content) => {
            let content2 = content.clone();
            release(
                heap,
                content2,
                stacktrace.add_frame("release subthing".into()),
            );
        }
    }
}

fn typecheck_many(heap: &Heap, heap_ids: &[HeapId], type_: &Type, stacktrace: StackTrace) {
    for heap_id in heap_ids {
        typecheck(
            heap,
            *heap_id,
            type_,
            stacktrace.add_frame("checking array contents".into()),
        );
    }
}

fn typecheck(heap: &Heap, heap_id: HeapId, type_: &Type, stacktrace: StackTrace) {
    let val = &heap[heap_id];
    let kind = &val;

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

        Type::Array(rep, item_type) => {
            let array_type = match rep {
                RepChoice::OptimizedMut => "flat array",
                RepChoice::FallbackImmut => "persistent array",
            };

            if let Value::Array(_rep, _status, _rc, values) = kind {
                typecheck_many(
                    heap,
                    &values,
                    item_type,
                    stacktrace.add_frame("typechecking array interior".into()),
                );
            } else {
                stacktrace.panic(format!["expected a {} received {:?}", array_type, kind]);
            }
        }

        Type::HoleArray(rep, item_type) => {
            let array_type = match rep {
                RepChoice::OptimizedMut => "flat hole array",
                RepChoice::FallbackImmut => "persistent hole array",
            };

            if let Value::HoleArray(_rep, _status, _index, _rc, values) = kind {
                typecheck_many(
                    heap,
                    &values,
                    item_type,
                    stacktrace.add_frame("typechecking array interior".into()),
                );
            } else {
                stacktrace.panic(format!["expected a {} received {:?}", array_type, kind]);
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
                    typecheck(
                        heap,
                        *value,
                        &*item_type,
                        stacktrace.add_frame("typechecking tuple interior".into()),
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

                typecheck(
                    heap,
                    *heap_id,
                    &variants[variant_id],
                    stacktrace.add_frame("typechecking variant interior".into()),
                );
            } else {
                stacktrace.panic(format!["expected a variant received {:?}", kind]);
            }
        }

        Type::Boxed(boxed_type) => {
            if let Value::Box(_rc, heap_id) = kind {
                typecheck(
                    heap,
                    *heap_id,
                    &*boxed_type,
                    stacktrace.add_frame("typechecking box interior".into()),
                );
            } else {
                stacktrace.panic(format!["expected a box received {:?}", kind]);
            }
        }

        Type::Custom(custom_type_id) => {
            if let Value::Custom(type_id, heap_id) = kind {
                if *custom_type_id != *type_id {
                    stacktrace.panic(format![
                        "differing custom type ids {:?} != {:?}",
                        *custom_type_id, *type_id
                    ]);
                }

                typecheck(
                    heap,
                    *heap_id,
                    &heap.program.custom_types[custom_type_id],
                    stacktrace,
                );
            } else {
                stacktrace.panic(format!["expected a custom received {:?}", kind]);
            }
        }
    }
}

fn unwrap_bool(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> bool {
    let kind = &heap[heap_id].assert_live(stacktrace.add_frame("unwrap bool".into()));
    if let Value::Bool(val) = kind {
        *val
    } else {
        stacktrace.panic(format!["expected a bool received {:?}", kind]);
    }
}

fn unwrap_byte(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> Wrapping<u8> {
    let kind = &heap[heap_id].assert_live(stacktrace.add_frame("unwrap byte".into()));
    if let Value::Num(NumValue::Byte(val)) = kind {
        *val
    } else {
        stacktrace.panic(format!["expected a byte received {:?}", kind]);
    }
}

fn unwrap_int(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> Wrapping<i64> {
    let kind = &heap[heap_id].assert_live(stacktrace.add_frame("unwrap int".into()));
    if let Value::Num(NumValue::Int(val)) = kind {
        *val
    } else {
        stacktrace.panic(format!["expected an int received {:?}", kind]);
    }
}

fn unwrap_float(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> f64 {
    let kind = &heap[heap_id].assert_live(stacktrace.add_frame("unwrap float".into()));
    if let Value::Num(NumValue::Float(val)) = kind {
        *val
    } else {
        stacktrace.panic(format!["expected a float received {:?}", kind]);
    }
}

fn unwrap_array(
    heap: &Heap,
    heap_id: HeapId,
    rep: RepChoice,
    stacktrace: StackTrace,
) -> Vec<HeapId> {
    let kind = &heap[heap_id].assert_live(stacktrace.add_frame("unwrap array".into()));
    if let Value::Array(runtime_rep, _status, _rc, values) = kind {
        if *runtime_rep != rep {
            stacktrace.panic(format![
                "expceted an array of different type, received {:?}",
                *kind
            ]);
        }
        values.clone()
    } else {
        stacktrace.panic(format!["expected an array received {:?}", kind]);
    }
}

fn unwrap_array_retain(
    heap: &mut Heap,
    heap_id: HeapId,
    rep: RepChoice,
    stacktrace: StackTrace,
) -> Vec<HeapId> {
    let result = unwrap_array(heap, heap_id, rep, stacktrace.clone());
    for &item_id in &result {
        retain(
            heap,
            item_id,
            stacktrace.add_frame("unwrap array retain".into()),
        );
    }
    result
}

fn unwrap_hole_array(
    heap: &Heap,
    heap_id: HeapId,
    rep: RepChoice,
    stacktrace: StackTrace,
) -> (i64, Vec<HeapId>) {
    let kind = &heap[heap_id].assert_live(stacktrace.add_frame("unwrap hole array".into()));
    if let Value::HoleArray(runtime_rep, _status, _rc, index, values) = kind {
        if *runtime_rep != rep {
            stacktrace.panic(format![
                "expceted an array of different type, received {:?}",
                *kind
            ]);
        }
        (*index, values.clone())
    } else {
        stacktrace.panic(format!["expected a hole array received {:?}", kind]);
    }
}

fn unwrap_hole_array_retain(
    heap: &mut Heap,
    heap_id: HeapId,
    rep: RepChoice,
    stacktrace: StackTrace,
) -> (i64, Vec<HeapId>) {
    let (idx, result) = unwrap_hole_array(heap, heap_id, rep, stacktrace.clone());
    for &item_id in &result {
        retain(
            heap,
            item_id,
            stacktrace.add_frame("unwrap hole array retain".into()),
        );
    }
    (idx, result)
}

fn unwrap_tuple(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> Vec<HeapId> {
    let kind = &heap[heap_id].assert_live(stacktrace.add_frame("unwrap tuple".into()));
    if let Value::Tuple(values) = kind {
        values.clone()
    } else {
        stacktrace.panic(format!["expected a tuple received {:?}", kind]);
    }
}

fn unwrap_variant(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> (VariantId, HeapId) {
    let kind = &heap[heap_id].assert_live(stacktrace.add_frame("unwrap variant".into()));
    if let Value::Variant(variant_id, heap_id) = kind {
        (*variant_id, *heap_id)
    } else {
        stacktrace.panic(format!["expected a variant received {:?}", kind]);
    }
}

fn unwrap_boxed(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> HeapId {
    let kind = &heap[heap_id].assert_live(stacktrace.add_frame("unwrap boxed".into()));
    if let Value::Box(_rc, heap_id) = kind {
        *heap_id
    } else {
        stacktrace.panic(format!["expected a box received {:?}", kind]);
    }
}

fn unwrap_custom(heap: &Heap, heap_id: HeapId, stacktrace: StackTrace) -> (CustomTypeId, HeapId) {
    let kind = &heap[heap_id].assert_live(stacktrace.add_frame("unwrap custom".into()));
    if let Value::Custom(type_id, heap_id) = kind {
        (*type_id, *heap_id)
    } else {
        stacktrace.panic(format!["expected a custom received {:?}", kind]);
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

    typecheck(
        heap,
        arg_id,
        &func.arg_type,
        stacktrace.add_frame(format!["typecheck function argument {:?}", func_id]),
    );

    let mut result = interpret_expr(
        &func.body,
        stdin,
        stdout,
        stderr,
        program,
        &Locals::new(arg_id),
        heap,
        stacktrace.add_frame(format!["func: {:?} arg: {:?}", func_id, arg_id]),
    );

    while let Err(Interruption::TailCall(tail_id, tail_arg)) = result {
        let tail_func = &func.tail_funcs[tail_id];

        typecheck(
            heap,
            tail_arg,
            &tail_func.arg_type,
            stacktrace.add_frame(format![
                "typecheck tail function argument {:?} {:?}",
                func_id, tail_id
            ]),
        );

        result = interpret_expr(
            &tail_func.body,
            stdin,
            stdout,
            stderr,
            program,
            &Locals::new(tail_arg),
            heap,
            stacktrace.add_frame(format![
                "tail func: {:?} {:?} arg: {:?}",
                func_id, tail_id, arg_id
            ]),
        );
    }

    match result {
        Ok(ret_id) => {
            typecheck(
                heap,
                ret_id,
                &func.ret_type,
                stacktrace.add_frame(format!["typecheck function return: {:?}", func_id]),
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
    locals: &Locals,
    heap: &mut Heap,
    stacktrace: StackTrace,
) -> Result<HeapId, Interruption> {
    stacker::maybe_grow(STACK_RED_ZONE_BYTES, STACK_GROW_BYTES, move || {
        Ok(match expr {
            Expr::Local(local_id) => locals[local_id],

            Expr::Call(func_id, arg_id) => interpret_call(
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
                    stacktrace.add_frame("computing discriminant of if".into()),
                );

                if discrim_value {
                    interpret_expr(
                        then_branch,
                        stdin,
                        stdout,
                        stderr,
                        program,
                        locals,
                        heap,
                        stacktrace.add_frame("going into if branch".into()),
                    )?
                } else {
                    interpret_expr(
                        else_branch,
                        stdin,
                        stdout,
                        stderr,
                        program,
                        locals,
                        heap,
                        stacktrace.add_frame("going into else branch".into()),
                    )?
                }
            }

            Expr::LetMany(bindings, final_local_id) => {
                let mut new_locals = locals.clone();

                for (expected_type, let_expr) in bindings {
                    let local_heap_id = interpret_expr(
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

            // I hope I don't regret this
            Expr::Unreachable(_) => panic!["Segmentation fault (core dumped)"],

            Expr::Tuple(elem_ids) => heap.add(Value::Tuple(
                elem_ids.iter().map(|elem_id| locals[*elem_id]).collect(),
            )),

            Expr::TupleField(tuple_id, index) => {
                let tuple = unwrap_tuple(
                    heap,
                    locals[tuple_id],
                    stacktrace.add_frame("tuple_field".into()),
                );
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
                    stacktrace.add_frame("wrap variant".into()),
                );

                heap.add(Value::Variant(*variant_id, heap_id))
            }

            Expr::UnwrapVariant(variants, variant_id, local_id) => {
                let heap_id = locals[local_id];
                typecheck(
                    heap,
                    heap_id,
                    &Type::Variants(variants.clone()),
                    stacktrace.add_frame("unwrap variant".into()),
                );
                let (runtime_variant_id, local_variant_id) =
                    unwrap_variant(heap, heap_id, stacktrace.add_frame("unwrap variant".into()));

                if *variant_id != runtime_variant_id {
                    stacktrace.panic(format![
                        "unwrap variant ids not equal {:?} != {:?}",
                        variant_id, runtime_variant_id
                    ]);
                }

                local_variant_id
            }

            Expr::WrapCustom(type_id, local_id) => {
                let heap_id = locals[local_id];

                heap.add(Value::Custom(*type_id, heap_id))
            }

            Expr::UnwrapCustom(custom_id, local_id) => {
                let heap_id = locals[local_id];
                let (runtime_custom_id, local_custom_id) =
                    unwrap_custom(heap, heap_id, stacktrace.add_frame("unwrap custom".into()));

                if runtime_custom_id != *custom_id {
                    stacktrace.panic(format![
                        "unwrap custom ids not equal, expected {:?} got {:?}",
                        custom_id, runtime_custom_id
                    ]);
                }

                local_custom_id
            }

            Expr::WrapBoxed(local_id, type_) => {
                typecheck(
                    heap,
                    locals[local_id],
                    &type_,
                    stacktrace.add_frame("wrap boxed typecheck".into()),
                );
                let heap_id = locals[local_id];

                heap.add(Value::Box(1, heap_id))
            }

            Expr::UnwrapBoxed(local_id, type_) => {
                let heap_id = locals[local_id];
                let local_heap_id =
                    unwrap_boxed(heap, heap_id, stacktrace.add_frame("unwrap boxed".into()));

                typecheck(
                    heap,
                    local_heap_id,
                    &type_,
                    stacktrace.add_frame("unwrap boxed typecheck".into()),
                );

                local_heap_id
            }

            Expr::Retain(local_id, type_) => {
                typecheck(
                    heap,
                    locals[local_id],
                    &type_,
                    stacktrace.add_frame("retain typecheck".into()),
                );
                retain(heap, locals[local_id], stacktrace);

                HeapId(0)
            }

            Expr::Release(local_id, type_) => {
                typecheck(
                    heap,
                    locals[local_id],
                    &type_,
                    stacktrace.add_frame("retain typecheck".into()),
                );
                release(heap, locals[local_id], stacktrace);

                HeapId(0)
            }

            Expr::CheckVariant(variant_id, local_id) => {
                let heap_id = locals[local_id];

                let (local_variant_id, _local_heap_id) =
                    unwrap_variant(heap, heap_id, stacktrace.add_frame("check variant".into()));

                heap.add(Value::Bool(*variant_id == local_variant_id))
            }

            Expr::ArithOp(ArithOp::Op(NumType::Byte, BinOp::Add, local_id1, local_id2)) => heap
                .add(Value::Num(NumValue::Byte(
                    unwrap_byte(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) + unwrap_byte(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                ))),

            Expr::ArithOp(ArithOp::Op(NumType::Int, BinOp::Add, local_id1, local_id2)) => {
                heap.add(Value::Num(NumValue::Int(
                    unwrap_int(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) + unwrap_int(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                )))
            }

            Expr::ArithOp(ArithOp::Op(NumType::Float, BinOp::Add, local_id1, local_id2)) => heap
                .add(Value::Num(NumValue::Float(
                    unwrap_float(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) + unwrap_float(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                ))),

            Expr::ArithOp(ArithOp::Op(NumType::Byte, BinOp::Sub, local_id1, local_id2)) => heap
                .add(Value::Num(NumValue::Byte(
                    unwrap_byte(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) - unwrap_byte(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                ))),

            Expr::ArithOp(ArithOp::Op(NumType::Int, BinOp::Sub, local_id1, local_id2)) => {
                heap.add(Value::Num(NumValue::Int(
                    unwrap_int(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) - unwrap_int(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                )))
            }

            Expr::ArithOp(ArithOp::Op(NumType::Float, BinOp::Sub, local_id1, local_id2)) => heap
                .add(Value::Num(NumValue::Float(
                    unwrap_float(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) - unwrap_float(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                ))),

            Expr::ArithOp(ArithOp::Op(NumType::Byte, BinOp::Mul, local_id1, local_id2)) => heap
                .add(Value::Num(NumValue::Byte(
                    unwrap_byte(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) * unwrap_byte(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                ))),

            Expr::ArithOp(ArithOp::Op(NumType::Int, BinOp::Mul, local_id1, local_id2)) => {
                heap.add(Value::Num(NumValue::Int(
                    unwrap_int(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) * unwrap_int(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                )))
            }

            Expr::ArithOp(ArithOp::Op(NumType::Float, BinOp::Mul, local_id1, local_id2)) => heap
                .add(Value::Num(NumValue::Float(
                    unwrap_float(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) * unwrap_float(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                ))),

            Expr::ArithOp(ArithOp::Op(NumType::Byte, BinOp::Div, local_id1, local_id2)) => {
                let divisor = unwrap_byte(
                    heap,
                    locals[local_id2],
                    stacktrace.add_frame("arith".into()),
                );

                if divisor.0 == 0 {
                    writeln!(stderr, "panicked due to division by zero").unwrap();
                    return Err(Interruption::Exit(ExitStatus::Failure(Some(1))));
                }

                heap.add(Value::Num(NumValue::Byte(
                    unwrap_byte(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) / divisor,
                )))
            }

            Expr::ArithOp(ArithOp::Op(NumType::Int, BinOp::Div, local_id1, local_id2)) => {
                let divisor = unwrap_int(
                    heap,
                    locals[local_id2],
                    stacktrace.add_frame("arith".into()),
                );

                if divisor.0 == 0 {
                    writeln!(stderr, "panicked due to division by zero").unwrap();
                    return Err(Interruption::Exit(ExitStatus::Failure(Some(1))));
                }

                heap.add(Value::Num(NumValue::Int(
                    unwrap_int(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) / divisor,
                )))
            }

            Expr::ArithOp(ArithOp::Op(NumType::Float, BinOp::Div, local_id1, local_id2)) => heap
                .add(Value::Num(NumValue::Float(
                    unwrap_float(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) / unwrap_float(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                ))),

            Expr::ArithOp(ArithOp::Cmp(NumType::Byte, Comparison::Less, local_id1, local_id2)) => {
                heap.add(Value::Bool(
                    unwrap_byte(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) < unwrap_byte(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                ))
            }

            Expr::ArithOp(ArithOp::Cmp(NumType::Int, Comparison::Less, local_id1, local_id2)) => {
                heap.add(Value::Bool(
                    unwrap_int(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) < unwrap_int(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                ))
            }

            Expr::ArithOp(ArithOp::Cmp(NumType::Float, Comparison::Less, local_id1, local_id2)) => {
                heap.add(Value::Bool(
                    unwrap_float(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) < unwrap_float(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                ))
            }

            Expr::ArithOp(ArithOp::Cmp(
                NumType::Byte,
                Comparison::LessEqual,
                local_id1,
                local_id2,
            )) => heap.add(Value::Bool(
                unwrap_byte(
                    heap,
                    locals[local_id1],
                    stacktrace.add_frame("arith".into()),
                ) <= unwrap_byte(
                    heap,
                    locals[local_id2],
                    stacktrace.add_frame("arith".into()),
                ),
            )),

            Expr::ArithOp(ArithOp::Cmp(
                NumType::Int,
                Comparison::LessEqual,
                local_id1,
                local_id2,
            )) => heap.add(Value::Bool(
                unwrap_int(
                    heap,
                    locals[local_id1],
                    stacktrace.add_frame("arith".into()),
                ) <= unwrap_int(
                    heap,
                    locals[local_id2],
                    stacktrace.add_frame("arith".into()),
                ),
            )),

            Expr::ArithOp(ArithOp::Cmp(
                NumType::Float,
                Comparison::LessEqual,
                local_id1,
                local_id2,
            )) => heap.add(Value::Bool(
                unwrap_float(
                    heap,
                    locals[local_id1],
                    stacktrace.add_frame("arith".into()),
                ) <= unwrap_float(
                    heap,
                    locals[local_id2],
                    stacktrace.add_frame("arith".into()),
                ),
            )),

            Expr::ArithOp(ArithOp::Cmp(NumType::Byte, Comparison::Equal, local_id1, local_id2)) => {
                heap.add(Value::Bool(
                    unwrap_byte(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) == unwrap_byte(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                ))
            }

            Expr::ArithOp(ArithOp::Cmp(NumType::Int, Comparison::Equal, local_id1, local_id2)) => {
                heap.add(Value::Bool(
                    unwrap_int(
                        heap,
                        locals[local_id1],
                        stacktrace.add_frame("arith".into()),
                    ) == unwrap_int(
                        heap,
                        locals[local_id2],
                        stacktrace.add_frame("arith".into()),
                    ),
                ))
            }

            Expr::ArithOp(ArithOp::Cmp(
                NumType::Float,
                Comparison::Equal,
                local_id1,
                local_id2,
            )) => heap.add(Value::Bool(
                unwrap_float(
                    heap,
                    locals[local_id1],
                    stacktrace.add_frame("arith".into()),
                ) == unwrap_float(
                    heap,
                    locals[local_id2],
                    stacktrace.add_frame("arith".into()),
                ),
            )),

            // Don't negate a byte u dummy
            Expr::ArithOp(ArithOp::Negate(NumType::Byte, local_id)) => {
                heap.add(Value::Num(NumValue::Byte(-unwrap_byte(
                    heap,
                    locals[local_id],
                    stacktrace.add_frame("arith".into()),
                ))))
            }

            Expr::ArithOp(ArithOp::Negate(NumType::Int, local_id)) => {
                heap.add(Value::Num(NumValue::Int(-unwrap_int(
                    heap,
                    locals[local_id],
                    stacktrace.add_frame("arith".into()),
                ))))
            }

            Expr::ArithOp(ArithOp::Negate(NumType::Float, local_id)) => {
                heap.add(Value::Num(NumValue::Float(-unwrap_float(
                    heap,
                    locals[local_id],
                    stacktrace.add_frame("arith".into()),
                ))))
            }

            Expr::Intrinsic(Intrinsic::ByteToInt, local_id) => {
                heap.add(Value::Num(NumValue::Int(Wrapping(
                    unwrap_byte(
                        heap,
                        locals[local_id],
                        stacktrace.add_frame("byte_to_int".into()),
                    )
                    .0 as i64,
                ))))
            }

            Expr::Intrinsic(Intrinsic::ByteToIntSigned, local_id) => {
                heap.add(Value::Num(NumValue::Int(Wrapping(
                    unwrap_byte(
                        heap,
                        locals[local_id],
                        stacktrace.add_frame("byte_to_int".into()),
                    )
                    .0 as i8 as i64,
                ))))
            }

            Expr::Intrinsic(Intrinsic::IntToByte, local_id) => {
                heap.add(Value::Num(NumValue::Byte(Wrapping(
                    unwrap_int(
                        heap,
                        locals[local_id],
                        stacktrace.add_frame("int_to_byte".into()),
                    )
                    .0 as u8,
                ))))
            }

            Expr::Intrinsic(Intrinsic::IntShiftLeft, local_id) => {
                let args = unwrap_tuple(
                    heap,
                    locals[local_id],
                    stacktrace.add_frame("int_shift_left".into()),
                );
                assert_eq!(args.len(), 2);
                let left = unwrap_int(heap, args[0], stacktrace.add_frame("int_shift_left".into()));
                let right =
                    unwrap_int(heap, args[1], stacktrace.add_frame("int_shift_left".into()));
                heap.add(Value::Num(NumValue::Int(Wrapping(
                    left.0 << (right.0 as u64 % 64),
                ))))
            }

            Expr::Intrinsic(Intrinsic::IntShiftRight, local_id) => {
                let args = unwrap_tuple(
                    heap,
                    locals[local_id],
                    stacktrace.add_frame("int_shift_right".into()),
                );
                assert_eq!(args.len(), 2);
                let left = unwrap_int(
                    heap,
                    args[0],
                    stacktrace.add_frame("int_shift_right".into()),
                );
                let right = unwrap_int(
                    heap,
                    args[1],
                    stacktrace.add_frame("int_shift_right".into()),
                );
                heap.add(Value::Num(NumValue::Int(Wrapping(
                    ((left.0 as u64) >> (right.0 as u64 % 64)) as i64,
                ))))
            }

            Expr::Intrinsic(Intrinsic::IntBitAnd, local_id) => {
                let args = unwrap_tuple(
                    heap,
                    locals[local_id],
                    stacktrace.add_frame("int_bit_and".into()),
                );
                assert_eq!(args.len(), 2);
                let left = unwrap_int(heap, args[0], stacktrace.add_frame("int_bit_and".into()));
                let right = unwrap_int(heap, args[1], stacktrace.add_frame("int_bit_and".into()));
                heap.add(Value::Num(NumValue::Int(left & right)))
            }

            Expr::Intrinsic(Intrinsic::IntBitOr, local_id) => {
                let args = unwrap_tuple(
                    heap,
                    locals[local_id],
                    stacktrace.add_frame("int_bit_or".into()),
                );
                assert_eq!(args.len(), 2);
                let left = unwrap_int(heap, args[0], stacktrace.add_frame("int_bit_or".into()));
                let right = unwrap_int(heap, args[1], stacktrace.add_frame("int_bit_or".into()));
                heap.add(Value::Num(NumValue::Int(left | right)))
            }

            Expr::ArrayOp(rep, _item_type, ArrayOp::New()) => {
                heap.add(Value::Array(*rep, ArrayStatus::Valid, 1, vec![]))
            }

            Expr::ArrayOp(rep, _item_type, ArrayOp::Len(array_id)) => {
                let array_heap_id = locals[array_id];

                let array = unwrap_array(
                    heap,
                    array_heap_id,
                    *rep,
                    stacktrace.add_frame("len".into()),
                );

                heap.add(Value::Num(NumValue::Int(Wrapping(array.len() as i64))))
            }

            Expr::ArrayOp(rep, _item_type, ArrayOp::Push(array_id, item_id)) => {
                let array_heap_id = locals[array_id];
                let item_heap_id = locals[item_id];

                let mut array = unwrap_array_retain(
                    heap,
                    array_heap_id,
                    *rep,
                    stacktrace.add_frame("push".into()),
                );

                release(
                    heap,
                    array_heap_id,
                    stacktrace.add_frame("release push".into()),
                );

                heap.maybe_invalidate(array_heap_id);

                array.push(item_heap_id);

                heap.add(Value::Array(*rep, ArrayStatus::Valid, 1, array))
            }

            Expr::ArrayOp(rep, _item_type, ArrayOp::Pop(array_id)) => {
                let array_heap_id = locals[array_id];

                let mut array = unwrap_array_retain(
                    heap,
                    array_heap_id,
                    *rep,
                    stacktrace.add_frame("pop".into()),
                );

                release(
                    heap,
                    array_heap_id,
                    stacktrace.add_frame("release pop".into()),
                );

                heap.maybe_invalidate(array_heap_id);

                let item_heap_id = match array.pop() {
                    None => {
                        writeln!(stderr, "pop: empty array").unwrap();
                        return Err(Interruption::Exit(ExitStatus::Failure(Some(1))));
                    }
                    Some(id) => id,
                };

                let new_array = heap.add(Value::Array(*rep, ArrayStatus::Valid, 1, array));
                heap.add(Value::Tuple(vec![new_array, item_heap_id]))
            }

            Expr::ArrayOp(rep, _item_type, ArrayOp::Item(array_id, index_id)) => {
                let array_heap_id = locals[array_id];
                let index_heap_id = locals[index_id];

                let array = unwrap_array_retain(
                    heap,
                    array_heap_id,
                    *rep,
                    stacktrace.add_frame("item array".into()),
                );
                let index = unwrap_int(
                    heap,
                    index_heap_id,
                    stacktrace.add_frame("item index".into()),
                );

                let hole_array_id = heap.add(Value::HoleArray(
                    *rep,
                    ArrayStatus::Valid,
                    1,
                    index.0,
                    array.clone(),
                ));

                bounds_check(stderr, array.len(), index.0)?;

                let get_item = array[index.0 as usize];
                retain(heap, get_item, stacktrace.add_frame("item retain".into()));
                heap.add(Value::Tuple(vec![get_item, hole_array_id]))
            }

            Expr::ArrayOp(rep, _item_type, ArrayOp::Replace(array_id, item_id)) => {
                let array_heap_id = locals[array_id];
                let item_heap_id = locals[item_id];

                let (index, mut array) = unwrap_hole_array_retain(
                    heap,
                    array_heap_id,
                    *rep,
                    stacktrace.add_frame("replace array".into()),
                );

                release(
                    heap,
                    array_heap_id,
                    stacktrace.add_frame("release replace".into()),
                );

                heap.maybe_invalidate(array_heap_id);

                bounds_check(stderr, array.len(), index)?;

                let old_item_id = array[index as usize];
                release(
                    heap,
                    old_item_id,
                    stacktrace.add_frame("replace release item".into()),
                );
                array[index as usize] = item_heap_id;
                heap.add(Value::Array(*rep, ArrayStatus::Valid, 1, array))
            }

            Expr::IoOp(rep, IoOp::Input) => {
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

                heap.add(Value::Array(*rep, ArrayStatus::Valid, 1, heap_ids))
            }

            Expr::IoOp(rep, IoOp::Output(array_id)) => {
                let array_heap_id = locals[array_id];

                let array = unwrap_array(
                    heap,
                    array_heap_id,
                    *rep,
                    stacktrace.add_frame("output".into()),
                );

                let mut bytes = vec![];
                for heap_id in array {
                    bytes.push(unwrap_byte(
                        heap,
                        heap_id,
                        stacktrace.add_frame("output byte".into()),
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

            Expr::Panic(_ret_type, rep, array_id) => {
                let array_heap_id = locals[array_id];

                let array = unwrap_array(
                    heap,
                    array_heap_id,
                    *rep,
                    stacktrace.add_frame("panic".into()),
                );

                let mut bytes = vec![];
                for heap_id in array {
                    bytes.push(unwrap_byte(
                        heap,
                        heap_id,
                        stacktrace.add_frame("panic byte".into()),
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

            Expr::BoolLit(val) => heap.add(Value::Bool(*val)),

            Expr::ByteLit(val) => heap.add(Value::Num(NumValue::Byte(Wrapping(*val)))),

            Expr::IntLit(val) => heap.add(Value::Num(NumValue::Int(Wrapping(*val)))),

            Expr::FloatLit(val) => heap.add(Value::Num(NumValue::Float(*val))),
        })
    })
}

pub fn interpret(stdio: Stdio, program: Program) -> Child {
    spawn_thread(stdio, move |stdin, stdout, stderr| {
        let mut heap = Heap::new(&program);
        match interpret_call(
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
