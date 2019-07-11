use crate::annot_aliases::{FieldId, FieldPath};
use crate::data::repr_specialized_ast as ast;
use crate::util::with_scope;
use im_rc::Vector;
use itertools::izip;
use stacker;
use std::cell::RefCell;
use std::io::{BufRead, Write};
use std::rc::Rc;

static DEBUG: bool = false;

pub fn interpret<R: BufRead, W: Write>(stdin: &mut R, stdout: &mut W, program: &ast::Program) {
    interpret_block(
        stdin,
        stdout,
        program,
        &mut vec![Value::Tuple(Vec::new())],
        &program.funcs[program.main.0].body,
    );
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Generation(usize);

static GENZERO: Generation = Generation(0);

type Env = Vec<Value>; // indexed by `LocalId`

#[derive(Clone, Debug, PartialEq)]
enum Value {
    Array(Rc<RefCell<Option<Vec<Value>>>>),
    HoleArray(i64, Rc<RefCell<Option<Vec<Value>>>>),
    PersistentArray(Vector<Value>),
    PersistentHoleArray(i64, Vector<Value>),
    Tuple(Vec<Value>),
    Prim(ast::PrimVal),
    Custom(ast::CustomTypeId, ast::VariantId, Option<Box<Value>>),
}

impl From<usize> for Value {
    fn from(num: usize) -> Value {
        Value::Prim(ast::PrimVal::Int(num as i64))
    }
}

impl From<i64> for Value {
    fn from(num: i64) -> Value {
        Value::Prim(ast::PrimVal::Int(num))
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Value {
        Value::Prim(ast::PrimVal::Bool(b))
    }
}

impl From<f64> for Value {
    fn from(b: f64) -> Value {
        Value::Prim(ast::PrimVal::Float(b))
    }
}

impl From<u8> for Value {
    fn from(b: u8) -> Value {
        Value::Prim(ast::PrimVal::Byte(b))
    }
}

impl Value {
    fn strict_eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Array(ptr_a), Value::Array(ptr_b)) => Rc::ptr_eq(ptr_a, ptr_b),
            (Value::HoleArray(i, ptr_a), Value::HoleArray(j, ptr_b)) => {
                i == j && Rc::ptr_eq(ptr_a, ptr_b)
            }
            (left, right) => left == right,
        }
    }
}
fn unwrap_int(v: Value) -> i64 {
    if let Value::Prim(ast::PrimVal::Int(v)) = v {
        v
    } else {
        panic!("expected an int, got {:?}", v)
    }
}

fn unwrap_float(v: Value) -> f64 {
    if let Value::Prim(ast::PrimVal::Float(v)) = v {
        v
    } else {
        panic!("expected a float, got {:?}", v)
    }
}

fn unwrap_byte(v: Value) -> u8 {
    if let Value::Prim(ast::PrimVal::Byte(v)) = v {
        v
    } else {
        panic!("expected a byte, got {:?}", v)
    }
}

fn unwrap_byte_ref(v: &Value) -> u8 {
    if let Value::Prim(ast::PrimVal::Byte(v)) = v {
        *v
    } else {
        panic!("expected a byte, got {:?}", v)
    }
}

fn unwrap_bool(v: Value) -> u8 {
    if let Value::Prim(ast::PrimVal::Byte(v)) = v {
        v
    } else {
        panic!("expected a bool, got {:?}", v)
    }
}

fn unwrap_array(v: Value) -> Rc<RefCell<Option<Vec<Value>>>> {
    if let Value::Array(arr) = v {
        arr.clone()
    } else {
        panic!("expected an array, got {:?}", v)
    }
}

fn unwrap_holearray(v: Value) -> (i64, Rc<RefCell<Option<Vec<Value>>>>) {
    if let Value::HoleArray(i, arr) = v {
        (i, arr.clone())
    } else {
        panic!("expected a holearray, got {:?}", v)
    }
}

fn try_persistent_array(v: &Value) -> Option<Vector<Value>> {
    if let Value::PersistentArray(vect) = v {
        Some(vect.clone())
    } else {
        None
    }
}

fn try_persistent_holearray(v: &Value) -> Option<(i64, Vector<Value>)> {
    if let Value::PersistentHoleArray(idx, vect) = v {
        Some((*idx, vect.clone()))
    } else {
        None
    }
}

fn interpret_block<R: BufRead, W: Write>(
    stdin: &mut R,
    stdout: &mut W,
    program: &ast::Program,
    env: &mut Env,
    block: &ast::Block,
) -> Value {
    with_scope(env, |sub_env| {
        assert!(!block.exprs.is_empty());
        for expr in &block.exprs {
            let val = interpret_expr(stdin, stdout, program, sub_env, expr);
            sub_env.push(val);
        }
        sub_env.pop().expect("env cannot be empty")
    })
}

// This "red zone" value depends on the maximum stack space required by `interpret_expr`, which is
// determined experimentally.  If you make a change to `interpret_expr and` `cargo test` starts
// segfaulting, bump this value until it works.
const STACK_RED_ZONE_BYTES: usize = 128 * 1024;
const STACK_GROW_BYTES: usize = 1024 * 1024;

fn interpret_expr<R: BufRead, W: Write>(
    stdin: &mut R,
    stdout: &mut W,
    program: &ast::Program,
    env: &mut Env,
    expr: &ast::Expr,
) -> Value {
    stacker::maybe_grow(STACK_RED_ZONE_BYTES, STACK_GROW_BYTES, move || {
        match expr {
            ast::Expr::Term(term) => interpret_term(env, &term),
            ast::Expr::ArithOp(arith_op) => match arith_op {
                // INTS
                ast::ArithOp::Op(ast::NumType::Int, ast::BinOp::Add, left, right) => {
                    ((unwrap_int(interpret_term(env, left))
                        + unwrap_int(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Op(ast::NumType::Int, ast::BinOp::Sub, left, right) => {
                    ((unwrap_int(interpret_term(env, left))
                        - unwrap_int(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Op(ast::NumType::Int, ast::BinOp::Mul, left, right) => {
                    ((unwrap_int(interpret_term(env, left))
                        * unwrap_int(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Op(ast::NumType::Int, ast::BinOp::Div, left, right) => {
                    ((unwrap_int(interpret_term(env, left))
                        / unwrap_int(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Cmp(ast::NumType::Int, ast::Comparison::Equal, left, right) => {
                    ((unwrap_int(interpret_term(env, left))
                        == unwrap_int(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Cmp(ast::NumType::Int, ast::Comparison::Less, left, right) => {
                    ((unwrap_int(interpret_term(env, left))
                        < unwrap_int(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Cmp(ast::NumType::Int, ast::Comparison::LessEqual, left, right) => {
                    ((unwrap_int(interpret_term(env, left))
                        <= unwrap_int(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Negate(ast::NumType::Int, term) => {
                    ((-unwrap_int(interpret_term(env, term))).into())
                }

                // FLOATS
                ast::ArithOp::Op(ast::NumType::Float, ast::BinOp::Add, left, right) => {
                    ((unwrap_float(interpret_term(env, left))
                        + unwrap_float(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Op(ast::NumType::Float, ast::BinOp::Sub, left, right) => {
                    ((unwrap_float(interpret_term(env, left))
                        - unwrap_float(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Op(ast::NumType::Float, ast::BinOp::Mul, left, right) => {
                    ((unwrap_float(interpret_term(env, left))
                        * unwrap_float(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Op(ast::NumType::Float, ast::BinOp::Div, left, right) => {
                    ((unwrap_float(interpret_term(env, left))
                        / unwrap_float(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Cmp(ast::NumType::Float, ast::Comparison::Equal, left, right) => {
                    ((unwrap_float(interpret_term(env, left))
                        == unwrap_float(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Cmp(ast::NumType::Float, ast::Comparison::Less, left, right) => {
                    ((unwrap_float(interpret_term(env, left))
                        < unwrap_float(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Cmp(ast::NumType::Float, ast::Comparison::LessEqual, left, right) => {
                    ((unwrap_float(interpret_term(env, left))
                        <= unwrap_float(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Negate(ast::NumType::Float, term) => {
                    ((-unwrap_float(interpret_term(env, term))).into())
                }

                // BYTES
                ast::ArithOp::Op(ast::NumType::Byte, ast::BinOp::Add, left, right) => {
                    ((unwrap_byte(interpret_term(env, left))
                        + unwrap_byte(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Op(ast::NumType::Byte, ast::BinOp::Sub, left, right) => {
                    ((unwrap_byte(interpret_term(env, left))
                        - unwrap_byte(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Op(ast::NumType::Byte, ast::BinOp::Mul, left, right) => {
                    ((unwrap_byte(interpret_term(env, left))
                        * unwrap_byte(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Op(ast::NumType::Byte, ast::BinOp::Div, left, right) => {
                    ((unwrap_byte(interpret_term(env, left))
                        / unwrap_byte(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Cmp(ast::NumType::Byte, ast::Comparison::Equal, left, right) => {
                    ((unwrap_byte(interpret_term(env, left))
                        == unwrap_byte(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Cmp(ast::NumType::Byte, ast::Comparison::Less, left, right) => {
                    ((unwrap_byte(interpret_term(env, left))
                        < unwrap_byte(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Cmp(ast::NumType::Byte, ast::Comparison::LessEqual, left, right) => {
                    ((unwrap_byte(interpret_term(env, left))
                        <= unwrap_byte(interpret_term(env, right)))
                    .into())
                }
                ast::ArithOp::Negate(ast::NumType::Byte, _term) => {
                    panic!("don't negate a byte u dummy")
                    // FIXME: use i8's, or disallow this.
                    // ((-unwrap_byte(interpret_term(env, term))).into())
                }
            },
            ast::Expr::ArrayOp(array_op) => match array_op {
                ast::ArrayOp::Construct(_item_t, ast::Repr::Shared, items) => {
                    // TODO: check type
                    if DEBUG {
                        println!("[constructing a flat array]");
                    }
                    Value::PersistentArray(
                        items
                            .into_iter()
                            .map(|item| interpret_term(env, &item))
                            .collect(),
                    )
                }
                ast::ArrayOp::Construct(_item_t, ast::Repr::Unique, items) => {
                    // TODO: check type
                    if DEBUG {
                        println!("[constructing a flat array]");
                    }
                    Value::Array(Rc::new(RefCell::new(Some(
                        items
                            .into_iter()
                            .map(|item| interpret_term(env, &item))
                            .collect(),
                    ))))
                }
                ast::ArrayOp::Item(array, index) => {
                    let array = interpret_term(env, array);
                    let idx = unwrap_int(interpret_term(env, index));
                    if let Some(pers) = try_persistent_array(&array) {
                        if DEBUG {
                            println!("[accessing a persistent array]");
                        }
                        Value::Tuple(vec![
                            pers[idx as usize].clone(),
                            Value::PersistentHoleArray(idx, pers),
                        ])
                    } else {
                        if DEBUG {
                            println!("[accessing a flat array]");
                        }
                        let vec_cell = unwrap_array(array);
                        let vec_borrow = vec_cell.borrow();
                        let vec = vec_borrow
                            .as_ref()
                            .expect("item called on invalidated array!");
                        if DEBUG {
                            println!("array is {:?}, idx is {:?}", &vec, idx);
                        }
                        let item = { vec[idx as usize].clone() };
                        Value::Tuple(vec![item, Value::HoleArray(idx, vec_cell.clone())])
                    }
                }
                ast::ArrayOp::Len(array) => {
                    let array = interpret_term(env, array);
                    if let Some(pers) = try_persistent_array(&array) {
                        if DEBUG {
                            println!("[getting length of a persistent array ({:?})]", pers.len());
                        }
                        pers.len().into()
                    } else {
                        let vec_cell = unwrap_array(array);
                        let vec_borrow = vec_cell.borrow();
                        let vec = vec_borrow
                            .as_ref()
                            .expect("len called on invalidated array!");
                        if DEBUG {
                            println!("[getting length of a flat array ({:?})]", vec.len());
                        }
                        vec.len().into()
                    }
                }
                ast::ArrayOp::Push(array, item) => {
                    let array = interpret_term(env, array);
                    let item = interpret_term(env, item);
                    if let Some(mut pers) = try_persistent_array(&array) {
                        if DEBUG {
                            println!("[pushing to a persistent array]");
                        }
                        pers.push_back(item);
                        Value::PersistentArray(pers)
                    } else {
                        if DEBUG {
                            println!("[pushing to a flat array]");
                        }
                        let vec_cell = unwrap_array(array);
                        let mut vec = vec_cell
                            .replace(None)
                            .expect("pushing to invalidated array!");;
                        vec.push(item);
                        Value::Array(Rc::new(RefCell::new(Some(vec))))
                    }
                }
                ast::ArrayOp::Pop(array) => {
                    let array = interpret_term(env, array);
                    if let Some(mut pers) = try_persistent_array(&array) {
                        if DEBUG {
                            println!("[popping from a persistent array]");
                        }
                        let item = pers
                            .pop_back()
                            .expect("Hopper program error: popped from empty array");
                        Value::Tuple(vec![Value::PersistentArray(pers), item])
                    } else {
                        if DEBUG {
                            println!("[popping from a flat array]");
                        }
                        let vec_cell = unwrap_array(array);
                        let mut vec = vec_cell
                            .replace(None)
                            .expect("pushing to invalidated array!");;
                        let item = vec
                            .pop()
                            .expect("Hopper program error: popped from empty array");
                        Value::Tuple(vec![Value::Array(Rc::new(RefCell::new(Some(vec)))), item])
                    }
                }
                ast::ArrayOp::Replace(hole_array, item) => {
                    let array = interpret_term(env, hole_array);
                    let item = interpret_term(env, item);
                    if let Some((idx, mut pers)) = try_persistent_holearray(&array) {
                        if DEBUG {
                            println!("[assigning to a persistent array]");
                        }
                        pers[idx as usize] = item;
                        Value::PersistentArray(pers)
                    } else {
                        if DEBUG {
                            println!("[assigning to a flat array]");
                        }
                        let (idx, vec_cell) = unwrap_holearray(array);
                        let mut vec = vec_cell
                            .replace(None)
                            .expect("pushing to invalidated array!");;
                        vec[idx as usize] = item;
                        Value::Array(Rc::new(RefCell::new(Some(vec))))
                    }
                }
            },
            ast::Expr::IOOp(ast::IOOp::Input(repr)) => {
                let mut input = String::new();
                stdin
                    .read_line(&mut input)
                    .ok()
                    .expect("failed reading stdin");
                match repr {
                    ast::Repr::Shared => Value::PersistentArray(
                        input
                            .into_bytes()
                            .into_iter()
                            .map(|byte| Value::Prim(ast::PrimVal::Byte(byte)))
                            .collect(),
                    ),
                    ast::Repr::Unique => Value::Array(Rc::new(RefCell::new(Some(
                        input
                            .into_bytes()
                            .into_iter()
                            .map(|byte| Value::Prim(ast::PrimVal::Byte(byte)))
                            .collect(),
                    )))),
                }
            }
            ast::Expr::IOOp(ast::IOOp::Output(array)) => {
                let array = interpret_term(env, array);
                let bytes = if let Some(pers) = try_persistent_array(&array) {
                    if DEBUG {
                        println!("[outputting a persistent array]");
                    }
                    pers.into_iter().map(|val| unwrap_byte(val)).collect()
                } else {
                    let output_cell = unwrap_array(array);
                    let output_borrow = output_cell.borrow();
                    let output_arr = output_borrow
                        .as_ref()
                        .expect("outputting an invalidated array!");
                    output_arr
                        .into_iter()
                        .map(|val| unwrap_byte_ref(val))
                        .collect()
                };
                writeln!(
                    stdout,
                    "{}",
                    String::from_utf8(bytes).expect("UTF-8 output error"),
                )
                .expect("output failed");
                Value::Tuple(Vec::new())
            }
            ast::Expr::Ctor(type_id, variant_id, Some(arg)) => Value::Custom(
                *type_id,
                *variant_id,
                Some(Box::new(interpret_term(env, arg))),
            ),
            ast::Expr::Ctor(type_id, variant_id, None) => {
                Value::Custom(*type_id, *variant_id, None)
            }
            ast::Expr::Tuple(items) => {
                Value::Tuple(items.iter().map(|t| interpret_term(env, t)).collect())
            }
            ast::Expr::Local(local_id) => env[local_id.0].clone(),
            ast::Expr::Call(purity, func_id, arg) => {
                if DEBUG {
                    println!(
                        "Calling function {:?} ({:?}) with arg {:?}",
                        func_id, purity, arg
                    );
                }
                let arg = interpret_term(env, arg);
                let mut callee_env = vec![arg];
                interpret_block(
                    stdin,
                    stdout,
                    program,
                    &mut callee_env,
                    &program.funcs[func_id.0].body,
                )
            }
            ast::Expr::Match(matched_local, branches, _result_t) => {
                // TODO: check type result_t
                let discriminant = &env[matched_local.0];
                let mut result = None;
                for (pat, branch) in branches {
                    if pat_matches(pat, discriminant) {
                        result = Some(interpret_block(stdin, stdout, program, env, branch));
                        break;
                    }
                }
                result.expect("inexhaustive match")
            }
        }
    })
}

fn interpret_term(env: &Env, term: &ast::Term) -> Value {
    match term {
        ast::Term::Access(local, actual_path, typefolded_path) => {
            let item = lookup_in_value(env[local.0].clone(), actual_path.clone());
            assert!(item.strict_eq(&lookup_in_value(
                env[local.0].clone(),
                typefolded_path.clone()
            )));
            item
        }
        &ast::Term::BoolLit(b) => b.into(),
        &ast::Term::IntLit(b) => b.into(),
        &ast::Term::FloatLit(b) => b.into(),
        &ast::Term::ByteLit(b) => b.into(),
    }
}

fn lookup_in_value(val: Value, path: FieldPath) -> Value {
    if path.is_empty() {
        return val;
    }
    let next = match (val, path[0]) {
        (Value::Tuple(els), FieldId::Field(i)) => els[i].clone(),
        (Value::Custom(_, real_variant, arg), FieldId::Variant(subscript_variant)) => {
            assert_eq!(real_variant, subscript_variant);
            *arg.clone()
                .expect("pattern mismatched field path: variant is None")
        }
        (Value::Prim(v), field) => panic!(
            "Tried to lookup field {:?} in {:?} (whole rest of field path: {:?}",
            field, v, path
        ),
        (val, field) => panic!(
            "Tried to lookup field {:?} in {:?} (whole rest of field path: {:?}",
            field, val, path
        ),
    };
    lookup_in_value(next, path.skip(1))
}

fn pat_matches(pat: &ast::Pattern, value: &Value) -> bool {
    match pat {
        ast::Pattern::Any => true,
        ast::Pattern::Const(match_val) => {
            if DEBUG {
                println!("matching on {:?}, for value {:?}", match_val, value);
            }
            match value {
                Value::Prim(val) => match_val == val,
                _ => false,
            }
        }
        ast::Pattern::Ctor(type_id, variant_id, Some(arg_pat)) => match value {
            Value::Custom(val_type_id, val_variant_id, Some(arg_val)) => {
                type_id == val_type_id
                    && variant_id == val_variant_id
                    && pat_matches(arg_pat, arg_val)
            }
            _ => false,
        },
        ast::Pattern::Ctor(type_id, variant_id, None) => match value {
            Value::Custom(val_type_id, val_variant_id, None) => {
                type_id == val_type_id && variant_id == val_variant_id
            }
            _ => false,
        },
        // TODO: check mismatches here which represent actual type errors
        ast::Pattern::Tuple(match_items) => match value {
            Value::Tuple(items) => {
                match_items.len() == items.len()
                    && izip!(match_items, items).all(|(m, i)| pat_matches(m, i))
            }
            _ => false,
        },
    }
}
