//! A small specification language for borrowing signatures and specifications for each built-in
//! operation.

use crate::data::first_order_ast::NumType;
use crate::data::mode_annot_ast2::{HeapModes, LtParam, ModeParam, Position, Res, ResModes};
use id_collections::{id_type, Count, Id};
use morphic_macros::declare_signatures;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Clone, Debug)]
enum RawTerm {
    Var(String),
    App(String, Vec<RawTerm>),
    Tuple(Vec<RawTerm>),
}

impl fmt::Display for RawTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RawTerm::Var(var) => write!(f, "{}", var),
            RawTerm::App(name, args) => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    let args = args
                        .iter()
                        .map(|arg| arg.to_string())
                        .collect::<Vec<_>>()
                        .join(" ");
                    write!(f, "{} {}", name, args)
                }
            }
            RawTerm::Tuple(fields) => {
                let fields = fields
                    .iter()
                    .map(|field| field.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", fields)
            }
        }
    }
}

#[derive(Clone, Debug)]
struct RawPropExpr {
    type_var: String,
    prop: String,
}

impl fmt::Display for RawPropExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.type_var, self.prop)
    }
}

#[derive(Clone, Debug)]
struct RawConstr {
    lhs: RawPropExpr,
    rhs: RawPropExpr,
}

impl fmt::Display for RawConstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
    }
}

#[derive(Clone, Debug)]
struct RawArgs {
    fixed: Vec<RawTerm>,
    variadic: Option<RawTerm>,
}

#[derive(Clone, Debug)]
struct RawSignature {
    args: RawArgs,
    ret: RawTerm,
    constrs: Vec<RawConstr>,
}

#[id_type]
pub struct TypeVar(pub usize);

#[derive(Clone, Debug)]
pub enum Type {
    Var(TypeVar),
    Bool,
    Num(NumType),
    Tuple(Vec<Type>),
    Array(Res<ModeParam, LtParam>, Box<Type>),
    HoleArray(Res<ModeParam, LtParam>, Box<Type>),
    Boxed(Res<ModeParam, LtParam>, Box<Type>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Prop {
    Stack,
    Access,
    Storage,
}

#[derive(Clone, Debug)]
pub struct PropExpr {
    pub type_var: TypeVar,
    pub prop: Prop,
}

#[derive(Clone, Debug)]
pub struct Constr {
    pub lhs: PropExpr,
    pub rhs: PropExpr,
}

#[derive(Clone, Debug)]
pub struct Args {
    pub fixed: Vec<Type>,
    pub variadic: Option<Type>,
}

impl Args {
    pub fn iter(&self) -> impl Iterator<Item = &Type> {
        self.fixed.iter().chain(self.variadic.iter().cycle())
    }
}

#[derive(Clone, Debug)]
pub struct Signature {
    pub args: Args,
    pub ret: Type,
    pub constrs: Vec<Constr>,

    pub unused_lts: BTreeSet<LtParam>,
    pub owned_modes: BTreeSet<ModeParam>,

    pub var_count: Count<TypeVar>,
    pub lt_count: Count<LtParam>,
    pub mode_count: Count<ModeParam>,
}

#[derive(Clone, Debug)]
struct IdGen<I: Id> {
    count: Count<I>,
    table: BTreeMap<String, I>,
}

impl<I: Id> IdGen<I> {
    fn new() -> Self {
        Self {
            count: Count::new(),
            table: BTreeMap::new(),
        }
    }

    fn fresh(&mut self) -> I {
        self.count.inc()
    }

    fn get(&mut self, name: String) -> I {
        *self.table.entry(name).or_insert_with(|| self.count.inc())
    }
}

#[derive(Clone, Debug)]
struct Context {
    type_var_count: Count<TypeVar>,
    type_var_table: BTreeMap<String, (TypeVar, Position)>,

    lt_gen: IdGen<LtParam>,
    mode_gen: IdGen<ModeParam>,

    unused_lts: BTreeSet<LtParam>,
    owned_modes: BTreeSet<ModeParam>,
}

#[derive(Clone, Debug, thiserror::Error)]
enum Error {
    #[error("wrong number of arguments for `{type_}`: expected {expected}, but found {actual}")]
    WrongArgCount {
        type_: String,
        expected: usize,
        actual: usize,
    },
    #[error("unknown type: `{0}`")]
    UnknownType(RawTerm),
    #[error("unknown mode: `{0}`")]
    UnknownMode(RawTerm),
    #[error("unknown lifetime: `{0}`")]
    UnknownLifetime(RawTerm),
    #[error("unknown property: `{0}`")]
    UnknownProp(String),
    #[error("unknown type variable `{0}` in expression: `{1}`")]
    UnknownVar(String, RawPropExpr),
    #[error("stack types do not have access or storage modes")]
    InvalidStackProp,
    #[error("heap types do not have stack modes")]
    InvalidHeapProp,
    #[error("type variable used in inconsistent positions")]
    InconsistentPosition,
}

#[must_use]
fn assert_args(type_: &str, expected: usize, args: &[RawTerm]) -> Result<(), Error> {
    if args.len() != expected {
        Err(Error::WrongArgCount {
            type_: type_.to_string(),
            expected,
            actual: args.len(),
        })
    } else {
        Ok(())
    }
}

fn resolve_lifetime(lt: RawTerm, ctx: &mut Context) -> Result<LtParam, Error> {
    match lt {
        RawTerm::Var(var) => Ok(ctx.lt_gen.get(var)),
        RawTerm::App(name, args) => {
            if name.as_str() == "Emp" {
                assert_args("Emp", 0, &args)?;
                let lt = ctx.lt_gen.fresh();
                ctx.unused_lts.insert(lt);
                Ok(lt)
            } else {
                Err(Error::UnknownLifetime(RawTerm::App(name, args)))
            }
        }
        _ => Err(Error::UnknownLifetime(lt)),
    }
}

fn resolve_mode(mode: RawTerm, ctx: &mut Context) -> Result<ModeParam, Error> {
    match mode {
        RawTerm::Var(var) => Ok(ctx.mode_gen.get(var)),
        RawTerm::App(name, args) => {
            if name.as_str() == "Own" {
                assert_args("Own", 0, &args)?;
                let mode = ctx.mode_gen.fresh();
                ctx.owned_modes.insert(mode);
                Ok(mode)
            } else {
                Err(Error::UnknownMode(RawTerm::App(name, args)))
            }
        }
        _ => Err(Error::UnknownMode(mode)),
    }
}

fn resolve_content(
    name: &str,
    pos: Position,
    ctx: &mut Context,
    mut args: Vec<RawTerm>,
) -> Result<(Res<ModeParam, LtParam>, Type), Error> {
    match pos {
        Position::Stack => {
            assert_args(name, 3, &args)?;
            let (type_, stack, lt) = (
                args.pop().unwrap(),
                args.pop().unwrap(),
                args.pop().unwrap(),
            );
            let lt = resolve_lifetime(lt, ctx)?;
            let stack = resolve_mode(stack, ctx)?;
            let modes = ResModes::Stack(stack);
            let type_ = resolve_type(Position::Heap, ctx, type_)?;
            Ok((Res { modes, lt }, type_))
        }
        Position::Heap => {
            assert_args(name, 4, &args)?;
            let (type_, storage, access, lt) = (
                args.pop().unwrap(),
                args.pop().unwrap(),
                args.pop().unwrap(),
                args.pop().unwrap(),
            );
            let lt = resolve_lifetime(lt, ctx)?;
            let access = resolve_mode(access, ctx)?;
            let storage = resolve_mode(storage, ctx)?;
            let modes = ResModes::Heap(HeapModes { access, storage });
            let type_ = resolve_type(Position::Heap, ctx, type_)?;
            Ok((Res { modes, lt }, type_))
        }
    }
}

fn resolve_type(pos: Position, ctx: &mut Context, type_: RawTerm) -> Result<Type, Error> {
    Ok(match type_ {
        RawTerm::Var(var) => {
            let (fresh, old_pos) = ctx
                .type_var_table
                .entry(var)
                .or_insert_with(|| (ctx.type_var_count.inc(), pos));
            if *old_pos != pos {
                return Err(Error::InconsistentPosition);
            }
            let fresh = *fresh;
            Type::Var(fresh)
        }
        RawTerm::App(name, args) => match name.as_str() {
            "Bool" => {
                assert_args("Bool", 0, &args)?;
                Type::Bool
            }
            "Byte" => {
                assert_args("Byte", 0, &args)?;
                Type::Num(NumType::Byte)
            }
            "Int" => {
                assert_args("Int", 0, &args)?;
                Type::Num(NumType::Int)
            }
            "Float" => {
                assert_args("Float", 0, &args)?;
                Type::Num(NumType::Float)
            }
            "Array" => {
                let (res, type_) = resolve_content("Array", pos, ctx, args)?;
                Type::Array(res, Box::new(type_))
            }
            "HoleArray" => {
                let (res, type_) = resolve_content("HoleArray", pos, ctx, args)?;
                Type::HoleArray(res, Box::new(type_))
            }
            "Boxed" => {
                let (res, type_) = resolve_content("Boxed", pos, ctx, args)?;
                Type::Boxed(res, Box::new(type_))
            }
            _ => return Err(Error::UnknownType(RawTerm::App(name, args))),
        },
        RawTerm::Tuple(fields) => Type::Tuple(
            fields
                .into_iter()
                .map(|field| resolve_type(pos, ctx, field))
                .collect::<Result<_, _>>()?,
        ),
    })
}

fn resolve_prop_expr(ctx: &mut Context, expr: RawPropExpr) -> Result<PropExpr, Error> {
    let &(type_var, pos) = ctx
        .type_var_table
        .get(&expr.type_var)
        .ok_or_else(|| Error::UnknownVar(expr.type_var.clone(), expr.clone()))?;
    let prop = match expr.prop.as_str() {
        "stack" => Prop::Stack,
        "access" => Prop::Access,
        "storage" => Prop::Storage,
        _ => return Err(Error::UnknownProp(expr.prop)),
    };
    match (pos, prop) {
        (Position::Stack, Prop::Access) | (Position::Stack, Prop::Storage) => {
            return Err(Error::InvalidStackProp);
        }
        (Position::Heap, Prop::Stack) => {
            return Err(Error::InvalidHeapProp);
        }
        _ => {}
    }
    Ok(PropExpr { type_var, prop })
}

fn resolve_signature(sig: RawSignature) -> Result<Signature, Error> {
    let mut ctx = Context {
        type_var_count: Count::new(),
        type_var_table: BTreeMap::new(),

        mode_gen: IdGen::new(),
        lt_gen: IdGen::new(),

        unused_lts: BTreeSet::new(),
        owned_modes: BTreeSet::new(),
    };
    let fixed = sig
        .args
        .fixed
        .into_iter()
        .map(|arg| resolve_type(Position::Stack, &mut ctx, arg))
        .collect::<Result<_, _>>()?;
    let variadic = sig
        .args
        .variadic
        .map(|arg| resolve_type(Position::Stack, &mut ctx, arg))
        .transpose()?;
    let ret = resolve_type(Position::Stack, &mut ctx, sig.ret)?;
    let constrs = sig
        .constrs
        .into_iter()
        .map(|constr| {
            let lhs = resolve_prop_expr(&mut ctx, constr.lhs)?;
            let rhs = resolve_prop_expr(&mut ctx, constr.rhs)?;
            Ok(Constr { lhs, rhs })
        })
        .collect::<Result<_, _>>()?;
    Ok(Signature {
        args: Args { fixed, variadic },
        ret,
        constrs,

        unused_lts: ctx.unused_lts,
        owned_modes: ctx.owned_modes,

        var_count: ctx.type_var_count,
        lt_count: ctx.lt_gen.count,
        mode_count: ctx.mode_gen.count,
    })
}

declare_signatures! {
    pub box_new: (u) -> Boxed a Own t
        where u.stack = t.storage, u.stack = t.access;

    pub box_get: (Boxed a m t) -> u
        where u.stack = t.access;

    pub array_new: (u..) -> Array a Own t
        where u.stack = t.storage, u.stack = t.access;

    pub array_get: (Array a m t, Int) -> u
        where u.stack = t.access;

    pub array_extract: (Array a Own t, Int) -> (HoleArray a Own t, u)
        where u.stack = t.storage;

    /// Since the `len` field of an array lives on the stack, it's technically OK to read it after
    /// the array has been released (i.e. it's backing buffer has been deallocated). Therefore, we
    /// use the empty lifetime.
    pub array_len: (Array Emp m t) -> Int;

    pub array_push: (Array a Own t, u) -> Array a Own t
        where u.stack = t.storage;

    pub array_pop: (Array a Own t) -> (Array a Own t, u)
        where u.stack = t.storage;

    pub array_replace: (HoleArray a Own t, u) -> Array a Own t
        where u.stack = t.storage;

    pub array_reserve: (Array a Own t, Int) -> Array a Own t;

    pub io_input: () -> Array Own Emp Byte;

    pub io_output: (Array a m Byte) -> ();

    /// Panic returns bottom, but it's convenient to model it as returning unit.
    pub panic: (Array a m Byte) -> ();
}
