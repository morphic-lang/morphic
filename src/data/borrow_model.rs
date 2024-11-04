//! A small specification language for borrowing signatures and specifications for each built-in
//! operation.

use crate::data::first_order_ast::NumType;
use crate::data::mode_annot_ast2::{
    self as annot, HeapModes, Position, Res, ResModes, Shape, ShapeInner, SlotId,
};
use crate::util::iter::IterExt;
use id_collections::{id_type, Count, Id, IdMap};
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
struct RawModeConstr {
    lhs: RawPropExpr,
    rhs: RawPropExpr,
}

impl fmt::Display for RawModeConstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
    }
}

#[derive(Clone, Debug)]
struct RawLtConstr {
    lhs: RawPropExpr,
    rhs: RawPropExpr,
}

impl fmt::Display for RawLtConstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} <- {}", self.lhs, self.rhs)
    }
}

#[derive(Clone, Debug)]
enum RawConstr {
    Mode(RawModeConstr),
    Lt(RawLtConstr),
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

#[id_type]
pub struct ModelMode(pub usize);

#[id_type]
pub struct ModelLt(pub usize);

#[derive(Clone, Debug)]
pub enum Type {
    Var(TypeVar),
    Bool,
    Num(NumType),
    Tuple(Vec<Type>),
    Array(Res<ModelMode, ModelLt>, Box<Type>),
    HoleArray(Res<ModelMode, ModelLt>, Box<Type>),
    Boxed(Res<ModelMode, ModelLt>, Box<Type>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModeProp {
    Stack,
    Access,
    Storage,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Prop {
    Stack,
    Access,
    Storage,
    Lt,
}

impl fmt::Display for Prop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Prop::Stack => write!(f, "stack"),
            Prop::Access => write!(f, "access"),
            Prop::Storage => write!(f, "storage"),
            Prop::Lt => write!(f, "lt"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ModePropExpr {
    pub type_var: TypeVar,
    pub prop: ModeProp,
}

#[derive(Clone, Debug)]
pub struct LtPropExpr {
    pub type_var: TypeVar,
}

#[derive(Clone, Debug)]
pub enum Constr {
    Mode {
        lhs: ModePropExpr,
        rhs: ModePropExpr,
    },
    Lt {
        lhs: LtPropExpr,
        rhs: LtPropExpr,
    },
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

    pub unused_lts: BTreeSet<ModelLt>,
    pub owned_modes: BTreeSet<ModelMode>,

    pub var_count: Count<TypeVar>,
    pub lt_count: Count<ModelLt>,
    pub mode_count: Count<ModelMode>,
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

    lt_gen: IdGen<ModelLt>,
    mode_gen: IdGen<ModelMode>,

    unused_lts: BTreeSet<ModelLt>,
    owned_modes: BTreeSet<ModelMode>,
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
    HasNoHeapProp,
    #[error("heap types do not have stack modes")]
    HasNoStackProp,
    #[error("expected mode property, but found lifetime property")]
    ExpectedModeProp,
    #[error("expected lifetime property, but found mode property")]
    ExpectedLtProp,
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

fn resolve_lifetime(lt: RawTerm, ctx: &mut Context) -> Result<ModelLt, Error> {
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

fn resolve_mode(mode: RawTerm, ctx: &mut Context) -> Result<ModelMode, Error> {
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
) -> Result<(Res<ModelMode, ModelLt>, Type), Error> {
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

fn resolve_mode_prop_expr(ctx: &mut Context, expr: RawPropExpr) -> Result<ModePropExpr, Error> {
    let &(type_var, pos) = ctx
        .type_var_table
        .get(&expr.type_var)
        .ok_or_else(|| Error::UnknownVar(expr.type_var.clone(), expr.clone()))?;
    match expr.prop.as_str() {
        "stack" => match pos {
            Position::Stack => Ok(ModePropExpr {
                type_var,
                prop: ModeProp::Stack,
            }),
            Position::Heap => Err(Error::HasNoHeapProp),
        },
        "access" => match pos {
            Position::Stack => Err(Error::HasNoStackProp),
            Position::Heap => Ok(ModePropExpr {
                type_var,
                prop: ModeProp::Access,
            }),
        },
        "storage" => match pos {
            Position::Stack => Err(Error::HasNoStackProp),
            Position::Heap => Ok(ModePropExpr {
                type_var,
                prop: ModeProp::Storage,
            }),
        },
        "lt" => Err(Error::ExpectedModeProp),
        _ => Err(Error::UnknownProp(expr.prop)),
    }
}

fn resolve_lt_prop_expr(ctx: &mut Context, expr: RawPropExpr) -> Result<LtPropExpr, Error> {
    let &(type_var, _pos) = ctx
        .type_var_table
        .get(&expr.type_var)
        .ok_or_else(|| Error::UnknownVar(expr.type_var.clone(), expr.clone()))?;
    match expr.prop.as_str() {
        "stack" | "access" | "storage" => Err(Error::ExpectedLtProp),
        "lt" => Ok(LtPropExpr { type_var }),
        _ => Err(Error::UnknownProp(expr.prop)),
    }
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
        .map(|constr| match constr {
            RawConstr::Mode(constr) => {
                let lhs = resolve_mode_prop_expr(&mut ctx, constr.lhs)?;
                let rhs = resolve_mode_prop_expr(&mut ctx, constr.rhs)?;
                Ok(Constr::Mode { lhs, rhs })
            }
            RawConstr::Lt(constr) => {
                let lhs = resolve_lt_prop_expr(&mut ctx, constr.lhs)?;
                let rhs = resolve_lt_prop_expr(&mut ctx, constr.rhs)?;
                Ok(Constr::Lt { lhs, rhs })
            }
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

#[derive(Debug, Clone, Copy)]
pub struct ArgLoc {
    pub start: usize,
    pub end: usize,
    pub occur_idx: usize,
}

#[derive(Debug, Clone)]
pub struct ArgOccur<Repr> {
    pub data: Repr,
    pub loc: ArgLoc,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarOccurKind {
    Arg(usize),
    Ret,
}

#[derive(Debug, Clone)]
pub struct VarOccurs<Repr> {
    pub args: Vec<ArgOccur<Repr>>,
    pub rets: Vec<Repr>,
}

impl<Repr> VarOccurs<Repr> {
    pub fn new() -> Self {
        VarOccurs {
            args: Vec::new(),
            rets: Vec::new(),
        }
    }

    pub fn rep(&self) -> Option<&Repr> {
        self.args
            .first()
            .map(|occ| &occ.data)
            .or_else(|| self.rets.first())
    }

    pub fn all(&self) -> impl Iterator<Item = &Repr> {
        self.args
            .iter()
            .map(|occ| &occ.data)
            .chain(self.rets.iter())
    }
}

fn get_res_impl<I>(
    model: &Type,
    shape: &Shape<I>,
    next_slot: usize,
    out_res: &mut BTreeMap<SlotId, Res<ModelMode, ModelLt>>,
) -> usize {
    match (model, &*shape.inner) {
        (Type::Var(_), _) => next_slot + shape.num_slots,
        (Type::Bool, ShapeInner::Bool) => next_slot,
        (Type::Num(model), ShapeInner::Num(shape)) if model == shape => next_slot,
        (Type::Tuple(models), ShapeInner::Tuple(shapes)) => {
            let iter = models.iter().zip_eq(shapes);
            iter.fold(next_slot, |start, (model, shape)| {
                get_res_impl(model, shape, start, out_res)
            })
        }
        (Type::Array(res, model), ShapeInner::Array(shape)) => {
            out_res.insert(SlotId::from_index(next_slot), res.clone());
            get_res_impl(model, shape, next_slot + 1, out_res)
        }
        (Type::HoleArray(res, model), ShapeInner::HoleArray(shape)) => {
            out_res.insert(SlotId::from_index(next_slot), res.clone());
            get_res_impl(model, shape, next_slot + 1, out_res)
        }
        (Type::Boxed(res, model), ShapeInner::Boxed(shape)) => {
            out_res.insert(SlotId::from_index(next_slot), res.clone());
            get_res_impl(model, shape, next_slot + 1, out_res)
        }
        _ => panic!("type does not match model"),
    }
}

fn extract_vars_impl<I, T, Repr>(
    make: &impl Fn(&Shape<I>, &[T]) -> Repr,
    kind: VarOccurKind,
    model: &Type,
    shape: &Shape<I>,
    start: usize,
    res: &[T],
    out: &mut IdMap<TypeVar, VarOccurs<Repr>>,
) {
    match (model, &*shape.inner) {
        (Type::Var(var), _) => {
            debug_assert!(shape.num_slots == res.len());
            let entry = out.entry(*var).or_insert_with(VarOccurs::new);
            let data = make(shape, res);
            match kind {
                VarOccurKind::Arg(occur_idx) => {
                    let end = start + shape.num_slots;
                    let loc = ArgLoc {
                        start,
                        end,
                        occur_idx,
                    };
                    entry.args.push(ArgOccur { data, loc });
                }
                VarOccurKind::Ret => {
                    entry.rets.push(data);
                }
            }
        }
        (Type::Bool, ShapeInner::Bool) => {}
        (Type::Num(model), ShapeInner::Num(shape)) if model == shape => {}
        (Type::Tuple(models), ShapeInner::Tuple(shapes)) => {
            let iter = models
                .iter()
                .zip_eq(annot::enumerate_shapes(shapes, res, start));
            for (model, (shape, (start, _), res)) in iter {
                extract_vars_impl(make, kind, model, shape, start, res, out);
            }
        }
        (Type::Array(_res, model), ShapeInner::Array(shape)) => {
            extract_vars_impl(make, kind, model, shape, start + 1, &res[1..], out);
        }
        (Type::HoleArray(_res, model), ShapeInner::HoleArray(shape)) => {
            extract_vars_impl(make, kind, model, shape, start + 1, &res[1..], out);
        }
        (Type::Boxed(_res, model), ShapeInner::Boxed(shape)) => {
            extract_vars_impl(make, kind, model, shape, start + 1, &res[1..], out);
        }
        _ => panic!("type does not match model"),
    }
}

impl Type {
    pub fn get_res<I>(&self, shape: &Shape<I>) -> BTreeMap<SlotId, Res<ModelMode, ModelLt>> {
        let mut out_res = BTreeMap::new();
        get_res_impl(self, shape, 0, &mut out_res);
        out_res
    }

    pub fn extract_vars<I, T, Repr>(
        &self,
        make: impl Fn(&Shape<I>, &[T]) -> Repr,
        kind: VarOccurKind,
        shape: &Shape<I>,
        res: &[T],
        out: &mut IdMap<TypeVar, VarOccurs<Repr>>,
    ) {
        extract_vars_impl(&make, kind, self, shape, 0, res, out);
    }
}

impl ModeProp {
    pub fn extract<T: Clone>(self, res: &ResModes<T>) -> T {
        match self {
            ModeProp::Stack => match res {
                ResModes::Stack(stack) => stack.clone(),
                _ => panic!("expected stack resource"),
            },
            ModeProp::Access => match res {
                ResModes::Heap(heap) => heap.access.clone(),
                _ => panic!("expected heap resource"),
            },
            ModeProp::Storage => match res {
                ResModes::Heap(heap) => heap.storage.clone(),
                _ => panic!("expected heap resource"),
            },
        }
    }
}

declare_signatures! {
    pub box_new: (u) -> Boxed a Own t
        where u.lt <- t.lt, u.stack = t.storage, u.stack = t.access;

    pub box_get: (Boxed a m t) -> u
        where t.lt <- u.lt, u.stack = t.access;

    pub array_new: (u..) -> Array a Own t
        where u.lt <- t.lt, u.stack = t.storage, u.stack = t.access;

    pub array_get: (Array a m t, Int) -> u
        where t.lt <- u.lt, u.stack = t.access;

    pub array_extract: (Array a Own t, Int) -> (u, HoleArray a Own t)
        where t.lt <- u.lt, u.stack = t.storage;

    /// Since the `len` field of an array lives on the stack, it's technically OK to read it after
    /// the array has been released (i.e. it's backing buffer has been deallocated). Therefore, we
    /// use the empty lifetime.
    pub array_len: (Array Emp m t) -> Int;

    pub array_push: (Array a Own t, u) -> Array a Own t
        where u.lt <- t.lt, u.stack = t.storage;

    pub array_pop: (Array a Own t) -> (Array a Own t, u)
        where t.lt <- u.lt, u.stack = t.storage;

    pub array_replace: (HoleArray a Own t, u) -> Array a Own t
        where u.lt <- t.lt, u.stack = t.storage;

    pub array_reserve: (Array a Own t, Int) -> Array a Own t;

    pub io_input: () -> Array a Own Byte;

    pub io_output: (Array a m Byte) -> ();

    /// Panic returns bottom, but it's convenient to model it as returning unit.
    pub panic: (Array a m Byte) -> ();
}
