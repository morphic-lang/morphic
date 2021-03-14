use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::repr_constrained_ast as constrain;
use crate::data::tail_rec_ast as tail;
use crate::util::id_vec::IdVec;

// Concepts and notational conventions in this module:
//
// - Unlike all previous passes, functions in this IR can accept multiple arguments and provide
//   multiple return values.  In comments denoting function signatures, we use square brackets `[]`
//   to denote argument and return lists, to avoid confusion with tuple types.
//
// - A program in this representation consists of a sequence of top-level "definitions", which may
//   declare both types and functions.  Types are identified by unique `TypeId`s, and functions by
//   unique `FuncId`s.  Some definitions are user-provided, others are compiler-generated.
//
// - In general, definitions will both refer to types and functions bound by other definitions, and
//   bind types and functions of their own.  When a definition references a type or function bound
//   by another definition, we represent this in the IR with a field of type `TypeId` or `FuncId`.
//   When a definition binds a new type or function to an id, we represent this in the IR with a
//   field of type `BindTo<TypeId>` or `BindTo<FuncId>`.  For example, the definition of a function
//   with id `FuncId(3)` would be represented with a definition of the form
//   `Def::CustomFunc(BindTo(FuncId(3)), ...)`.
//
// - Unless otherwise noted, definitions may be given in an arbitrary order.  In particular,
//   definitions are *not* guaranteed to be given in topological/dependency order, and in general
//   the dependency graph between definitions may contain cycles.  The only place where we make
//   guarantees about ordering is in `CustomTypeDef` definitions; see the comments on that type for
//   more details.

id_type!(pub TypeId);
id_type!(pub FuncId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct BindTo<T>(T);

#[derive(Clone, Debug)]
pub enum Type {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Type>),
    Variants(IdVec<first_ord::VariantId, Type>),
    Opaque(TypeId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArrayRep {
    RepChoice(constrain::RepChoice),
    ZeroSized,
}

#[derive(Clone, Debug)]
pub struct ArrayDef {
    pub rep: ArrayRep,
    pub item_type: Type,

    // [item_type (borrowed)] -> []
    pub item_retain: Option<FuncId>,

    // [item_type (borrowed)] -> []
    pub item_release: Option<FuncId>,

    // Type bindings:
    pub array_type: BindTo<TypeId>,
    pub hole_array_type: BindTo<TypeId>,

    // Function bindings:

    // [] -> [array_type (owned)]
    pub new: BindTo<FuncId>,

    // [array_type (borrowed), int] -> item_type (borrowed)
    pub get: BindTo<FuncId>,

    // [array_type (owned), int] -> [item_type (owned), hole_array_type (owned)]
    pub extract: BindTo<FuncId>,

    // [array_type (borrowed)] -> [int]
    pub len: BindTo<FuncId>,

    // [array_type (owned), item_type (owned)] -> [array_type (owned)]
    pub push: BindTo<FuncId>,

    // [array_type (owned)] -> [array_type (owned), item_type (owned)]
    pub pop: BindTo<FuncId>,

    // [hole_array_type (owned), item_type (owned)] -> [array_type (owned)]
    pub replace: BindTo<FuncId>,

    // [array_type (owned), Int] -> [array_type (owned)]
    pub reserve: BindTo<FuncId>,

    // [array_type (borrowed)] -> []
    pub retain: BindTo<FuncId>,

    // [array_type (borrowed)] -> []
    pub release: BindTo<FuncId>,
}

#[derive(Clone, Debug)]
pub struct IoDef {
    pub byte_array_rep: constrain::RepChoice,

    // Must be the `TypeId` of a byte array with representation `byte_array_rep`.
    // TODO: Is there some better way to structure this?
    pub byte_array_type: TypeId,

    // Bindings:

    // [] -> [byte_array_type (owned)]
    pub input: BindTo<FuncId>,

    // [byte_array_type (borrowed)] -> []
    pub output: BindTo<FuncId>,

    // [byte_array_type (borrowed)] -> []
    pub panic: BindTo<FuncId>,
}

#[derive(Clone, Debug)]
pub struct BoxedDef {
    pub item_type: Type,

    // Type bindings:
    pub boxed_type: BindTo<TypeId>,

    // Function bindings:

    // [item_type (owned)] -> [boxed_type (owned)]
    pub new: BindTo<FuncId>,

    // [boxed_type (borrowed)] -> [item_type (borrowed)]
    pub get: BindTo<FuncId>,

    // [boxed_type (borrowed)] -> []
    pub retain: BindTo<FuncId>,

    // [boxed_type (owned)] -> []
    pub release: BindTo<FuncId>,
}

#[derive(Clone, Debug)]
pub struct CustomTypeDef {
    // Invariant: The *size* of `content_type` must be determinable using only the sizes of types
    // already defined earlier in the top-level definition list.  This is roughly a topological
    // ordering constraint, although it does not forbid `content_type` from (transitively)
    // mentioning custom >[custom_type]
    // Does not touch refcounts; agnostic to owned/borrowed status.
    pub wrap: BindTo<FuncId>,

    // [custom_type] -> [content_type]
    // Does not touch refcounts; agnostic to owned/borrowed status.
    pub unwrap: BindTo<FuncId>,
}

id_type!(pub LocalId);

#[derive(Clone, Debug)]
pub struct LetBinding {
    // Types of bound variables.  Each is assigned a new sequential `LocalId`.
    types: Vec<Type>,
    // "Right hand side" of assignment.  The `value` expression should return `types.len()` values.
    values: Expr,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(LocalId),

    // May return zero or more values depending on the signature of the called function
    Call(FuncId, Vec<LocalId>),

    // At the type level, returns the same types as the enclosing function.  Semantically, does not
    // actually return, but rather acts as a jump.
    TailCall(tail::TailFuncId, LocalId),

    // Each branch of the `if` must return exactly one value.
    If(LocalId, Box<Expr>, Box<Expr>),

    LetManyMulti(
        Vec<LetBinding>, // Bindings
        Vec<LocalId>,    // Body.  May return zero or more values.
    ),

    Tuple(Vec<LocalId>),
    TupleField(LocalId, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        LocalId,
    ),
    UnwrapVariant(
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        LocalId,
    ),

    // Unlike prior passes, intrinsics here accept multiple arguments rather than tuples.
    // For example, the `AddInt` intrinsic accepts two arguments.
    Intrinsic(Intrinsic, Vec<LocalId>),

    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
pub struct TailFunc {
    // Each argument binds a distinct `Localid` in `body`, starting from `LocalId(0)`.
    pub arg_types: Vec<Type>,
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CallingConvention {
    /// Pass this argument or return value in a (virtual) register.
    Register,
    /// Pass this argument or return value in memory, through a pointer.
    Memory,
}

#[derive(Clone, Debug)]
pub struct CustomFuncDef {
    // Each argument binds a distinct `LocalId` in `body`, starting from `LocalId(0)`.
    pub arg_types: Vec<(Type, CallingConvention)>,
    pub ret_types: Vec<(Type, CallingConvention)>,

    pub tail_funcs: IdVec<tail::TailFuncId, TailFunc>,
    pub body: Expr,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub enum Def {
    CustomTypeDef(CustomTypeDef),
    CustomFuncDef(CustomFuncDef),

    ArrayDef(ArrayDef),
    IoDef(IoDef),
    BoxedDef(BoxedDef),
}

#[derive(Clone, Debug)]
pub struct Program {
    pub defs: Vec<Def>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,

    // Must have signature [] -> []
    pub main: FuncId,
}
