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
// - A program in this representation consists of a sequence of top-level type definitions, followed
//   by a sequence of top-level function definitions.  Types are identified by unique `TypeId`s, and
//   functions by unique `FuncId`s.  Some definitions are user-provided, others are
//   compiler-generated.
//
// - In general, definitions will both refer to types and functions bound by other definitions, and
//   bind types and functions of their own.  When a definition references a type or function bound
//   by another definition, we represent this in the IR with a field of type `TypeId` or `FuncId`.
//   When a definition binds a new type or function to an id, we represent this in the IR with a
//   field of type `BindTo<TypeId>` or `BindTo<FuncId>`.  For example, the definition of a function
//   with id `FuncId(3)` would be represented with a definition of the form
//   `Def::CustomFunc(BindTo(FuncId(3)), ...)`.
//
// - Type definitions are given in strict topological/dependency order; a type definition will only
//   ever mention types defined earlier in the sequence of type definitions.  This means that you
//   are always guaranteed to be able to to compute the layout (size and alignment) of any type you
//   encounter in a type definition, so the sequence of type definitions may be processed in a
//   single pass.  Some type definitions take the form of "forward declarations", which provide just
//   enough information to compute the layout of a type before its full content is provided by a
//   later definition.
//
// - Function definitions are given in an arbitrary (non-topological) order, and the dependency
//   graph between function definitions may contain cycles (i.e., functions may be recursive).  This
//   means you must process the sequence of function definitions in two passes: a first pass to
//   forward-declare the signatures of all functions, and a second pass to populate their bodies.

id_type!(pub TypeId);
id_type!(pub FuncId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct BindTo<T>(pub T);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Bool,
    Num(first_ord::NumType),
    Tuple(Vec<Type>),
    Opaque(TypeId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum IsZeroSized {
    NonZeroSized,
    ZeroSized,
}

#[derive(Clone, Debug)]
pub struct ArrayTypeDef {
    pub rep: constrain::RepChoice,
    pub item_zero_sized: IsZeroSized,
    pub item_type: Type,

    // Bindings:
    pub array_type: BindTo<TypeId>,
    pub hole_array_type: BindTo<TypeId>,
}

#[derive(Clone, Debug)]
pub struct BoxedTypeDef {
    pub item_type: Type,

    // Binding:
    pub boxed_type: BindTo<TypeId>,
}

#[derive(Clone, Debug)]
pub struct CustomTypeDef {
    pub content_type: Type,

    // Binding:
    pub custom_type: BindTo<TypeId>,
}

/// Forward-declare a variant type.  This should be paired with a `VariantTypeDef` later in the
/// program which references the same `variant_type` type id.
///
/// Note: This definition intentionally does not provide the content types for each case of the
/// variant type.  These are provided in the corresponding `VariantTypeDef`.  Separating variant
/// type declarations from definitions in this way allows us to break cycles in the type dependency
/// graph, because generating the concrete representation of a variant type requires knowing the
/// layout of all of the types that it wraps.
#[derive(Clone, Debug)]
pub struct VariantTypeDecl {
    // Binding:
    pub variant_type: BindTo<TypeId>,
}

/// Define a variant type, generating a concrete representation for it.  This should be paired with
/// a `VariantTypeDecl` earlier in the program which binds the same `variant_type` type id.
///
/// Note: the backend *must* generate non-zero-sized representations for all variant types, even if
/// they could otherwise be represented in zero bytes.
#[derive(Clone, Debug)]
pub struct VariantTypeDef {
    // Invariant: the layout of every type in `content_types` must be determinable entirely from
    // type defintiions which appear earlier in the program.  In particular, no type in
    // `content_types` will have a layout which depends on the layout of a variant type which has
    // been declared (with `VariantTypeDecl`) but not yet defined (with `VariantTypeDef`).
    pub content_types: IdVec<first_ord::VariantId, Type>,
    pub variant_type: TypeId,
}

#[derive(Clone, Debug)]
pub enum TypeDef {
    ArrayTypeDef(ArrayTypeDef),
    BoxedTypeDef(BoxedTypeDef),
    CustomTypeDef(CustomTypeDef),
    VariantTypeDecl(VariantTypeDecl),
    VariantTypeDef(VariantTypeDef),
}

#[derive(Clone, Debug)]
pub struct ArrayOpsDef {
    pub rep: constrain::RepChoice,
    pub item_zero_sized: IsZeroSized,
    pub item_type: Type,
    pub array_type: TypeId,
    pub hole_array_type: TypeId,

    // Dependencies:

    // [item_type (borrowed)] -> []
    pub item_retain: Option<FuncId>,

    // [item_type (borrowed)] -> []
    pub item_release: Option<FuncId>,

    // Bindings:

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
pub struct IoOpsDef {
    pub byte_array_rep: constrain::RepChoice,

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
pub struct BoxedOpsDef {
    pub item_type: Type,
    pub boxed_type: TypeId,

    // Dependencies:
    pub item_release: Option<FuncId>,

    // Bindings:

    // [item_type (owned)] -> [boxed_type (owned)]
    pub new: BindTo<FuncId>,

    // [boxed_type (borrowed)] -> [item_type (borrowed)]
    pub get: BindTo<FuncId>,

    // [boxed_type] -> []
    pub retain: BindTo<FuncId>,

    // [boxed_type] -> []
    pub release: BindTo<FuncId>,
}

id_type!(pub LocalId);

#[derive(Clone, Debug)]
pub struct LetBinding {
    // Types of bound variables.  Each is assigned a new sequential `LocalId`.
    pub types: Vec<Type>,
    // "Right hand side" of assignment.  The `value` expression should return `types.len()` values.
    pub values: Expr,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Local(LocalId),

    // May return zero or more values depending on the signature of the called function
    Call(FuncId, Vec<LocalId>),

    // At the type level, returns zero return values.  Semantically, does not actually return, but
    // rather acts as a jump.
    TailCall(tail::TailFuncId, Vec<LocalId>),

    // Unconditionally invokes undefined behavior.  Allowed to return any type.
    Unreachable(Type),

    // Each branch of the `if` must return exactly one value.
    If(LocalId, Box<Expr>, Box<Expr>),

    LetManyMulti(
        Vec<LetBinding>, // Bindings
        Vec<LocalId>,    // Body.  May return zero or more values.
    ),

    Tuple(Vec<LocalId>),
    TupleField(LocalId, usize),
    WrapVariant(
        TypeId,
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        LocalId,
    ),
    UnwrapVariant(
        TypeId,
        IdVec<first_ord::VariantId, Type>,
        first_ord::VariantId,
        LocalId,
    ),
    WrapCustom(
        TypeId, // custom type
        Type,   // content type
        LocalId,
    ),
    UnwrapCustom(
        TypeId, // custom type
        Type,   // content type
        LocalId,
    ),

    // Returns a bool
    CheckVariant(TypeId, first_ord::VariantId, LocalId),

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
pub enum FuncDef {
    ArrayOpsDef(ArrayOpsDef),
    IoOpsDef(IoOpsDef),
    BoxedOpsDefs(BoxedOpsDef),
    CustomFuncDef(CustomFuncDef),
}

#[derive(Clone, Debug)]
pub struct Program {
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub type_defs: Vec<TypeDef>,
    pub func_defs: Vec<FuncDef>,

    // Must have signature [] -> []
    pub main: FuncId,
}
