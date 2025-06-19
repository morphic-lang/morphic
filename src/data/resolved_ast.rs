use crate::data::intrinsics::Intrinsic;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use crate::ErrorId;
use id_collections::{id_type, IdVec};
use std::path::PathBuf;
use std::rc::Rc;

// 'ModId' is used only for the purposes of reporting human-readable module information to the user,
// for example during error reporting. After the initial name resolution pass is complete, the
// module from which a particular type or value originated is semantically irrelevant.
#[id_type]
pub struct ModId(pub usize);

#[id_type]
pub struct CustomTypeId(pub usize);

#[id_type]
pub struct VariantId(pub usize);

#[id_type]
pub struct TypeParamId(pub usize);

#[id_type]
pub struct CustomGlobalId(pub usize);

#[id_type]
pub struct LocalId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AnyId {
    Mod(ModId),
    CustomType(CustomTypeId),
    CustomGlobal(CustomGlobalId),
    Expr(ExprId),
    Type(TypeId),
    Pattern(PatternId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum NominalType {
    Bool,
    Byte,
    Int,
    Float,
    Array,
    Custom(CustomTypeId),
}

#[derive(Clone, Debug)]
pub enum TypeData {
    Var(TypeParamId),
    App(NominalType, Vec<Type>),
    Tuple(Vec<Type>),
    Func(Purity, Type, Type),
    Error(ErrorId),
}

#[derive(Clone, Debug)]
pub struct Type {
    pub id: NominalType,
    pub data: Rc<TypeData>,
}

impl Type {
    pub fn new(store: &mut Store, data: TypeData) -> Type {
        let data = Rc::new(data);
        let id = store.types.push(data.clone());
        Type { id, data }
    }
}

#[derive(Clone, Debug)]
pub struct TypeScheme {
    pub num_params: usize,
    pub body: Type,
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub num_params: usize,
    pub variants: IdVec<VariantId, Option<Type>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum IoOp {
    Input,
    Output,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArrayOp {
    Get,
    Extract,
    Len,
    Push,
    Pop,
    Reserve,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Global {
    Intrinsic(Intrinsic),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic,
    Ctor(NominalType, VariantId),
    Custom(CustomGlobalId),
}

#[derive(Clone, Debug)]
pub enum ExprData {
    Global(Global),
    Local(LocalId),
    Tuple(Vec<Expr>),
    Lam(Purity, Pattern, Expr, Option<prof::ProfilePointId>),
    App(Purity, Expr, Expr),
    Match(Expr, Vec<(Pattern, Expr)>),
    LetMany(Vec<(Pattern, Expr)>, Expr),

    ArrayLit(Vec<Expr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),

    Error(ErrorId),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub id: ExprId,
    pub data: Rc<ExprData>,
}

impl Expr {
    pub fn new(store: &mut Store, data: ExprData) -> Expr {
        let data = Rc::new(data);
        let id = store.exprs.push(data.clone());
        Expr { id, data }
    }
}

#[derive(Clone, Debug)]
pub struct ValDef {
    pub scheme: TypeScheme,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub enum PatternData {
    Any,
    Var,
    Tuple(Vec<Pattern>),
    Ctor(NominalType, VariantId, Option<Pattern>),

    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),

    Error(ErrorId),
}

#[derive(Clone, Debug)]
pub struct Pattern {
    pub id: PatternId,
    pub data: Rc<PatternData>,
}

impl Pattern {
    pub fn new(store: &mut Store, data: PatternData) -> Pattern {
        let data = Rc::new(data);
        let id = store.patterns.push(data.clone());
        Pattern { id, data }
    }
}

#[derive(Clone, Debug)]
pub struct VariantSymbols {
    pub variant_name: raw::CtorName,
}

#[derive(Clone, Debug)]
pub struct TypeSymbols {
    pub mod_: ModId,
    pub type_name: raw::TypeName,
    pub variant_symbols: IdVec<VariantId, VariantSymbols>,
}

#[derive(Clone, Debug)]
pub struct ValSymbols {
    pub mod_: ModId,
    pub type_param_names: IdVec<TypeParamId, raw::TypeParam>,
    pub val_name: raw::ValName,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModDeclLoc {
    Root,
    ChildOf { parent: ModId, name: raw::ModName },
}

#[derive(Clone, Debug)]
pub struct ModSymbols {
    pub file: PathBuf,
    pub decl_loc: ModDeclLoc,
}

#[derive(Clone, Debug)]
pub struct Store {
    pub expr_map: BTreeMap<raw::ExprId, ExprId>,
    pub type_map: BTreeMap<raw::TypeId, TypeId>,
    pub pattern_map: BTreeMap<raw::PatternId, PatternId>,

    pub exprs: IdVec<ExprId, Rc<ExprData>>,
    pub types: IdVec<TypeId, Rc<TypeData>>,
    pub patterns: IdVec<PatternId, Rc<PatternData>>,
}

impl Store {
    pub fn new() -> Store {
        Store {
            expr_map: BTreeMap::new(),
            type_map: BTreeMap::new(),
            pattern_map: BTreeMap::new(),
            exprs: IdVec::new(),
            types: IdVec::new(),
            patterns: IdVec::new(),
        }
    }

    pub fn get_expr(&self, id: ExprId) -> Expr {
        Expr {
            id,
            data: self.exprs[id].clone(),
        }
    }

    pub fn get_type(&self, id: TypeId) -> Type {
        Type {
            id,
            data: self.types[id].clone(),
        }
    }

    pub fn get_pattern(&self, id: PatternId) -> Pattern {
        Pattern {
            id,
            data: self.patterns[id].clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Program {
    // Data
    pub main: CustomGlobalId,
    pub custom_types: IdVec<CustomTypeId, TypeDef>,
    pub vals: IdVec<CustomGlobalId, ValDef>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub store: Store,

    // Metadata
    pub mod_symbols: IdVec<ModId, ModSymbols>,
    pub custom_type_symbols: IdVec<CustomTypeId, TypeSymbols>,
    pub val_symbols: IdVec<CustomGlobalId, ValSymbols>,
    pub spans: BTreeMap<raw::AnyId, Span>,
}
