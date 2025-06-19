use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;
use crate::ErrorId;
use id_collections::{id_type, IdVec};

#[id_type]
pub struct ExprId(pub usize);

#[id_type]
pub struct PatternId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AnyId {
    Mod(res::ModId),
    CustomType(res::CustomTypeId),
    CustomGlobal(res::CustomGlobalId),
    Expr(ExprId),
    Type(res::TypeId),
    Pattern(PatternId),
}

#[derive(Clone, Debug)]
pub enum ExprData {
    Global(res::Global, IdVec<res::TypeParamId, res::Type>),
    Local(res::LocalId),
    Tuple(Vec<Expr>),
    Lam(
        Purity,
        res::Type, // Argument type
        res::Type, // Return type
        Pattern,
        Box<Expr>,
        Option<prof::ProfilePointId>,
    ),
    App(Purity, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>, res::Type),
    LetMany(Vec<(Pattern, Expr)>, Box<Expr>),

    ArrayLit(res::Type, Vec<Expr>),
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
    pub scheme: res::TypeScheme,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub enum PatternData {
    Any(res::Type),
    Var(res::Type),
    Tuple(Vec<Pattern>),
    Ctor(
        res::NominalType,
        Vec<res::Type>,
        res::VariantId,
        Option<Box<Pattern>>,
    ),
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
pub struct Store {
    pub expr_map: BTreeMap<raw::ExprId, ExprId>,
    pub type_map: BTreeMap<raw::TypeId, TypeId>,
    pub pattern_map: BTreeMap<raw::PatternId, PatternId>,

    pub exprs: IdVec<ExprId, Rc<ExprData>>,
    pub types: IdVec<res::TypeId, Rc<res::TypeData>>,
    pub patterns: IdVec<PatternId, Rc<PatternData>>,
}

#[derive(Clone, Debug)]
pub struct Program {
    // Data
    pub main: res::CustomGlobalId,
    pub custom_types: IdVec<res::CustomTypeId, res::TypeDef>,
    pub vals: IdVec<res::CustomGlobalId, ValDef>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,

    // Metadata
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_type_symbols: IdVec<res::CustomTypeId, res::TypeSymbols>,
    pub val_symbols: IdVec<res::CustomGlobalId, res::ValSymbols>,
    pub spans: BTreeMap<AnyId, Span>,
}
