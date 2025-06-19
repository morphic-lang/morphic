use crate::data::intrinsics::Intrinsic;
use crate::data::purity::Purity;
use crate::data::visibility::Visibility;
use crate::report_error::Span;
use crate::ErrorId;
use id_collections::{id_type, IdVec};
use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;

// Either a successfully parsed AST node or the ID of an error that occurred during parsing. The
// actual error values are stored in a side store so that parts of the AST can be dropped during
// program transformations without losing information.
pub type RawResult<T> = Result<T, ErrorId>;

#[id_type]
pub struct ModId(pub usize);

#[id_type]
pub struct ItemId(pub usize);

#[id_type]
pub struct ModBindingId(pub usize);

#[id_type]
pub struct ModSpecId(pub usize);

#[id_type]
pub struct ExposeItemId(pub usize);

#[id_type]
pub struct ExposeSpecId(pub usize);

#[id_type]
pub struct ExprId(pub usize);

#[id_type]
pub struct TypeId(pub usize);

#[id_type]
pub struct PatternId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AnyId {
    Mod(ModId),
    Item(ItemId),
    ModBinding(ModBindingId),
    ModSpec(ModSpecId),
    ExposeItem(ExposeItemId),
    ExposeSpec(ExposeSpecId),
    Expr(ExprId),
    Type(TypeId),
    Pattern(PatternId),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeName(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CtorName(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeParam(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ValName(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModName(pub String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModPath(pub Vec<ModName>);

#[derive(Clone, Debug)]
pub enum TypeData {
    Var(TypeParam),
    App(ModPath, TypeName, Vec<Type>),
    Tuple(Vec<Type>),
    Func(Purity, Type, Type),
    Error(ErrorId),
}

#[derive(Clone, Debug)]
pub struct Type {
    pub id: TypeId,
    pub data: Rc<TypeData>,
}

impl Type {
    pub fn new(store: &mut Store, span: Option<Span>, data: TypeData) -> Type {
        let data = Rc::new(data);
        let id = store.types.push(data.clone());
        if let Some(span) = span {
            store.spans.insert(AnyId::Type(id), span);
        }
        Type { id, data }
    }
}

#[derive(Clone, Debug)]
pub enum ExprData {
    // Qualified and unqualified names have sufficiently different resolution rules that it is
    // useful to think of them as separate single syntactic constructs.  An unqualified name
    // *cannot* be regarded as a qualified name with an empty mod path, because unqualified names
    // are special in that they may refer to local variables as well as module-scoped values.
    Var(ValName),
    QualName(ModPath, ValName),
    Ctor(ModPath, CtorName),
    Tuple(Vec<Expr>),
    Lam(Purity, Pattern, Expr),
    // App expressions in the raw AST need to explicitly distinguish between taking "multiple
    // arguments" and taking a single tuple as an argument, because this distinction is relevant for
    // pipe desugaring.  Subsequent passes in the compiler do not make this distinction.
    //
    // The `usize`s denote the span of the argument list.
    App(Purity, Expr, (usize, usize, Vec<Expr>)),
    // This distinguishes function applications arising from operator expressions from all other
    // function applications. Without this variant, error messages for `(a + b) <| c` would be
    // horrible.
    OpApp(Intrinsic, Expr),
    Match(Expr, Vec<(Pattern, Expr)>),
    LetMany(VecDeque<(Pattern, Expr)>, Expr),

    // `!` can be treated as an ordinary `OpApp`, since it follows normal evaluation rules
    And(Expr, Expr),
    Or(Expr, Expr),

    PipeLeft(Expr, Expr),
    PipeRight(Expr, Expr),

    ArrayLit(Vec<Expr>),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),

    Error(ErrorId),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub id: ExprId,
    pub data: Rc<ExprData>,
}

impl Expr {
    pub fn new(store: &mut Store, span: Option<Span>, data: ExprData) -> Expr {
        let data = Rc::new(data);
        let id = store.exprs.push(data.clone());
        if let Some(span) = span {
            store.spans.insert(AnyId::Expr(id), span);
        }
        Expr { id, data }
    }

    pub fn unop(_table: &mut Store, op: Intrinsic, arg: Expr) -> ExprData {
        ExprData::OpApp(op, arg)
    }

    pub fn binop(store: &mut Store, op: Intrinsic, l: Expr, r: Expr) -> ExprData {
        let args = Expr::new(store, None, ExprData::Tuple(vec![l, r]));
        ExprData::OpApp(op, args)
    }
}

#[derive(Clone, Debug)]
pub enum PatternData {
    Any,
    Var(ValName),
    Tuple(Vec<Pattern>),
    Ctor(ModPath, CtorName, Option<Pattern>),

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
    pub fn new(store: &mut Store, span: Option<Span>, data: PatternData) -> Pattern {
        let data = Rc::new(data);
        let id = store.patterns.push(data.clone());
        if let Some(span) = span {
            store.spans.insert(AnyId::Pattern(id), span);
        }
        Pattern { id, data }
    }
}

#[derive(Clone, Debug)]
pub struct ModBindingData {
    pub name: ModName,
    pub binding: ModPath,
}

#[derive(Clone, Debug)]
pub struct ModBinding {
    pub id: ModBindingId,
    pub data: Rc<ModBindingData>,
}

impl ModBinding {
    pub fn new(store: &mut Store, span: Option<Span>, data: ModBindingData) -> ModBinding {
        let data = Rc::new(data);
        let id = store.mod_bindings.push(data.clone());
        if let Some(span) = span {
            store.spans.insert(AnyId::ModBinding(id), span);
        }
        ModBinding { id, data }
    }
}

#[derive(Clone, Debug)]
pub enum ModSpecData {
    File(Vec<String>),
    Inline(ModId),
}

#[derive(Clone, Debug)]
pub struct ModSpec {
    pub id: ModSpecId,
    pub data: Rc<ModSpecData>,
}

impl ModSpec {
    pub fn new(store: &mut Store, span: Option<Span>, data: ModSpecData) -> ModSpec {
        let data = Rc::new(data);
        let id = store.mod_specs.push(data.clone());
        if let Some(span) = span {
            store.spans.insert(AnyId::ModSpec(id), span);
        }
        ModSpec { id, data }
    }
}

#[derive(Clone, Debug)]
pub enum ExposeItemData {
    Val(Visibility, ValName),
    Type(Visibility, TypeName, Vec<(Visibility, CtorName)>),
    Mod(Visibility, ModName, ExposeSpec),
}

#[derive(Clone, Debug)]
pub struct ExposeItem {
    pub id: ExposeItemId,
    pub data: Rc<ExposeItemData>,
}

impl ExposeItem {
    pub fn new(store: &mut Store, span: Option<Span>, data: ExposeItemData) -> ExposeItem {
        let data = Rc::new(data);
        let id = store.expose_items.push(data.clone());
        if let Some(span) = span {
            store.spans.insert(AnyId::ExposeItem(id), span);
        }
        ExposeItem { id, data }
    }
}

#[derive(Clone, Debug)]
pub enum ExposeSpecData {
    // TODO: Add support for glob imports
    Specific(Vec<RawResult<ExposeItem>>),
}

#[derive(Clone, Debug)]
pub struct ExposeSpec {
    pub id: ExposeSpecId,
    pub data: Rc<ExposeSpecData>,
}

impl ExposeSpec {
    pub fn new(store: &mut Store, span: Option<Span>, data: ExposeSpecData) -> ExposeSpec {
        let data = Rc::new(data);
        let id = store.expose_specs.push(data.clone());
        if let Some(span) = span {
            store.spans.insert(AnyId::ExposeSpec(id), span);
        }
        ExposeSpec { id, data }
    }
}

#[derive(Clone, Debug)]
pub enum ItemData {
    TypeDef(
        Visibility,
        TypeName,
        Vec<TypeParam>,
        Vec<RawResult<(Visibility, CtorName, Option<Type>)>>,
    ),
    ValDef(Visibility, ValName, Type, Expr),
    ModDef(
        Visibility,
        ModName,
        ModSpec,
        Vec<RawResult<ModBinding>>,
        ExposeSpec,
    ),
    ModImport(ModName, ExposeSpec),
    ModExpose(ModPath, ExposeSpec),
}

#[derive(Clone, Debug)]
pub struct Item {
    pub id: ItemId,
    pub data: Rc<ItemData>,
}

impl Item {
    pub fn new(store: &mut Store, span: Option<Span>, data: ItemData) -> Item {
        let data = Rc::new(data);
        let id = store.items.push(data.clone());
        if let Some(span) = span {
            store.spans.insert(AnyId::Item(id), span);
        }
        Item { id, data }
    }
}

#[derive(Clone, Debug)]
pub struct ModData {
    pub items: Vec<RawResult<Item>>,
}

#[derive(Clone, Debug)]
pub struct Mod {
    pub id: ModId,
    pub data: Rc<ModData>,
}

impl Mod {
    pub fn new(store: &mut Store, span: Option<Span>, data: ModData) -> Mod {
        let data = Rc::new(data);
        let id = store.mods.push(data.clone());
        if let Some(span) = span {
            store.spans.insert(AnyId::Mod(id), span);
        }
        Mod { id, data }
    }
}

#[derive(Clone, Debug)]
pub struct Store {
    pub mods: IdVec<ModId, Rc<ModData>>,
    pub items: IdVec<ItemId, Rc<ItemData>>,
    pub mod_bindings: IdVec<ModBindingId, Rc<ModBindingData>>,
    pub mod_specs: IdVec<ModSpecId, Rc<ModSpecData>>,
    pub expose_items: IdVec<ExposeItemId, Rc<ExposeItemData>>,
    pub expose_specs: IdVec<ExposeSpecId, Rc<ExposeSpecData>>,
    pub exprs: IdVec<ExprId, Rc<ExprData>>,
    pub types: IdVec<TypeId, Rc<TypeData>>,
    pub patterns: IdVec<PatternId, Rc<PatternData>>,
    pub spans: BTreeMap<AnyId, Span>,
}

impl Store {
    pub fn new() -> Store {
        Store {
            mods: IdVec::new(),
            items: IdVec::new(),
            mod_bindings: IdVec::new(),
            mod_specs: IdVec::new(),
            expose_items: IdVec::new(),
            expose_specs: IdVec::new(),
            exprs: IdVec::new(),
            types: IdVec::new(),
            patterns: IdVec::new(),
            spans: BTreeMap::new(),
        }
    }

    pub fn get_mod(&self, id: ModId) -> Mod {
        Mod {
            id,
            data: self.mods[id].clone(),
        }
    }

    pub fn get_item(&self, id: ItemId) -> Item {
        Item {
            id,
            data: self.items[id].clone(),
        }
    }

    pub fn get_mod_binding(&self, id: ModBindingId) -> ModBinding {
        ModBinding {
            id,
            data: self.mod_bindings[id].clone(),
        }
    }

    pub fn get_mod_spec(&self, id: ModSpecId) -> ModSpec {
        ModSpec {
            id,
            data: self.mod_specs[id].clone(),
        }
    }

    pub fn get_expose_item(&self, id: ExposeItemId) -> ExposeItem {
        ExposeItem {
            id,
            data: self.expose_items[id].clone(),
        }
    }

    pub fn get_expose_spec(&self, id: ExposeSpecId) -> ExposeSpec {
        ExposeSpec {
            id,
            data: self.expose_specs[id].clone(),
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
