use std::collections::BTreeMap;
use std::iter;

use crate::data::builtin_traits::trait_name;
use crate::data::elaborated_ast as elab;
use crate::data::num_type::NumType;
use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;
use id_collections::IdVec;

/// Intermediate representation of partially-inferred types used for error reporting
#[derive(Clone, Debug)]
pub enum Type {
    App(Head, Vec<Type>),
    Tuple(Vec<Type>),
    Func(Purity, Box<Type>, Box<Type>),
}

#[derive(Clone, Debug)]
pub enum Head {
    Ctor(res::TypeId),
    Var(res::TypeParamId),
    /// A type that inference has not determined.
    Unknown,
    /// A type that would have to contain itself.
    RecursiveOccurrence,
}

/// A trait applied to partially-inferred types.
#[derive(Clone, Debug)]
pub struct TraitApp {
    pub trait_: res::TraitId,
    pub args: Vec<Type>,
}

impl TraitApp {
    pub fn from_resolved(app: &res::TraitApp) -> TraitApp {
        TraitApp {
            trait_: app.trait_,
            args: app.args.iter().map(Type::from_resolved).collect(),
        }
    }

    pub fn from_elab<E>(app: &elab::TraitApp<E>) -> TraitApp {
        TraitApp {
            trait_: app.trait_,
            args: app.args.iter().map(Type::from_elab).collect(),
        }
    }
}

/// Rendering of a type that inference has not determined.  Error messages should refer to this
/// constant rather than repeating the literal. `render_to` might need to insert parentheses if
/// this symbol is changed to something that doesn't look atomic, like "...".
pub const UNKNOWN_TYPE: &str = "?";

/// Rendering of a type that would have to contain itself (an "occurs check" failure).
pub const RECURSIVE_TYPE: &str = "...";

pub fn is_concrete(type_: &Type) -> bool {
    match type_ {
        Type::App(head, args) => {
            let head_concrete = match head {
                Head::Ctor(_) | Head::Var(_) => true,
                Head::Unknown | Head::RecursiveOccurrence => false,
            };
            head_concrete && args.iter().all(is_concrete)
        }
        Type::Tuple(items) => items.iter().all(is_concrete),
        Type::Func(_, arg, ret) => is_concrete(arg) && is_concrete(ret),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum BuiltinType {
    Bool,
    Num(NumType),
    Array,
}

fn builtins() -> impl Iterator<Item = BuiltinType> {
    iter::once(BuiltinType::Bool)
        .chain(NumType::ALL.into_iter().map(BuiltinType::Num))
        .chain(iter::once(BuiltinType::Array))
}

fn builtin_name(type_: BuiltinType) -> &'static str {
    match type_ {
        BuiltinType::Bool => "Bool",
        BuiltinType::Num(num) => num.name(),
        BuiltinType::Array => "Array",
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum CategorizedTypeId {
    Builtin(BuiltinType),
    Custom(res::CustomTypeId),
}

fn categorize(type_id: res::TypeId) -> CategorizedTypeId {
    match type_id {
        res::TypeId::Bool => CategorizedTypeId::Builtin(BuiltinType::Bool),
        res::TypeId::Num(num) => CategorizedTypeId::Builtin(BuiltinType::Num(num)),
        res::TypeId::Array => CategorizedTypeId::Builtin(BuiltinType::Array),

        res::TypeId::Custom(custom) => CategorizedTypeId::Custom(custom),
    }
}

#[derive(Clone, Copy, Debug)]
enum Qualification {
    Qualified,
    Unqualified,
}

pub struct TypeRenderer<'a> {
    mod_symbols: &'a IdVec<res::ModId, res::ModSymbols>,
    custom_type_symbols: &'a IdVec<res::CustomTypeId, res::TypeSymbols>,

    builtin_quals: BTreeMap<BuiltinType, Qualification>,
    custom_quals: IdVec<res::CustomTypeId, Qualification>,
}

impl Type {
    pub fn from_resolved(type_: &res::Type) -> Type {
        match type_ {
            res::Type::App(head, args) => Type::App(
                match head {
                    res::TypeHead::Ctor(id) => Head::Ctor(*id),
                    res::TypeHead::Var(param) => Head::Var(*param),
                },
                args.iter().map(Type::from_resolved).collect(),
            ),
            res::Type::Tuple(items) => Type::Tuple(items.iter().map(Type::from_resolved).collect()),
            res::Type::Func(purity, arg, ret) => Type::Func(
                *purity,
                Box::new(Type::from_resolved(arg)),
                Box::new(Type::from_resolved(ret)),
            ),
        }
    }

    /// Rendering ignores a type's evidence.
    pub fn from_elab<E>(type_: &elab::Type<E>) -> Type {
        match type_ {
            elab::Type::App(head, args) => Type::App(
                match head {
                    res::TypeHead::Ctor(id) => Head::Ctor(*id),
                    res::TypeHead::Var(param) => Head::Var(*param),
                },
                args.iter().map(Type::from_elab).collect(),
            ),
            elab::Type::Constrained(id, args, _) => Type::App(
                Head::Ctor(res::TypeId::Custom(*id)),
                args.iter().map(Type::from_elab).collect(),
            ),
            elab::Type::Tuple(items) => Type::Tuple(items.iter().map(Type::from_elab).collect()),
            elab::Type::Func(purity, arg, ret) => Type::Func(
                *purity,
                Box::new(Type::from_elab(arg)),
                Box::new(Type::from_elab(ret)),
            ),
        }
    }
}

fn find_builtin_quals(
    mod_symbols: &IdVec<res::ModId, res::ModSymbols>,
    custom_type_symbols: &IdVec<res::CustomTypeId, res::TypeSymbols>,
) -> BTreeMap<BuiltinType, Qualification> {
    let mut quals: BTreeMap<BuiltinType, Qualification> = builtins()
        .map(|builtin| (builtin, Qualification::Unqualified))
        .collect();

    let names: BTreeMap<&'static str, BuiltinType> = builtins()
        .map(|builtin| (builtin_name(builtin), builtin))
        .collect();

    for (_, type_syms) in custom_type_symbols {
        let in_root_module = mod_symbols[type_syms.mod_].decl_loc == res::ModDeclLoc::Root;

        if in_root_module {
            if let Some(builtin) = names.get(&type_syms.type_name.0 as &str) {
                quals.insert(*builtin, Qualification::Qualified);
            }
        }
    }

    quals
}

fn find_custom_quals(
    custom_type_symbols: &IdVec<res::CustomTypeId, res::TypeSymbols>,
) -> IdVec<res::CustomTypeId, Qualification> {
    let mut name_counts = BTreeMap::<raw::TypeName, u32>::new();

    for builtin in builtins() {
        name_counts.insert(raw::TypeName(builtin_name(builtin).to_owned()), 1);
    }

    for (_, type_syms) in custom_type_symbols {
        *name_counts.entry(type_syms.type_name.clone()).or_insert(0) += 1;
    }

    let mut quals = IdVec::from_vec(vec![Qualification::Unqualified; custom_type_symbols.len()]);

    for (id, type_syms) in custom_type_symbols {
        debug_assert!(name_counts[&type_syms.type_name] > 0);
        if name_counts[&type_syms.type_name] > 1 {
            quals[id] = Qualification::Qualified;
        }
    }

    quals
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    Root,
    FuncRet,
    FuncArg,
    AppArg,
}

impl<'a> TypeRenderer<'a> {
    pub fn new(
        mod_symbols: &'a IdVec<res::ModId, res::ModSymbols>,
        custom_type_symbols: &'a IdVec<res::CustomTypeId, res::TypeSymbols>,
    ) -> Self {
        let builtin_quals = find_builtin_quals(mod_symbols, custom_type_symbols);
        let custom_quals = find_custom_quals(custom_type_symbols);

        TypeRenderer {
            mod_symbols,
            custom_type_symbols,

            builtin_quals,
            custom_quals,
        }
    }

    pub fn render_trait_app(
        &self,
        params: &IdVec<res::TypeParamId, raw::TypeParam>,
        app: &TraitApp,
        trait_symbols: &IdVec<res::CustomTraitId, res::TraitSymbols>,
    ) -> String {
        let mut result = trait_name(trait_symbols, app.trait_);
        for arg in &app.args {
            result.push(' ');
            self.render_to(params, arg, &mut result, Precedence::AppArg);
        }
        result
    }

    fn render_mod_path(&self, mod_: res::ModId, dest: &mut String) {
        match &self.mod_symbols[mod_].decl_loc {
            res::ModDeclLoc::ChildOf { parent, name } => {
                self.render_mod_path(*parent, dest);
                dest.push_str(&name.0);
                dest.push('.');
            }

            res::ModDeclLoc::Root => {}
        }
    }

    fn render_id_to(&self, id: res::TypeId, dest: &mut String) {
        match categorize(id) {
            CategorizedTypeId::Builtin(builtin) => {
                match self.builtin_quals[&builtin] {
                    Qualification::Unqualified => {}
                    Qualification::Qualified => dest.push_str("[Builtins]."),
                }

                dest.push_str(builtin_name(builtin));
            }

            CategorizedTypeId::Custom(custom) => {
                match self.custom_quals[&custom] {
                    Qualification::Unqualified => {}
                    Qualification::Qualified => {
                        self.render_mod_path(self.custom_type_symbols[custom].mod_, dest);
                    }
                }

                dest.push_str(&self.custom_type_symbols[custom].type_name.0);
            }
        }
    }

    fn render_to(
        &self,
        params: &IdVec<res::TypeParamId, raw::TypeParam>,
        type_: &Type,
        dest: &mut String,
        prec: Precedence,
    ) {
        match type_ {
            Type::App(head, args) => {
                // A recursive occurrence renders as "...", which does not look atomic, so it is
                // parenthesized anywhere but at the root even when it has no arguments.
                let parenthesize = match head {
                    Head::RecursiveOccurrence if args.is_empty() => prec > Precedence::Root,
                    _ => prec >= Precedence::AppArg && !args.is_empty(),
                };

                if parenthesize {
                    dest.push('(');
                }

                match head {
                    Head::Ctor(id) => self.render_id_to(*id, dest),
                    Head::Var(param) => dest.push_str(&params[param].0),
                    Head::Unknown => dest.push_str(UNKNOWN_TYPE),
                    Head::RecursiveOccurrence => dest.push_str(RECURSIVE_TYPE),
                }

                for arg in args {
                    dest.push(' ');
                    self.render_to(params, arg, dest, Precedence::AppArg);
                }

                if parenthesize {
                    dest.push(')');
                }
            }

            Type::Tuple(items) => {
                dest.push('(');
                for (i, item) in items.iter().enumerate() {
                    self.render_to(params, item, dest, Precedence::Root);
                    if i + 1 != items.len() {
                        dest.push_str(", ");
                    }
                }
                dest.push(')');
            }

            Type::Func(purity, arg, ret) => {
                let parenthesize = prec >= Precedence::FuncArg;

                if parenthesize {
                    dest.push('(');
                }

                match purity {
                    Purity::Pure => {}
                    Purity::Impure => dest.push_str("proc "),
                }

                self.render_to(params, arg, dest, Precedence::FuncArg);

                dest.push_str(" -> ");

                self.render_to(params, ret, dest, Precedence::FuncRet);

                if parenthesize {
                    dest.push(')');
                }
            }
        }
    }

    pub fn render(&self, params: &IdVec<res::TypeParamId, raw::TypeParam>, type_: &Type) -> String {
        let mut result = String::new();
        self.render_to(params, type_, &mut result, Precedence::Root);
        result
    }

    pub fn render_ctor(&self, id: res::TypeId, variant: res::VariantId) -> (String, String) {
        let mut id_rendered = String::new();
        self.render_id_to(id, &mut id_rendered);

        let ctor_rendered = match (id, variant) {
            (res::TypeId::Bool, res::VariantId(0)) => "False".to_owned(),
            (res::TypeId::Bool, res::VariantId(1)) => "True".to_owned(),

            (res::TypeId::Custom(custom), _) => self.custom_type_symbols[custom].variant_symbols
                [variant]
                .variant_name
                .0
                .to_owned(),

            _ => unreachable!(),
        };

        (id_rendered, ctor_rendered)
    }
}
