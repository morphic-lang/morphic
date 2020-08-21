use std::collections::BTreeMap;

use crate::data::purity::Purity;
use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;
use crate::util::id_vec::IdVec;

/// Intermediate representation of partially-inferred types used for error reporting
#[derive(Clone, Debug)]
pub enum Type {
    Var(res::TypeParamId),
    App(res::TypeId, Vec<Type>),
    Tuple(Vec<Type>),
    Func(Purity, Box<Type>, Box<Type>),
    Unknown,
    RecursiveOccurrence,
}

pub fn is_concrete(type_: &Type) -> bool {
    match type_ {
        Type::Var(_) => true,
        Type::App(_, args) => args.iter().all(is_concrete),
        Type::Tuple(items) => items.iter().all(is_concrete),
        Type::Func(_, arg, ret) => is_concrete(arg) && is_concrete(ret),
        Type::Unknown => false,
        Type::RecursiveOccurrence => false,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum BuiltinType {
    Bool,
    Byte,
    Int,
    Float,
    Array,
}

const BUILTINS: &[BuiltinType] = &[
    BuiltinType::Bool,
    BuiltinType::Byte,
    BuiltinType::Int,
    BuiltinType::Float,
    BuiltinType::Array,
];

fn builtin_name(type_: BuiltinType) -> &'static str {
    match type_ {
        BuiltinType::Bool => "Bool",
        BuiltinType::Byte => "Byte",
        BuiltinType::Int => "Int",
        BuiltinType::Float => "Float",
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
        res::TypeId::Byte => CategorizedTypeId::Builtin(BuiltinType::Byte),
        res::TypeId::Int => CategorizedTypeId::Builtin(BuiltinType::Int),
        res::TypeId::Float => CategorizedTypeId::Builtin(BuiltinType::Float),
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
    program: &'a res::Program,

    builtin_quals: BTreeMap<BuiltinType, Qualification>,
    custom_quals: IdVec<res::CustomTypeId, Qualification>,
}

fn find_builtin_quals(program: &res::Program) -> BTreeMap<BuiltinType, Qualification> {
    let mut quals: BTreeMap<BuiltinType, Qualification> = BUILTINS
        .iter()
        .map(|&builtin| (builtin, Qualification::Unqualified))
        .collect();

    let names: BTreeMap<&'static str, BuiltinType> = BUILTINS
        .iter()
        .map(|&builtin| (builtin_name(builtin), builtin))
        .collect();

    for (_, type_syms) in &program.custom_type_symbols {
        let in_root_module = program.mod_symbols[type_syms.mod_].decl_loc == res::ModDeclLoc::Root;

        if in_root_module {
            if let Some(builtin) = names.get(&type_syms.type_name.0 as &str) {
                quals.insert(*builtin, Qualification::Qualified);
            }
        }
    }

    quals
}

fn find_custom_quals(program: &res::Program) -> IdVec<res::CustomTypeId, Qualification> {
    let mut name_counts = BTreeMap::<raw::TypeName, u32>::new();

    for &builtin in BUILTINS {
        name_counts.insert(raw::TypeName(builtin_name(builtin).to_owned()), 1);
    }

    for (_, type_syms) in &program.custom_type_symbols {
        *name_counts.entry(type_syms.type_name.clone()).or_insert(0) += 1;
    }

    let mut quals = IdVec::from_items(vec![Qualification::Unqualified; program.custom_types.len()]);

    for (id, type_syms) in &program.custom_type_symbols {
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
    pub fn new(program: &'a res::Program) -> Self {
        debug_assert_eq!(
            program.custom_types.len(),
            program.custom_type_symbols.len()
        );

        let builtin_quals = find_builtin_quals(program);
        let custom_quals = find_custom_quals(program);

        TypeRenderer {
            program,

            builtin_quals,
            custom_quals,
        }
    }

    fn render_mod_path(&self, mod_: res::ModId, dest: &mut String) {
        match &self.program.mod_symbols[mod_].decl_loc {
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
                        self.render_mod_path(self.program.custom_type_symbols[custom].mod_, dest);
                    }
                }

                dest.push_str(&self.program.custom_type_symbols[custom].type_name.0);
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
            Type::Var(param) => {
                dest.push_str(&params[param].0);
            }

            Type::App(id, args) => {
                let parenthesize = prec >= Precedence::AppArg && args.len() > 0;

                if parenthesize {
                    dest.push('(');
                }

                self.render_id_to(*id, dest);

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

            Type::Unknown | Type::RecursiveOccurrence => {
                let parenthesize = prec > Precedence::Root;

                if parenthesize {
                    dest.push_str("(...)");
                } else {
                    dest.push_str("...");
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

            (res::TypeId::Custom(custom), _) => self.program.custom_type_symbols[custom]
                .variant_symbols[variant]
                .variant_name
                .0
                .to_owned(),

            _ => unreachable!(),
        };

        (id_rendered, ctor_rendered)
    }
}
