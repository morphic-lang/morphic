use crate::data::purity::Purity;
use crate::data::visibility::Visibility;
use lalrpop_util::ParseError;
use once_cell::sync::Lazy;
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::iter;
use std::path::{Path, PathBuf};

use crate::data::builtin_traits::{BuiltinImpl, BuiltinTrait, BuiltinTraitFunc};
use crate::data::intrinsics as intrs;
use crate::data::profile as prof;
use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;
use crate::file_cache::FileCache;
use crate::lex;
use crate::parse;
use crate::parse_error;
use crate::report_type;
use id_collections::{Count, IdVec};
use morphic_common::config::{self as cfg, ProfileMode};
use morphic_common::intrinsic_config::INTRINSIC_NAMES;
use morphic_common::lines;
use morphic_common::report_error::{locate_path, locate_span, ColorMode, Locate, Reportable};

#[derive(Debug)]
pub enum ErrorKind {
    ReadFailed(PathBuf, io::Error),
    ParseFailed(ParseError<usize, lex::Token, lex::Error>),
    PipeNotAppLeft,
    PipeNotAppRight,
    ParseProfileSymFailed(cfg::SymbolName),
    ResolveProfileSymFailed(cfg::SymbolName),
    ProfileSymNotFunction,
    IllegalFilePath(String),
    DuplicateModName(String),
    DuplicateTypeName(String),
    DuplicateCtorName(String),
    DuplicateVarName(String),
    TypeNotFound(String),
    TypeParamNotFound(String),
    VarNotFound(String),
    CtorNotFound(String),
    ModNotFound(String),
    TypeNotVisible(String),
    VarNotVisible(String),
    CtorNotVisible(String),
    ModNotVisible(String),
    TraitNotFound(String),
    TraitNotVisible(String),
    ImplNotFound(String),
    ImplNotVisible(String),
    DuplicateTraitName(String),
    DuplicateImplName(String),
    TraitArity {
        trait_: String,
        expected: usize,
        actual: usize,
    },
    ImplMissingFunc {
        impl_: String,
        func: String,
    },
    ImplExtraFunc {
        impl_: String,
        func: String,
    },
    ImplFuncMismatch {
        impl_: String,
        func: String,
        expected: String,
        actual: String,
    },
    TraitFuncNotFound {
        trait_: String,
        func: String,
    },
    MainNotFound,
}

type RawError = Locate<ErrorKind>;

#[derive(Debug)]
pub struct Error(RawError);

impl Reportable for Error {
    fn report(
        &self,
        dest: &mut impl io::Write,
        files: &FileCache,
        color: ColorMode,
    ) -> io::Result<()> {
        use ErrorKind::*;

        match &self.0.error {
            ReadFailed(path, err) if err.kind() != io::ErrorKind::NotFound => {
                writeln!(dest, "Could not read {}: {}", path.display(), err)?;
                return Ok(());
            }
            ParseFailed(err) => {
                parse_error::report(
                    dest,
                    files,
                    color,
                    self.0.path.as_ref().map(|path| path.as_ref()),
                    err,
                )?;
                return Ok(());
            }
            _ => {}
        }

        // This is repeated in two different error messages, so we factor it out.
        let profile_explanation =
            "Arguments to '--profile' must be function names relative to the root \
             module. For example, you could profile a function 'foo' in the root \
             module by just passing '--profile foo', or you could profile a function \
             'bar' in the module 'Baz' by passing '--profile Baz.bar'.";

        self.0.report_with(dest, files, color, |kind| match kind {
            ReadFailed(path, err) => {
                // Other cases are handled above
                assert!(err.kind() == io::ErrorKind::NotFound);
                (
                    "File Not Found",
                    format!(
                        lines!["I couldn't find a file at this path:", "", "    {}",],
                        path.display()
                    ),
                )
            }
            ParseFailed(_) => {
                // Handled above
                unreachable!()
            }
            PipeNotAppLeft => ("Invalid Left Pipe Syntax", "".to_owned()),
            PipeNotAppRight => ("Invalid Right Pipe Syntax", "".to_owned()),
            ParseProfileSymFailed(sym_name) => (
                "Incorrect Syntax in '--profile' Argument",
                format!(
                    lines![
                        "I couldn't parse this '--profile' argument:",
                        "",
                        "    --profile {sym}",
                        "",
                        "{explanation}",
                    ],
                    sym = sym_name.0,
                    explanation = profile_explanation,
                ),
            ),
            ResolveProfileSymFailed(sym_name) => (
                "Function Not Found in '--profile' Argument",
                format!(
                    lines![
                        "I couldn't find the function mentioned in this '--profile' argument:",
                        "",
                        "    --profile {sym}",
                        "",
                        "{explanation}"
                    ],
                    sym = sym_name.0,
                    explanation = profile_explanation,
                ),
            ),
            ProfileSymNotFunction => (
                "Unsupported '--profile' Argument",
                "I can't add profiling instrumentation to this expression. I can only \
                 profile top-level function definitions."
                    .to_owned(),
            ),
            IllegalFilePath(path) => (
                "Invalid File Path",
                format!(
                    lines![
                        "You cannot access a module using the path",
                        "",
                        "    {}",
                        "",
                        "Module file paths must be specified relative to the parent module's \
                         directory, and may only access that directory and its subdirectories \
                         (that is, module paths may not use the \"parent directory\" symbol '..').",
                    ],
                    path
                ),
            ),
            DuplicateModName(name) => (
                "Duplicate Module Name",
                format!(
                    "You have already declared a module named '{}' in this scope.",
                    name
                ),
            ),
            DuplicateTypeName(name) => (
                "Duplicate Type Name",
                format!(
                    "You have already declared a type named '{}' in this scope.",
                    name
                ),
            ),
            DuplicateCtorName(name) => (
                "Duplicate Constructor Name",
                format!(
                    "You have already declared a constructor named '{}' in this scope.",
                    name
                ),
            ),
            DuplicateVarName(name) => (
                "Duplicate Variable Name",
                format!(
                    "You have already declared a variable named '{}' in this scope.",
                    name
                ),
            ),
            TypeNotFound(name) => (
                "Type Not Found",
                format!(
                    "There is no type named '{}' available in the current scope.",
                    name
                ),
            ),
            TypeParamNotFound(name) => (
                "Type Parameter Not Found",
                format!(
                    lines![
                        "There is no type parameter named '{}' in scope.",
                        "",
                        "Type variables in a type annotation must come from the signature \
                         of the enclosing definition or the parameter list of the enclosing \
                         type declaration.",
                    ],
                    name
                ),
            ),
            VarNotFound(name) => (
                "Variable Not Found",
                format!(
                    "There is no variable named '{}' available in the current scope.",
                    name
                ),
            ),
            CtorNotFound(name) => (
                "Constructor Not Found",
                format!(
                    "There is no constructor named '{}' available in the current scope.",
                    name
                ),
            ),
            ModNotFound(name) => (
                "Module Not Found",
                format!(
                    "There is no module named '{}' available in the current scope.",
                    name
                ),
            ),
            TypeNotVisible(name) => (
                "Type Not Visible",
                format!(
                    "Type '{}' is private and therefore not available in the current scope.",
                    name
                ),
            ),
            VarNotVisible(name) => (
                "Variable Not Visible",
                format!(
                    "Variable '{}' is private and therefore not available in the current scope.",
                    name
                ),
            ),
            CtorNotVisible(name) => (
                "Constructor Not Visible",
                format!(
                    "Constructor '{}' is private and therefore not available in the current scope.",
                    name
                ),
            ),
            ModNotVisible(name) => (
                "Module Not Visible",
                format!(
                    "Module '{}' is private and therefore not available in the current scope.",
                    name
                ),
            ),
            TraitNotFound(name) => (
                "Trait Not Found",
                format!(
                    "There is no trait named '{}' available in the current scope.",
                    name
                ),
            ),
            TraitNotVisible(name) => (
                "Trait Not Visible",
                format!(
                    "The trait '{}' is private to the module that declares it.",
                    name
                ),
            ),
            ImplNotFound(name) => (
                "Impl Not Found",
                format!(
                    "There is no impl named '{}' available in the current scope.",
                    name
                ),
            ),
            ImplNotVisible(name) => (
                "Impl Not Visible",
                format!(
                    "The impl '{}' is private to the module that declares it.",
                    name
                ),
            ),
            DuplicateTraitName(name) => (
                "Duplicate Trait Name",
                format!(
                    "You have already declared a trait named '{}' in this scope.",
                    name
                ),
            ),
            DuplicateImplName(name) => (
                "Duplicate Impl Name",
                format!(
                    "You have already declared an impl named '{}' in this scope.",
                    name
                ),
            ),
            TraitArity {
                trait_,
                expected,
                actual,
            } => (
                "Wrong Number of Trait Arguments",
                format!(
                    "The trait '{}' takes {} type argument(s), but {} were given here.",
                    trait_, expected, actual
                ),
            ),
            ImplMissingFunc { impl_, func } => (
                "Missing Impl Func",
                format!(
                    "The impl '{}' does not define '{}', which its trait requires.",
                    impl_, func
                ),
            ),
            ImplExtraFunc { impl_, func } => (
                "Unexpected Impl Func",
                format!(
                    "The impl '{}' defines '{}', but its trait has no func of that name.",
                    impl_, func
                ),
            ),
            ImplFuncMismatch {
                impl_,
                func,
                expected,
                actual,
            } => (
                "Impl Func Signature Mismatch",
                format!(
                    lines![
                        "In the impl '{impl_}', the func '{func}' should have the signature",
                        "",
                        "    {expected}",
                        "",
                        "but it is declared with the signature",
                        "",
                        "    {actual}",
                    ],
                    impl_ = impl_,
                    func = func,
                    expected = expected,
                    actual = actual,
                ),
            ),
            TraitFuncNotFound { trait_, func } => (
                "Trait Func Not Found",
                format!("The trait '{}' has no func named '{}'.", trait_, func),
            ),
            MainNotFound => (
                "Main Not Found",
                format!(
                    "Your program does not have a 'main' function declared in its root module."
                ),
            ),
        })
    }

    fn exit_status(&self) -> i32 {
        1
    }
}

static BUILTIN_TYPES: Lazy<BTreeMap<raw::TypeName, res::TypeId>> = Lazy::new(|| {
    let mut type_map = BTreeMap::new();

    type_map.insert(raw::TypeName("Bool".to_owned()), res::TypeId::Bool);
    type_map.insert(raw::TypeName("Byte".to_owned()), res::TypeId::Byte);
    type_map.insert(raw::TypeName("Int".to_owned()), res::TypeId::Int);
    type_map.insert(raw::TypeName("Float".to_owned()), res::TypeId::Float);
    type_map.insert(raw::TypeName("Array".to_owned()), res::TypeId::Array);

    type_map
});
static BUILTIN_CTORS: Lazy<BTreeMap<raw::CtorName, (res::TypeId, res::VariantId)>> =
    Lazy::new(|| {
        let mut ctor_map = BTreeMap::new();

        ctor_map.insert(
            raw::CtorName("False".to_owned()),
            (res::TypeId::Bool, res::VariantId(0)),
        );
        ctor_map.insert(
            raw::CtorName("True".to_owned()),
            (res::TypeId::Bool, res::VariantId(1)),
        );

        ctor_map
    });
/// The funcs of the builtin traits are builtin value names, so that `add` can be passed along
/// or called directly, and so that a user impl of a builtin trait can be checked by name.
static BUILTIN_TRAIT_FUNCS: Lazy<BTreeMap<raw::ValName, res::GlobalRef>> = Lazy::new(|| {
    BuiltinTraitFunc::ALL
        .into_iter()
        .map(|func| {
            (
                raw::ValName(func.name().to_owned()),
                res::GlobalRef::TraitFunc(res::TraitId::Builtin(func.trait_()), func.id()),
            )
        })
        .collect()
});

/// The builtin impls are in scope in every module, except where a declared or imported impl of
/// the same name covers one up, as a declared or imported type, value, or trait covers up the
/// builtin one.
static BUILTIN_IMPLS: Lazy<BTreeMap<raw::ImplName, res::ImplId>> = Lazy::new(|| {
    BuiltinImpl::all()
        .map(|impl_| (raw::ImplName(impl_.name()), res::ImplId::Builtin(impl_)))
        .collect()
});

static BUILTIN_GLOBALS: Lazy<BTreeMap<raw::ValName, res::GlobalId>> = Lazy::new(|| {
    let mut global_map = BTreeMap::new();

    global_map.insert(
        raw::ValName("get".to_owned()),
        res::GlobalId::ArrayOp(res::ArrayOp::Get),
    );
    global_map.insert(
        raw::ValName("extract".to_owned()),
        res::GlobalId::ArrayOp(res::ArrayOp::Extract),
    );
    global_map.insert(
        raw::ValName("len".to_owned()),
        res::GlobalId::ArrayOp(res::ArrayOp::Len),
    );
    global_map.insert(
        raw::ValName("push".to_owned()),
        res::GlobalId::ArrayOp(res::ArrayOp::Push),
    );
    global_map.insert(
        raw::ValName("pop".to_owned()),
        res::GlobalId::ArrayOp(res::ArrayOp::Pop),
    );
    global_map.insert(
        raw::ValName("reserve".to_owned()),
        res::GlobalId::ArrayOp(res::ArrayOp::Reserve),
    );
    global_map.insert(
        raw::ValName("input".to_owned()),
        res::GlobalId::IoOp(res::IoOp::Input),
    );
    global_map.insert(
        raw::ValName("output".to_owned()),
        res::GlobalId::IoOp(res::IoOp::Output),
    );
    global_map.insert(raw::ValName("panic".to_owned()), res::GlobalId::Panic);

    for &(intrinsic, name) in INTRINSIC_NAMES {
        match name {
            intrs::Name::Op { debug_name: _ } => {}
            intrs::Name::Func { source_name } => {
                global_map.insert(
                    raw::ValName(source_name.to_owned()),
                    res::GlobalId::Intrinsic(intrinsic),
                );
            }
        }
    }

    global_map
});

#[derive(Clone, Debug)]
struct ModMap {
    mods: BTreeMap<raw::ModName, (Visibility, res::ModId)>,
    types: BTreeMap<raw::TypeName, (Visibility, res::TypeId)>,
    ctors: BTreeMap<raw::CtorName, (Visibility, res::CustomTypeId, res::VariantId)>,
    vals: BTreeMap<raw::ValName, (Visibility, res::GlobalRef)>,
    traits: BTreeMap<raw::TraitName, (Visibility, res::TraitId)>,
    // The impls visible in the module, which is exactly the set the trait solver may use for the
    // module's definitions.
    impls: BTreeMap<raw::ImplName, (Visibility, res::ImplId)>,
}

impl ModMap {
    fn new() -> Self {
        ModMap {
            mods: BTreeMap::new(),
            types: BTreeMap::new(),
            ctors: BTreeMap::new(),
            vals: BTreeMap::new(),
            traits: BTreeMap::new(),
            impls: BTreeMap::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct GlobalContext {
    mods: IdVec<res::ModId, ModMap>,
    mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    types: IdVec<res::CustomTypeId, Option<res::TypeDef>>,
    type_symbols: IdVec<res::CustomTypeId, res::TypeSymbols>,
    vals: IdVec<res::CustomGlobalId, Option<res::ValDef>>,
    val_symbols: IdVec<res::CustomGlobalId, Option<res::ValSymbols>>,
    traits: IdVec<res::CustomTraitId, Option<res::TraitDef>>,
    trait_symbols: IdVec<res::CustomTraitId, Option<res::TraitSymbols>>,
    // Known from the declaration alone, so that a constraint can be checked for the right number
    // of arguments before the trait's definition has been resolved.
    trait_arities: IdVec<res::CustomTraitId, usize>,
    impls: IdVec<res::CustomImplId, Option<res::ImplDef>>,
    impl_symbols: IdVec<res::CustomImplId, Option<res::ImplSymbols>>,
}

#[derive(Clone, Debug)]
struct LocalScope {
    names: Vec<raw::ValName>,
    next_id: res::LocalId,
}

impl LocalScope {
    fn new(next_id: res::LocalId) -> Self {
        Self {
            names: Vec::new(),
            next_id,
        }
    }
}

#[derive(Clone, Debug)]
struct LocalContext {
    scopes: Vec<LocalScope>,
    locals: BTreeMap<raw::ValName, res::LocalId>,
}

impl LocalContext {
    fn new() -> Self {
        Self {
            scopes: vec![LocalScope::new(res::LocalId(0))],
            locals: BTreeMap::new(),
        }
    }

    fn get(&self, name: &raw::ValName) -> Option<res::LocalId> {
        self.locals.get(name).cloned()
    }

    fn insert(&mut self, name: raw::ValName) -> Result<(), RawError> {
        let local_id = self.next_local_id();
        insert_unique(&mut self.locals, name.clone(), local_id)
            .map_err(|()| ErrorKind::DuplicateVarName(name.0.clone()))?;

        let scope = self.scopes.last_mut().unwrap();
        scope.names.push(name);
        scope.next_id.0 += 1;

        Ok(())
    }

    fn insert_anon(&mut self) -> res::LocalId {
        let scope = self.scopes.last_mut().unwrap();
        let id = scope.next_id;
        scope.next_id.0 += 1;
        id
    }

    fn next_local_id(&self) -> res::LocalId {
        self.scopes.last().unwrap().next_id
    }

    fn new_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        self.scopes.push(LocalScope::new(self.next_local_id()));
        let ret = f(self);

        let scope = self.scopes.pop().unwrap();
        for name in &scope.names {
            self.locals.remove(name);
        }

        ret
    }
}

pub fn resolve_program(
    files: &mut FileCache,
    file_path: &Path,
    profile_syms: &[cfg::SymbolName],
    profile_mode: ProfileMode,
) -> Result<res::Program, Error> {
    let profile_record_rc = profile_mode == ProfileMode::RecordRc;

    let mut ctx = GlobalContext {
        mods: IdVec::new(),
        mod_symbols: IdVec::new(),
        types: IdVec::new(),
        type_symbols: IdVec::new(),
        vals: IdVec::new(),
        val_symbols: IdVec::new(),
        traits: IdVec::new(),
        trait_symbols: IdVec::new(),
        trait_arities: IdVec::new(),
        impls: IdVec::new(),
        impl_symbols: IdVec::new(),
    };

    let main_mod = resolve_mod_from_file(
        files,
        &mut ctx,
        BTreeMap::new(),
        file_path,
        res::ModDeclLoc::Root,
    )
    .map_err(Error)?;

    let main_proc = if let Some(&(_, res::GlobalRef::Global(res::GlobalId::Custom(id)))) = ctx.mods
        [main_mod]
        .vals
        .get(&raw::ValName("main".to_owned()))
    {
        id
    } else {
        return Err(Error(locate_path(file_path)(
            ErrorKind::MainNotFound.into(),
        )));
    };

    let val_symbols = ctx.val_symbols.map(|_id, val_syms| val_syms.unwrap());

    let mut vals = ctx.vals.map(|_id, val_def| val_def.unwrap());

    let profile_points = resolve_profile_points(
        &ctx.mod_symbols,
        &val_symbols,
        &ctx.mods,
        main_mod,
        &mut vals,
        profile_syms,
        profile_record_rc,
    )
    .map_err(Error)?;

    let impl_scope = ctx.mods.map_refs(|_id, mod_map| {
        BUILTIN_IMPLS
            .iter()
            .filter(|(name, _)| !mod_map.impls.contains_key(name))
            .map(|(_, id)| *id)
            .chain(mod_map.impls.values().map(|(_, id)| *id))
            .collect()
    });

    Ok(res::Program {
        mod_symbols: ctx.mod_symbols,
        custom_types: ctx.types.map(|_id, typedef| typedef.unwrap()),
        custom_type_symbols: ctx.type_symbols,
        profile_points,
        vals,
        val_symbols,
        traits: ctx.traits.map(|_id, def| def.unwrap()),
        trait_symbols: ctx.trait_symbols.map(|_id, symbols| symbols.unwrap()),
        impls: ctx.impls.map(|_id, def| def.unwrap()),
        impl_symbols: ctx.impl_symbols.map(|_id, symbols| symbols.unwrap()),
        impl_scope,
        main: main_proc,
    })
}

fn resolve_mod(
    files: &mut FileCache,
    ctx: &mut GlobalContext,
    file_path: &Path,
    decl_loc: res::ModDeclLoc,
    bindings: BTreeMap<raw::ModName, res::ModId>,
    content: raw::Program,
) -> Result<res::ModId, RawError> {
    // Pre-"allocate" a module id initially populated with a dummy 'ModMap'.  We populate this
    // module id with the actual 'ModMap' at the end of this function.
    //
    // We need to generate this module id early in order to include it in the "symbols" structures
    // associated to this modules' type and value declarations.
    let self_mod_id = ctx.mods.push(ModMap::new());

    {
        let self_mod_symbols_id = ctx.mod_symbols.push(res::ModSymbols {
            file: file_path.to_owned(),
            decl_loc,
        });
        debug_assert_eq!(self_mod_symbols_id, self_mod_id);
    }

    // Generate mappings
    //
    // This pass also populates `type_symbols`
    //
    // We can't populate 'val_symbols' yet, because we  populate the 'type_param_names' field of
    // each 'ValSymbols' struct at the same time that we resolve the corresponding value's type
    // scheme.

    let (mod_map, pending_type_defs, pending_trait_defs, pending_impl_defs, pending_val_defs) = {
        let mut mod_map = ModMap::new();
        let mut pending_trait_defs = Vec::new();
        let mut pending_impl_defs = Vec::new();

        let mut pending_type_defs = Vec::new();
        let mut pending_val_defs = Vec::new();

        for item in content.0 {
            match item {
                raw::Item::TypeDef(visibility, name, params, constrs, variants) => {
                    let type_id = ctx.types.push(None);
                    {
                        let type_symbols_id = ctx.type_symbols.push(res::TypeSymbols {
                            mod_: self_mod_id,
                            type_name: name.clone(),
                            type_param_names: IdVec::from_vec(params.clone()),
                            constr_spans: IdVec::from_vec(
                                constrs.iter().map(|constr| constr.span).collect(),
                            ),
                            variant_symbols: IdVec::from_vec(
                                variants
                                    .iter()
                                    .map(|(_, variant_name, variant_type, span)| {
                                        res::VariantSymbols {
                                            variant_name: variant_name.clone(),
                                            span: *span,
                                            content_spans: variant_type
                                                .as_ref()
                                                .map(res::TypeSpans::of),
                                        }
                                    })
                                    .collect(),
                            ),
                        });
                        debug_assert_eq!(type_id, type_symbols_id);
                    }

                    insert_unique(
                        &mut mod_map.types,
                        name.clone(),
                        (visibility, res::TypeId::Custom(type_id)),
                    )
                    .map_err(|()| ErrorKind::DuplicateTypeName(name.0.clone()).into())
                    .map_err(locate_path(file_path))?;

                    for (idx, (ctor_visibility, ctor_name, _, _)) in variants.iter().enumerate() {
                        insert_unique(
                            &mut mod_map.ctors,
                            ctor_name.clone(),
                            (*ctor_visibility, type_id, res::VariantId(idx)),
                        )
                        .map_err(|()| ErrorKind::DuplicateCtorName(ctor_name.0.clone()).into())
                        .map_err(locate_path(file_path))?;
                    }

                    pending_type_defs.push((type_id, params, constrs, variants));
                }

                raw::Item::ValDef(visibility, name, type_, constrs, body, span) => {
                    let val_id = ctx.vals.push(None);
                    {
                        let val_symbols_id = ctx.val_symbols.push(None);
                        debug_assert_eq!(val_id, val_symbols_id);
                    }

                    insert_unique(
                        &mut mod_map.vals,
                        name.clone(),
                        (
                            visibility,
                            res::GlobalRef::Global(res::GlobalId::Custom(val_id)),
                        ),
                    )
                    .map_err(|()| ErrorKind::DuplicateVarName(name.0.clone()).into())
                    .map_err(locate_path(file_path))?;

                    pending_val_defs.push((name, val_id, type_, constrs, body, span));
                }

                raw::Item::TraitDef(visibility, name, params, supers, funcs) => {
                    let trait_id = ctx.traits.push(None);
                    {
                        let symbols_id = ctx.trait_symbols.push(None);
                        debug_assert_eq!(trait_id, symbols_id);
                        let arity_id = ctx.trait_arities.push(params.len());
                        debug_assert_eq!(trait_id, arity_id);
                    }

                    insert_unique(
                        &mut mod_map.traits,
                        name.clone(),
                        (visibility, res::TraitId::Custom(trait_id)),
                    )
                    .map_err(|()| ErrorKind::DuplicateTraitName(name.0.clone()).into())
                    .map_err(locate_path(file_path))?;

                    // A trait's funcs are module-scoped values, exactly as a type's constructors
                    // are module-scoped names.
                    for (idx, func) in funcs.iter().enumerate() {
                        insert_unique(
                            &mut mod_map.vals,
                            func.name.clone(),
                            (
                                visibility,
                                res::GlobalRef::TraitFunc(
                                    res::TraitId::Custom(trait_id),
                                    res::TraitFuncId(idx),
                                ),
                            ),
                        )
                        .map_err(|()| ErrorKind::DuplicateVarName(func.name.0.clone()).into())
                        .map_err(locate_span(func.span.0, func.span.1))
                        .map_err(locate_path(file_path))?;
                    }

                    pending_trait_defs.push((trait_id, name, params, supers, funcs));
                }

                raw::Item::ImplDef(visibility, name, head, constrs, funcs) => {
                    let impl_id = ctx.impls.push(None);
                    {
                        let symbols_id = ctx.impl_symbols.push(None);
                        debug_assert_eq!(impl_id, symbols_id);
                    }

                    insert_unique(
                        &mut mod_map.impls,
                        name.clone(),
                        (visibility, res::ImplId::Custom(impl_id)),
                    )
                    .map_err(|()| ErrorKind::DuplicateImplName(name.0.clone()).into())
                    .map_err(locate_path(file_path))?;

                    pending_impl_defs.push((impl_id, name, head, constrs, funcs));
                }

                raw::Item::ModDef(visibility, name, spec, bindings, expose) => {
                    let sub_mod_bindings: BTreeMap<_, _> = bindings
                        .into_iter()
                        .map(|binding| {
                            Ok((
                                binding.name,
                                resolve_mod_path(&ctx.mods, &mod_map.mods, &binding.binding)
                                    .map_err(locate_path(file_path))?,
                            ))
                        })
                        .collect::<Result<_, RawError>>()?;

                    let sub_decl_loc = res::ModDeclLoc::ChildOf {
                        parent: self_mod_id,
                        name: name.clone(),
                    };

                    let sub_mod_id = resolve_mod_spec(
                        files,
                        ctx,
                        file_path,
                        sub_decl_loc,
                        sub_mod_bindings,
                        spec,
                    )?;

                    insert_unique(&mut mod_map.mods, name.clone(), (visibility, sub_mod_id))
                        .map_err(|()| ErrorKind::DuplicateModName(name.0.clone()).into())
                        .map_err(locate_path(file_path))?;

                    resolve_exposures(&ctx.mods, &mut mod_map, sub_mod_id, expose)
                        .map_err(locate_path(file_path))?;
                }

                raw::Item::ModImport(name, expose) => {
                    let bound_mod_id = *bindings
                        .get(&name)
                        .ok_or_else(|| ErrorKind::ModNotFound(name.0.clone()).into())
                        .map_err(locate_path(file_path))?;

                    insert_unique(
                        &mut mod_map.mods,
                        name.clone(),
                        (Visibility::Private, bound_mod_id),
                    )
                    .map_err(|()| ErrorKind::DuplicateModName(name.0.clone()).into())
                    .map_err(locate_path(file_path))?;

                    resolve_exposures(&ctx.mods, &mut mod_map, bound_mod_id, expose)
                        .map_err(locate_path(file_path))?;
                }

                raw::Item::ModExpose(local_mod_path, expose) => {
                    let exposed_id = resolve_mod_path(&ctx.mods, &mod_map.mods, &local_mod_path)
                        .map_err(locate_path(file_path))?;

                    resolve_exposures(&ctx.mods, &mut mod_map, exposed_id, expose)
                        .map_err(locate_path(file_path))?;
                }
            }
        }

        (
            mod_map,
            pending_type_defs,
            pending_trait_defs,
            pending_impl_defs,
            pending_val_defs,
        )
    };

    // Resolve content of type and value definitions

    for (type_id, params, constrs, variants) in pending_type_defs {
        let mut param_names = IdVec::new();
        let mut param_map = BTreeMap::new();
        for param_name in params {
            let id = param_names.push(param_name.clone());
            insert_unique(&mut param_map, param_name.clone(), id)
                .map_err(|()| ErrorKind::DuplicateTypeName(param_name.0).into())
                .map_err(locate_path(file_path))?;
        }

        let resolved_variants = IdVec::from_vec(
            variants
                .iter()
                .map(|(_, _, variant_type, _)| match variant_type {
                    None => Ok(None),
                    Some(variant_type) => Ok(Some(resolve_type(
                        &ctx.mods,
                        &mod_map,
                        &param_map,
                        variant_type,
                    )?)),
                })
                .collect::<Result<_, _>>()
                .map_err(locate_path(file_path))?,
        );

        let trait_constrs = IdVec::from_vec(
            constrs
                .iter()
                .map(|constr| resolve_trait_app(&ctx, &mod_map, &param_map, constr))
                .collect::<Result<Vec<_>, RawError>>()
                .map_err(locate_path(file_path))?,
        );

        debug_assert!(ctx.types[type_id].is_none());
        ctx.types[type_id] = Some(res::TypeDef {
            num_params: param_names.count(),
            trait_constrs,
            variants: resolved_variants,
        });
    }

    // Traits come before impls, which need the traits' func schemes, and both come before values,
    // whose bodies may mention trait funcs and whose signatures may mention traits.

    for (trait_id, name, params, supers, funcs) in pending_trait_defs {
        resolve_trait_def(
            ctx,
            &mod_map,
            self_mod_id,
            file_path,
            trait_id,
            name,
            params,
            supers,
            funcs,
        )?;
    }

    for (impl_id, name, head, constrs, funcs) in pending_impl_defs {
        resolve_impl_def(
            ctx,
            &mod_map,
            self_mod_id,
            file_path,
            impl_id,
            name,
            head,
            constrs,
            funcs,
        )?;
    }

    for (val_name, val_id, type_, constrs, body, span) in pending_val_defs {
        let (res_scheme, type_param_names, scheme_params) =
            resolve_scheme(ctx, &mod_map, &type_, &constrs).map_err(locate_path(file_path))?;

        let res_body = resolve_expr(
            &ctx.mods,
            &mod_map,
            &scheme_params,
            &mut LocalContext::new(),
            &body,
        )
        .map_err(locate_path(file_path))?;

        debug_assert!(ctx.vals[val_id].is_none());
        ctx.vals[val_id] = Some(res::ValDef {
            scheme: res_scheme,
            body: res_body,
        });

        debug_assert!(ctx.val_symbols[val_id].is_none());
        ctx.val_symbols[val_id] = Some(res::ValSymbols {
            mod_: self_mod_id,
            type_param_names,
            val_name,
            span,
            type_spans: res::TypeSpans::of(&type_),
            trait_constr_spans: IdVec::from_vec(constrs.iter().map(|constr| constr.span).collect()),
            impl_: None,
        });
    }

    // Finally register module

    ctx.mods[self_mod_id] = mod_map;
    Ok(self_mod_id)
}

fn resolve_mod_spec(
    files: &mut FileCache,
    ctx: &mut GlobalContext,
    file_path: &Path,
    decl_loc: res::ModDeclLoc,
    bindings: BTreeMap<raw::ModName, res::ModId>,
    spec: raw::ModSpec,
) -> Result<res::ModId, RawError> {
    match spec {
        raw::ModSpec::File(sibling_path_components) => resolve_mod_from_file(
            files,
            ctx,
            bindings,
            &sibling_path_from(file_path, sibling_path_components)?,
            decl_loc,
        ),

        raw::ModSpec::Inline(content) => {
            resolve_mod(files, ctx, file_path, decl_loc, bindings, content)
        }
    }
}

fn resolve_mod_from_file(
    files: &mut FileCache,
    ctx: &mut GlobalContext,
    bindings: BTreeMap<raw::ModName, res::ModId>,
    file_path: &Path,
    decl_loc: res::ModDeclLoc,
) -> Result<res::ModId, RawError> {
    let src = files.read(file_path).map_err(|err| Locate {
        error: ErrorKind::ReadFailed(file_path.to_owned(), err),
        span: None,
        path: None,
    })?;

    let content = parse::ProgramParser::new()
        .parse(lex::Lexer::new(&src))
        .map_err(|err| ErrorKind::ParseFailed(err).into())
        .map_err(locate_path(file_path))?;

    resolve_mod(files, ctx, file_path, decl_loc, bindings, content)
}

fn resolve_mod_path(
    global_mods: &IdVec<res::ModId, ModMap>,
    local_mods: &BTreeMap<raw::ModName, (Visibility, res::ModId)>,
    path: &raw::ModPath,
) -> Result<res::ModId, RawError> {
    let local_mod_name = path.0.first().expect("ModPath should not be empty");

    let (_, mut result) = *local_mods
        .get(&local_mod_name)
        .ok_or_else(|| ErrorKind::ModNotFound(local_mod_name.0.clone()))?;

    for child_name in &path.0[1..] {
        result = resolve_sub_mod(global_mods, result, child_name)?;
    }

    Ok(result)
}

fn resolve_sub_mod(
    global_mods: &IdVec<res::ModId, ModMap>,
    mod_id: res::ModId,
    sub_mod_name: &raw::ModName,
) -> Result<res::ModId, RawError> {
    let (visibility, id) = *global_mods[mod_id]
        .mods
        .get(sub_mod_name)
        .ok_or_else(|| ErrorKind::ModNotFound(sub_mod_name.0.clone()))?;
    match visibility {
        Visibility::Public => Ok(id),
        Visibility::Private => Err(ErrorKind::ModNotVisible(sub_mod_name.0.clone()).into()),
    }
}

fn resolve_mod_val(
    global_mods: &IdVec<res::ModId, ModMap>,
    mod_id: res::ModId,
    val_name: &raw::ValName,
) -> Result<res::GlobalRef, RawError> {
    let (visibility, id) = *global_mods[mod_id]
        .vals
        .get(val_name)
        .ok_or_else(|| ErrorKind::VarNotFound(val_name.0.clone()))?;
    match visibility {
        Visibility::Public => Ok(id),
        Visibility::Private => Err(ErrorKind::VarNotVisible(val_name.0.clone()).into()),
    }
}

fn resolve_mod_trait(
    global_mods: &IdVec<res::ModId, ModMap>,
    mod_id: res::ModId,
    trait_name: &raw::TraitName,
) -> Result<res::TraitId, RawError> {
    let (visibility, id) = *global_mods[mod_id]
        .traits
        .get(trait_name)
        .ok_or_else(|| ErrorKind::TraitNotFound(trait_name.0.clone()))?;
    match visibility {
        Visibility::Public => Ok(id),
        Visibility::Private => Err(ErrorKind::TraitNotVisible(trait_name.0.clone()).into()),
    }
}

fn resolve_mod_impl(
    global_mods: &IdVec<res::ModId, ModMap>,
    mod_id: res::ModId,
    impl_name: &raw::ImplName,
) -> Result<res::ImplId, RawError> {
    let (visibility, id) = *global_mods[mod_id]
        .impls
        .get(impl_name)
        .ok_or_else(|| ErrorKind::ImplNotFound(impl_name.0.clone()))?;
    match visibility {
        Visibility::Public => Ok(id),
        Visibility::Private => Err(ErrorKind::ImplNotVisible(impl_name.0.clone()).into()),
    }
}

fn resolve_trait_with_path(
    global_mods: &IdVec<res::ModId, ModMap>,
    local_mod_map: &ModMap,
    path: &raw::ModPath,
    name: &raw::TraitName,
) -> Result<res::TraitId, RawError> {
    if path.0.is_empty() {
        // A builtin trait is in scope everywhere, like a builtin type, unless shadowed.
        local_mod_map
            .traits
            .get(name)
            .map(|(_, id)| *id)
            .or_else(|| BuiltinTrait::from_name(&name.0).map(res::TraitId::Builtin))
            .ok_or_else(|| ErrorKind::TraitNotFound(name.0.clone()).into())
    } else {
        resolve_mod_trait(
            global_mods,
            resolve_mod_path(global_mods, &local_mod_map.mods, path)?,
            name,
        )
    }
}

/// Resolves a trait constraint, checking that the trait is given the right number of arguments.
/// Errors are located at the constraint.
fn resolve_trait_app(
    ctx: &GlobalContext,
    local_mod_map: &ModMap,
    param_map: &BTreeMap<raw::TypeParam, res::TypeParamId>,
    constr: &raw::TraitApp,
) -> Result<res::TraitApp, RawError> {
    let resolved = (|| {
        let trait_ =
            resolve_trait_with_path(&ctx.mods, local_mod_map, &constr.path, &constr.trait_name)?;
        let expected = match trait_ {
            res::TraitId::Builtin(_) => BuiltinTrait::num_params().to_value(),
            res::TraitId::Custom(custom) => ctx.trait_arities[custom],
        };
        if constr.args.len() != expected {
            return Err(ErrorKind::TraitArity {
                trait_: constr.trait_name.0.clone(),
                expected,
                actual: constr.args.len(),
            }
            .into());
        }
        let args = constr
            .args
            .iter()
            .map(|arg| resolve_type(&ctx.mods, local_mod_map, param_map, arg))
            .collect::<Result<_, RawError>>()?;
        Ok(res::TraitApp { trait_, args })
    })();
    resolved.map_err(locate_span(constr.span.0, constr.span.1))
}

fn resolve_mod_type(
    global_mods: &IdVec<res::ModId, ModMap>,
    mod_id: res::ModId,
    type_name: &raw::TypeName,
) -> Result<res::TypeId, RawError> {
    let (visibility, id) = *global_mods[mod_id]
        .types
        .get(type_name)
        .ok_or_else(|| ErrorKind::TypeNotFound(type_name.0.clone()))?;
    match visibility {
        Visibility::Public => Ok(id),
        Visibility::Private => Err(ErrorKind::TypeNotVisible(type_name.0.clone()).into()),
    }
}

fn resolve_mod_ctor(
    global_mods: &IdVec<res::ModId, ModMap>,
    mod_id: res::ModId,
    ctor_name: &raw::CtorName,
) -> Result<(res::CustomTypeId, res::VariantId), RawError> {
    let (visibility, custom_id, variant_id) = *global_mods[mod_id]
        .ctors
        .get(ctor_name)
        .ok_or_else(|| ErrorKind::CtorNotFound(ctor_name.0.clone()))?;
    match visibility {
        Visibility::Public => Ok((custom_id, variant_id)),
        Visibility::Private => Err(ErrorKind::CtorNotVisible(ctor_name.0.clone()).into()),
    }
}

fn resolve_exposures(
    global_mods: &IdVec<res::ModId, ModMap>,
    local_mod_map: &mut ModMap,
    exposed_id: res::ModId,
    spec: raw::ExposeSpec,
) -> Result<(), RawError> {
    match spec {
        raw::ExposeSpec::Specific(items) => {
            for item in items {
                match item {
                    raw::ExposeItem::Val(visibility, name) => {
                        let resolved_val = resolve_mod_val(global_mods, exposed_id, &name)?;

                        insert_unique(
                            &mut local_mod_map.vals,
                            name.clone(),
                            (visibility, resolved_val),
                        )
                        .map_err(|()| ErrorKind::DuplicateVarName(name.0))?;
                    }

                    raw::ExposeItem::Type(visibility, name, variants) => {
                        let resolved_type = resolve_mod_type(global_mods, exposed_id, &name)?;

                        insert_unique(
                            &mut local_mod_map.types,
                            name.clone(),
                            (visibility, resolved_type),
                        )
                        .map_err(|()| ErrorKind::DuplicateTypeName(name.0))?;

                        for (ctor_visibility, ctor_name) in variants {
                            let (ctor_type, resolved_ctor) =
                                resolve_mod_ctor(global_mods, exposed_id, &ctor_name)?;

                            if res::TypeId::Custom(ctor_type) != resolved_type {
                                return Err(ErrorKind::CtorNotFound(ctor_name.0).into());
                            }

                            insert_unique(
                                &mut local_mod_map.ctors,
                                ctor_name.clone(),
                                (ctor_visibility, ctor_type, resolved_ctor),
                            )
                            .map_err(|()| ErrorKind::DuplicateCtorName(ctor_name.0))?;
                        }
                    }

                    raw::ExposeItem::Trait(visibility, name, funcs) => {
                        let resolved_trait = resolve_mod_trait(global_mods, exposed_id, &name)?;

                        insert_unique(
                            &mut local_mod_map.traits,
                            name.clone(),
                            (visibility, resolved_trait),
                        )
                        .map_err(|()| ErrorKind::DuplicateTraitName(name.0.clone()))?;

                        for (func_visibility, func_name) in funcs {
                            let resolved_func =
                                resolve_mod_val(global_mods, exposed_id, &func_name)?;

                            match resolved_func {
                                res::GlobalRef::TraitFunc(trait_, _)
                                    if trait_ == resolved_trait => {}
                                _ => {
                                    return Err(ErrorKind::TraitFuncNotFound {
                                        trait_: name.0,
                                        func: func_name.0,
                                    }
                                    .into());
                                }
                            }

                            insert_unique(
                                &mut local_mod_map.vals,
                                func_name.clone(),
                                (func_visibility, resolved_func),
                            )
                            .map_err(|()| ErrorKind::DuplicateVarName(func_name.0))?;
                        }
                    }

                    raw::ExposeItem::Impl(visibility, name) => {
                        let resolved_impl = resolve_mod_impl(global_mods, exposed_id, &name)?;

                        insert_unique(
                            &mut local_mod_map.impls,
                            name.clone(),
                            (visibility, resolved_impl),
                        )
                        .map_err(|()| ErrorKind::DuplicateImplName(name.0))?;
                    }

                    raw::ExposeItem::Mod(visibility, name, sub_expose) => {
                        let resolved_sub_mod = resolve_sub_mod(global_mods, exposed_id, &name)?;

                        insert_unique(
                            &mut local_mod_map.mods,
                            name.clone(),
                            (visibility, resolved_sub_mod),
                        )
                        .map_err(|()| ErrorKind::DuplicateModName(name.0))?;

                        resolve_exposures(
                            global_mods,
                            local_mod_map,
                            resolved_sub_mod,
                            *sub_expose,
                        )?;
                    }
                }
            }
        }
    }

    Ok(())
}

fn resolve_type_with_builtins(
    global_mods: &IdVec<res::ModId, ModMap>,
    local_mod_map: &ModMap,
    path: &raw::ModPath,
    name: &raw::TypeName,
) -> Result<res::TypeId, RawError> {
    if path.0.is_empty() {
        local_mod_map
            .types
            .get(name)
            .map(|(_, id)| id)
            .or_else(|| BUILTIN_TYPES.get(name))
            .cloned()
            .ok_or_else(|| ErrorKind::TypeNotFound(name.0.clone()).into())
    } else {
        global_mods[resolve_mod_path(global_mods, &local_mod_map.mods, path)?]
            .types
            .get(name)
            .ok_or_else(|| ErrorKind::TypeNotFound(name.0.clone()).into())
            .and_then(|(visibility, id)| match visibility {
                Visibility::Public => Ok(*id),
                Visibility::Private => Err(ErrorKind::TypeNotVisible(name.0.clone()).into()),
            })
    }
}

fn resolve_type_param(
    param_map: &BTreeMap<raw::TypeParam, res::TypeParamId>,
    param_name: &raw::TypeParam,
) -> Result<res::TypeParamId, RawError> {
    param_map
        .get(param_name)
        .copied()
        .ok_or_else(|| ErrorKind::TypeParamNotFound(param_name.0.clone()).into())
}

fn resolve_type(
    global_mods: &IdVec<res::ModId, ModMap>,
    local_mod_map: &ModMap,
    param_map: &BTreeMap<raw::TypeParam, res::TypeParamId>,
    type_: &raw::Type,
) -> Result<res::Type, RawError> {
    match type_ {
        raw::Type::Var(param_name) => {
            let id = resolve_type_param(param_map, param_name)?;
            Ok(res::Type::param(id))
        }

        raw::Type::AppVar(param_name, args) => {
            let id = resolve_type_param(param_map, param_name)?;

            let resolved_args = args
                .iter()
                .map(|arg| resolve_type(global_mods, local_mod_map, param_map, arg))
                .collect::<Result<_, _>>()?;

            Ok(res::Type::App(res::TypeHead::Var(id), resolved_args))
        }

        raw::Type::App(path, name, args) => {
            let type_id = resolve_type_with_builtins(global_mods, local_mod_map, path, name)?;

            let resolved_args = args
                .iter()
                .map(|arg| resolve_type(global_mods, local_mod_map, param_map, arg))
                .collect::<Result<_, _>>()?;

            Ok(res::Type::App(res::TypeHead::Ctor(type_id), resolved_args))
        }

        raw::Type::Tuple(items) => Ok(res::Type::Tuple(
            items
                .iter()
                .map(|item| resolve_type(global_mods, local_mod_map, param_map, item))
                .collect::<Result<_, _>>()?,
        )),

        raw::Type::Func(purity, arg, ret) => Ok(res::Type::Func(
            *purity,
            Box::new(resolve_type(global_mods, local_mod_map, param_map, &*arg)?),
            Box::new(resolve_type(global_mods, local_mod_map, param_map, &*ret)?),
        )),

        raw::Type::Span(lo, hi, inner) => {
            resolve_type(global_mods, local_mod_map, param_map, inner)
                .map_err(locate_span(*lo, *hi))
        }
    }
}

fn resolve_ctor_with_builtins(
    global_mods: &IdVec<res::ModId, ModMap>,
    local_mod_map: &ModMap,
    path: &raw::ModPath,
    name: &raw::CtorName,
) -> Result<(res::TypeId, res::VariantId), RawError> {
    if path.0.is_empty() {
        local_mod_map
            .ctors
            .get(name)
            .map(|(_, custom_id, variant_id)| (res::TypeId::Custom(*custom_id), *variant_id))
            .or_else(|| BUILTIN_CTORS.get(name).cloned())
            .ok_or_else(|| ErrorKind::CtorNotFound(name.0.clone()).into())
    } else {
        global_mods[resolve_mod_path(global_mods, &local_mod_map.mods, path)?]
            .ctors
            .get(name)
            .ok_or_else(|| ErrorKind::CtorNotFound(name.0.clone()).into())
            .and_then(|(visibility, custom_id, variant_id)| match visibility {
                Visibility::Public => Ok((res::TypeId::Custom(*custom_id), *variant_id)),
                Visibility::Private => Err(ErrorKind::CtorNotVisible(name.0.clone()).into()),
            })
    }
}

fn args_to_expr(args_lo: usize, args_hi: usize, args: Vec<res::Expr>) -> res::Expr {
    let args_expr = if args.len() == 1 {
        args.into_iter().next().unwrap()
    } else {
        res::Expr::Tuple(args)
    };
    res::Expr::Span(args_lo, args_hi, Box::new(args_expr))
}

// Invariant: always leaves `local_ctx` exactly how it found it!
fn resolve_expr(
    global_mods: &IdVec<res::ModId, ModMap>,
    local_mod_map: &ModMap,
    param_map: &BTreeMap<raw::TypeParam, res::TypeParamId>,
    local_ctx: &mut LocalContext,
    expr: &raw::Expr,
) -> Result<res::Expr, RawError> {
    match expr {
        raw::Expr::Var(name) => {
            if let Some(local_id) = local_ctx.get(name) {
                Ok(res::Expr::Local(local_id))
            } else if let Some(&(_, global_ref)) = local_mod_map.vals.get(name) {
                Ok(res::Expr::Global(global_ref))
            } else if let Some(&global_id) = BUILTIN_GLOBALS.get(name) {
                Ok(res::Expr::Global(res::GlobalRef::Global(global_id)))
            } else if let Some(&global_ref) = BUILTIN_TRAIT_FUNCS.get(name) {
                Ok(res::Expr::Global(global_ref))
            } else {
                Err(ErrorKind::VarNotFound(name.0.clone()).into())
            }
        }

        raw::Expr::QualName(path, name) => {
            let mod_id = resolve_mod_path(global_mods, &local_mod_map.mods, path)?;
            let global_ref = resolve_mod_val(global_mods, mod_id, name)?;
            Ok(res::Expr::Global(global_ref))
        }

        raw::Expr::Ctor(path, name) => {
            let (type_, variant) =
                resolve_ctor_with_builtins(global_mods, local_mod_map, path, name)?;

            Ok(res::Expr::Global(res::GlobalRef::Global(
                res::GlobalId::Ctor(type_, variant),
            )))
        }

        raw::Expr::Tuple(items) => Ok(res::Expr::Tuple(
            items
                .iter()
                .map(|item| resolve_expr(global_mods, local_mod_map, param_map, local_ctx, item))
                .collect::<Result<_, _>>()?,
        )),

        raw::Expr::Lam(purity, pattern, body) => local_ctx.new_scope(|local_ctx| {
            let mut vars = Vec::new();
            let res_pattern =
                resolve_pattern(global_mods, local_mod_map, param_map, pattern, &mut vars)?;
            for var in vars {
                local_ctx.insert(var.clone())?;
            }

            let res_body = resolve_expr(global_mods, local_mod_map, param_map, local_ctx, body)?;
            Ok(res::Expr::Lam(
                *purity,
                res_pattern,
                Box::new(res_body),
                None,
            ))
        }),

        raw::Expr::App(purity, func, (args_lo, args_hi, args)) => {
            let res_func = resolve_expr(global_mods, local_mod_map, param_map, local_ctx, &*func)?;
            let res_arg = args_to_expr(
                *args_lo,
                *args_hi,
                args.iter()
                    .map(|arg| resolve_expr(global_mods, local_mod_map, param_map, local_ctx, arg))
                    .collect::<Result<_, _>>()?,
            );
            Ok(res::Expr::App(
                *purity,
                Box::new(res_func),
                Box::new(res_arg),
            ))
        }

        raw::Expr::OpApp(func, arg) => {
            let res_arg = resolve_expr(global_mods, local_mod_map, param_map, local_ctx, arg)?;
            let func = res::GlobalRef::TraitFunc(res::TraitId::Builtin(func.trait_()), func.id());
            Ok(res::Expr::App(
                Purity::Pure,
                Box::new(res::Expr::Global(func)),
                Box::new(res_arg),
            ))
        }

        raw::Expr::Match(discrim, cases) => {
            let res_discrim =
                resolve_expr(global_mods, local_mod_map, param_map, local_ctx, discrim)?;

            let res_cases = cases
                .iter()
                .map(|(pattern, body)| {
                    local_ctx.new_scope(|local_ctx| {
                        let mut vars = Vec::new();
                        let res_pattern = resolve_pattern(
                            global_mods,
                            local_mod_map,
                            param_map,
                            pattern,
                            &mut vars,
                        )?;
                        for var in vars {
                            local_ctx.insert(var.clone())?;
                        }

                        let res_body =
                            resolve_expr(global_mods, local_mod_map, param_map, local_ctx, body)?;
                        Ok((res_pattern, res_body))
                    })
                })
                .collect::<Result<_, RawError>>()?;

            Ok(res::Expr::Match(Box::new(res_discrim), res_cases))
        }

        raw::Expr::LetMany(bindings, body) => local_ctx.new_scope(|local_ctx| {
            let mut vars = Vec::new();
            let mut new_bindings = Vec::new();

            for (pattern, expr) in bindings {
                let res_expr =
                    resolve_expr(global_mods, local_mod_map, param_map, local_ctx, expr)?;

                let mut current_vars = Vec::new();
                let res_pattern = resolve_pattern(
                    global_mods,
                    local_mod_map,
                    param_map,
                    pattern,
                    &mut current_vars,
                )?;
                vars.extend(current_vars.clone());

                for var in &current_vars {
                    local_ctx.insert(var.clone())?;
                }
                new_bindings.push((res_pattern, res_expr));
            }

            let res_body = resolve_expr(global_mods, local_mod_map, param_map, local_ctx, &*body)?;

            Ok(res::Expr::LetMany(new_bindings, Box::new(res_body)))
        }),

        raw::Expr::And(left, right) => {
            let res_left = resolve_expr(global_mods, local_mod_map, param_map, local_ctx, left)?;
            let res_right = resolve_expr(global_mods, local_mod_map, param_map, local_ctx, right)?;

            let false_pattern = res::Pattern::Ctor(res::TypeId::Bool, res::VariantId(0), None);
            let false_expr = res::Expr::Global(res::GlobalRef::Global(res::GlobalId::Ctor(
                res::TypeId::Bool,
                res::VariantId(0),
            )));
            let true_pattern = res::Pattern::Ctor(res::TypeId::Bool, res::VariantId(1), None);

            Ok(res::Expr::Match(
                Box::new(res_left),
                vec![(false_pattern, false_expr), (true_pattern, res_right)],
            ))
        }

        raw::Expr::Or(left, right) => {
            let res_left = resolve_expr(global_mods, local_mod_map, param_map, local_ctx, left)?;
            let res_right = resolve_expr(global_mods, local_mod_map, param_map, local_ctx, right)?;

            let true_pattern = res::Pattern::Ctor(res::TypeId::Bool, res::VariantId(1), None);
            let true_expr = res::Expr::Global(res::GlobalRef::Global(res::GlobalId::Ctor(
                res::TypeId::Bool,
                res::VariantId(1),
            )));
            let false_pattern = res::Pattern::Ctor(res::TypeId::Bool, res::VariantId(0), None);

            Ok(res::Expr::Match(
                Box::new(res_left),
                vec![(true_pattern, true_expr), (false_pattern, res_right)],
            ))
        }

        raw::Expr::PipeLeft(left, right) => {
            // `f(a) <| b` gets converted to `f(a, b)`

            let (app, respan_app) = unspan(&**left);
            match app {
                raw::Expr::App(purity, func, (args_lo, args_hi, args)) => {
                    let res_func =
                        resolve_expr(global_mods, local_mod_map, param_map, local_ctx, func)?;
                    let res_arg = args_to_expr(
                        *args_lo,
                        *args_hi,
                        args.iter()
                            .chain(iter::once(&**right))
                            .map(|arg| {
                                resolve_expr(global_mods, local_mod_map, param_map, local_ctx, arg)
                            })
                            .collect::<Result<_, _>>()?,
                    );
                    Ok(respan_app(res::Expr::App(
                        *purity,
                        Box::new(res_func),
                        Box::new(res_arg),
                    )))
                }
                _ => Err(ErrorKind::PipeNotAppLeft.into()),
            }
        }

        raw::Expr::PipeRight(left, right) => {
            // `a |> f(b)` gets converted to `let tmp = a in f(tmp, b)`

            let (app, respan_app) = unspan(&**right);
            match app {
                raw::Expr::App(purity, func, (args_lo, args_hi, args)) => {
                    local_ctx.new_scope(|local_ctx| {
                        let (left_unspanned, respan_left) = unspan(&**left);
                        let res_left = resolve_expr(
                            global_mods,
                            local_mod_map,
                            param_map,
                            local_ctx,
                            left_unspanned,
                        )?;

                        let anon_var = res::Expr::Local(local_ctx.insert_anon());
                        let binding = vec![(res::Pattern::Var, respan_left(res_left))];

                        let res_func =
                            resolve_expr(global_mods, local_mod_map, param_map, local_ctx, func)?;

                        let mut res_args = vec![respan_left(anon_var)];
                        for arg in args {
                            res_args.push(resolve_expr(
                                global_mods,
                                local_mod_map,
                                param_map,
                                local_ctx,
                                arg,
                            )?);
                        }

                        let res_app_arg = args_to_expr(*args_lo, *args_hi, res_args);

                        Ok(res::Expr::LetMany(
                            binding,
                            Box::new(respan_app(res::Expr::App(
                                *purity,
                                Box::new(res_func),
                                Box::new(res_app_arg),
                            ))),
                        ))
                    })
                }
                _ => Err(ErrorKind::PipeNotAppRight.into()),
            }
        }

        raw::Expr::ArrayLit(items) => Ok(res::Expr::ArrayLit(
            items
                .iter()
                .map(|item| resolve_expr(global_mods, local_mod_map, param_map, local_ctx, item))
                .collect::<Result<_, _>>()?,
        )),

        &raw::Expr::ByteLit(val) => Ok(res::Expr::ByteLit(val)),

        &raw::Expr::IntLit(val) => Ok(res::Expr::IntLit(val)),

        &raw::Expr::FloatLit(val) => Ok(res::Expr::FloatLit(val)),

        raw::Expr::TextLit(text) => Ok(res::Expr::ArrayLit(
            text.clone()
                .into_bytes()
                .iter()
                .map(|byte| res::Expr::ByteLit(*byte))
                .collect(),
        )),

        raw::Expr::Span(lo, hi, body) => Ok(res::Expr::Span(
            *lo,
            *hi,
            Box::new(
                resolve_expr(global_mods, local_mod_map, param_map, local_ctx, body)
                    .map_err(locate_span(*lo, *hi))?,
            ),
        )),
    }
}

fn resolve_pattern(
    global_mods: &IdVec<res::ModId, ModMap>,
    local_mod_map: &ModMap,
    param_map: &BTreeMap<raw::TypeParam, res::TypeParamId>,
    pattern: &raw::Pattern,
    vars: &mut Vec<raw::ValName>,
) -> Result<res::Pattern, RawError> {
    match pattern {
        raw::Pattern::Any => Ok(res::Pattern::Any),

        raw::Pattern::Var(name) => {
            vars.push(name.clone());
            Ok(res::Pattern::Var)
        }

        raw::Pattern::Tuple(items) => Ok(res::Pattern::Tuple(
            items
                .iter()
                .map(|item| resolve_pattern(global_mods, local_mod_map, param_map, item, vars))
                .collect::<Result<_, _>>()?,
        )),

        raw::Pattern::Ctor(path, ctor_name, content) => {
            let (type_, variant) =
                resolve_ctor_with_builtins(global_mods, local_mod_map, path, ctor_name)?;

            let res_content = if let Some(content) = content {
                Some(Box::new(resolve_pattern(
                    global_mods,
                    local_mod_map,
                    param_map,
                    content,
                    vars,
                )?))
            } else {
                None
            };

            Ok(res::Pattern::Ctor(type_, variant, res_content))
        }

        raw::Pattern::Annot(content, type_) => Ok(res::Pattern::Annot(
            Box::new(resolve_pattern(
                global_mods,
                local_mod_map,
                param_map,
                content,
                vars,
            )?),
            resolve_type(global_mods, local_mod_map, param_map, type_)?,
        )),

        &raw::Pattern::ByteConst(val) => Ok(res::Pattern::ByteConst(val)),

        &raw::Pattern::IntConst(val) => Ok(res::Pattern::IntConst(val)),

        &raw::Pattern::FloatConst(val) => Ok(res::Pattern::FloatConst(val)),

        raw::Pattern::Span(lo, hi, content) => Ok(res::Pattern::Span(
            *lo,
            *hi,
            Box::new(
                resolve_pattern(global_mods, local_mod_map, param_map, content, vars)
                    .map_err(locate_span(*lo, *hi))?,
            ),
        )),
    }
}

fn find_scheme_params(
    scheme: &raw::Type,
    param_names: &mut IdVec<res::TypeParamId, raw::TypeParam>,
    params: &mut BTreeMap<raw::TypeParam, res::TypeParamId>,
) {
    match scheme {
        raw::Type::Var(param) => {
            debug_assert_eq!(param_names.len(), params.len());
            if let Entry::Vacant(entry) = params.entry(param.clone()) {
                let id = param_names.push(param.clone());
                entry.insert(id);
            }
        }

        raw::Type::AppVar(param, args) => {
            find_scheme_params(&raw::Type::Var(param.clone()), param_names, params);
            for arg in args {
                find_scheme_params(arg, param_names, params);
            }
        }

        raw::Type::App(_, _, args) => {
            for arg in args {
                find_scheme_params(arg, param_names, params);
            }
        }

        raw::Type::Tuple(items) => {
            for item in items {
                find_scheme_params(item, param_names, params);
            }
        }

        raw::Type::Func(_, arg, ret) => {
            find_scheme_params(&*arg, param_names, params);
            find_scheme_params(&*ret, param_names, params);
        }

        raw::Type::Span(_, _, inner) => find_scheme_params(inner, param_names, params),
    }
}

fn resolve_scheme(
    ctx: &GlobalContext,
    local_mod_map: &ModMap,
    scheme: &raw::Type,
    constrs: &[raw::TraitApp],
) -> Result<
    (
        res::TypeScheme,
        IdVec<res::TypeParamId, raw::TypeParam>,
        BTreeMap<raw::TypeParam, res::TypeParamId>,
    ),
    RawError,
> {
    let mut scheme_param_names = IdVec::new();
    let mut scheme_params = BTreeMap::new();
    find_scheme_params(scheme, &mut scheme_param_names, &mut scheme_params);
    for constr in constrs {
        for arg in &constr.args {
            find_scheme_params(arg, &mut scheme_param_names, &mut scheme_params);
        }
    }

    let res_type = resolve_type(&ctx.mods, local_mod_map, &scheme_params, scheme)?;

    let trait_constrs = IdVec::from_vec(
        constrs
            .iter()
            .map(|constr| resolve_trait_app(ctx, local_mod_map, &scheme_params, constr))
            .collect::<Result<_, RawError>>()?,
    );

    let scheme = res::TypeScheme {
        num_params: scheme_param_names.count(),
        trait_constrs,
        body: res_type,
    };

    Ok((scheme, scheme_param_names, scheme_params))
}

fn resolve_trait_def(
    ctx: &mut GlobalContext,
    mod_map: &ModMap,
    self_mod_id: res::ModId,
    file_path: &Path,
    trait_id: res::CustomTraitId,
    name: raw::TraitName,
    params: Vec<raw::TypeParam>,
    supers: Vec<raw::TraitApp>,
    funcs: Vec<raw::TraitFunc>,
) -> Result<(), RawError> {
    let mut param_names = IdVec::new();
    let mut param_map = BTreeMap::new();
    for param_name in params {
        let id = param_names.push(param_name.clone());
        insert_unique(&mut param_map, param_name.clone(), id)
            .map_err(|()| ErrorKind::DuplicateTypeName(param_name.0).into())
            .map_err(locate_path(file_path))?;
    }

    let res_supers = supers
        .iter()
        .map(|constr| resolve_trait_app(ctx, mod_map, &param_map, constr))
        .collect::<Result<Vec<_>, RawError>>()
        .map_err(locate_path(file_path))?;

    let mut res_funcs = IdVec::new();
    let mut func_symbols = IdVec::new();
    for func in &funcs {
        // Scanning the func's signature with the trait's parameters already in place numbers the
        // func's own parameters after them, which is the numbering `TraitFuncLayout` describes.
        let mut func_param_names = param_names.clone();
        let mut func_param_map = param_map.clone();
        find_scheme_params(&func.type_, &mut func_param_names, &mut func_param_map);
        for constr in &func.trait_constrs {
            for arg in &constr.args {
                find_scheme_params(arg, &mut func_param_names, &mut func_param_map);
            }
        }

        let body = resolve_type(&ctx.mods, mod_map, &func_param_map, &func.type_)
            .map_err(locate_span(func.span.0, func.span.1))
            .map_err(locate_path(file_path))?;

        let own_constrs = IdVec::from_vec(
            func.trait_constrs
                .iter()
                .map(|constr| resolve_trait_app(ctx, mod_map, &func_param_map, constr))
                .collect::<Result<Vec<_>, RawError>>()
                .map_err(locate_path(file_path))?,
        );

        let _ = res_funcs.push(res::TraitFuncSig {
            num_own_params: Count::from_value(func_param_names.len() - param_names.len()),
            own_constrs,
            body,
        });
        let _ = func_symbols.push(res::TraitFuncSymbols {
            func_name: func.name.clone(),
            span: func.span,
            type_param_names: func_param_names,
            type_spans: res::TypeSpans::of(&func.type_),
            constr_spans: IdVec::from_vec(
                func.trait_constrs
                    .iter()
                    .map(|constr| constr.span)
                    .collect(),
            ),
        });
    }

    debug_assert!(ctx.traits[trait_id].is_none());
    ctx.traits[trait_id] = Some(res::TraitDef {
        num_params: param_names.count(),
        supers: IdVec::from_vec(res_supers),
        funcs: res_funcs,
    });

    debug_assert!(ctx.trait_symbols[trait_id].is_none());
    ctx.trait_symbols[trait_id] = Some(res::TraitSymbols {
        mod_: self_mod_id,
        trait_name: name,
        type_param_names: param_names,
        super_spans: IdVec::from_vec(supers.iter().map(|constr| constr.span).collect()),
        func_symbols,
    });

    Ok(())
}

fn resolve_impl_def(
    ctx: &mut GlobalContext,
    mod_map: &ModMap,
    self_mod_id: res::ModId,
    file_path: &Path,
    impl_id: res::CustomImplId,
    name: raw::ImplName,
    head: raw::TraitApp,
    constrs: Vec<raw::TraitApp>,
    funcs: Vec<raw::ImplFunc>,
) -> Result<(), RawError> {
    // The impl's parameters are whatever its head and constraints mention.
    let mut param_names = IdVec::new();
    let mut param_map = BTreeMap::new();
    for arg in &head.args {
        find_scheme_params(arg, &mut param_names, &mut param_map);
    }
    for constr in &constrs {
        for arg in &constr.args {
            find_scheme_params(arg, &mut param_names, &mut param_map);
        }
    }
    let num_impl_params = param_names.count();

    let res_head =
        resolve_trait_app(ctx, mod_map, &param_map, &head).map_err(locate_path(file_path))?;

    let res_constrs: IdVec<res::TraitConstrId, _> = IdVec::from_vec(
        constrs
            .iter()
            .map(|constr| resolve_trait_app(ctx, mod_map, &param_map, constr))
            .collect::<Result<Vec<_>, RawError>>()
            .map_err(locate_path(file_path))?,
    );
    let constr_spans: IdVec<res::TraitConstrId, _> =
        IdVec::from_vec(constrs.iter().map(|constr| constr.span).collect());

    // The trait's definition, and the name and parameter names of each of its funcs.  Traits are
    // resolved before impls, in this module and in every module it imports.
    let (trait_def, func_names, func_param_names) = match res_head.trait_ {
        res::TraitId::Custom(custom_trait) => {
            let def = ctx.traits[custom_trait]
                .clone()
                .expect("traits are resolved before impls");
            let symbols = ctx.trait_symbols[custom_trait]
                .as_ref()
                .expect("traits are resolved before impls");
            (
                def,
                symbols
                    .func_symbols
                    .map_refs(|_, func| func.func_name.clone()),
                symbols
                    .func_symbols
                    .map_refs(|_, func| func.type_param_names.clone()),
            )
        }
        res::TraitId::Builtin(builtin) => {
            let def = builtin.res_def();
            let names = IdVec::from_vec(
                builtin
                    .funcs()
                    .iter()
                    .map(|func| raw::ValName(func.name().to_owned()))
                    .collect(),
            );
            let params = def
                .funcs
                .map_refs(|_, _| IdVec::from_vec(vec![raw::TypeParam("a".to_owned())]));
            (def, names, params)
        }
    };

    let mut provided: BTreeMap<raw::ValName, &raw::ImplFunc> = BTreeMap::new();
    for func in &funcs {
        if provided.insert(func.name.clone(), func).is_some() {
            return Err(locate_path(file_path)(locate_span(
                func.span.0,
                func.span.1,
            )(
                ErrorKind::DuplicateVarName(func.name.0.clone()).into(),
            )));
        }
    }

    let layout = res::ImplFuncLayout {
        num_impl_params,
        num_impl_constrs: res_constrs.count(),
    };

    let mut res_funcs = IdVec::new();
    for (func_id, trait_sig) in &trait_def.funcs {
        let func_name = &func_names[func_id];

        let func = provided.remove(func_name).ok_or_else(|| {
            locate_path(file_path)(locate_span(head.span.0, head.span.1)(
                ErrorKind::ImplMissingFunc {
                    impl_: name.0.clone(),
                    func: func_name.0.clone(),
                }
                .into(),
            ))
        })?;

        let trait_layout = trait_def.func_layout(func_id);
        let (expected, expected_locals) = expected_impl_func_scheme(
            layout,
            trait_layout,
            trait_sig,
            &res_head.args,
            &res_constrs,
        );

        // The declared header is resolved with the impl's parameters fixed, so that anything else
        // it mentions is one of the func's own parameters.
        let mut declared_names = param_names.clone();
        let mut declared_map = param_map.clone();
        find_scheme_params(&func.type_, &mut declared_names, &mut declared_map);
        for constr in &func.trait_constrs {
            for arg in &constr.args {
                find_scheme_params(arg, &mut declared_names, &mut declared_map);
            }
        }
        let declared = resolve_type(&ctx.mods, mod_map, &declared_map, &func.type_)
            .map_err(locate_span(func.span.0, func.span.1))
            .map_err(locate_path(file_path))?;
        let declared_constrs = func
            .trait_constrs
            .iter()
            .map(|constr| resolve_trait_app(ctx, mod_map, &declared_map, constr))
            .collect::<Result<Vec<_>, RawError>>()
            .map_err(locate_path(file_path))?;

        let (mapping, constr_order) = alpha_map(&expected.body, &declared, num_impl_params)
            .filter(|mapping| mapping.len() == trait_layout.num_own_params.to_value())
            .and_then(|mapping| {
                let renamed: Vec<_> = declared_constrs
                    .iter()
                    .map(|constr| {
                        rename_params(constr, &mapping, num_impl_params, declared_names.count())
                    })
                    .collect();
                match_constrs(&expected_locals, &renamed).map(|order| (mapping, order))
            })
            .ok_or_else(|| {
                let renderer = report_type::TypeRenderer::new(&ctx.mod_symbols, &ctx.type_symbols);
                let expected_names = expected_impl_func_param_names(
                    layout,
                    &param_names,
                    trait_layout,
                    &func_param_names[func_id],
                );
                let trait_symbols = ctx.trait_symbols.map_refs(|_, symbols| {
                    symbols.clone().expect("traits are resolved before impls")
                });
                locate_path(file_path)(locate_span(func.span.0, func.span.1)(
                    ErrorKind::ImplFuncMismatch {
                        impl_: name.0.clone(),
                        func: func_name.0.clone(),
                        expected: render_signature(
                            &renderer,
                            &expected_names,
                            &expected.body,
                            expected_locals.as_slice(),
                            &trait_symbols,
                        ),
                        actual: render_signature(
                            &renderer,
                            &declared_names,
                            &declared,
                            &declared_constrs,
                            &trait_symbols,
                        ),
                    }
                    .into(),
                ))
            })?;

        // The body is resolved against the expected numbering, so that the definition's parameters
        // are the impl's followed by the trait func's own, in the trait's order.
        let mut body_param_map = BTreeMap::new();
        let mut type_param_names =
            IdVec::from_count_with(expected.num_params, |_| raw::TypeParam(String::new()));
        for (declared_id, param_name) in &declared_names {
            let expected_id = if num_impl_params.contains(declared_id) {
                declared_id
            } else {
                mapping[&declared_id]
            };
            body_param_map.insert(param_name.clone(), expected_id);
            type_param_names[expected_id] = param_name.clone();
        }

        let body = resolve_expr(
            &ctx.mods,
            mod_map,
            &body_param_map,
            &mut LocalContext::new(),
            &func.body,
        )
        .map_err(locate_path(file_path))?;

        let val_id = ctx.vals.push(Some(res::ValDef {
            scheme: expected,
            body,
        }));
        // Constraint spans follow the expected scheme's layout, with the func's own in the
        // trait's order.
        let trait_constr_spans = layout.constrs(
            constr_spans.clone(),
            constr_order.map_refs(|_, &declared_index| func.trait_constrs[declared_index].span),
        );

        let val_symbols_id = ctx.val_symbols.push(Some(res::ValSymbols {
            mod_: self_mod_id,
            type_param_names,
            val_name: func_name.clone(),
            span: func.span,
            type_spans: res::TypeSpans::of(&func.type_),
            trait_constr_spans,
            impl_: Some(impl_id),
        }));
        debug_assert_eq!(val_id, val_symbols_id);

        let _ = res_funcs.push(val_id);
    }

    if let Some((extra_name, extra)) = provided.into_iter().next() {
        return Err(locate_path(file_path)(locate_span(
            extra.span.0,
            extra.span.1,
        )(
            ErrorKind::ImplExtraFunc {
                impl_: name.0.clone(),
                func: extra_name.0,
            }
            .into(),
        )));
    }

    debug_assert!(ctx.impls[impl_id].is_none());
    ctx.impls[impl_id] = Some(res::ImplDef {
        trait_: res_head.trait_,
        num_params: num_impl_params,
        head: res_head.args,
        trait_constrs: res_constrs,
        funcs: res_funcs,
    });

    debug_assert!(ctx.impl_symbols[impl_id].is_none());
    ctx.impl_symbols[impl_id] = Some(res::ImplSymbols {
        mod_: self_mod_id,
        impl_name: name,
        type_param_names: param_names,
        head_span: head.span,
        constr_spans,
    });

    Ok(())
}

/// The scheme an impl func must have, and separately the constraints the func itself must
/// declare: the trait func's signature with the impl head substituted for the trait's
/// parameters, laid out as `ImplFuncLayout` describes.  The impl's constraints are not repeated
/// on the func, and the trait's own constraint needs no counterpart, since the impl is what
/// discharges it.
fn expected_impl_func_scheme(
    layout: res::ImplFuncLayout,
    trait_layout: res::TraitFuncLayout,
    trait_sig: &res::TraitFuncSig,
    head: &[res::Type],
    impl_constrs: &IdVec<res::TraitConstrId, res::TraitApp>,
) -> (
    res::TypeScheme,
    IdVec<res::TraitFuncConstrId, res::TraitApp>,
) {
    // From the signature's numbering to the impl func's: the head stands for the trait's
    // parameters, and the impl func's own parameters for the func's own.
    let subst = trait_layout.params(
        IdVec::from_vec(head.to_vec()),
        IdVec::from_count_with(trait_layout.num_own_params, |param| {
            res::Type::param(layout.own_param(param))
        }),
    );

    let own_constrs = trait_sig
        .own_constrs
        .map_refs(|_, constr| constr.subst(&subst));

    let scheme = res::TypeScheme {
        num_params: layout.num_params(trait_layout.num_own_params),
        trait_constrs: layout.constrs(impl_constrs.clone(), own_constrs.clone()),
        body: res::subst_type(&subst, &trait_sig.body),
    };
    (scheme, own_constrs)
}

/// Parameter names for rendering an expected impl func scheme: the impl's, then the trait func's
/// own as the trait declared them.
fn expected_impl_func_param_names(
    layout: res::ImplFuncLayout,
    impl_param_names: &IdVec<res::TypeParamId, raw::TypeParam>,
    trait_layout: res::TraitFuncLayout,
    trait_func_param_names: &IdVec<res::TypeParamId, raw::TypeParam>,
) -> IdVec<res::TypeParamId, raw::TypeParam> {
    layout.params(
        impl_param_names.clone(),
        IdVec::from_count_with(trait_layout.num_own_params, |param| {
            trait_func_param_names[trait_layout.own_param(param)].clone()
        }),
    )
}

/// Renders a signature as it would be written: the type, then its constraints if any.
fn render_signature(
    renderer: &report_type::TypeRenderer,
    params: &IdVec<res::TypeParamId, raw::TypeParam>,
    type_: &res::Type,
    constrs: &[res::TraitApp],
    trait_symbols: &IdVec<res::CustomTraitId, res::TraitSymbols>,
) -> String {
    let mut result = renderer.render(params, &report_type::Type::from_resolved(type_));
    let rendered: Vec<_> = constrs
        .iter()
        .map(|constr| {
            renderer.render_trait_app(
                params,
                &report_type::TraitApp::from_resolved(constr),
                trait_symbols,
            )
        })
        .collect();
    match rendered.len() {
        0 => {}
        1 => result.push_str(&format!(" where {}", rendered[0])),
        _ => result.push_str(&format!(" where ({})", rendered.join(", "))),
    }
    result
}

/// Renames the func-local parameters of a declared constraint into the expected numbering.
fn rename_params(
    constr: &res::TraitApp,
    mapping: &BTreeMap<res::TypeParamId, res::TypeParamId>,
    fixed: Count<res::TypeParamId>,
    num_declared_params: Count<res::TypeParamId>,
) -> res::TraitApp {
    let subst = IdVec::from_count_with(num_declared_params, |id| {
        if fixed.contains(id) {
            res::Type::param(id)
        } else {
            res::Type::param(mapping[&id])
        }
    });
    constr.subst(&subst)
}

/// Matches the declared constraints of an impl func against the expected ones regardless of
/// order, returning for each expected constraint the position of the declared one it matches.
fn match_constrs(
    expected: &IdVec<res::TraitFuncConstrId, res::TraitApp>,
    declared: &[res::TraitApp],
) -> Option<IdVec<res::TraitFuncConstrId, usize>> {
    if expected.len() != declared.len() {
        return None;
    }
    let mut used = vec![false; declared.len()];
    expected
        .try_map_refs(|_, constr| -> Result<usize, ()> {
            let index = declared
                .iter()
                .enumerate()
                .position(|(index, candidate)| !used[index] && candidate == constr)
                .ok_or(())?;
            used[index] = true;
            Ok(index)
        })
        .ok()
}

/// Finds the bijection between the func-local type parameters of a declared impl func type and
/// those of the expected type, treating the first `fixed` parameters (the impl's own) as identical
/// on both sides.  Returns `None` if the two types are not alpha-equivalent.
fn alpha_map(
    expected: &res::Type,
    declared: &res::Type,
    fixed: Count<res::TypeParamId>,
) -> Option<BTreeMap<res::TypeParamId, res::TypeParamId>> {
    let mut forward = BTreeMap::new();
    let mut backward = BTreeMap::new();
    if alpha_rec(expected, declared, fixed, &mut forward, &mut backward) {
        Some(forward)
    } else {
        None
    }
}

fn alpha_rec(
    expected: &res::Type,
    declared: &res::Type,
    fixed: Count<res::TypeParamId>,
    forward: &mut BTreeMap<res::TypeParamId, res::TypeParamId>,
    backward: &mut BTreeMap<res::TypeParamId, res::TypeParamId>,
) -> bool {
    match (expected, declared) {
        (
            res::Type::App(expected_head, expected_args),
            res::Type::App(declared_head, declared_args),
        ) => {
            let heads_match = match (expected_head, declared_head) {
                (res::TypeHead::Ctor(expected_id), res::TypeHead::Ctor(declared_id)) => {
                    expected_id == declared_id
                }
                (res::TypeHead::Var(expected_id), res::TypeHead::Var(declared_id)) => {
                    if fixed.contains(expected_id) || fixed.contains(declared_id) {
                        expected_id == declared_id
                    } else {
                        match (forward.get(declared_id), backward.get(expected_id)) {
                            (None, None) => {
                                forward.insert(*declared_id, *expected_id);
                                backward.insert(*expected_id, *declared_id);
                                true
                            }
                            (Some(mapped_expected), Some(mapped_declared)) => {
                                mapped_expected == expected_id && mapped_declared == declared_id
                            }
                            _ => false,
                        }
                    }
                }
                _ => false,
            };
            heads_match
                && expected_args.len() == declared_args.len()
                && expected_args
                    .iter()
                    .zip(declared_args)
                    .all(|(e, d)| alpha_rec(e, d, fixed, forward, backward))
        }
        (res::Type::Tuple(expected_items), res::Type::Tuple(declared_items)) => {
            expected_items.len() == declared_items.len()
                && expected_items
                    .iter()
                    .zip(declared_items)
                    .all(|(e, d)| alpha_rec(e, d, fixed, forward, backward))
        }
        (
            res::Type::Func(expected_purity, expected_arg, expected_ret),
            res::Type::Func(declared_purity, declared_arg, declared_ret),
        ) => {
            expected_purity == declared_purity
                && alpha_rec(expected_arg, declared_arg, fixed, forward, backward)
                && alpha_rec(expected_ret, declared_ret, fixed, forward, backward)
        }
        _ => false,
    }
}

fn resolve_profile_points(
    mod_symbols: &IdVec<res::ModId, res::ModSymbols>, // For error reporting only
    val_symbols: &IdVec<res::CustomGlobalId, res::ValSymbols>, // For error reporting only
    global_mods: &IdVec<res::ModId, ModMap>,
    main_mod: res::ModId,
    vals: &mut IdVec<res::CustomGlobalId, res::ValDef>,
    profile_syms: &[cfg::SymbolName],
    record_rc: bool,
) -> Result<IdVec<prof::ProfilePointId, prof::ProfilePoint>, RawError> {
    let mut profile_points = IdVec::new();

    for sym_name in profile_syms {
        let (path, val_name) = parse::QualNameParser::new()
            .parse(lex::Lexer::new(&sym_name.0))
            .map_err(|_| ErrorKind::ParseProfileSymFailed(sym_name.clone()))?;

        // We don't use `resolve_mod_path` here because we want to ignore visibility restrictions.
        let mut sym_mod_id = main_mod;
        for mod_name in &path.0 {
            sym_mod_id = global_mods[sym_mod_id]
                .mods
                .get(mod_name)
                .map(|(_visibility, sub_mod_id)| *sub_mod_id)
                .ok_or_else(|| ErrorKind::ResolveProfileSymFailed(sym_name.clone()))?;
        }

        // We don't use `resolve_mod_val` here because we want to ignore visibility restrictions.
        let sym_val_id = global_mods[sym_mod_id]
            .vals
            .get(&val_name)
            .and_then(|(_visibility, global_id)| match global_id {
                &res::GlobalRef::Global(res::GlobalId::Custom(custom)) => Some(custom),
                _ => None,
            })
            .ok_or_else(|| ErrorKind::ResolveProfileSymFailed(sym_name.clone()))?;

        annotate_profile_point(
            &mut profile_points,
            &mut vals[sym_val_id].body,
            path,
            val_name,
            record_rc,
        )
        .map_err(locate_path(&mod_symbols[val_symbols[sym_val_id].mod_].file))?;
    }

    Ok(profile_points)
}

fn annotate_profile_point(
    profile_points: &mut IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    body: &mut res::Expr,
    path: raw::ModPath,
    val_name: raw::ValName,
    record_rc: bool,
) -> Result<(), RawError> {
    match body {
        res::Expr::Span(lo, hi, content) => {
            annotate_profile_point(profile_points, content, path, val_name, record_rc)
                .map_err(locate_span(*lo, *hi))
        }

        res::Expr::Lam(_, _, _, opt_prof_id) => {
            let prof_id = opt_prof_id.get_or_insert_with(|| {
                profile_points.push(prof::ProfilePoint {
                    reporting_names: BTreeSet::new(),
                    record_rc,
                })
            });

            profile_points[prof_id]
                .reporting_names
                .insert((path, val_name));

            Ok(())
        }

        _ => Err(ErrorKind::ProfileSymNotFunction.into()),
    }
}

fn insert_unique<K: Ord, V>(map: &mut BTreeMap<K, V>, key: K, value: V) -> Result<(), ()> {
    let existing = map.insert(key, value);

    if existing.is_some() {
        Err(())
    } else {
        Ok(())
    }
}

fn sibling_path_from(self_path: &Path, components: Vec<String>) -> Result<PathBuf, RawError> {
    // Validate path
    for component in &components {
        // This check also ensures we reject empty components.
        if component.chars().all(|c| c == '.') {
            return Err(Locate {
                error: ErrorKind::IllegalFilePath(components.join("/")),
                span: None,
                path: Some(self_path.to_owned()),
            });
        }
    }

    let mut result = self_path
        .parent()
        .expect("Any file we are able to read should have a parent")
        .to_owned();
    result.extend(components);

    Ok(result)
}

fn unspan<'a>(expr: &'a raw::Expr) -> (&'a raw::Expr, Box<dyn Fn(res::Expr) -> res::Expr>) {
    if let raw::Expr::Span(lo, hi, inner_expr) = expr {
        let lo = *lo;
        let hi = *hi;
        (
            inner_expr,
            Box::new(move |x| res::Expr::Span(lo, hi, Box::new(x))),
        )
    } else {
        (expr, Box::new(|x| x))
    }
}
