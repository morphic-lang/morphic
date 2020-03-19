use lalrpop_util::ParseError;
use lazy_static::lazy_static;
use std::collections::BTreeMap;
use std::io;
use std::path::{Path, PathBuf};

use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;
use crate::file_cache::FileCache;
use crate::lex;
use crate::parse;
use crate::parse_error;
use crate::report_error::{report_error, Report};
use crate::util::id_vec::IdVec;

#[derive(Debug)]
pub enum ErrorKind {
    ReadFailed(PathBuf, io::Error),
    ParseFailed(ParseError<usize, lex::Token, lex::Error>),
    IllegalFilePath(String),
    DuplicateModName(String),
    DuplicateTypeName(String),
    DuplicateCtorName(String),
    DuplicateVarName(String),
    TypeNotFound(String),
    VarNotFound(String),
    CtorNotFound(String),
    ModNotFound(String),
    MainNotFound,
}

#[derive(Debug)]
pub struct Error {
    pub file: Option<PathBuf>,
    pub span: Option<(usize, usize)>,
    pub kind: ErrorKind,
}

impl From<ErrorKind> for Error {
    fn from(kind: ErrorKind) -> Error {
        Error {
            file: None,
            span: None,
            kind,
        }
    }
}

impl Error {
    pub fn report(&self, dest: &mut impl io::Write, files: &FileCache) -> io::Result<()> {
        use ErrorKind::*;

        let path = self.file.as_ref().map(|path| path.as_ref());

        match &self.kind {
            ReadFailed(path, err) if err.kind() != io::ErrorKind::NotFound => {
                writeln!(dest, "Could not read {}: {}", path.display(), err)?;
                return Ok(());
            }
            ParseFailed(err) => {
                parse_error::report(dest, files, path, err)?;
                return Ok(());
            }
            _ => {}
        }

        let (title, message) = match &self.kind {
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
            MainNotFound => (
                "Main Not Found",
                format!(
                    "Your program does not have a 'main' function declared in its root module."
                ),
            ),
        };

        report_error(
            dest,
            files,
            Report {
                path,
                span: self.span, // TODO: Add spans!
                title,
                message: Some(&message),
            },
        )?;

        Ok(())
    }
}

fn locate<'a>(file: &'a Path) -> impl FnOnce(Error) -> Error + 'a {
    move |err| Error {
        file: Some(file.to_owned()),
        ..err
    }
}

fn locate_span(lo: usize, hi: usize) -> impl FnOnce(Error) -> Error {
    move |err| Error {
        span: Some(err.span.unwrap_or((lo, hi))),
        ..err
    }
}

lazy_static! {
    static ref BUILTIN_TYPES: BTreeMap<raw::TypeName, res::TypeId> = {
        let mut type_map = BTreeMap::new();

        type_map.insert(raw::TypeName("Bool".to_owned()), res::TypeId::Bool);
        type_map.insert(raw::TypeName("Byte".to_owned()), res::TypeId::Byte);
        type_map.insert(raw::TypeName("Int".to_owned()), res::TypeId::Int);
        type_map.insert(raw::TypeName("Float".to_owned()), res::TypeId::Float);
        type_map.insert(raw::TypeName("Array".to_owned()), res::TypeId::Array);

        type_map
    };
    static ref BUILTIN_CTORS: BTreeMap<raw::CtorName, (res::TypeId, res::VariantId)> = {
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
    };
    static ref BUILTIN_GLOBALS: BTreeMap<raw::ValName, res::GlobalId> = {
        let mut global_map = BTreeMap::new();

        global_map.insert(
            raw::ValName("item".to_owned()),
            res::GlobalId::ArrayOp(res::ArrayOp::Item),
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
            raw::ValName("input".to_owned()),
            res::GlobalId::IOOp(res::IOOp::Input),
        );
        global_map.insert(
            raw::ValName("output".to_owned()),
            res::GlobalId::IOOp(res::IOOp::Output),
        );

        global_map
    };
}

id_type!(ModId);

#[derive(Clone, Debug)]
struct ModMap {
    mods: BTreeMap<raw::ModName, ModId>,
    types: BTreeMap<raw::TypeName, res::TypeId>,
    ctors: BTreeMap<raw::CtorName, (res::CustomTypeId, res::VariantId)>,
    vals: BTreeMap<raw::ValName, res::GlobalId>,
}

#[derive(Clone, Debug)]
pub struct GlobalContext {
    mods: IdVec<ModId, ModMap>,
    types: IdVec<res::CustomTypeId, Option<res::TypeDef>>,
    type_symbols: IdVec<res::CustomTypeId, res::TypeSymbols>,
    vals: IdVec<res::CustomGlobalId, Option<res::ValDef>>,
    val_symbols: IdVec<res::CustomGlobalId, res::ValSymbols>,
}

pub fn resolve_program(files: &mut FileCache, file_path: &Path) -> Result<res::Program, Error> {
    let mut ctx = GlobalContext {
        mods: IdVec::new(),
        types: IdVec::new(),
        type_symbols: IdVec::new(),
        vals: IdVec::new(),
        val_symbols: IdVec::new(),
    };

    let main_mod = resolve_mod_from_file(files, &mut ctx, BTreeMap::new(), file_path)?;

    let main_proc = if let Some(&res::GlobalId::Custom(id)) = ctx.mods[main_mod]
        .vals
        .get(&raw::ValName("main".to_owned()))
    {
        id
    } else {
        return Err(locate(file_path)(ErrorKind::MainNotFound.into()));
    };

    Ok(res::Program {
        custom_types: ctx.types.into_mapped(|_id, typedef| typedef.unwrap()),
        custom_type_symbols: ctx.type_symbols,
        vals: ctx.vals.into_mapped(|_id, val_def| val_def.unwrap()),
        val_symbols: ctx.val_symbols,
        main: main_proc,
    })
}

fn resolve_mod(
    files: &mut FileCache,
    ctx: &mut GlobalContext,
    file_path: &Path,
    bindings: BTreeMap<raw::ModName, ModId>,
    content: raw::Program,
) -> Result<ModId, Error> {
    // Generate mappings
    //
    // This pass also populates `type_symbols` and `val_symbols`

    let (mod_map, pending_type_defs, pending_val_defs) = {
        let mut mod_map = ModMap {
            mods: BTreeMap::new(),
            types: BTreeMap::new(),
            ctors: BTreeMap::new(),
            vals: BTreeMap::new(),
        };

        let mut pending_type_defs = Vec::new();
        let mut pending_val_defs = Vec::new();

        for item in content.0 {
            match item {
                raw::Item::TypeDef(name, params, variants) => {
                    let type_id = ctx.types.push(None);
                    {
                        let type_symbols_id = ctx.type_symbols.push(res::TypeSymbols {
                            type_name: name.clone(),
                            variant_symbols: IdVec::from_items(
                                variants
                                    .iter()
                                    .map(|(variant_name, _)| res::VariantSymbols {
                                        variant_name: variant_name.clone(),
                                    })
                                    .collect(),
                            ),
                        });
                        debug_assert_eq!(type_id, type_symbols_id);
                    }

                    insert_unique(
                        &mut mod_map.types,
                        name.clone(),
                        res::TypeId::Custom(type_id),
                    )
                    .map_err(|()| ErrorKind::DuplicateTypeName(name.0.clone()).into())
                    .map_err(locate(file_path))?;

                    for (idx, (ctor_name, _)) in variants.iter().enumerate() {
                        insert_unique(
                            &mut mod_map.ctors,
                            ctor_name.clone(),
                            (type_id, res::VariantId(idx)),
                        )
                        .map_err(|()| ErrorKind::DuplicateCtorName(name.0.clone()).into())
                        .map_err(locate(file_path))?;
                    }

                    pending_type_defs.push((type_id, params, variants));
                }

                raw::Item::ValDef(name, type_, body) => {
                    let val_id = ctx.vals.push(None);
                    {
                        let val_symbols_id = ctx.val_symbols.push(res::ValSymbols {
                            val_name: name.clone(),
                        });
                        debug_assert_eq!(val_id, val_symbols_id);
                    }

                    insert_unique(
                        &mut mod_map.vals,
                        name.clone(),
                        res::GlobalId::Custom(val_id),
                    )
                    .map_err(|()| ErrorKind::DuplicateVarName(name.0.clone()).into())
                    .map_err(locate(file_path))?;

                    pending_val_defs.push((val_id, type_, body));
                }

                raw::Item::ModDef(name, spec, bindings, expose) => {
                    let sub_mod_bindings: BTreeMap<_, _> = bindings
                        .into_iter()
                        .map(|binding| {
                            Ok((
                                binding.name,
                                resolve_mod_path(&ctx.mods, &mod_map.mods, &binding.binding)
                                    .map_err(locate(file_path))?,
                            ))
                        })
                        .collect::<Result<_, Error>>()?;

                    let sub_mod_id =
                        resolve_mod_spec(files, ctx, file_path, sub_mod_bindings, spec)?;

                    insert_unique(&mut mod_map.mods, name.clone(), sub_mod_id)
                        .map_err(|()| ErrorKind::DuplicateModName(name.0.clone()).into())
                        .map_err(locate(file_path))?;

                    resolve_exposures(&ctx.mods, &mut mod_map, sub_mod_id, expose)
                        .map_err(locate(file_path))?;
                }

                raw::Item::ModImport(name, expose) => {
                    let bound_mod_id = *bindings
                        .get(&name)
                        .ok_or_else(|| ErrorKind::ModNotFound(name.0.clone()).into())
                        .map_err(locate(file_path))?;

                    insert_unique(&mut mod_map.mods, name.clone(), bound_mod_id)
                        .map_err(|()| ErrorKind::DuplicateModName(name.0.clone()).into())
                        .map_err(locate(file_path))?;

                    resolve_exposures(&ctx.mods, &mut mod_map, bound_mod_id, expose)
                        .map_err(locate(file_path))?;
                }

                raw::Item::ModExpose(local_mod_path, expose) => {
                    let exposed_id = resolve_mod_path(&ctx.mods, &mod_map.mods, &local_mod_path)
                        .map_err(locate(file_path))?;

                    resolve_exposures(&ctx.mods, &mut mod_map, exposed_id, expose)
                        .map_err(locate(file_path))?;
                }
            }
        }

        (mod_map, pending_type_defs, pending_val_defs)
    };

    // Resolve content of type and value definitions

    for (type_id, params, variants) in pending_type_defs {
        let mut param_map = BTreeMap::new();
        for (idx, param_name) in params.into_iter().enumerate() {
            insert_unique(&mut param_map, param_name.clone(), res::TypeParamId(idx))
                .map_err(|()| ErrorKind::DuplicateTypeName(param_name.0).into())
                .map_err(locate(file_path))?;
        }

        let resolved_variants = IdVec::from_items(
            variants
                .iter()
                .map(|(_, variant_type)| match variant_type {
                    None => Ok(None),
                    Some(variant_type) => Ok(Some(resolve_type(
                        &ctx.mods,
                        &mod_map,
                        &param_map,
                        variant_type,
                    )?)),
                })
                .collect::<Result<_, _>>()
                .map_err(locate(file_path))?,
        );

        debug_assert!(ctx.types[type_id].is_none());
        ctx.types[type_id] = Some(res::TypeDef {
            num_params: param_map.len(),
            variants: resolved_variants,
        });
    }

    for (val_id, type_, body) in pending_val_defs {
        let res_scheme = resolve_scheme(&ctx.mods, &mod_map, &type_).map_err(locate(file_path))?;

        let res_body = resolve_expr(&ctx.mods, &mod_map, &mut BTreeMap::new(), &body)
            .map_err(locate(file_path))?;

        debug_assert!(ctx.vals[val_id].is_none());
        ctx.vals[val_id] = Some(res::ValDef {
            scheme: res_scheme,
            body: res_body,
        });
    }

    // Finally register module

    let self_mod_id = ctx.mods.push(mod_map);
    Ok(self_mod_id)
}

fn resolve_mod_spec(
    files: &mut FileCache,
    ctx: &mut GlobalContext,
    file_path: &Path,
    bindings: BTreeMap<raw::ModName, ModId>,
    spec: raw::ModSpec,
) -> Result<ModId, Error> {
    match spec {
        raw::ModSpec::File(sibling_path_components) => resolve_mod_from_file(
            files,
            ctx,
            bindings,
            &sibling_path_from(file_path, sibling_path_components)?,
        ),

        raw::ModSpec::Inline(content) => resolve_mod(files, ctx, file_path, bindings, content),
    }
}

fn resolve_mod_from_file(
    files: &mut FileCache,
    ctx: &mut GlobalContext,
    bindings: BTreeMap<raw::ModName, ModId>,
    file_path: &Path,
) -> Result<ModId, Error> {
    let src = files.read(file_path).map_err(|err| Error {
        kind: ErrorKind::ReadFailed(file_path.to_owned(), err),
        span: None,
        file: None,
    })?;

    let content = parse::ProgramParser::new()
        .parse(lex::Lexer::new(&src))
        .map_err(|err| ErrorKind::ParseFailed(err).into())
        .map_err(locate(file_path))?;

    resolve_mod(files, ctx, file_path, bindings, content)
}

fn resolve_mod_path(
    global_mods: &IdVec<ModId, ModMap>,
    local_mods: &BTreeMap<raw::ModName, ModId>,
    path: &raw::ModPath,
) -> Result<ModId, Error> {
    let local_mod_name = path.0.first().expect("ModPath should not be empty");

    let mut result = *local_mods
        .get(&local_mod_name)
        .ok_or_else(|| ErrorKind::ModNotFound(local_mod_name.0.clone()))?;

    for child_name in &path.0[1..] {
        result = resolve_sub_mod(global_mods, result, child_name)?;
    }

    Ok(result)
}

fn resolve_sub_mod(
    global_mods: &IdVec<ModId, ModMap>,
    mod_id: ModId,
    sub_mod_name: &raw::ModName,
) -> Result<ModId, Error> {
    Ok(*global_mods[mod_id]
        .mods
        .get(sub_mod_name)
        .ok_or_else(|| ErrorKind::ModNotFound(sub_mod_name.0.clone()))?)
}

fn resolve_mod_val(
    global_mods: &IdVec<ModId, ModMap>,
    mod_id: ModId,
    val_name: &raw::ValName,
) -> Result<res::GlobalId, Error> {
    Ok(*global_mods[mod_id]
        .vals
        .get(val_name)
        .ok_or_else(|| ErrorKind::VarNotFound(val_name.0.clone()))?)
}

fn resolve_mod_type(
    global_mods: &IdVec<ModId, ModMap>,
    mod_id: ModId,
    type_name: &raw::TypeName,
) -> Result<res::TypeId, Error> {
    Ok(*global_mods[mod_id]
        .types
        .get(type_name)
        .ok_or_else(|| ErrorKind::TypeNotFound(type_name.0.clone()))?)
}

fn resolve_mod_ctor(
    global_mods: &IdVec<ModId, ModMap>,
    mod_id: ModId,
    ctor_name: &raw::CtorName,
) -> Result<(res::CustomTypeId, res::VariantId), Error> {
    Ok(*global_mods[mod_id]
        .ctors
        .get(ctor_name)
        .ok_or_else(|| ErrorKind::CtorNotFound(ctor_name.0.clone()))?)
}

fn resolve_exposures(
    global_mods: &IdVec<ModId, ModMap>,
    local_mod_map: &mut ModMap,
    exposed_id: ModId,
    spec: raw::ExposeSpec,
) -> Result<(), Error> {
    match spec {
        raw::ExposeSpec::Specific(items) => {
            for item in items {
                match item {
                    raw::ExposeItem::Val(name) => {
                        let resolved_val = resolve_mod_val(global_mods, exposed_id, &name)?;

                        insert_unique(&mut local_mod_map.vals, name.clone(), resolved_val)
                            .map_err(|()| ErrorKind::DuplicateVarName(name.0))?;
                    }

                    raw::ExposeItem::Type(name, variants) => {
                        let resolved_type = resolve_mod_type(global_mods, exposed_id, &name)?;

                        insert_unique(&mut local_mod_map.types, name.clone(), resolved_type)
                            .map_err(|()| ErrorKind::DuplicateTypeName(name.0))?;

                        for ctor_name in variants {
                            let (ctor_type, resolved_ctor) =
                                resolve_mod_ctor(global_mods, exposed_id, &ctor_name)?;

                            if res::TypeId::Custom(ctor_type) != resolved_type {
                                return Err(ErrorKind::CtorNotFound(ctor_name.0).into());
                            }

                            insert_unique(
                                &mut local_mod_map.ctors,
                                ctor_name.clone(),
                                (ctor_type, resolved_ctor),
                            )
                            .map_err(|()| ErrorKind::DuplicateCtorName(ctor_name.0))?;
                        }
                    }

                    raw::ExposeItem::Mod(name, sub_expose) => {
                        let resolved_sub_mod = resolve_sub_mod(global_mods, exposed_id, &name)?;

                        insert_unique(&mut local_mod_map.mods, name.clone(), resolved_sub_mod)
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

fn resolve_mod_map<'a>(
    global_mods: &'a IdVec<ModId, ModMap>,
    local_mod_map: &'a ModMap,
    path: &raw::ModPath,
) -> Result<&'a ModMap, Error> {
    if path.0.is_empty() {
        Ok(local_mod_map)
    } else {
        Ok(&global_mods[resolve_mod_path(global_mods, &local_mod_map.mods, path)?])
    }
}

fn resolve_type_with_builtins(
    global_mods: &IdVec<ModId, ModMap>,
    local_mod_map: &ModMap,
    path: &raw::ModPath,
    name: &raw::TypeName,
) -> Result<res::TypeId, Error> {
    if let Some(&id) = resolve_mod_map(global_mods, local_mod_map, path)?
        .types
        .get(name)
    {
        return Ok(id);
    }
    if path.0.is_empty() {
        if let Some(&id) = BUILTIN_TYPES.get(name) {
            return Ok(id);
        }
    }
    Err(ErrorKind::TypeNotFound(name.0.clone()).into())
}

fn resolve_type(
    global_mods: &IdVec<ModId, ModMap>,
    local_mod_map: &ModMap,
    param_map: &BTreeMap<raw::TypeParam, res::TypeParamId>,
    type_: &raw::Type,
) -> Result<res::Type, Error> {
    match type_ {
        raw::Type::Var(param_name) => {
            if let Some(&id) = param_map.get(param_name) {
                Ok(res::Type::Var(id))
            } else {
                Err(ErrorKind::TypeNotFound(param_name.0.clone()).into())
            }
        }

        raw::Type::App(path, name, args) => {
            let type_id = resolve_type_with_builtins(global_mods, local_mod_map, path, name)?;

            let resolved_args = args
                .iter()
                .map(|arg| resolve_type(global_mods, local_mod_map, param_map, arg))
                .collect::<Result<_, _>>()?;

            Ok(res::Type::App(type_id, resolved_args))
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
    }
}

fn resolve_ctor_with_builtins(
    global_mods: &IdVec<ModId, ModMap>,
    local_mod_map: &ModMap,
    path: &raw::ModPath,
    name: &raw::CtorName,
) -> Result<(res::TypeId, res::VariantId), Error> {
    if let Some(&(type_id, variant_id)) = resolve_mod_map(global_mods, local_mod_map, path)?
        .ctors
        .get(name)
    {
        return Ok((res::TypeId::Custom(type_id), variant_id));
    }
    if path.0.is_empty() {
        if let Some(&ids) = BUILTIN_CTORS.get(name) {
            return Ok(ids);
        }
    }
    Err(ErrorKind::CtorNotFound(name.0.clone()).into())
}

// Invariant: always leaves `local_map` exactly how it found it!
fn resolve_expr(
    global_mods: &IdVec<ModId, ModMap>,
    local_mod_map: &ModMap,
    local_map: &mut BTreeMap<raw::ValName, res::LocalId>,
    expr: &raw::Expr,
) -> Result<res::Expr, Error> {
    match expr {
        raw::Expr::Var(name) => {
            if let Some(&local_id) = local_map.get(name) {
                Ok(res::Expr::Local(local_id))
            } else if let Some(&global_id) = local_mod_map.vals.get(name) {
                Ok(res::Expr::Global(global_id))
            } else if let Some(&global_id) = BUILTIN_GLOBALS.get(name) {
                Ok(res::Expr::Global(global_id))
            } else {
                Err(ErrorKind::VarNotFound(name.0.clone()).into())
            }
        }

        raw::Expr::QualName(path, name) => {
            let mod_id = resolve_mod_path(global_mods, &local_mod_map.mods, path)?;
            let global_id = resolve_mod_val(global_mods, mod_id, name)?;
            Ok(res::Expr::Global(global_id))
        }

        &raw::Expr::Op(arith_op) => Ok(res::Expr::Global(res::GlobalId::ArithOp(arith_op))),

        raw::Expr::Ctor(path, name) => {
            let (type_, variant) =
                resolve_ctor_with_builtins(global_mods, local_mod_map, path, name)?;

            Ok(res::Expr::Global(res::GlobalId::Ctor(type_, variant)))
        }

        raw::Expr::Tuple(items) => Ok(res::Expr::Tuple(
            items
                .iter()
                .map(|item| resolve_expr(global_mods, local_mod_map, local_map, item))
                .collect::<Result<_, _>>()?,
        )),

        raw::Expr::Lam(purity, pattern, body) => with_pattern(
            global_mods,
            local_mod_map,
            local_map,
            pattern,
            |res_pattern, sub_local_map| {
                let res_body = resolve_expr(global_mods, local_mod_map, sub_local_map, body)?;
                Ok(res::Expr::Lam(*purity, res_pattern, Box::new(res_body)))
            },
        ),

        raw::Expr::App(purity, func, arg) => {
            let res_func = resolve_expr(global_mods, local_mod_map, local_map, &*func)?;
            let res_arg = resolve_expr(global_mods, local_mod_map, local_map, &*arg)?;
            Ok(res::Expr::App(
                *purity,
                Box::new(res_func),
                Box::new(res_arg),
            ))
        }

        raw::Expr::Match(discrim, cases) => {
            let res_discrim = resolve_expr(global_mods, local_mod_map, local_map, discrim)?;

            let res_cases = cases
                .iter()
                .map(|(pattern, body)| {
                    with_pattern(
                        global_mods,
                        local_mod_map,
                        local_map,
                        pattern,
                        |res_pattern, sub_local_map| {
                            let res_body =
                                resolve_expr(global_mods, local_mod_map, sub_local_map, body)?;
                            Ok((res_pattern, res_body))
                        },
                    )
                })
                .collect::<Result<_, _>>()?;

            Ok(res::Expr::Match(Box::new(res_discrim), res_cases))
        }

        raw::Expr::Let(lhs, rhs, body) => {
            let res_rhs = resolve_expr(global_mods, local_mod_map, local_map, rhs)?;

            with_pattern(
                global_mods,
                local_mod_map,
                local_map,
                &*lhs,
                |res_lhs, sub_local_map| {
                    let res_body = resolve_expr(global_mods, local_mod_map, sub_local_map, &*body)?;
                    Ok(res::Expr::Let(
                        res_lhs,
                        Box::new(res_rhs),
                        Box::new(res_body),
                    ))
                },
            )
        }

        raw::Expr::ArrayLit(items) => Ok(res::Expr::ArrayLit(
            items
                .iter()
                .map(|item| resolve_expr(global_mods, local_mod_map, local_map, item))
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

        raw::Expr::Span(lo, hi, expr) => {
            resolve_expr(global_mods, local_mod_map, local_map, expr).map_err(locate_span(*lo, *hi))
        }
    }
}

fn resolve_pattern(
    global_mods: &IdVec<ModId, ModMap>,
    local_mod_map: &ModMap,
    pattern: &raw::Pattern,
    vars: &mut Vec<raw::ValName>,
) -> Result<res::Pattern, Error> {
    match pattern {
        raw::Pattern::Any => Ok(res::Pattern::Any),

        raw::Pattern::Var(name) => {
            vars.push(name.clone());
            Ok(res::Pattern::Var)
        }

        raw::Pattern::Tuple(items) => Ok(res::Pattern::Tuple(
            items
                .iter()
                .map(|item| resolve_pattern(global_mods, local_mod_map, item, vars))
                .collect::<Result<_, _>>()?,
        )),

        raw::Pattern::Ctor(path, ctor_name, content) => {
            let (type_, variant) =
                resolve_ctor_with_builtins(global_mods, local_mod_map, path, ctor_name)?;

            let res_content = if let Some(content) = content {
                Some(Box::new(resolve_pattern(
                    global_mods,
                    local_mod_map,
                    content,
                    vars,
                )?))
            } else {
                None
            };

            Ok(res::Pattern::Ctor(type_, variant, res_content))
        }

        &raw::Pattern::ByteConst(val) => Ok(res::Pattern::ByteConst(val)),

        &raw::Pattern::IntConst(val) => Ok(res::Pattern::IntConst(val)),

        &raw::Pattern::FloatConst(val) => Ok(res::Pattern::FloatConst(val)),
    }
}

fn with_pattern<R, F>(
    global_mods: &IdVec<ModId, ModMap>,
    local_mod_map: &ModMap,
    local_map: &mut BTreeMap<raw::ValName, res::LocalId>,
    pattern: &raw::Pattern,
    body: F,
) -> Result<R, Error>
where
    F: for<'a> FnOnce(
        res::Pattern,
        &'a mut BTreeMap<raw::ValName, res::LocalId>,
    ) -> Result<R, Error>,
{
    let mut vars = Vec::new();
    let res_pattern = resolve_pattern(global_mods, local_mod_map, pattern, &mut vars)?;

    for var in &vars {
        insert_unique(local_map, var.clone(), res::LocalId(local_map.len()))
            .map_err(|()| ErrorKind::DuplicateVarName(var.0.clone()))?;
    }

    let result = body(res_pattern, local_map)?;

    for var in &vars {
        local_map.remove(var);
    }

    Ok(result)
}

fn find_scheme_params(scheme: &raw::Type, params: &mut BTreeMap<raw::TypeParam, res::TypeParamId>) {
    match scheme {
        raw::Type::Var(param) => {
            let id_if_new = res::TypeParamId(params.len());
            params.entry(param.clone()).or_insert(id_if_new);
        }

        raw::Type::App(_, _, args) => {
            for arg in args {
                find_scheme_params(arg, params);
            }
        }

        raw::Type::Tuple(items) => {
            for item in items {
                find_scheme_params(item, params);
            }
        }

        raw::Type::Func(_, arg, ret) => {
            find_scheme_params(&*arg, params);
            find_scheme_params(&*ret, params);
        }
    }
}

fn resolve_scheme(
    global_mods: &IdVec<ModId, ModMap>,
    local_mod_map: &ModMap,
    scheme: &raw::Type,
) -> Result<res::TypeScheme, Error> {
    let mut scheme_params = BTreeMap::new();
    find_scheme_params(scheme, &mut scheme_params);

    let res_type = resolve_type(global_mods, local_mod_map, &scheme_params, scheme)?;

    Ok(res::TypeScheme {
        num_params: scheme_params.len(),
        body: res_type,
    })
}

fn insert_unique<K: Ord, V>(map: &mut BTreeMap<K, V>, key: K, value: V) -> Result<(), ()> {
    let existing = map.insert(key, value);

    if existing.is_some() {
        Err(())
    } else {
        Ok(())
    }
}

fn sibling_path_from(self_path: &Path, components: Vec<String>) -> Result<PathBuf, Error> {
    // Validate path
    for component in &components {
        // This check also ensures we reject empty components.
        if component.chars().all(|c| c == '.') {
            return Err(Error {
                file: Some(self_path.to_owned()),
                span: None,
                kind: ErrorKind::IllegalFilePath(components.join("/")),
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
