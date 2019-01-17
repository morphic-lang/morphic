use failure::Fail;
use std::collections::BTreeMap;

use crate::data::raw_ast as raw;
use crate::data::resolved_ast as res;

#[derive(Debug, Fail)]
pub enum Error {
    // TODO: Implement Display for raw::TypeName
    #[fail(display = "Duplicate type name '{}'", _0)]
    DuplicateTypeName(String),

    #[fail(display = "Duplicate constructor name '{}'", _0)]
    DuplicateCtorName(String),

    #[fail(display = "Duplicate variable name '{}'", _0)]
    DuplicateVarName(String),

    #[fail(display = "Could not find a type named '{}'", _0)]
    TypeNotFound(String),

    #[fail(display = "Could not find a variable named '{}'", _0)]
    VarNotFound(String),
}

fn builtin_names() -> (
    BTreeMap<raw::TypeName, res::TypeId>,
    BTreeMap<raw::CtorName, (res::TypeId, res::VariantId)>,
    BTreeMap<raw::ValName, res::GlobalId>,
) {
    let mut type_map = BTreeMap::new();

    type_map.insert(raw::TypeName("Bool".to_owned()), res::TypeId::Bool);
    type_map.insert(raw::TypeName("Int".to_owned()), res::TypeId::Int);
    type_map.insert(raw::TypeName("Float".to_owned()), res::TypeId::Float);
    type_map.insert(raw::TypeName("Text".to_owned()), res::TypeId::Text);
    type_map.insert(raw::TypeName("Array".to_owned()), res::TypeId::Array);

    let mut ctor_map = BTreeMap::new();

    ctor_map.insert(
        raw::CtorName("False".to_owned()),
        (res::TypeId::Bool, res::VariantId(0)),
    );
    ctor_map.insert(
        raw::CtorName("True".to_owned()),
        (res::TypeId::Bool, res::VariantId(1)),
    );

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

    (type_map, ctor_map, global_map)
}

#[derive(Clone, Debug)]
struct TypeDef(
    raw::TypeName,
    Vec<raw::TypeParam>,
    Vec<(raw::CtorName, Option<raw::Type>)>,
);

#[derive(Clone, Debug)]
struct ValDef(raw::ValName, raw::Type, raw::Expr);

fn organize_items(program: raw::Program) -> (Vec<TypeDef>, Vec<ValDef>) {
    let mut types = Vec::new();
    let mut vals = Vec::new();

    for item in program.0 {
        match item {
            raw::Item::TypeDef(name, params, variants) => {
                types.push(TypeDef(name, params, variants))
            }
            raw::Item::ValDef(name, type_, body) => vals.push(ValDef(name, type_, body)),
        }
    }

    (types, vals)
}

fn resolve_type(
    type_map: &BTreeMap<raw::TypeName, res::TypeId>,
    param_map: &BTreeMap<raw::TypeParam, res::TypeParamId>,
    type_: &raw::Type,
) -> Result<res::Type, Error> {
    match type_ {
        raw::Type::Var(param_name) => {
            if let Some(&id) = param_map.get(param_name) {
                Ok(res::Type::Var(id))
            } else {
                Err(Error::TypeNotFound(param_name.0.clone()))
            }
        }

        raw::Type::App(name, args) => {
            if let Some(&id) = type_map.get(name) {
                let resolved_args = args
                    .iter()
                    .map(|arg| resolve_type(type_map, param_map, arg))
                    .collect::<Result<_, _>>()?;

                Ok(res::Type::App(id, resolved_args))
            } else {
                Err(Error::TypeNotFound(name.0.clone()))
            }
        }

        raw::Type::Tuple(items) => Ok(res::Type::Tuple(
            items
                .iter()
                .map(|item| resolve_type(type_map, param_map, item))
                .collect::<Result<_, _>>()?,
        )),

        raw::Type::Func(arg, ret) => Ok(res::Type::Func(
            Box::new(resolve_type(type_map, param_map, &*arg)?),
            Box::new(resolve_type(type_map, param_map, &*ret)?),
        )),
    }
}

fn resolve_typedefs(
    type_map: &mut BTreeMap<raw::TypeName, res::TypeId>,
    ctor_map: &mut BTreeMap<raw::CtorName, (res::TypeId, res::VariantId)>,
    types: &[TypeDef],
) -> Result<Vec<res::TypeDef>, Error> {
    for (index, TypeDef(name, _, _)) in types.iter().enumerate() {
        let existing = type_map.insert(name.clone(), res::TypeId::Custom(res::CustomTypeId(index)));
        if existing.is_some() {
            return Err(Error::DuplicateTypeName(name.0.clone()));
        }
    }

    let mut resolved_types = Vec::new();

    for (index, TypeDef(_, params, variants)) in types.iter().enumerate() {
        let mut param_map = BTreeMap::new();
        for (param_index, param) in params.iter().enumerate() {
            let existing = param_map.insert(param.clone(), res::TypeParamId(param_index));
            if existing.is_some() {
                return Err(Error::DuplicateTypeName(param.0.clone()));
            }
        }

        let mut resolved_variants = Vec::new();
        for (variant_index, (ctor_name, content)) in variants.iter().enumerate() {
            let res_content = if let Some(content) = content {
                Some(resolve_type(&type_map, &param_map, content)?)
            } else {
                None
            };

            let existing = ctor_map.insert(
                ctor_name.clone(),
                (
                    res::TypeId::Custom(res::CustomTypeId(index)),
                    res::VariantId(variant_index),
                ),
            );
            if existing.is_some() {
                return Err(Error::DuplicateCtorName(ctor_name.0.clone()));
            }

            resolved_variants.push(res_content);
        }

        resolved_types.push(res::TypeDef {
            num_params: params.len(),
            variants: resolved_variants,
        });
    }

    Ok(resolved_types)
}

// Invariant: always leaves `local_map` exactly how it found it!
fn resolve_expr(
    ctor_map: &BTreeMap<raw::CtorName, (res::TypeId, res::VariantId)>,
    global_map: &BTreeMap<raw::ValName, res::GlobalId>,
    local_map: &mut BTreeMap<raw::ValName, res::LocalId>,
    expr: &raw::Expr,
) -> Result<res::Expr, Error> {
    match expr {
        raw::Expr::Var(name) => {
            if let Some(&local_id) = local_map.get(name) {
                Ok(res::Expr::Local(local_id))
            } else if let Some(&global_id) = global_map.get(name) {
                Ok(res::Expr::Global(global_id))
            } else {
                Err(Error::VarNotFound(name.0.clone()))
            }
        }

        &raw::Expr::Op(arith_op) => Ok(res::Expr::Global(res::GlobalId::ArithOp(arith_op))),

        raw::Expr::Ctor(ctor_name) => {
            if let Some(&(type_, variant)) = ctor_map.get(ctor_name) {
                Ok(res::Expr::Global(res::GlobalId::Ctor(type_, variant)))
            } else {
                Err(Error::VarNotFound(ctor_name.0.clone()))
            }
        }

        raw::Expr::Tuple(items) => Ok(res::Expr::Tuple(
            items
                .iter()
                .map(|item| resolve_expr(ctor_map, global_map, local_map, item))
                .collect::<Result<_, _>>()?,
        )),

        raw::Expr::Lam(pattern, body) => with_pattern(
            ctor_map,
            local_map,
            pattern,
            |res_pattern, sub_local_map| {
                let res_body = resolve_expr(ctor_map, global_map, sub_local_map, body)?;
                Ok(res::Expr::Lam(res_pattern, Box::new(res_body)))
            },
        ),

        raw::Expr::App(func, arg) => {
            let res_func = resolve_expr(ctor_map, global_map, local_map, &*func)?;
            let res_arg = resolve_expr(ctor_map, global_map, local_map, &*arg)?;
            Ok(res::Expr::App(Box::new(res_func), Box::new(res_arg)))
        }

        raw::Expr::Match(discrim, cases) => {
            let res_discrim = resolve_expr(ctor_map, global_map, local_map, discrim)?;

            let res_cases = cases
                .iter()
                .map(|(pattern, body)| {
                    with_pattern(
                        ctor_map,
                        local_map,
                        pattern,
                        |res_pattern, sub_local_map| {
                            let res_body = resolve_expr(ctor_map, global_map, sub_local_map, body)?;
                            Ok((res_pattern, res_body))
                        },
                    )
                })
                .collect::<Result<_, _>>()?;

            Ok(res::Expr::Match(Box::new(res_discrim), res_cases))
        }

        raw::Expr::Let(lhs, rhs, body) => {
            let res_rhs = resolve_expr(ctor_map, global_map, local_map, rhs)?;

            with_pattern(ctor_map, local_map, &*lhs, |res_lhs, sub_local_map| {
                let res_body = resolve_expr(ctor_map, global_map, sub_local_map, &*body)?;
                Ok(res::Expr::Let(
                    res_lhs,
                    Box::new(res_rhs),
                    Box::new(res_body),
                ))
            })
        }

        raw::Expr::ArrayLit(items) => Ok(res::Expr::ArrayLit(
            items
                .iter()
                .map(|item| resolve_expr(ctor_map, global_map, local_map, item))
                .collect::<Result<_, _>>()?,
        )),

        &raw::Expr::IntLit(val) => Ok(res::Expr::IntLit(val)),

        &raw::Expr::FloatLit(val) => Ok(res::Expr::FloatLit(val)),

        raw::Expr::TextLit(text) => Ok(res::Expr::TextLit(text.clone())),
    }
}

fn resolve_pattern(
    ctor_map: &BTreeMap<raw::CtorName, (res::TypeId, res::VariantId)>,
    pattern: &raw::Pattern,
    vars: &mut Vec<raw::ValName>,
) -> Result<res::PatternBody, Error> {
    match pattern {
        raw::Pattern::Any => Ok(res::PatternBody::Any),

        raw::Pattern::Var(name) => {
            vars.push(name.clone());
            Ok(res::PatternBody::Var)
        }

        raw::Pattern::Tuple(items) => Ok(res::PatternBody::Tuple(
            items
                .iter()
                .map(|item| resolve_pattern(ctor_map, item, vars))
                .collect::<Result<_, _>>()?,
        )),

        raw::Pattern::Ctor(ctor_name, content) => {
            if let Some(&(type_, variant)) = ctor_map.get(ctor_name) {
                let res_content = if let Some(content) = content {
                    Some(Box::new(resolve_pattern(ctor_map, &*content, vars)?))
                } else {
                    None
                };

                Ok(res::PatternBody::Ctor(type_, variant, res_content))
            } else {
                Err(Error::VarNotFound(ctor_name.0.clone()))
            }
        }

        &raw::Pattern::IntConst(val) => Ok(res::PatternBody::IntConst(val)),

        &raw::Pattern::FloatConst(val) => Ok(res::PatternBody::FloatConst(val)),

        raw::Pattern::TextConst(text) => Ok(res::PatternBody::TextConst(text.clone())),
    }
}

fn with_pattern<R, F>(
    ctor_map: &BTreeMap<raw::CtorName, (res::TypeId, res::VariantId)>,
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
    let res_pattern = resolve_pattern(ctor_map, pattern, &mut vars)?;

    for var in &vars {
        let existing = local_map.insert(var.clone(), res::LocalId(local_map.len()));
        if existing.is_some() {
            return Err(Error::DuplicateVarName(var.0.clone()));
        }
    }

    let result = body(
        res::Pattern {
            num_vars: vars.len(),
            body: res_pattern,
        },
        local_map,
    )?;

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

        raw::Type::App(_, args) => {
            for arg in args {
                find_scheme_params(arg, params);
            }
        }

        raw::Type::Tuple(items) => {
            for item in items {
                find_scheme_params(item, params);
            }
        }

        raw::Type::Func(arg, ret) => {
            find_scheme_params(&*arg, params);
            find_scheme_params(&*ret, params);
        }
    }
}

fn resolve_scheme(
    type_map: &BTreeMap<raw::TypeName, res::TypeId>,
    scheme: &raw::Type,
) -> Result<res::TypeScheme, Error> {
    let mut scheme_params = BTreeMap::new();
    find_scheme_params(scheme, &mut scheme_params);

    let res_type = resolve_type(type_map, &scheme_params, scheme)?;

    Ok(res::TypeScheme {
        num_params: scheme_params.len(),
        body: res_type,
    })
}

fn resolve_val_defs(
    type_map: &BTreeMap<raw::TypeName, res::TypeId>,
    ctor_map: &BTreeMap<raw::CtorName, (res::TypeId, res::VariantId)>,
    global_map: &mut BTreeMap<raw::ValName, res::GlobalId>,
    vals: &[ValDef],
) -> Result<Vec<res::ValDef>, Error> {
    for (index, ValDef(name, _, _)) in vals.iter().enumerate() {
        let existing = global_map.insert(
            name.clone(),
            res::GlobalId::Custom(res::CustomGlobalId(index)),
        );
        if existing.is_some() {
            return Err(Error::DuplicateVarName(name.0.clone()));
        }
    }

    let mut res_defs = Vec::new();

    for ValDef(_, scheme, body) in vals {
        let res_scheme = resolve_scheme(type_map, scheme)?;
        let res_body = resolve_expr(ctor_map, global_map, &mut BTreeMap::new(), body)?;
        res_defs.push(res::ValDef {
            scheme: res_scheme,
            body: res_body,
        });
    }

    Ok(res_defs)
}

pub fn resolve(program: raw::Program) -> Result<res::Program, Error> {
    let (types, vals) = organize_items(program);

    let (mut type_map, mut ctor_map, mut global_map) = builtin_names();

    let resolved_types = resolve_typedefs(&mut type_map, &mut ctor_map, &types)?;

    let resolved_defs = resolve_val_defs(&type_map, &ctor_map, &mut global_map, &vals)?;

    Ok(res::Program {
        custom_types: resolved_types,
        vals: resolved_defs,
    })
}
