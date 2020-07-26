use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::util::id_vec::IdVec;

pub fn flatten(program: anon::Program) -> flat::Program {
    let flat_funcs = program
        .funcs
        .map(|_, func_def| flatten_func_def(&program, func_def));

    flat::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs: flat_funcs,
        func_symbols: program.func_symbols,
        profile_points: program.profile_points,
        main: program.main,
    }
}

#[derive(Clone, Debug)]
struct LetManyBuilder {
    free_locals: usize,
    bindings: Vec<(anon::Type, flat::Expr)>,
}

impl LetManyBuilder {
    fn new_with_free(free_locals: usize) -> Self {
        LetManyBuilder {
            free_locals,
            bindings: Vec::new(),
        }
    }

    fn add_binding(&mut self, type_: anon::Type, rhs: flat::Expr) -> flat::LocalId {
        let binding_id = flat::LocalId(self.free_locals + self.bindings.len());
        self.bindings.push((type_, rhs));
        binding_id
    }

    fn to_expr(self, ret: flat::LocalId) -> flat::Expr {
        debug_assert!(ret.0 < self.free_locals + self.bindings.len());
        flat::Expr::LetMany(self.bindings, ret)
    }
}

#[derive(Clone, Debug)]
struct LocalsContext {
    locals: IdVec<first_ord::LocalId, (flat::LocalId, anon::Type)>,
}

impl LocalsContext {
    fn new() -> Self {
        LocalsContext {
            locals: IdVec::new(),
        }
    }

    fn with_scope<R, F: for<'a> FnOnce(&'a mut LocalsContext) -> R>(&mut self, body: F) -> R {
        let num_locals = self.locals.len();
        let result = body(self);
        self.locals.truncate(num_locals);
        result
    }
}

fn add_flattened_binding(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    ctx: &mut LocalsContext,
    builder: &mut LetManyBuilder,
    lhs: &anon::Pattern,
    rhs_flat: flat::LocalId,
    rhs_type: &anon::Type,
) {
    match lhs {
        anon::Pattern::Any(type_) => {
            debug_assert_eq!(type_, rhs_type);
        }

        anon::Pattern::Var(type_) => {
            debug_assert_eq!(type_, rhs_type);
            let _ = ctx.locals.push((rhs_flat, type_.clone()));
        }

        anon::Pattern::Tuple(items) => {
            let item_types = if let anon::Type::Tuple(item_types) = rhs_type {
                item_types
            } else {
                unreachable!()
            };

            debug_assert_eq!(items.len(), item_types.len());

            for (field_idx, (item, item_type)) in items.iter().zip(item_types.iter()).enumerate() {
                let item_flat_local = builder.add_binding(
                    item_type.clone(),
                    flat::Expr::TupleField(rhs_flat, field_idx),
                );
                add_flattened_binding(typedefs, ctx, builder, item, item_flat_local, item_type);
            }
        }

        anon::Pattern::Variant(variant_types, variant, content) => {
            debug_assert_eq!(&anon::Type::Variants(variant_types.clone()), rhs_type);

            let variant_content_type = &variant_types[variant];

            let content_flat_local = builder.add_binding(
                variant_content_type.clone(),
                flat::Expr::UnwrapVariant(*variant, rhs_flat),
            );
            add_flattened_binding(
                typedefs,
                ctx,
                builder,
                content,
                content_flat_local,
                variant_content_type,
            );
        }

        anon::Pattern::Boxed(content, content_type) => {
            let content_flat_local = builder.add_binding(
                content_type.clone(),
                flat::Expr::UnwrapBoxed(rhs_flat, content_type.clone()),
            );

            add_flattened_binding(
                typedefs,
                ctx,
                builder,
                content,
                content_flat_local,
                content_type,
            )
        }

        anon::Pattern::Custom(type_id, content) => {
            debug_assert_eq!(&anon::Type::Custom(*type_id), rhs_type);

            let content_type = &typedefs[type_id];

            let content_flat_local = builder.add_binding(
                content_type.clone(),
                flat::Expr::UnwrapCustom(*type_id, rhs_flat),
            );
            add_flattened_binding(
                typedefs,
                ctx,
                builder,
                content,
                content_flat_local,
                content_type,
            );
        }

        anon::Pattern::BoolConst(_) => {
            debug_assert_eq!(rhs_type, &anon::Type::Bool);
        }

        anon::Pattern::ByteConst(_) => {
            debug_assert_eq!(rhs_type, &anon::Type::Num(first_ord::NumType::Byte));
        }

        anon::Pattern::IntConst(_) => {
            debug_assert_eq!(rhs_type, &anon::Type::Num(first_ord::NumType::Int));
        }

        anon::Pattern::FloatConst(_) => {
            debug_assert_eq!(rhs_type, &anon::Type::Num(first_ord::NumType::Float));
        }
    }
}

fn to_condition(pat: &anon::Pattern) -> flat::Condition {
    match pat {
        anon::Pattern::Any(_) => flat::Condition::Any,
        anon::Pattern::Var(_) => flat::Condition::Any,
        anon::Pattern::Tuple(items) => {
            flat::Condition::Tuple(items.iter().map(to_condition).collect())
        }
        anon::Pattern::Variant(_variant_types, variant, content) => {
            flat::Condition::Variant(*variant, Box::new(to_condition(content)))
        }
        anon::Pattern::Boxed(content, content_type) => {
            flat::Condition::Boxed(Box::new(to_condition(content)), content_type.clone())
        }
        anon::Pattern::Custom(type_id, content) => {
            flat::Condition::Custom(*type_id, Box::new(to_condition(content)))
        }
        anon::Pattern::BoolConst(val) => flat::Condition::BoolConst(*val),
        anon::Pattern::ByteConst(val) => flat::Condition::ByteConst(*val),
        anon::Pattern::IntConst(val) => flat::Condition::IntConst(*val),
        anon::Pattern::FloatConst(val) => flat::Condition::FloatConst(*val),
    }
}

fn flatten_expr(
    orig: &anon::Program,
    ctx: &mut LocalsContext,
    builder: &mut LetManyBuilder,
    expr: &anon::Expr,
) -> (flat::LocalId, anon::Type) {
    fn bind(
        builder: &mut LetManyBuilder,
        type_: anon::Type,
        expr: flat::Expr,
    ) -> (flat::LocalId, anon::Type) {
        let local = builder.add_binding(type_.clone(), expr);
        (local, type_)
    }

    match expr {
        anon::Expr::ArithOp(anon::ArithOp::Op(num_type, op, left, right)) => {
            let (left_local, left_type) = flatten_expr(orig, ctx, builder, left);
            let (right_local, right_type) = flatten_expr(orig, ctx, builder, right);

            let type_ = anon::Type::Num(*num_type);
            debug_assert_eq!(&left_type, &type_);
            debug_assert_eq!(&right_type, &type_);

            bind(
                builder,
                type_,
                flat::Expr::ArithOp(flat::ArithOp::Op(*num_type, *op, left_local, right_local)),
            )
        }

        anon::Expr::ArithOp(anon::ArithOp::Cmp(num_type, cmp, left, right)) => {
            let (left_local, left_type) = flatten_expr(orig, ctx, builder, left);
            let (right_local, right_type) = flatten_expr(orig, ctx, builder, right);

            let operand_type = anon::Type::Num(*num_type);
            debug_assert_eq!(&left_type, &operand_type);
            debug_assert_eq!(&right_type, &operand_type);

            bind(
                builder,
                anon::Type::Bool,
                flat::Expr::ArithOp(flat::ArithOp::Cmp(*num_type, *cmp, left_local, right_local)),
            )
        }

        anon::Expr::ArithOp(anon::ArithOp::Negate(num_type, val)) => {
            let (val_local, val_type) = flatten_expr(orig, ctx, builder, val);

            let type_ = anon::Type::Num(*num_type);
            debug_assert_eq!(&val_type, &type_);

            bind(
                builder,
                type_.clone(),
                flat::Expr::ArithOp(flat::ArithOp::Negate(*num_type, val_local)),
            )
        }

        anon::Expr::ArrayOp(anon::ArrayOp::Item(item_type, array, index)) => {
            let (array_local, array_type) = flatten_expr(orig, ctx, builder, array);
            let (index_local, index_type) = flatten_expr(orig, ctx, builder, index);

            debug_assert_eq!(&anon::Type::Array(Box::new(item_type.clone())), &array_type);
            debug_assert_eq!(&anon::Type::Num(first_ord::NumType::Int), &index_type);

            bind(
                builder,
                anon::Type::Tuple(vec![
                    item_type.clone(),
                    anon::Type::HoleArray(Box::new(item_type.clone())),
                ]),
                flat::Expr::ArrayOp(flat::ArrayOp::Item(
                    item_type.clone(),
                    array_local,
                    index_local,
                )),
            )
        }

        anon::Expr::ArrayOp(anon::ArrayOp::Len(item_type, array)) => {
            let (array_local, array_type) = flatten_expr(orig, ctx, builder, array);

            debug_assert_eq!(&anon::Type::Array(Box::new(item_type.clone())), &array_type);

            bind(
                builder,
                anon::Type::Num(first_ord::NumType::Int),
                flat::Expr::ArrayOp(flat::ArrayOp::Len(item_type.clone(), array_local)),
            )
        }

        anon::Expr::ArrayOp(anon::ArrayOp::Push(item_type, array, item)) => {
            let (array_local, array_type) = flatten_expr(orig, ctx, builder, array);
            let (item_local, item_expr_type) = flatten_expr(orig, ctx, builder, item);

            debug_assert_eq!(&anon::Type::Array(Box::new(item_type.clone())), &array_type);
            debug_assert_eq!(item_type, &item_expr_type);

            bind(
                builder,
                anon::Type::Array(Box::new(item_type.clone())),
                flat::Expr::ArrayOp(flat::ArrayOp::Push(
                    item_type.clone(),
                    array_local,
                    item_local,
                )),
            )
        }

        anon::Expr::ArrayOp(anon::ArrayOp::Pop(item_type, array)) => {
            let (array_local, array_type) = flatten_expr(orig, ctx, builder, array);

            debug_assert_eq!(&anon::Type::Array(Box::new(item_type.clone())), &array_type);

            bind(
                builder,
                anon::Type::Tuple(vec![
                    anon::Type::Array(Box::new(item_type.clone())),
                    item_type.clone(),
                ]),
                flat::Expr::ArrayOp(flat::ArrayOp::Pop(item_type.clone(), array_local)),
            )
        }

        anon::Expr::ArrayOp(anon::ArrayOp::Replace(item_type, hole_array, item)) => {
            let (hole_array_local, hole_array_type) = flatten_expr(orig, ctx, builder, hole_array);
            let (item_local, item_expr_type) = flatten_expr(orig, ctx, builder, item);

            debug_assert_eq!(
                &anon::Type::HoleArray(Box::new(item_type.clone())),
                &hole_array_type
            );
            debug_assert_eq!(item_type, &item_expr_type);

            bind(
                builder,
                anon::Type::Array(Box::new(item_type.clone())),
                flat::Expr::ArrayOp(flat::ArrayOp::Replace(
                    item_type.clone(),
                    hole_array_local,
                    item_local,
                )),
            )
        }

        anon::Expr::IoOp(anon::IoOp::Input) => bind(
            builder,
            anon::Type::Array(Box::new(anon::Type::Num(first_ord::NumType::Byte))),
            flat::Expr::IoOp(flat::IoOp::Input),
        ),

        anon::Expr::IoOp(anon::IoOp::Output(array)) => {
            let (array_local, array_type) = flatten_expr(orig, ctx, builder, array);

            debug_assert_eq!(
                &anon::Type::Array(Box::new(anon::Type::Num(first_ord::NumType::Byte))),
                &array_type
            );

            bind(
                builder,
                anon::Type::Tuple(Vec::new()),
                flat::Expr::IoOp(flat::IoOp::Output(array_local)),
            )
        }

        anon::Expr::WrapVariant(variant_types, variant, content) => {
            let (content_local, content_type) = flatten_expr(orig, ctx, builder, content);

            debug_assert_eq!(&variant_types[variant], &content_type);

            bind(
                builder,
                anon::Type::Variants(variant_types.clone()),
                flat::Expr::WrapVariant(variant_types.clone(), *variant, content_local),
            )
        }

        anon::Expr::WrapBoxed(content, content_type) => {
            let (content_local, child_content_type) = flatten_expr(orig, ctx, builder, content);

            debug_assert_eq!(&child_content_type, content_type);

            bind(
                builder,
                anon::Type::Boxed(Box::new(child_content_type)),
                flat::Expr::WrapBoxed(content_local, content_type.clone()),
            )
        }

        anon::Expr::WrapCustom(type_id, content) => {
            let (content_local, content_type) = flatten_expr(orig, ctx, builder, content);

            debug_assert_eq!(&orig.custom_types[type_id], &content_type);

            bind(
                builder,
                anon::Type::Custom(*type_id),
                flat::Expr::WrapCustom(*type_id, content_local),
            )
        }

        anon::Expr::Local(local) => ctx.locals[local].clone(),

        anon::Expr::Tuple(items) => {
            let mut item_locals = Vec::with_capacity(items.len());
            let mut item_types = Vec::with_capacity(items.len());

            for item in items {
                let (item_local, item_type) = flatten_expr(orig, ctx, builder, item);
                item_locals.push(item_local);
                item_types.push(item_type);
            }

            bind(
                builder,
                anon::Type::Tuple(item_types),
                flat::Expr::Tuple(item_locals),
            )
        }

        anon::Expr::Call(purity, func, arg) => {
            let (arg_local, arg_type) = flatten_expr(orig, ctx, builder, arg);

            debug_assert_eq!(&arg_type, &orig.funcs[func].arg_type);

            bind(
                builder,
                orig.funcs[func].ret_type.clone(),
                flat::Expr::Call(*purity, *func, arg_local),
            )
        }

        anon::Expr::Match(discrim, cases, result_type) => {
            let (discrim_local, discrim_type) = flatten_expr(orig, ctx, builder, discrim);

            let cases_flat = cases
                .iter()
                .map(|(pat, body)| {
                    let cond = to_condition(pat);

                    let body_flat = ctx.with_scope(|sub_ctx| {
                        let mut sub_builder = LetManyBuilder::new_with_free(
                            builder.free_locals + builder.bindings.len(),
                        );
                        add_flattened_binding(
                            &orig.custom_types,
                            sub_ctx,
                            &mut sub_builder,
                            pat,
                            discrim_local,
                            &discrim_type,
                        );
                        let (body_local, body_type) =
                            flatten_expr(orig, sub_ctx, &mut sub_builder, body);
                        debug_assert_eq!(&body_type, result_type);
                        sub_builder.to_expr(body_local)
                    });

                    (cond, body_flat)
                })
                .collect();

            bind(
                builder,
                result_type.clone(),
                flat::Expr::Branch(discrim_local, cases_flat, result_type.clone()),
            )
        }

        anon::Expr::LetMany(bindings, body) => ctx.with_scope(|sub_ctx| {
            for (lhs, rhs) in bindings {
                let (rhs_local, rhs_type) = flatten_expr(orig, sub_ctx, builder, rhs);

                add_flattened_binding(
                    &orig.custom_types,
                    sub_ctx,
                    builder,
                    lhs,
                    rhs_local,
                    &rhs_type,
                );
            }
            flatten_expr(orig, sub_ctx, builder, body)
        }),

        anon::Expr::ArrayLit(item_type, items) => {
            let item_locals = items
                .iter()
                .map(|item| {
                    let (item_local, item_expr_type) = flatten_expr(orig, ctx, builder, item);
                    debug_assert_eq!(&item_expr_type, item_type);
                    item_local
                })
                .collect();

            bind(
                builder,
                anon::Type::Array(Box::new(item_type.clone())),
                flat::Expr::ArrayLit(item_type.clone(), item_locals),
            )
        }

        anon::Expr::BoolLit(val) => bind(builder, anon::Type::Bool, flat::Expr::BoolLit(*val)),

        anon::Expr::ByteLit(val) => bind(
            builder,
            anon::Type::Num(first_ord::NumType::Byte),
            flat::Expr::ByteLit(*val),
        ),

        anon::Expr::IntLit(val) => bind(
            builder,
            anon::Type::Num(first_ord::NumType::Int),
            flat::Expr::IntLit(*val),
        ),

        anon::Expr::FloatLit(val) => bind(
            builder,
            anon::Type::Num(first_ord::NumType::Float),
            flat::Expr::FloatLit(*val),
        ),
    }
}

fn flatten_func_def(orig: &anon::Program, func_def: &anon::FuncDef) -> flat::FuncDef {
    let mut ctx = LocalsContext::new();
    let mut root_builder = LetManyBuilder::new_with_free(1);

    add_flattened_binding(
        &orig.custom_types,
        &mut ctx,
        &mut root_builder,
        &func_def.arg,
        flat::ARG_LOCAL,
        &func_def.arg_type,
    );

    let (ret_local, ret_type) = flatten_expr(orig, &mut ctx, &mut root_builder, &func_def.body);

    debug_assert_eq!(&ret_type, &func_def.ret_type);

    flat::FuncDef {
        purity: func_def.purity,
        arg_type: func_def.arg_type.clone(),
        ret_type: func_def.ret_type.clone(),
        body: root_builder.to_expr(ret_local),
        profile_point: func_def.profile_point,
    }
}
