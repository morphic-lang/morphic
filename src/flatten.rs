use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::util::id_vec::IdVec;

pub fn flatten(program: first_ord::Program) -> flat::Program {
    let flat_funcs = program
        .funcs
        .map(|_, func_def| flatten_func_def(&program, func_def));

    flat::Program {
        custom_types: program.custom_types,
        funcs: flat_funcs,
        main: program.main,
    }
}

#[derive(Clone, Debug)]
struct LetManyBuilder {
    free_locals: usize,
    bindings: Vec<(first_ord::Type, flat::Expr)>,
}

impl LetManyBuilder {
    fn new_with_free(free_locals: usize) -> Self {
        LetManyBuilder {
            free_locals,
            bindings: Vec::new(),
        }
    }

    fn add_binding(&mut self, type_: first_ord::Type, rhs: flat::Expr) -> flat::LocalId {
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
    locals: IdVec<first_ord::LocalId, (flat::LocalId, first_ord::Type)>,
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
    typedefs: &IdVec<first_ord::CustomTypeId, first_ord::TypeDef>,
    ctx: &mut LocalsContext,
    builder: &mut LetManyBuilder,
    lhs: &first_ord::Pattern,
    rhs_flat: flat::LocalId,
    rhs_type: &first_ord::Type,
) {
    match lhs {
        first_ord::Pattern::Any(type_) => {
            debug_assert_eq!(type_, rhs_type);
        }

        first_ord::Pattern::Var(type_) => {
            debug_assert_eq!(type_, rhs_type);
            let _ = ctx.locals.push((rhs_flat, type_.clone()));
        }

        first_ord::Pattern::Tuple(items) => {
            let item_types = if let first_ord::Type::Tuple(item_types) = rhs_type {
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

        first_ord::Pattern::Ctor(type_id, variant, content) => {
            debug_assert_eq!(&first_ord::Type::Custom(*type_id), rhs_type);

            let variant_content_type = &typedefs[type_id].variants[variant];

            match (content, variant_content_type) {
                (Some(content), Some(variant_content_type)) => {
                    let content_flat_local = builder.add_binding(
                        variant_content_type.clone(),
                        flat::Expr::UnwrapVariant(*type_id, *variant, rhs_flat),
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

                (None, None) => {}

                (_, _) => unreachable!(),
            }
        }

        first_ord::Pattern::BoolConst(_) => {
            debug_assert_eq!(rhs_type, &first_ord::Type::Bool);
        }

        first_ord::Pattern::ByteConst(_) => {
            debug_assert_eq!(rhs_type, &first_ord::Type::Num(first_ord::NumType::Byte));
        }

        first_ord::Pattern::IntConst(_) => {
            debug_assert_eq!(rhs_type, &first_ord::Type::Num(first_ord::NumType::Int));
        }

        first_ord::Pattern::FloatConst(_) => {
            debug_assert_eq!(rhs_type, &first_ord::Type::Num(first_ord::NumType::Float));
        }
    }
}

fn to_condition(pat: &first_ord::Pattern) -> flat::Condition {
    match pat {
        first_ord::Pattern::Any(_) => flat::Condition::Any,
        first_ord::Pattern::Var(_) => flat::Condition::Any,
        first_ord::Pattern::Tuple(items) => {
            flat::Condition::Tuple(items.iter().map(to_condition).collect())
        }
        first_ord::Pattern::Ctor(type_id, variant, content) => flat::Condition::Ctor(
            *type_id,
            *variant,
            content
                .as_ref()
                .map(|content| Box::new(to_condition(&*content))),
        ),
        first_ord::Pattern::BoolConst(val) => flat::Condition::BoolConst(*val),
        first_ord::Pattern::ByteConst(val) => flat::Condition::ByteConst(*val),
        first_ord::Pattern::IntConst(val) => flat::Condition::IntConst(*val),
        first_ord::Pattern::FloatConst(val) => flat::Condition::FloatConst(*val),
    }
}

#[allow(unconditional_recursion)]
fn flatten_expr(
    orig: &first_ord::Program,
    ctx: &mut LocalsContext,
    builder: &mut LetManyBuilder,
    expr: &first_ord::Expr,
) -> (flat::LocalId, first_ord::Type) {
    fn bind(
        builder: &mut LetManyBuilder,
        type_: first_ord::Type,
        expr: flat::Expr,
    ) -> (flat::LocalId, first_ord::Type) {
        let local = builder.add_binding(type_.clone(), expr);
        (local, type_)
    }

    match expr {
        first_ord::Expr::ArithOp(first_ord::ArithOp::Op(num_type, op, left, right)) => {
            let (left_local, left_type) = flatten_expr(orig, ctx, builder, left);
            let (right_local, right_type) = flatten_expr(orig, ctx, builder, right);

            let type_ = first_ord::Type::Num(*num_type);
            debug_assert_eq!(&left_type, &type_);
            debug_assert_eq!(&right_type, &type_);

            bind(
                builder,
                type_,
                flat::Expr::ArithOp(flat::ArithOp::Op(*num_type, *op, left_local, right_local)),
            )
        }

        first_ord::Expr::ArithOp(first_ord::ArithOp::Cmp(num_type, cmp, left, right)) => {
            let (left_local, left_type) = flatten_expr(orig, ctx, builder, left);
            let (right_local, right_type) = flatten_expr(orig, ctx, builder, right);

            let operand_type = first_ord::Type::Num(*num_type);
            debug_assert_eq!(&left_type, &operand_type);
            debug_assert_eq!(&right_type, &operand_type);

            bind(
                builder,
                first_ord::Type::Bool,
                flat::Expr::ArithOp(flat::ArithOp::Cmp(*num_type, *cmp, left_local, right_local)),
            )
        }

        first_ord::Expr::ArithOp(first_ord::ArithOp::Negate(num_type, val)) => {
            let (val_local, val_type) = flatten_expr(orig, ctx, builder, val);

            let type_ = first_ord::Type::Num(*num_type);
            debug_assert_eq!(&val_type, &type_);

            bind(
                builder,
                type_.clone(),
                flat::Expr::ArithOp(flat::ArithOp::Negate(*num_type, val_local)),
            )
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Item(item_type, array, index)) => {
            let (array_local, array_type) = flatten_expr(orig, ctx, builder, array);
            let (index_local, index_type) = flatten_expr(orig, ctx, builder, index);

            debug_assert_eq!(
                &first_ord::Type::Array(Box::new(item_type.clone())),
                &array_type
            );
            debug_assert_eq!(&first_ord::Type::Num(first_ord::NumType::Int), &index_type);

            bind(
                builder,
                first_ord::Type::Tuple(vec![
                    item_type.clone(),
                    first_ord::Type::HoleArray(Box::new(item_type.clone())),
                ]),
                flat::Expr::ArrayOp(flat::ArrayOp::Item(
                    item_type.clone(),
                    array_local,
                    index_local,
                )),
            )
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Len(item_type, array)) => {
            let (array_local, array_type) = flatten_expr(orig, ctx, builder, array);

            debug_assert_eq!(
                &first_ord::Type::Array(Box::new(item_type.clone())),
                &array_type
            );

            bind(
                builder,
                first_ord::Type::Num(first_ord::NumType::Int),
                flat::Expr::ArrayOp(flat::ArrayOp::Len(item_type.clone(), array_local)),
            )
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Push(item_type, array, item)) => {
            let (array_local, array_type) = flatten_expr(orig, ctx, builder, array);
            let (item_local, item_expr_type) = flatten_expr(orig, ctx, builder, item);

            debug_assert_eq!(
                &first_ord::Type::Array(Box::new(item_type.clone())),
                &array_type
            );
            debug_assert_eq!(item_type, &item_expr_type);

            bind(
                builder,
                first_ord::Type::Array(Box::new(item_type.clone())),
                flat::Expr::ArrayOp(flat::ArrayOp::Push(
                    item_type.clone(),
                    array_local,
                    item_local,
                )),
            )
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Pop(item_type, array)) => {
            let (array_local, array_type) = flatten_expr(orig, ctx, builder, array);

            debug_assert_eq!(
                &first_ord::Type::Array(Box::new(item_type.clone())),
                &array_type
            );

            bind(
                builder,
                first_ord::Type::Tuple(vec![
                    first_ord::Type::Array(Box::new(item_type.clone())),
                    item_type.clone(),
                ]),
                flat::Expr::ArrayOp(flat::ArrayOp::Pop(item_type.clone(), array_local)),
            )
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Replace(item_type, hole_array, item)) => {
            let (hole_array_local, hole_array_type) = flatten_expr(orig, ctx, builder, hole_array);
            let (item_local, item_expr_type) = flatten_expr(orig, ctx, builder, item);

            debug_assert_eq!(
                &first_ord::Type::HoleArray(Box::new(item_type.clone())),
                &hole_array_type
            );
            debug_assert_eq!(item_type, &item_expr_type);

            bind(
                builder,
                first_ord::Type::Array(Box::new(item_type.clone())),
                flat::Expr::ArrayOp(flat::ArrayOp::Replace(
                    item_type.clone(),
                    hole_array_local,
                    item_local,
                )),
            )
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Concat(_, _, _)) => {
            panic!("concat is an illusion")
        }

        first_ord::Expr::IOOp(first_ord::IOOp::Input) => bind(
            builder,
            first_ord::Type::Array(Box::new(first_ord::Type::Num(first_ord::NumType::Byte))),
            flat::Expr::IOOp(flat::IOOp::Input),
        ),

        first_ord::Expr::IOOp(first_ord::IOOp::Output(array)) => {
            let (array_local, array_type) = flatten_expr(orig, ctx, builder, array);

            debug_assert_eq!(
                &first_ord::Type::Array(Box::new(first_ord::Type::Num(first_ord::NumType::Byte))),
                &array_type
            );

            bind(
                builder,
                first_ord::Type::Tuple(Vec::new()),
                flat::Expr::IOOp(flat::IOOp::Output(array_local)),
            )
        }

        first_ord::Expr::Ctor(type_id, variant, content) => {
            let content_local = match content {
                Some(content) => {
                    let (content_local, content_type) = flatten_expr(orig, ctx, builder, content);
                    debug_assert_eq!(
                        orig.custom_types[type_id].variants[variant].as_ref(),
                        Some(&content_type)
                    );
                    Some(content_local)
                }

                None => {
                    debug_assert!(orig.custom_types[type_id].variants[variant].is_none());
                    None
                }
            };

            bind(
                builder,
                first_ord::Type::Custom(*type_id),
                flat::Expr::Ctor(*type_id, *variant, content_local),
            )
        }

        first_ord::Expr::Local(local) => ctx.locals[local].clone(),

        first_ord::Expr::Tuple(items) => {
            let mut item_locals = Vec::with_capacity(items.len());
            let mut item_types = Vec::with_capacity(items.len());

            for item in items {
                let (item_local, item_type) = flatten_expr(orig, ctx, builder, item);
                item_locals.push(item_local);
                item_types.push(item_type);
            }

            bind(
                builder,
                first_ord::Type::Tuple(item_types),
                flat::Expr::Tuple(item_locals),
            )
        }

        first_ord::Expr::Call(purity, func, arg) => {
            let (arg_local, arg_type) = flatten_expr(orig, ctx, builder, arg);

            debug_assert_eq!(&arg_type, &orig.funcs[func].arg_type);

            bind(
                builder,
                orig.funcs[func].ret_type.clone(),
                flat::Expr::Call(*purity, *func, arg_local),
            )
        }

        first_ord::Expr::Match(discrim, cases, result_type) => {
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

        first_ord::Expr::Let(lhs, rhs, body) => {
            let (rhs_local, rhs_type) = flatten_expr(orig, ctx, builder, rhs);

            ctx.with_scope(|sub_ctx| {
                add_flattened_binding(
                    &orig.custom_types,
                    sub_ctx,
                    builder,
                    lhs,
                    rhs_local,
                    &rhs_type,
                );
                flatten_expr(orig, sub_ctx, builder, body)
            })
        }

        first_ord::Expr::ArrayLit(item_type, items) => {
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
                first_ord::Type::Array(Box::new(item_type.clone())),
                flat::Expr::ArrayLit(item_type.clone(), item_locals),
            )
        }

        first_ord::Expr::BoolLit(val) => {
            bind(builder, first_ord::Type::Bool, flat::Expr::BoolLit(*val))
        }

        first_ord::Expr::ByteLit(val) => bind(
            builder,
            first_ord::Type::Num(first_ord::NumType::Byte),
            flat::Expr::ByteLit(*val),
        ),

        first_ord::Expr::IntLit(val) => bind(
            builder,
            first_ord::Type::Num(first_ord::NumType::Int),
            flat::Expr::IntLit(*val),
        ),

        first_ord::Expr::FloatLit(val) => bind(
            builder,
            first_ord::Type::Num(first_ord::NumType::Float),
            flat::Expr::FloatLit(*val),
        ),
    }
}

fn flatten_func_def(orig: &first_ord::Program, func_def: &first_ord::FuncDef) -> flat::FuncDef {
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
    }
}
