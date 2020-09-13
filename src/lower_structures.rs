use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::low_ast as low;
use crate::data::repr_specialized_ast as special;
use crate::data::repr_unified_ast as unif;
use crate::data::tail_rec_ast as tail;
use crate::util::id_vec::IdVec;
use crate::util::local_context::LocalContext;
use im_rc::OrdMap;
use im_rc::OrdSet;

#[derive(Clone, Debug)]
struct MoveInfo {
    move_info: OrdMap<flat::LocalId, u64>,
}

#[derive(Clone, Debug)]
struct FutureUsageInfo {
    future_usages: OrdSet<flat::LocalId>,
}

#[derive(Clone, Debug)]
struct AnnotExpr {
    kind: AnnotExprKind,
    move_info: MoveInfo,
}

#[derive(Clone, Debug)]
enum AnnotExprKind {
    Branch(
        flat::LocalId,
        Vec<(special::Condition, AnnotExpr)>,
        special::Type,
    ),
    LetMany(
        Vec<(special::Type, AnnotExpr, FutureUsageInfo)>,
        flat::LocalId,
    ),
    Leaf(tail::Expr),
}

fn annotate_expr(
    expr: tail::Expr,
    future_usages: &FutureUsageInfo,
    ids_in_scope: usize,
) -> AnnotExpr {
    match expr {
        tail::Expr::LetMany(exprs, final_local) => {
            let mut current_future_usages = future_usages.clone();
            current_future_usages.future_usages.insert(final_local);

            let mut let_move_info = MoveInfo {
                move_info: OrdMap::new(),
            };
            if final_local.0 < ids_in_scope {
                if !current_future_usages.future_usages.contains(&final_local) {
                    let_move_info.move_info.insert(final_local, 1);
                } else {
                    let_move_info.move_info.insert(final_local, 0);
                }
            }

            let mut new_bindings_reversed = Vec::new();

            for (index, (type_, binding)) in exprs.into_iter().enumerate().rev() {
                let post_binding_future_usages = current_future_usages.clone();

                current_future_usages
                    .future_usages
                    .remove(&flat::LocalId(index + ids_in_scope));

                let annotated_binding =
                    annotate_expr(binding, &current_future_usages, ids_in_scope + index);

                let binding_move_info = annotated_binding.move_info.clone();

                new_bindings_reversed.push((type_, annotated_binding, post_binding_future_usages));

                for (var, _moves) in &binding_move_info.move_info {
                    if var.0 < ids_in_scope {
                        let entry = let_move_info.move_info.entry(*var).or_insert(0);
                        if !current_future_usages.future_usages.contains(var) {
                            *entry = 1;
                        }
                    }
                }
                for var in binding_move_info.move_info.keys() {
                    current_future_usages.future_usages.insert(*var);
                }
            }

            let mut new_bindings = new_bindings_reversed;
            new_bindings.reverse();

            AnnotExpr {
                kind: AnnotExprKind::LetMany(new_bindings, final_local),
                move_info: let_move_info,
            }
        }

        tail::Expr::Branch(discrim, cases, res_type) => {
            let mut branch_move_info = MoveInfo {
                move_info: OrdMap::unit(discrim, 0),
            };
            if !future_usages.future_usages.contains(&discrim) {
                branch_move_info.move_info.insert(discrim, 1);
            }

            let mut new_cases = Vec::new();

            for (cond, body) in cases {
                let annotated_body = annotate_expr(body, future_usages, ids_in_scope);

                for (var, _move_count) in &annotated_body.move_info.move_info {
                    let entry = branch_move_info.move_info.entry(*var).or_insert(0);
                    if !future_usages.future_usages.contains(var) {
                        *entry = 1;
                    }
                }

                new_cases.push((cond, annotated_body));
            }

            AnnotExpr {
                move_info: branch_move_info,
                kind: AnnotExprKind::Branch(discrim, new_cases, res_type),
            }
        }

        _ => AnnotExpr {
            move_info: count_moves(&expr),
            kind: AnnotExprKind::Leaf(expr),
        },
    }
}

impl MoveInfo {
    fn add_borrow(&mut self, local_id: flat::LocalId) {
        self.move_info.entry(local_id).or_insert(0);
    }

    fn add_move(&mut self, local_id: flat::LocalId) {
        *self.move_info.entry(local_id).or_insert(0) += 1;
    }
}

fn count_moves(expr: &tail::Expr) -> MoveInfo {
    let mut move_info = MoveInfo {
        move_info: OrdMap::new(),
    };

    match expr {
        tail::Expr::Local(local_id) => move_info.add_move(*local_id),

        tail::Expr::Call(_, _, local_id) | tail::Expr::TailCall(_, local_id) => {
            move_info.add_move(*local_id)
        }

        tail::Expr::Tuple(local_ids) => {
            for local_id in local_ids {
                move_info.add_move(*local_id);
            }
        }
        tail::Expr::TupleField(local_id, _index) => move_info.add_borrow(*local_id),

        tail::Expr::WrapVariant(_variants, _variant_id, local_id) => {
            move_info.add_move(*local_id);
        }
        tail::Expr::UnwrapVariant(_variant_id, local_id) => move_info.add_move(*local_id),

        tail::Expr::WrapBoxed(local_id, _content_type) => move_info.add_move(*local_id),
        tail::Expr::UnwrapBoxed(local_id, _content_type) => move_info.add_borrow(*local_id),

        tail::Expr::WrapCustom(_type_id, local_id) => move_info.add_move(*local_id),
        tail::Expr::UnwrapCustom(_type_id, local_id) => move_info.add_move(*local_id),

        // NOTE [intrinsics]: If we ever add intrinsics which can take heap values as arguments, we
        // may need to modify this.
        tail::Expr::Intrinsic(_intr, local_id) => move_info.add_move(*local_id),
        tail::Expr::ArrayOp(_rep_choice, _item_type, array_op) => match array_op {
            unif::ArrayOp::Item(array_id, index_id) => {
                move_info.add_borrow(*array_id);
                move_info.add_move(*index_id);
            }
            unif::ArrayOp::Len(array_id) => {
                move_info.add_borrow(*array_id);
            }
            unif::ArrayOp::Push(array_id, item_id) => {
                move_info.add_move(*array_id);
                move_info.add_move(*item_id);
            }
            unif::ArrayOp::Pop(array_id) => {
                move_info.add_move(*array_id);
            }
            unif::ArrayOp::Replace(array_id, item_id) => {
                move_info.add_move(*array_id);
                move_info.add_move(*item_id);
            }
        },
        tail::Expr::IoOp(_rep_choice, io_op) => match io_op {
            flat::IoOp::Input => {}
            flat::IoOp::Output(local_id) => {
                move_info.add_borrow(*local_id);
            }
        },
        tail::Expr::Panic(_ret_type, _rep_choice, message) => {
            move_info.add_borrow(*message);
        }

        tail::Expr::ArrayLit(_rep_choice, _item_type, elem_ids) => {
            for elem_id in elem_ids {
                move_info.add_move(*elem_id);
            }
        }
        tail::Expr::BoolLit(_)
        | tail::Expr::ByteLit(_)
        | tail::Expr::IntLit(_)
        | tail::Expr::FloatLit(_) => {}

        tail::Expr::LetMany(_, _) => unreachable![],
        tail::Expr::Branch(_, _, _) => unreachable![],
    }

    move_info
}

// we need to add retain and releases
// every time we have a syntactic occurence of a variable, we need to add a retain
// we need to change branches to ifs
// we need to unwrap array literals

struct LowAstBuilder {
    offset: low::LocalId,
    exprs: Vec<(low::Type, low::Expr)>,
}

impl LowAstBuilder {
    fn new(offset: low::LocalId) -> LowAstBuilder {
        LowAstBuilder {
            offset,
            exprs: Vec::new(),
        }
    }

    fn child(&self) -> LowAstBuilder {
        LowAstBuilder::new(low::LocalId(self.offset.0 + self.exprs.len()))
    }

    fn add_expr(&mut self, type_: low::Type, expr: low::Expr) -> low::LocalId {
        #[cfg(debug_assertions)]
        {
            // TODO: Use 'matches' macro
            if let Some((_, low::Expr::TailCall(_, _))) = self.exprs.last() {
                panic!(
                    "The pass 'lower_strucures' tried to generate an expression immediately after \
                     a tail call, which violates the invariant that a tail call must be the last \
                     expression in its block."
                );
            }
        }

        let new_id = low::LocalId(self.offset.0 + self.exprs.len());
        self.exprs.push((type_, expr));
        new_id
    }

    fn build(self, final_local_id: low::LocalId) -> low::Expr {
        low::Expr::LetMany(self.exprs, final_local_id)
    }
}

// Used to lower constant conditions
fn build_comp(
    lhs: low::LocalId,
    rhs: low::LocalId,
    type_: first_ord::NumType,
    op: Intrinsic,
    builder: &mut LowAstBuilder,
) -> low::LocalId {
    let args = builder.add_expr(
        low::Type::Tuple(vec![low::Type::Num(type_), low::Type::Num(type_)]),
        low::Expr::Tuple(vec![lhs, rhs]),
    );

    builder.add_expr(low::Type::Bool, low::Expr::Intrinsic(op, args))
}

fn lower_condition(
    discrim: low::LocalId,
    condition: &special::Condition,
    builder: &mut LowAstBuilder,
    match_type: &low::Type,
    typedefs: &IdVec<special::CustomTypeId, low::Type>,
) -> low::LocalId {
    match condition {
        special::Condition::Any => builder.add_expr(low::Type::Bool, low::Expr::BoolLit(true)),
        special::Condition::Tuple(subconditions) => {
            let item_types = if let low::Type::Tuple(item_types) = match_type {
                item_types
            } else {
                unreachable![];
            };

            let subcondition_ids = item_types
                .iter()
                .zip(subconditions.iter())
                .enumerate()
                .map(|(index, (item_type, subcondition))| {
                    let item_id =
                        builder.add_expr(item_type.clone(), low::Expr::TupleField(discrim, index));
                    lower_condition(item_id, subcondition, builder, item_type, typedefs)
                })
                .collect::<Vec<low::LocalId>>();
            let if_expr =
                subcondition_ids
                    .into_iter()
                    .rfold(low::Expr::BoolLit(true), |accum, item| {
                        low::Expr::If(item, Box::new(accum), Box::new(low::Expr::BoolLit(false)))
                    });

            builder.add_expr(low::Type::Bool, if_expr)
        }
        special::Condition::Variant(variant_id, subcondition) => {
            let variant_id = first_ord::VariantId(variant_id.0);

            let variant_check = builder.add_expr(
                low::Type::Bool,
                low::Expr::CheckVariant(variant_id, discrim),
            );

            let mut new_builder = builder.child();
            let variant_types = if let low::Type::Variants(variant_types) = match_type {
                variant_types
            } else {
                unreachable![];
            };

            let variant_type = &variant_types[variant_id];

            let sub_discrim = new_builder.add_expr(
                variant_type.clone(),
                low::Expr::UnwrapVariant(
                    variant_types.clone(),
                    first_ord::VariantId(variant_id.0),
                    discrim,
                ),
            );

            let sub_cond_id = lower_condition(
                sub_discrim,
                subcondition,
                &mut new_builder,
                variant_type,
                typedefs,
            );

            builder.add_expr(
                low::Type::Bool,
                low::Expr::If(
                    variant_check,
                    Box::new(new_builder.build(sub_cond_id)),
                    Box::new(low::Expr::BoolLit(false)),
                ),
            )
        }
        special::Condition::Boxed(subcondition, content_type) => {
            let content = builder.add_expr(
                content_type.clone(),
                low::Expr::UnwrapBoxed(discrim, content_type.clone()),
            );

            lower_condition(content, subcondition, builder, content_type, typedefs)
        }
        special::Condition::Custom(custom_type_id, subcondition) => {
            let content_type = &typedefs[custom_type_id];

            let content = builder.add_expr(
                content_type.clone(),
                low::Expr::UnwrapCustom(*custom_type_id, discrim),
            );

            lower_condition(content, subcondition, builder, content_type, typedefs)
        }
        special::Condition::BoolConst(val) => {
            if *val {
                discrim
            } else {
                builder.add_expr(
                    low::Type::Bool,
                    low::Expr::If(
                        discrim,
                        Box::new(low::Expr::BoolLit(false)),
                        Box::new(low::Expr::BoolLit(true)),
                    ),
                )
            }
        }
        special::Condition::ByteConst(val) => {
            let val_id = builder.add_expr(
                low::Type::Num(first_ord::NumType::Byte),
                low::Expr::ByteLit(*val),
            );

            build_comp(
                val_id,
                discrim,
                first_ord::NumType::Byte,
                Intrinsic::EqByte,
                builder,
            )
        }
        special::Condition::IntConst(val) => {
            let val_id = builder.add_expr(
                low::Type::Num(first_ord::NumType::Int),
                low::Expr::IntLit(*val),
            );

            build_comp(
                val_id,
                discrim,
                first_ord::NumType::Int,
                Intrinsic::EqInt,
                builder,
            )
        }

        special::Condition::FloatConst(val) => {
            let val_id = builder.add_expr(
                low::Type::Num(first_ord::NumType::Float),
                low::Expr::FloatLit(*val),
            );

            build_comp(
                val_id,
                discrim,
                first_ord::NumType::Float,
                Intrinsic::EqFloat,
                builder,
            )
        }
    }
}

fn lower_branch(
    discrim: flat::LocalId,
    cases: &[(special::Condition, AnnotExpr)],
    result_type: &low::Type,
    move_info: &MoveInfo,
    context: &mut LocalContext<flat::LocalId, (special::Type, low::LocalId)>,
    builder: &mut LowAstBuilder,
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
) -> low::LocalId {
    match cases.first() {
        None => builder.add_expr(
            result_type.clone(),
            low::Expr::Unreachable(result_type.clone()),
        ),
        Some((cond, body)) => {
            let condition_id = lower_condition(
                context.local_binding(discrim).1,
                cond,
                builder,
                &context.local_binding(discrim).0,
                typedefs,
            );

            let mut then_builder = builder.child();
            for (var, move_count) in &body.move_info.move_info {
                let context_info = context.local_binding(*var);
                for _ in move_info.move_info[var]..*move_count {
                    then_builder.add_expr(
                        low::Type::Tuple(vec![]),
                        low::Expr::Retain(context_info.1, context_info.0.clone()),
                    );
                }
            }

            for (var, move_count) in &move_info.move_info {
                debug_assert!(*move_count == 0 || *move_count == 1);
                let context_info = context.local_binding(*var);
                if *move_count == 1 && !body.move_info.move_info.contains_key(&var) {
                    then_builder.add_expr(
                        low::Type::Tuple(vec![]),
                        low::Expr::Release(context_info.1, context_info.0.clone()),
                    );
                }
            }

            let then_final_id = lower_expr(body, result_type, context, &mut then_builder, typedefs);

            for (var, move_count) in &body.move_info.move_info {
                let branch_move_count = move_info.move_info[var];

                debug_assert!(branch_move_count == 0 || branch_move_count == 1);

                let context_info = context.local_binding(*var);
                if branch_move_count == 1 && *move_count == 0 {
                    then_builder.add_expr(
                        low::Type::Tuple(vec![]),
                        low::Expr::Release(context_info.1, context_info.0.clone()),
                    );
                }
            }
            let then_branch = then_builder.build(then_final_id);

            let mut else_builder = builder.child();
            let else_local_id = lower_branch(
                discrim,
                &cases[1..],
                result_type,
                move_info,
                context,
                &mut else_builder,
                typedefs,
            );

            let else_branch = else_builder.build(else_local_id);

            builder.add_expr(
                result_type.clone(),
                low::Expr::If(condition_id, Box::new(then_branch), Box::new(else_branch)),
            )
        }
    }
}

impl flat::LocalId {
    fn lookup_in(
        &self,
        context: &LocalContext<flat::LocalId, (special::Type, low::LocalId)>,
    ) -> low::LocalId {
        context.local_binding(*self).1
    }
}

fn lower_leaf(
    expr: &tail::Expr,
    result_type: &low::Type,
    context: &LocalContext<flat::LocalId, (special::Type, low::LocalId)>,
    builder: &mut LowAstBuilder,
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
) -> low::LocalId {
    match expr {
        tail::Expr::Local(local_id) => local_id.lookup_in(context),
        tail::Expr::Call(_purity, func_id, arg_id) => builder.add_expr(
            result_type.clone(),
            low::Expr::Call(low::CustomFuncId(func_id.0), arg_id.lookup_in(context)),
        ),
        tail::Expr::TailCall(tail_func_id, arg_id) => builder.add_expr(
            result_type.clone(),
            low::Expr::TailCall(*tail_func_id, arg_id.lookup_in(context)),
        ),
        tail::Expr::Tuple(elem_ids) => builder.add_expr(
            result_type.clone(),
            low::Expr::Tuple(
                elem_ids
                    .iter()
                    .map(|elem_id| elem_id.lookup_in(context))
                    .collect(),
            ),
        ),
        tail::Expr::TupleField(tuple_id, index) => {
            let tuple_elem_id = builder.add_expr(
                result_type.clone(),
                low::Expr::TupleField(tuple_id.lookup_in(context), *index),
            );
            builder.add_expr(
                low::Type::Tuple(vec![]),
                low::Expr::Retain(tuple_elem_id, result_type.clone()),
            );
            tuple_elem_id
        }
        tail::Expr::WrapBoxed(content_id, content_type) => builder.add_expr(
            result_type.clone(),
            low::Expr::WrapBoxed(content_id.lookup_in(context), content_type.clone()),
        ),
        tail::Expr::UnwrapBoxed(boxed_id, content_type) => {
            let content_id = builder.add_expr(
                result_type.clone(),
                low::Expr::UnwrapBoxed(boxed_id.lookup_in(context), content_type.clone()),
            );
            builder.add_expr(
                low::Type::Tuple(vec![]),
                low::Expr::Retain(content_id, result_type.clone()),
            );
            content_id
        }
        tail::Expr::WrapVariant(variants, variant_id, content_id) => builder.add_expr(
            result_type.clone(),
            low::Expr::WrapVariant(
                variants.clone(),
                first_ord::VariantId(variant_id.0),
                content_id.lookup_in(context),
            ),
        ),
        tail::Expr::UnwrapVariant(variant_id, content_id) => {
            builder.add_expr(result_type.clone(), {
                let variant_type = &context.local_binding(*content_id).0;
                let variants = if let special::Type::Variants(variants) = variant_type {
                    variants
                } else {
                    panic![];
                };

                low::Expr::UnwrapVariant(
                    variants.clone(),
                    first_ord::VariantId(variant_id.0),
                    content_id.lookup_in(context),
                )
            })
        }
        tail::Expr::WrapCustom(type_id, content_id) => builder.add_expr(
            low::Type::Custom(*type_id),
            low::Expr::WrapCustom(*type_id, content_id.lookup_in(context)),
        ),
        tail::Expr::UnwrapCustom(type_id, wrapped_id) => builder.add_expr(
            typedefs[type_id].clone(),
            low::Expr::UnwrapCustom(*type_id, wrapped_id.lookup_in(context)),
        ),
        tail::Expr::Intrinsic(intr, local_id) => builder.add_expr(
            result_type.clone(),
            low::Expr::Intrinsic(*intr, local_id.lookup_in(context)),
        ),
        tail::Expr::ArrayOp(rep, item_type, array_op) => {
            let array_expr = match array_op {
                unif::ArrayOp::Item(array_id, index_id) => {
                    low::ArrayOp::Item(array_id.lookup_in(context), index_id.lookup_in(context))
                }
                unif::ArrayOp::Len(array_id) => low::ArrayOp::Len(array_id.lookup_in(context)),
                unif::ArrayOp::Push(array_id, item_id) => {
                    low::ArrayOp::Push(array_id.lookup_in(context), item_id.lookup_in(context))
                }
                unif::ArrayOp::Pop(array_id) => low::ArrayOp::Pop(array_id.lookup_in(context)),
                unif::ArrayOp::Replace(array_id, item_id) => {
                    low::ArrayOp::Replace(array_id.lookup_in(context), item_id.lookup_in(context))
                }
            };
            builder.add_expr(
                result_type.clone(),
                low::Expr::ArrayOp(*rep, item_type.clone(), array_expr),
            )
        }
        tail::Expr::IoOp(rep, io_type) => builder.add_expr(
            result_type.clone(),
            low::Expr::IoOp(
                *rep,
                match io_type {
                    flat::IoOp::Input => low::IoOp::Input,
                    flat::IoOp::Output(output_id) => {
                        low::IoOp::Output(output_id.lookup_in(context))
                    }
                },
            ),
        ),
        tail::Expr::Panic(ret_type, rep, message) => builder.add_expr(
            result_type.clone(),
            low::Expr::Panic(ret_type.clone(), *rep, message.lookup_in(context)),
        ),
        tail::Expr::ArrayLit(rep, elem_type, elems) => {
            let mut result_id = builder.add_expr(
                result_type.clone(),
                low::Expr::ArrayOp(*rep, elem_type.clone(), low::ArrayOp::New()),
            );

            for elem_id in elems {
                result_id = builder.add_expr(
                    result_type.clone(),
                    low::Expr::ArrayOp(
                        *rep,
                        elem_type.clone(),
                        low::ArrayOp::Push(result_id, elem_id.lookup_in(context)),
                    ),
                );
            }

            result_id
        }
        tail::Expr::BoolLit(val) => builder.add_expr(result_type.clone(), low::Expr::BoolLit(*val)),
        tail::Expr::ByteLit(val) => builder.add_expr(result_type.clone(), low::Expr::ByteLit(*val)),
        tail::Expr::IntLit(val) => builder.add_expr(result_type.clone(), low::Expr::IntLit(*val)),
        tail::Expr::FloatLit(val) => {
            builder.add_expr(result_type.clone(), low::Expr::FloatLit(*val))
        }

        tail::Expr::Branch(_, _, _) | tail::Expr::LetMany(_, _) => {
            unreachable![];
        }
    }
}

fn lower_expr(
    expr: &AnnotExpr,
    result_type: &low::Type,
    context: &mut LocalContext<flat::LocalId, (special::Type, low::LocalId)>,
    builder: &mut LowAstBuilder,
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
) -> low::LocalId {
    match &expr.kind {
        AnnotExprKind::LetMany(bindings, final_local_id) => {
            context.with_scope(|subcontext| {
                for (type_, binding, future_usages) in bindings {
                    // emit retains
                    for (var, move_count) in &binding.move_info.move_info {
                        if *move_count != 0 {
                            let retain_count = if future_usages.future_usages.contains(var) {
                                *move_count
                            } else {
                                *move_count - 1
                            };

                            let var_info = subcontext.local_binding(*var);

                            for _retain in 0..retain_count {
                                builder.add_expr(
                                    low::Type::Tuple(vec![]),
                                    low::Expr::Retain(var_info.1, var_info.0.clone()),
                                );
                            }
                        }
                    }

                    // emit expressions
                    let low_binding_id = lower_expr(binding, &type_, subcontext, builder, typedefs);
                    let flat_binding_id = subcontext.add_local((type_.clone(), low_binding_id));

                    // emit releases
                    for (var, move_count) in &binding.move_info.move_info {
                        let var_info = subcontext.local_binding(*var);
                        if *move_count == 0 && !future_usages.future_usages.contains(var) {
                            builder.add_expr(
                                low::Type::Tuple(vec![]),
                                low::Expr::Release(var_info.1, var_info.0.clone()),
                            );
                        }
                    }

                    if !future_usages.future_usages.contains(&flat_binding_id) {
                        builder.add_expr(
                            low::Type::Tuple(vec![]),
                            low::Expr::Release(
                                subcontext.local_binding(flat_binding_id).1,
                                type_.clone(),
                            ),
                        );
                    }
                }

                if expr.move_info.move_info.get(final_local_id) == Some(&0) {
                    let var_info = subcontext.local_binding(*final_local_id);
                    builder.add_expr(
                        low::Type::Tuple(vec![]),
                        low::Expr::Retain(var_info.1, var_info.0.clone()),
                    );
                }

                subcontext.local_binding(*final_local_id).1
            })
        }
        AnnotExprKind::Branch(discrim, cases, result_type) => lower_branch(
            *discrim,
            cases,
            result_type,
            &expr.move_info,
            context,
            builder,
            typedefs,
        ),
        AnnotExprKind::Leaf(leaf) => lower_leaf(leaf, result_type, context, builder, typedefs),
    }
}

fn lower_function_body(
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
    arg_type: &special::Type,
    ret_type: &special::Type,
    body: tail::Expr,
) -> low::Expr {
    let future_usages = FutureUsageInfo {
        future_usages: OrdSet::new(),
    };
    let annotated_body = annotate_expr(body, &future_usages, 1);

    let mut builder = LowAstBuilder::new(low::LocalId(1));

    for _ in 1..*annotated_body
        .move_info
        .move_info
        .get(&flat::ARG_LOCAL)
        .unwrap_or(&0)
    {
        builder.add_expr(
            low::Type::Tuple(vec![]),
            low::Expr::Retain(low::ARG_LOCAL, arg_type.clone()),
        );
    }

    let mut context = LocalContext::new();

    context.add_local((arg_type.clone(), low::ARG_LOCAL));

    if !annotated_body
        .move_info
        .move_info
        .contains_key(&flat::ARG_LOCAL)
    {
        // If the argument is unused, it is important that we release it *before* the main body of
        // the function, so as to not interfere with tail calls.
        builder.add_expr(
            low::Type::Tuple(vec![]),
            low::Expr::Release(low::ARG_LOCAL, arg_type.clone()),
        );
    }

    let final_local_id = lower_expr(
        &annotated_body,
        ret_type,
        &mut context,
        &mut builder,
        typedefs,
    );

    if annotated_body.move_info.move_info.get(&flat::ARG_LOCAL) == Some(&0) {
        builder.add_expr(
            low::Type::Tuple(vec![]),
            low::Expr::Release(low::ARG_LOCAL, arg_type.clone()),
        );
    }

    builder.build(final_local_id)
}

fn lower_function(
    func: tail::FuncDef,
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
) -> low::FuncDef {
    // Appease the borrow checker
    let ret_type = &func.ret_type;

    let tail_funcs = func.tail_funcs.into_mapped(|_, tail_func| low::TailFunc {
        arg_type: tail_func.arg_type.clone(),
        body: lower_function_body(typedefs, &tail_func.arg_type, ret_type, tail_func.body),
        profile_point: tail_func.profile_point,
    });

    let body = lower_function_body(typedefs, &func.arg_type, &func.ret_type, func.body);

    low::FuncDef {
        tail_funcs,
        arg_type: func.arg_type,
        ret_type: func.ret_type,
        body,
        profile_point: func.profile_point,
    }
}

pub fn lower_structures(program: tail::Program) -> low::Program {
    let typedefs = program.custom_types;

    let lowered_funcs = program
        .funcs
        .items
        .into_iter()
        .map(|func| lower_function(func, &typedefs))
        .collect();

    low::Program {
        mod_symbols: program.mod_symbols.clone(),
        custom_types: typedefs,
        funcs: IdVec::from_items(lowered_funcs),
        profile_points: program.profile_points,
        main: low::CustomFuncId(program.main.0),
    }
}
