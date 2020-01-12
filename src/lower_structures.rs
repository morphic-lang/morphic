use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::low_ast as low;
use crate::data::repr_specialized_ast as special;
use crate::data::repr_unified_ast as unif;
use crate::util::graph::{self, Graph};
use crate::util::id_vec::IdVec;
use crate::util::local_context::LocalContext;
use im_rc::OrdMap;
use im_rc::OrdSet;
use std::collections::BTreeSet;

fn lower_type(type_: &special::Type) -> low::Type {
    match type_ {
        special::Type::Bool => low::Type::Bool,
        special::Type::Num(num) => low::Type::Num(*num),
        special::Type::Array(rep, item_type) => {
            low::Type::Array(*rep, Box::new(lower_type(item_type)))
        }
        special::Type::HoleArray(rep, item_type) => {
            low::Type::HoleArray(*rep, Box::new(lower_type(item_type)))
        }
        special::Type::Tuple(types) => low::Type::Tuple(
            types
                .iter()
                .map(|item_type| lower_type(item_type))
                .collect(),
        ),
        special::Type::Variants(variants) => low::Type::Variants(IdVec::from_items(
            variants
                .items
                .iter()
                .map(|item_type| lower_type(item_type))
                .collect(),
        )),
        special::Type::Custom(id) => low::Type::Custom(*id),
    }
}

fn add_size_deps(type_: &special::Type, deps: &mut BTreeSet<special::CustomTypeId>) {
    match type_ {
        special::Type::Bool | special::Type::Num(_) => {}

        special::Type::Array(_, _) | special::Type::HoleArray(_, _) => {}

        special::Type::Tuple(items) => {
            for item in items {
                add_size_deps(item, deps)
            }
        }

        special::Type::Variants(variants) => {
            for (_, variant) in variants {
                add_size_deps(variant, deps)
            }
        }

        special::Type::Custom(custom) => {
            deps.insert(*custom);
        }
    }
}

#[derive(Clone, Debug)]
struct BoxInfo {
    scc: BTreeSet<special::CustomTypeId>,
}

fn find_box_infos(
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
) -> IdVec<special::CustomTypeId, BoxInfo> {
    let size_deps = Graph {
        edges_out: typedefs.map(|_, def| {
            let mut deps = BTreeSet::new();
            add_size_deps(def, &mut deps);
            deps.into_iter().collect()
        }),
    };

    let sccs = graph::strongly_connected(&size_deps);

    let mut maybe_box_infos = IdVec::from_items(vec![None; typedefs.len()]);

    for scc_vec in sccs {
        let scc: BTreeSet<_> = scc_vec.iter().cloned().collect();

        for custom_type in &scc {
            maybe_box_infos[custom_type] = Some(BoxInfo { scc: scc.clone() });
        }
    }

    maybe_box_infos.into_mapped(|_, value| value.unwrap())
}

fn needs_boxing(boxinfo: &BoxInfo, type_: &special::Type) -> bool {
    match type_ {
        special::Type::Bool => false,
        special::Type::Num(_num_type) => false,
        special::Type::Array(_rep, _item_type) => false,
        special::Type::HoleArray(_rep, _item_type) => false,
        special::Type::Tuple(types) => types
            .iter()
            .any(|item_type| needs_boxing(boxinfo, item_type)),
        special::Type::Variants(variants) => variants
            .iter()
            .any(|(_, item_type)| needs_boxing(boxinfo, item_type)),
        special::Type::Custom(id) => boxinfo.scc.contains(id),
    }
}

fn box_type(boxinfo: &BoxInfo, type_: &special::Type) -> low::Type {
    match type_ {
        special::Type::Variants(variants) => low::Type::Variants(IdVec::from_items(
            variants
                .items
                .iter()
                .map(|variant_type| box_type(boxinfo, variant_type))
                .collect(),
        )),
        _ => {
            if needs_boxing(boxinfo, type_) {
                low::Type::Boxed(Box::new(lower_type(type_)))
            } else {
                lower_type(type_)
            }
        }
    }
}

fn find_boxed_types(
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
) -> IdVec<special::CustomTypeId, low::Type> {
    let box_infos = find_box_infos(typedefs);

    typedefs.map(|id, typedef| box_type(&box_infos[id], typedef))
}

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
    Leaf(special::Expr),
}

fn annotate_expr(
    expr: special::Expr,
    future_usages: &FutureUsageInfo,
    ids_in_scope: usize,
) -> AnnotExpr {
    match expr {
        special::Expr::LetMany(exprs, final_local) => {
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
                let annotated_binding =
                    annotate_expr(binding, &current_future_usages, ids_in_scope + index);

                let binding_move_info = annotated_binding.move_info.clone();

                new_bindings_reversed.push((
                    type_,
                    annotated_binding,
                    current_future_usages.clone(),
                ));

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

                current_future_usages
                    .future_usages
                    .remove(&flat::LocalId(index + ids_in_scope));
            }

            let mut new_bindings = new_bindings_reversed;
            new_bindings.reverse();

            AnnotExpr {
                kind: AnnotExprKind::LetMany(new_bindings, final_local),
                move_info: let_move_info,
            }
        }

        special::Expr::Branch(discrim, cases, res_type) => {
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

fn count_moves(expr: &special::Expr) -> MoveInfo {
    let mut move_info = MoveInfo {
        move_info: OrdMap::new(),
    };

    match expr {
        special::Expr::Local(local_id) => move_info.add_move(*local_id),
        special::Expr::Call(_purity, _func_id, local_id) => move_info.add_move(*local_id),

        special::Expr::Tuple(local_ids) => {
            for local_id in local_ids {
                move_info.add_move(*local_id);
            }
        }
        special::Expr::TupleField(local_id, _index) => move_info.add_borrow(*local_id),
        special::Expr::WrapVariant(_variants, _variant_id, local_id) => {
            move_info.add_move(*local_id);
        }

        special::Expr::UnwrapVariant(_variant_id, local_id) => move_info.add_move(*local_id),
        special::Expr::WrapCustom(_type_id, local_id) => move_info.add_move(*local_id),
        special::Expr::UnwrapCustom(_type_id, local_id) => move_info.add_move(*local_id),

        special::Expr::ArithOp(arith_op) => match arith_op {
            flat::ArithOp::Op(_, _, local_id1, local_id2)
            | flat::ArithOp::Cmp(_, _, local_id1, local_id2) => {
                move_info.add_move(*local_id1);
                move_info.add_move(*local_id2);
            }
            flat::ArithOp::Negate(_num_type, local_id) => {
                move_info.add_move(*local_id);
            }
        },
        special::Expr::ArrayOp(_rep_choice, _item_type, array_op) => match array_op {
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
        special::Expr::IoOp(_rep_choice, io_op) => match io_op {
            flat::IOOp::Input => {}
            flat::IOOp::Output(local_id) => {
                move_info.add_borrow(*local_id);
            }
        },

        special::Expr::ArrayLit(_rep_choice, _item_type, elem_ids) => {
            for elem_id in elem_ids {
                move_info.add_move(*elem_id);
            }
        }
        special::Expr::BoolLit(_)
        | special::Expr::ByteLit(_)
        | special::Expr::IntLit(_)
        | special::Expr::FloatLit(_) => {}

        special::Expr::LetMany(_, _) => unreachable![],
        special::Expr::Branch(_, _, _) => unreachable![],
    }

    move_info
}

// we need to add retain and releases
// every time we have a syntactic occurence of a variable, we need to add a retain
// we need to change branches to ifs
// we need to unwrap array literals
// we need to add boxing/unboxing in places

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
        let new_id = low::LocalId(self.offset.0 + self.exprs.len());
        self.exprs.push((type_, expr));
        new_id
    }

    fn build(self, final_local_id: low::LocalId) -> low::Expr {
        low::Expr::LetMany(self.exprs, final_local_id)
    }
}

fn lower_condition(
    discrim: low::LocalId,
    condition: &special::Condition,
    builder: &mut LowAstBuilder,
    match_type: &low::Type,
    boxed_typedefs: &IdVec<special::CustomTypeId, low::Type>,
) -> low::LocalId {
    if let low::Type::Boxed(boxed_type) = match_type {
        let unboxed_id = builder.add_expr((**boxed_type).clone(), low::Expr::UnwrapBoxed(discrim));
        return lower_condition(unboxed_id, condition, builder, boxed_type, boxed_typedefs);
    }

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
                    lower_condition(item_id, subcondition, builder, item_type, boxed_typedefs)
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
            let variant_id = low::VariantId(variant_id.0);

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
                low::Expr::UnwrapVariant(low::VariantId(variant_id.0), discrim),
            );

            let sub_cond_id = lower_condition(
                sub_discrim,
                subcondition,
                &mut new_builder,
                variant_type,
                boxed_typedefs,
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
        special::Condition::Custom(custom_type_id, subcondition) => {
            let content_type = &boxed_typedefs[custom_type_id];

            let content = builder.add_expr(
                content_type.clone(),
                low::Expr::UnwrapCustom(*custom_type_id, discrim),
            );

            lower_condition(content, subcondition, builder, content_type, boxed_typedefs)
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

            builder.add_expr(
                low::Type::Bool,
                low::Expr::ArithOp(low::ArithOp::Cmp(
                    first_ord::NumType::Byte,
                    first_ord::Comparison::Equal,
                    val_id,
                    discrim,
                )),
            )
        }
        special::Condition::IntConst(val) => {
            let val_id = builder.add_expr(
                low::Type::Num(first_ord::NumType::Int),
                low::Expr::IntLit(*val),
            );

            builder.add_expr(
                low::Type::Bool,
                low::Expr::ArithOp(low::ArithOp::Cmp(
                    first_ord::NumType::Int,
                    first_ord::Comparison::Equal,
                    val_id,
                    discrim,
                )),
            )
        }

        special::Condition::FloatConst(val) => {
            let val_id = builder.add_expr(
                low::Type::Num(first_ord::NumType::Float),
                low::Expr::FloatLit(*val),
            );

            builder.add_expr(
                low::Type::Bool,
                low::Expr::ArithOp(low::ArithOp::Cmp(
                    first_ord::NumType::Float,
                    first_ord::Comparison::Equal,
                    val_id,
                    discrim,
                )),
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
    boxed_typedefs: &IdVec<special::CustomTypeId, low::Type>,
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
                &lower_type(&context.local_binding(discrim).0),
                boxed_typedefs,
            );

            let mut then_builder = builder.child();
            for (var, move_count) in &body.move_info.move_info {
                for _ in move_info.move_info[var]..*move_count {
                    then_builder.add_expr(
                        low::Type::Tuple(vec![]),
                        low::Expr::Retain(context.local_binding(*var).1),
                    );
                }
            }

            for (var, move_count) in &move_info.move_info {
                debug_assert!(*move_count == 0 || *move_count == 1);
                if *move_count == 1 && !body.move_info.move_info.contains_key(&var) {
                    then_builder.add_expr(
                        low::Type::Tuple(vec![]),
                        low::Expr::Release(context.local_binding(*var).1),
                    );
                }
            }

            let then_final_id = lower_expr(
                body,
                result_type,
                context,
                &mut then_builder,
                typedefs,
                boxed_typedefs,
            );

            for (var, move_count) in &body.move_info.move_info {
                let branch_move_count = move_info.move_info[var];

                debug_assert!(branch_move_count == 0 || branch_move_count == 1);
                if branch_move_count == 1 && *move_count == 0 {
                    then_builder.add_expr(
                        low::Type::Tuple(vec![]),
                        low::Expr::Release(context.local_binding(*var).1),
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
                boxed_typedefs,
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

fn coerce_variants(
    local_id: low::LocalId,
    original_variants: &IdVec<low::VariantId, low::Type>,
    target_variants: &IdVec<low::VariantId, low::Type>,
    offset: usize,
    builder: &mut LowAstBuilder,
    coerce: impl for<'a> Fn(
        low::LocalId,
        &'a low::Type,
        &'a low::Type,
        &'a mut LowAstBuilder,
    ) -> low::LocalId,
) -> low::LocalId {
    debug_assert!(offset <= target_variants.len());

    let result_type = low::Type::Variants(target_variants.clone());
    if offset == target_variants.len() {
        builder.add_expr(result_type.clone(), low::Expr::Unreachable(result_type))
    } else {
        let variant_id = low::VariantId(offset);
        let target_variant_type = &target_variants[variant_id];
        let original_variant_type = &original_variants[variant_id];

        let is_this_variant = builder.add_expr(
            low::Type::Bool,
            low::Expr::CheckVariant(variant_id, local_id),
        );

        let mut then_builder = builder.child();

        let unwrapped_variant_id = then_builder.add_expr(
            original_variant_type.clone(),
            low::Expr::UnwrapVariant(variant_id, local_id),
        );

        let boxed_content_unwrapped = coerce(
            unwrapped_variant_id,
            original_variant_type,
            target_variant_type,
            &mut then_builder,
        );

        let boxed_then_id = then_builder.add_expr(
            result_type.clone(),
            low::Expr::WrapVariant(target_variants.clone(), variant_id, boxed_content_unwrapped),
        );

        let mut else_builder = builder.child();
        let boxed_else_id = coerce_variants(
            local_id,
            original_variants,
            target_variants,
            offset + 1,
            &mut else_builder,
            coerce,
        );
        builder.add_expr(
            result_type,
            low::Expr::If(
                is_this_variant,
                Box::new(then_builder.build(boxed_then_id)),
                Box::new(else_builder.build(boxed_else_id)),
            ),
        )
    }
}

fn box_content(
    local_id: low::LocalId,
    original_type: &low::Type,
    target_type: &low::Type,
    builder: &mut LowAstBuilder,
) -> low::LocalId {
    match target_type {
        low::Type::Boxed(_inner_type) => {
            builder.add_expr(target_type.clone(), low::Expr::WrapBoxed(local_id))
        }
        low::Type::Variants(target_variants) => {
            if let low::Type::Variants(original_variants) = original_type {
                coerce_variants(
                    local_id,
                    original_variants,
                    target_variants,
                    0,
                    builder,
                    box_content,
                )
            } else {
                unreachable![];
            }
        }
        _ => local_id,
    }
}

fn unbox_content(
    local_id: low::LocalId,
    original_type: &low::Type,
    target_type: &low::Type,
    builder: &mut LowAstBuilder,
) -> low::LocalId {
    match original_type {
        low::Type::Boxed(inner_type) => {
            let inner_id =
                builder.add_expr((**inner_type).clone(), low::Expr::UnwrapBoxed(local_id));
            builder.add_expr(low::Type::Tuple(vec![]), low::Expr::Release(inner_id));
            inner_id
        }
        low::Type::Variants(original_variants) => {
            if let low::Type::Variants(target_variants) = target_type {
                coerce_variants(
                    local_id,
                    original_variants,
                    target_variants,
                    0,
                    builder,
                    unbox_content,
                )
            } else {
                unreachable![];
            }
        }
        _ => local_id,
    }
}

fn lower_leaf(
    expr: &special::Expr,
    result_type: &low::Type,
    context: &LocalContext<flat::LocalId, (special::Type, low::LocalId)>,
    builder: &mut LowAstBuilder,
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
    boxed_typedefs: &IdVec<special::CustomTypeId, low::Type>,
) -> low::LocalId {
    match expr {
        special::Expr::Local(local_id) => local_id.lookup_in(context),
        special::Expr::Call(_purity, func_id, arg_id) => builder.add_expr(
            result_type.clone(),
            low::Expr::Call(low::CustomFuncId(func_id.0), arg_id.lookup_in(context)),
        ),
        special::Expr::Tuple(elem_ids) => builder.add_expr(
            result_type.clone(),
            low::Expr::Tuple(
                elem_ids
                    .iter()
                    .map(|elem_id| elem_id.lookup_in(context))
                    .collect(),
            ),
        ),
        special::Expr::TupleField(tuple_id, index) => {
            let tuple_elem_id = builder.add_expr(
                result_type.clone(),
                low::Expr::TupleField(tuple_id.lookup_in(context), *index),
            );
            builder.add_expr(low::Type::Tuple(vec![]), low::Expr::Retain(tuple_elem_id));
            tuple_elem_id
        }
        special::Expr::WrapVariant(variants, variant_id, content_id) => builder.add_expr(
            result_type.clone(),
            low::Expr::WrapVariant(
                IdVec::from_items(
                    variants
                        .iter()
                        .map(|(_index, variant)| lower_type(variant))
                        .collect(),
                ),
                low::VariantId(variant_id.0),
                content_id.lookup_in(context),
            ),
        ),
        special::Expr::UnwrapVariant(variant_id, content_id) => builder.add_expr(
            result_type.clone(),
            low::Expr::UnwrapVariant(low::VariantId(variant_id.0), content_id.lookup_in(context)),
        ),
        special::Expr::WrapCustom(type_id, content_id) => {
            let unboxed_type = lower_type(&typedefs[type_id]);
            let boxed_type = &boxed_typedefs[type_id];

            let boxed_content_id = box_content(
                content_id.lookup_in(context),
                &unboxed_type,
                boxed_type,
                builder,
            );

            builder.add_expr(
                low::Type::Custom(*type_id),
                low::Expr::WrapCustom(*type_id, boxed_content_id),
            )
        }
        special::Expr::UnwrapCustom(type_id, content_id) => {
            let unboxed_type = lower_type(&typedefs[type_id]);
            let boxed_type = &boxed_typedefs[type_id];

            let unwrapped_id = builder.add_expr(
                boxed_type.clone(),
                low::Expr::UnwrapCustom(*type_id, content_id.lookup_in(context)),
            );

            unbox_content(unwrapped_id, boxed_type, &unboxed_type, builder)
        }
        special::Expr::ArithOp(arith_op) => {
            let arith_expr = match arith_op {
                flat::ArithOp::Op(num_type, bin_op, local_id1, local_id2) => low::ArithOp::Op(
                    *num_type,
                    *bin_op,
                    local_id1.lookup_in(context),
                    local_id2.lookup_in(context),
                ),
                flat::ArithOp::Cmp(num_type, comp, local_id1, local_id2) => low::ArithOp::Cmp(
                    *num_type,
                    *comp,
                    local_id1.lookup_in(context),
                    local_id2.lookup_in(context),
                ),
                flat::ArithOp::Negate(num_type, local_id) => {
                    low::ArithOp::Negate(*num_type, local_id.lookup_in(context))
                }
            };
            builder.add_expr(result_type.clone(), low::Expr::ArithOp(arith_expr))
        }

        special::Expr::ArrayOp(rep, item_type, array_op) => {
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
                low::Expr::ArrayOp(*rep, lower_type(item_type), array_expr),
            )
        }
        special::Expr::IoOp(rep, io_type) => builder.add_expr(
            result_type.clone(),
            low::Expr::IoOp(
                *rep,
                match io_type {
                    flat::IOOp::Input => low::IoOp::Input,
                    flat::IOOp::Output(output_id) => {
                        low::IoOp::Output(output_id.lookup_in(context))
                    }
                },
            ),
        ),
        special::Expr::ArrayLit(rep, elem_type, elems) => {
            let mut result_id = builder.add_expr(
                result_type.clone(),
                low::Expr::ArrayOp(*rep, lower_type(elem_type), low::ArrayOp::New()),
            );

            for elem_id in elems {
                result_id = builder.add_expr(
                    result_type.clone(),
                    low::Expr::ArrayOp(
                        *rep,
                        lower_type(elem_type),
                        low::ArrayOp::Push(result_id, elem_id.lookup_in(context)),
                    ),
                );
            }

            result_id
        }
        special::Expr::BoolLit(val) => {
            builder.add_expr(result_type.clone(), low::Expr::BoolLit(*val))
        }
        special::Expr::ByteLit(val) => {
            builder.add_expr(result_type.clone(), low::Expr::ByteLit(*val))
        }
        special::Expr::IntLit(val) => {
            builder.add_expr(result_type.clone(), low::Expr::IntLit(*val))
        }
        special::Expr::FloatLit(val) => {
            builder.add_expr(result_type.clone(), low::Expr::FloatLit(*val))
        }

        special::Expr::Branch(_, _, _) | special::Expr::LetMany(_, _) => {
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
    boxed_typedefs: &IdVec<special::CustomTypeId, low::Type>,
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

                            for _retain in 0..retain_count {
                                builder.add_expr(
                                    low::Type::Tuple(vec![]),
                                    low::Expr::Retain(subcontext.local_binding(*var).1),
                                );
                            }
                        }
                    }

                    // emit expressions
                    let low_binding_id = lower_expr(
                        binding,
                        &lower_type(type_),
                        subcontext,
                        builder,
                        typedefs,
                        boxed_typedefs,
                    );
                    let flat_binding_id = subcontext.add_local((type_.clone(), low_binding_id));

                    // emit releases
                    for (var, move_count) in &binding.move_info.move_info {
                        if *move_count == 0 && !future_usages.future_usages.contains(var) {
                            builder.add_expr(
                                low::Type::Tuple(vec![]),
                                low::Expr::Release(subcontext.local_binding(*var).1),
                            );
                        }
                    }

                    if !future_usages.future_usages.contains(&flat_binding_id) {
                        builder.add_expr(
                            low::Type::Tuple(vec![]),
                            low::Expr::Release(subcontext.local_binding(flat_binding_id).1),
                        );
                    }
                }

                if expr.move_info.move_info.get(final_local_id) == Some(&0) {
                    builder.add_expr(
                        low::Type::Tuple(vec![]),
                        low::Expr::Retain(subcontext.local_binding(*final_local_id).1),
                    );
                }

                subcontext.local_binding(*final_local_id).1
            })
        }
        AnnotExprKind::Branch(discrim, cases, result_type) => lower_branch(
            *discrim,
            cases,
            &lower_type(result_type),
            &expr.move_info,
            context,
            builder,
            typedefs,
            boxed_typedefs,
        ),
        AnnotExprKind::Leaf(leaf) => lower_leaf(
            leaf,
            result_type,
            context,
            builder,
            typedefs,
            boxed_typedefs,
        ),
    }
}

fn lower_function(
    func: special::FuncDef,
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
    boxed_typedefs: &IdVec<special::CustomTypeId, low::Type>,
) -> low::FuncDef {
    let future_usages = FutureUsageInfo {
        future_usages: OrdSet::new(),
    };
    let annotated_body = annotate_expr(func.body, &future_usages, 1);

    let mut builder = LowAstBuilder::new(low::LocalId(1));

    for _ in 1..*annotated_body
        .move_info
        .move_info
        .get(&flat::LocalId(0))
        .unwrap_or(&0)
    {
        builder.add_expr(low::Type::Tuple(vec![]), low::Expr::Retain(low::LocalId(0)));
    }

    let mut context = LocalContext::new();

    context.add_local((func.arg_type.clone(), low::LocalId(0)));

    let final_local_id = lower_expr(
        &annotated_body,
        &lower_type(&func.ret_type),
        &mut context,
        &mut builder,
        typedefs,
        boxed_typedefs,
    );

    if annotated_body
        .move_info
        .move_info
        .get(&flat::LocalId(0))
        .unwrap_or(&0)
        == &0
    {
        builder.add_expr(
            low::Type::Tuple(vec![]),
            low::Expr::Release(low::LocalId(0)),
        );
    }

    low::FuncDef {
        arg_type: lower_type(&func.arg_type),
        ret_type: lower_type(&func.ret_type),
        body: builder.build(final_local_id),
    }
}

pub fn lower_structures(program: special::Program) -> low::Program {
    let typedefs = program.custom_types;
    let boxed_typedefs = find_boxed_types(&typedefs);

    let lowered_funcs = program
        .funcs
        .items
        .into_iter()
        .map(|func| lower_function(func, &typedefs, &boxed_typedefs))
        .collect();

    low::Program {
        custom_types: boxed_typedefs,
        funcs: IdVec::from_items(lowered_funcs),
        main: low::CustomFuncId(program.main.0),
    }
}
