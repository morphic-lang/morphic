//! In this pass we:
//! - Guard custom types to improve the precision of borrow inference.
//! - Lower `Condition`s to `If`s to reduce the complexity of borrow inference.

use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast::{self as first_ord, CustomTypeId};
use crate::data::flat_ast::{self as flat};
use crate::data::guarded_ast::{self as guard, CanGuard, GuardPhase, RecipeContent, UnfoldRecipe};
use crate::data::intrinsics::Intrinsic;
use crate::data::metadata::Metadata;
use crate::pretty_print::utils::FuncRenderer;
use crate::util::collection_ext::VecExt;
use crate::util::let_builder::{FromBindings, LetManyBuilder};
use crate::util::local_context::LocalContext;
use id_collections::{Count, IdMap, IdVec};
use id_graph_sccs::{SccKind, Sccs};
use std::collections::BTreeSet;

impl FromBindings for guard::Expr {
    type LocalId = guard::LocalId;
    type Type = guard::Type;

    fn from_bindings(bindings: Vec<(Self::Type, Self, Metadata)>, ret: Self::LocalId) -> Self {
        guard::Expr::LetMany(bindings, ret)
    }
}

#[derive(Clone, Debug)]
struct LocalInfo {
    new_id: guard::LocalId,
    orig_type: anon::Type, // pre-guarded type
}

type Builder = LetManyBuilder<guard::Expr>;
type Context = LocalContext<flat::LocalId, LocalInfo>;

fn add_size_deps(ty: &anon::Type, deps: &mut BTreeSet<CustomTypeId>) {
    match ty {
        anon::Type::Bool
        | anon::Type::Num(_)
        | anon::Type::Array(_)
        | anon::Type::HoleArray(_)
        | anon::Type::Boxed(_) => {}
        anon::Type::Tuple(tys) => {
            for ty in tys {
                add_size_deps(ty, deps);
            }
        }
        anon::Type::Variants(tys) => {
            for (_, ty) in tys {
                add_size_deps(ty, deps);
            }
        }
        anon::Type::Custom(id) => {
            deps.insert(*id);
        }
    }
}

fn can_guard_customs(customs: &flat::CustomTypes) -> IdVec<CustomTypeId, CanGuard> {
    let sccs: Sccs<usize, _> = id_graph_sccs::find_components(customs.types.count(), |id| {
        let mut deps = BTreeSet::new();
        add_size_deps(&customs.types[id].content, &mut deps);
        deps
    });

    let mut can_guard = IdMap::new();
    for (_, component) in &sccs {
        let can_guard_component = match component.kind {
            SccKind::Acyclic => CanGuard::Yes,
            SccKind::Cyclic => CanGuard::No,
        };
        for id in component.nodes {
            can_guard.insert(*id, can_guard_component);
        }
    }

    can_guard.to_id_vec(customs.types.count())
}

fn guard(
    customs: &flat::CustomTypes,
    can_guard: &IdVec<CustomTypeId, CanGuard>,
    phase: GuardPhase,
    ty: &anon::Type,
) -> guard::Type {
    match ty {
        anon::Type::Bool => guard::Type::Bool,
        anon::Type::Num(num_ty) => guard::Type::Num(*num_ty),
        anon::Type::Tuple(tys) => {
            let tys: Vec<_> = tys
                .iter()
                .map(|ty| guard(customs, can_guard, phase, ty))
                .collect();
            guard::Type::Tuple(tys)
        }
        anon::Type::Variants(tys) => {
            let tys: Vec<_> = tys
                .values()
                .map(|ty| guard(customs, can_guard, phase, ty))
                .collect();
            guard::Type::Variants(IdVec::from_vec(tys))
        }
        anon::Type::Custom(id) => {
            let custom = &customs.types[*id];
            let kind = customs.sccs.component(custom.scc).kind;
            let should_guard = phase.should_guard(can_guard[*id], kind, custom.scc);

            if should_guard {
                guard(
                    customs,
                    can_guard,
                    GuardPhase::Direct(custom.scc),
                    &custom.content,
                )
            } else {
                guard::Type::Custom(*id)
            }
        }
        anon::Type::Array(ty) => {
            let ty = guard(customs, can_guard, phase.indirect(), ty);
            guard::Type::Array(Box::new(ty))
        }
        anon::Type::HoleArray(ty) => {
            let ty = guard(customs, can_guard, phase.indirect(), ty);
            guard::Type::HoleArray(Box::new(ty))
        }
        anon::Type::Boxed(ty) => {
            let ty = guard(customs, can_guard, phase.indirect(), ty);
            guard::Type::Boxed(Box::new(ty))
        }
    }
}

// The result tells us how to unfold a guarded type such that that unfolding is the same as if we
// first unfolded the type and then guarded. The trick is to track where the result of guarding a
// custom (`shadow_phase`) and guarding its content directly (`phase`) would differ.
fn recipe_content(
    customs: &flat::CustomTypes,
    can_guard: &IdVec<CustomTypeId, CanGuard>,
    phase: GuardPhase,
    shadow_phase: GuardPhase,
    ty: &anon::Type,
) -> RecipeContent<CustomTypeId> {
    match ty {
        anon::Type::Bool => RecipeContent::Bool,
        anon::Type::Num(num_ty) => RecipeContent::Num(*num_ty),
        anon::Type::Tuple(tys) => {
            let recipes: Vec<_> = tys
                .iter()
                .map(|ty| recipe_content(customs, can_guard, phase, shadow_phase, ty))
                .collect();
            RecipeContent::Tuple(recipes)
        }
        anon::Type::Variants(tys) => {
            let recipes: Vec<_> = tys
                .values()
                .map(|ty| recipe_content(customs, can_guard, phase, shadow_phase, ty))
                .collect();
            RecipeContent::Variants(IdVec::from_vec(recipes))
        }
        anon::Type::Custom(id) => {
            let custom = &customs.types[*id];
            let kind = customs.sccs.component(custom.scc).kind;

            let should_guard = phase.should_guard(can_guard[*id], kind, custom.scc);
            let shadow_should_guard = shadow_phase.should_guard(can_guard[*id], kind, custom.scc);

            if should_guard {
                if shadow_should_guard {
                    // TODO: as an optimization, we could just stop recursing here since `phase ==
                    // shadow_phase` in the recursive call. But, that makes consuming our result a
                    // bit more annoying.
                    let new_phase = GuardPhase::Direct(custom.scc);
                    recipe_content(customs, can_guard, new_phase, new_phase, &custom.content)
                } else {
                    RecipeContent::Unfold(*id)
                }
            } else {
                debug_assert!(!shadow_should_guard);
                RecipeContent::DoNothing(*id)
            }
        }
        anon::Type::Array(ty) => {
            let recipe = recipe_content(
                customs,
                can_guard,
                phase.indirect(),
                shadow_phase.indirect(),
                ty,
            );
            RecipeContent::Array(Box::new(recipe))
        }
        anon::Type::HoleArray(ty) => {
            let recipe = recipe_content(
                customs,
                can_guard,
                phase.indirect(),
                shadow_phase.indirect(),
                ty,
            );
            RecipeContent::HoleArray(Box::new(recipe))
        }
        anon::Type::Boxed(ty) => {
            let recipe = recipe_content(
                customs,
                can_guard,
                phase.indirect(),
                shadow_phase.indirect(),
                ty,
            );
            RecipeContent::Boxed(Box::new(recipe))
        }
    }
}

struct Trans<'a> {
    customs: &'a flat::CustomTypes,
    can_guard: &'a IdVec<CustomTypeId, CanGuard>,
}

impl Trans<'_> {
    fn guard(&self, ty: &anon::Type) -> guard::Type {
        guard(self.customs, self.can_guard, GuardPhase::Structural, ty)
    }

    fn unfold_recipe(&self, id: CustomTypeId) -> UnfoldRecipe<CustomTypeId> {
        let custom = &self.customs.types[id];
        let guard_unfolds = GuardPhase::should_guard(
            GuardPhase::Structural,
            self.can_guard[id],
            self.customs.sccs.component(custom.scc).kind,
            custom.scc,
        );
        let recipe = recipe_content(
            self.customs,
            self.can_guard,
            GuardPhase::Structural,
            GuardPhase::Direct(custom.scc),
            &custom.content,
        );
        if guard_unfolds {
            // Guarding unfolds the type, but processes the body using `GuardPhase::Direct` instead
            // of `GuardPhase::Structural`, as it would if the type were first unfolded in a
            // separate operation.
            UnfoldRecipe::Recurse(recipe)
        } else {
            // Guarding does not unfold the type at all because it is either acyclic or trivial.
            UnfoldRecipe::UnfoldThenRecurse(recipe)
        }
    }

    fn guard_custom(&self, def: &flat::CustomTypeDef) -> guard::Type {
        guard(
            self.customs,
            self.can_guard,
            GuardPhase::Direct(def.scc),
            &def.content,
        )
    }
}

fn build_comp(
    lhs: guard::LocalId,
    rhs: guard::LocalId,
    ty: first_ord::NumType,
    op: Intrinsic,
    builder: &mut Builder,
) -> guard::LocalId {
    let args = builder.add_binding(
        guard::Type::Tuple(vec![guard::Type::Num(ty), guard::Type::Num(ty)]),
        guard::Expr::Tuple(vec![lhs, rhs]),
    );

    builder.add_binding(guard::Type::Bool, guard::Expr::Intrinsic(op, args))
}

fn lower_condition(
    trans: &Trans,
    customs: &flat::CustomTypes,
    discrim: guard::LocalId,
    condition: &flat::Condition,
    builder: &mut Builder,
    match_type: &anon::Type,
) -> guard::LocalId {
    match condition {
        flat::Condition::Any => builder.add_binding(guard::Type::Bool, guard::Expr::BoolLit(true)),
        flat::Condition::Tuple(subconditions) => {
            let anon::Type::Tuple(item_types) = match_type else {
                unreachable!();
            };

            let subcondition_ids = item_types
                .iter()
                .zip(subconditions.iter())
                .enumerate()
                .map(|(index, (item_type, subcondition))| {
                    let item_id = builder.add_binding(
                        trans.guard(item_type),
                        guard::Expr::TupleField(discrim, index),
                    );
                    lower_condition(trans, customs, item_id, subcondition, builder, item_type)
                })
                .collect::<Vec<_>>();
            let if_expr =
                subcondition_ids
                    .into_iter()
                    .rfold(guard::Expr::BoolLit(true), |accum, item| {
                        guard::Expr::If(
                            item,
                            Box::new(accum),
                            Box::new(guard::Expr::BoolLit(false)),
                        )
                    });

            builder.add_binding(guard::Type::Bool, if_expr)
        }
        flat::Condition::Variant(variant_id, subcondition) => {
            let variant_id = first_ord::VariantId(variant_id.0);

            let variant_check = builder.add_binding(
                guard::Type::Bool,
                guard::Expr::CheckVariant(variant_id, discrim),
            );

            let mut new_builder = builder.child();
            let anon::Type::Variants(variant_types) = match_type else {
                unreachable!();
            };

            let variant_type = &variant_types[variant_id];

            let sub_discrim = new_builder.add_binding(
                trans.guard(variant_type),
                guard::Expr::UnwrapVariant(
                    variant_types.map_refs(|_, ty| trans.guard(ty)),
                    first_ord::VariantId(variant_id.0),
                    discrim,
                ),
            );

            let sub_cond_id = lower_condition(
                trans,
                customs,
                sub_discrim,
                subcondition,
                &mut new_builder,
                variant_type,
            );

            builder.add_binding(
                guard::Type::Bool,
                guard::Expr::If(
                    variant_check,
                    Box::new(new_builder.to_expr(sub_cond_id)),
                    Box::new(guard::Expr::BoolLit(false)),
                ),
            )
        }
        flat::Condition::Boxed(subcondition, _) => {
            let anon::Type::Boxed(content_type) = match_type else {
                unreachable!();
            };

            let guarded_type = trans.guard(content_type);
            let content = builder.add_binding(
                guarded_type.clone(),
                guard::Expr::UnwrapBoxed(discrim, guarded_type),
            );

            lower_condition(trans, customs, content, subcondition, builder, content_type)
        }
        flat::Condition::Custom(_, subcondition) => {
            let anon::Type::Custom(custom_type_id) = match_type else {
                unreachable!();
            };

            let content_type = &customs.types[custom_type_id].content;
            let content = builder.add_binding(
                trans.guard(content_type),
                guard::Expr::UnwrapCustom(
                    *custom_type_id,
                    trans.unfold_recipe(*custom_type_id),
                    discrim,
                ),
            );

            lower_condition(trans, customs, content, subcondition, builder, content_type)
        }
        flat::Condition::BoolConst(val) => {
            if *val {
                discrim
            } else {
                builder.add_binding(
                    guard::Type::Bool,
                    guard::Expr::If(
                        discrim,
                        Box::new(guard::Expr::BoolLit(false)),
                        Box::new(guard::Expr::BoolLit(true)),
                    ),
                )
            }
        }
        flat::Condition::ByteConst(val) => {
            let val_id = builder.add_binding(
                guard::Type::Num(first_ord::NumType::Byte),
                guard::Expr::ByteLit(*val),
            );

            build_comp(
                val_id,
                discrim,
                first_ord::NumType::Byte,
                Intrinsic::EqByte,
                builder,
            )
        }
        flat::Condition::IntConst(val) => {
            let val_id = builder.add_binding(
                guard::Type::Num(first_ord::NumType::Int),
                guard::Expr::IntLit(*val),
            );

            build_comp(
                val_id,
                discrim,
                first_ord::NumType::Int,
                Intrinsic::EqInt,
                builder,
            )
        }

        flat::Condition::FloatConst(val) => {
            let val_id = builder.add_binding(
                guard::Type::Num(first_ord::NumType::Float),
                guard::Expr::FloatLit(*val),
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

fn guard_branch(
    trans: &Trans,
    customs: &flat::CustomTypes,
    discrim: flat::LocalId,
    cases: &[(flat::Condition, flat::Expr)],
    result_type: &anon::Type,
    ctx: &mut Context,
    builder: &mut Builder,
) -> guard::LocalId {
    match cases.first() {
        None => {
            let guarded_type = trans.guard(result_type);
            builder.add_binding(guarded_type.clone(), guard::Expr::Unreachable(guarded_type))
        }
        Some((cond, body)) => {
            let binding = ctx.local_binding(discrim);
            let condition_id = lower_condition(
                trans,
                customs,
                binding.new_id,
                cond,
                builder,
                &binding.orig_type,
            );

            let mut then_builder = builder.child();

            let then_final_id =
                guard_expr(trans, customs, result_type, body, ctx, &mut then_builder);

            let then_branch = then_builder.to_expr(then_final_id);

            let mut else_builder = builder.child();
            let else_local_id = guard_branch(
                trans,
                customs,
                discrim,
                &cases[1..],
                result_type,
                ctx,
                &mut else_builder,
            );

            let else_branch = else_builder.to_expr(else_local_id);

            let mut metadata = Metadata::default();
            metadata.add_comment(format!(
                "guard_types: lowered from condition '{}'",
                cond.display()
            ));
            builder.add_binding_with_metadata(
                trans.guard(result_type),
                guard::Expr::If(condition_id, Box::new(then_branch), Box::new(else_branch)),
                metadata,
            )
        }
    }
}

fn guard_expr(
    trans: &Trans,
    customs: &flat::CustomTypes,
    ret_ty: &anon::Type,
    expr: &flat::Expr,
    ctx: &mut Context,
    builder: &mut Builder,
) -> guard::LocalId {
    let new_expr = match expr {
        &flat::Expr::Local(local) => guard::Expr::Local(ctx.local_binding(local).new_id),
        &flat::Expr::Call(purity, func, arg) => {
            guard::Expr::Call(purity, func, ctx.local_binding(arg).new_id)
        }
        flat::Expr::Branch(discrim, cases, ret_ty) => {
            return guard_branch(trans, customs, *discrim, cases, ret_ty, ctx, builder);
        }
        flat::Expr::LetMany(bindings, ret) => {
            let final_local = ctx.with_scope(|ctx| {
                for (binding_ty, expr) in bindings {
                    // if let flat::Expr::WrapCustom(CustomTypeId(10), local) = expr {
                    //     let arg = ctx.local_binding(*local);
                    //     println!(
                    //         "GUARD: {} -> {} (orig: {} -> {})",
                    //         trans.guard(&arg.orig_type).display(),
                    //         trans.guard(binding_ty).display(),
                    //         arg.orig_type.display(),
                    //         binding_ty.display()
                    //     );
                    //     println!("recipe: {:?}", trans.unfold_recipe(CustomTypeId(10)));
                    // }
                    let new_id = guard_expr(trans, customs, binding_ty, expr, ctx, builder);
                    ctx.add_local(LocalInfo {
                        new_id,
                        orig_type: binding_ty.clone(),
                    });
                }
                ctx.local_binding(*ret).new_id
            });

            // Note: Early return! We circumvent the usual return flow because we don't actually
            // want to create an expression directly corresponding to this 'let' block. The 'let'
            // block's bindings just get absorbed into the ambient `builder`.
            return final_local;
        }
        flat::Expr::Tuple(items) => {
            guard::Expr::Tuple(items.map_refs(|item| ctx.local_binding(*item).new_id))
        }
        &flat::Expr::TupleField(tup, idx) => {
            guard::Expr::TupleField(ctx.local_binding(tup).new_id, idx)
        }
        flat::Expr::WrapVariant(variants, variant_id, content) => guard::Expr::WrapVariant(
            variants.map_refs(|_, ty| trans.guard(ty)),
            *variant_id,
            ctx.local_binding(*content).new_id,
        ),
        &flat::Expr::UnwrapVariant(variant_id, wrapped) => {
            let wrapped = ctx.local_binding(wrapped);
            let anon::Type::Variants(variants) = &wrapped.orig_type else {
                unreachable!();
            };

            guard::Expr::UnwrapVariant(
                variants.map_refs(|_, ty| trans.guard(ty)),
                variant_id,
                wrapped.new_id,
            )
        }
        flat::Expr::WrapBoxed(content, item_ty) => {
            guard::Expr::WrapBoxed(ctx.local_binding(*content).new_id, trans.guard(item_ty))
        }
        flat::Expr::UnwrapBoxed(wrapped, item_ty) => {
            guard::Expr::UnwrapBoxed(ctx.local_binding(*wrapped).new_id, trans.guard(item_ty))
        }
        &flat::Expr::WrapCustom(custom_id, content) => guard::Expr::WrapCustom(
            custom_id,
            trans.unfold_recipe(custom_id),
            ctx.local_binding(content).new_id,
        ),
        &flat::Expr::UnwrapCustom(custom_id, wrapped) => guard::Expr::UnwrapCustom(
            custom_id,
            trans.unfold_recipe(custom_id),
            ctx.local_binding(wrapped).new_id,
        ),
        &flat::Expr::Intrinsic(intr, arg) => {
            guard::Expr::Intrinsic(intr, ctx.local_binding(arg).new_id)
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Get(item_ty, arr, idx)) => {
            guard::Expr::ArrayOp(guard::ArrayOp::Get(
                trans.guard(item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*idx).new_id,
            ))
        }
        flat::Expr::ArrayOp(flat::ArrayOp::Extract(item_ty, arr, idx)) => {
            guard::Expr::ArrayOp(guard::ArrayOp::Extract(
                trans.guard(item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*idx).new_id,
            ))
        }
        flat::Expr::ArrayOp(flat::ArrayOp::Len(item_ty, arr)) => guard::Expr::ArrayOp(
            guard::ArrayOp::Len(trans.guard(item_ty), ctx.local_binding(*arr).new_id),
        ),
        flat::Expr::ArrayOp(flat::ArrayOp::Push(item_ty, arr, item)) => {
            guard::Expr::ArrayOp(guard::ArrayOp::Push(
                trans.guard(item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*item).new_id,
            ))
        }
        flat::Expr::ArrayOp(flat::ArrayOp::Pop(item_ty, arr)) => guard::Expr::ArrayOp(
            guard::ArrayOp::Pop(trans.guard(item_ty), ctx.local_binding(*arr).new_id),
        ),
        flat::Expr::ArrayOp(flat::ArrayOp::Replace(item_ty, hole_arr, item)) => {
            guard::Expr::ArrayOp(guard::ArrayOp::Replace(
                trans.guard(item_ty),
                ctx.local_binding(*hole_arr).new_id,
                ctx.local_binding(*item).new_id,
            ))
        }
        flat::Expr::ArrayOp(flat::ArrayOp::Reserve(item_ty, arr, cap)) => {
            guard::Expr::ArrayOp(guard::ArrayOp::Reserve(
                trans.guard(item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*cap).new_id,
            ))
        }

        flat::Expr::IoOp(flat::IoOp::Input) => guard::Expr::IoOp(guard::IoOp::Input),
        &flat::Expr::IoOp(flat::IoOp::Output(msg)) => {
            guard::Expr::IoOp(guard::IoOp::Output(ctx.local_binding(msg).new_id))
        }

        flat::Expr::Panic(ret_ty, msg) => {
            guard::Expr::Panic(trans.guard(ret_ty), ctx.local_binding(*msg).new_id)
        }
        flat::Expr::ArrayLit(item_ty, items) => guard::Expr::ArrayLit(
            trans.guard(item_ty),
            items.map_refs(|item| ctx.local_binding(*item).new_id),
        ),
        &flat::Expr::BoolLit(lit) => guard::Expr::BoolLit(lit),
        &flat::Expr::ByteLit(lit) => guard::Expr::ByteLit(lit),
        &flat::Expr::IntLit(lit) => guard::Expr::IntLit(lit),
        &flat::Expr::FloatLit(lit) => guard::Expr::FloatLit(lit),
    };

    builder.add_binding(trans.guard(ret_ty), new_expr)
}

pub fn guard_types(prog: flat::Program) -> guard::Program {
    let _func_renderer = FuncRenderer::from_symbols(&prog.func_symbols);
    let can_guard = can_guard_customs(&prog.custom_types);

    let trans = Trans {
        customs: &prog.custom_types,
        can_guard: &can_guard,
    };

    // for (_, scc) in &prog.custom_types.sccs {
    //     if scc.nodes.contains(&CustomTypeId(10)) || scc.nodes.contains(&CustomTypeId(11)) {
    //         for node in scc.nodes {
    //             print!("{}, ", node.0);
    //         }
    //         println!();
    //     }
    // }

    // println!(
    //     "unfold Custom#10 = {}",
    //     trans
    //         .guard(&prog.custom_types.types[CustomTypeId(10)].content)
    //         .display()
    // );

    let funcs = prog.funcs.map(|_func_id, func| {
        let mut builder = Builder::new(Count::from_value(1));
        let mut ctx = Context::new();
        ctx.add_local(LocalInfo {
            new_id: guard::ARG_LOCAL,
            orig_type: func.arg_type.clone(),
        });

        let final_local = guard_expr(
            &trans,
            &prog.custom_types,
            &func.ret_type,
            &func.body,
            &mut ctx,
            &mut builder,
        );

        guard::FuncDef {
            purity: func.purity,
            arg_type: trans.guard(&func.arg_type),
            ret_type: trans.guard(&func.ret_type),
            body: builder.to_expr(final_local),
            profile_point: func.profile_point,
        }
    });

    let types = prog
        .custom_types
        .types
        .map_refs(|id, def| guard::CustomTypeDef {
            content: trans.guard_custom(def),
            scc: def.scc,
            can_guard: can_guard[id],
        });

    let custom_types = guard::CustomTypes {
        types,
        sccs: prog.custom_types.sccs,
    };

    guard::Program {
        mod_symbols: prog.mod_symbols,
        custom_types,
        custom_type_symbols: prog.custom_type_symbols,
        funcs,
        func_symbols: prog.func_symbols,
        profile_points: prog.profile_points,
        main: prog.main,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_guard() {
        let a_list = |tail, item| {
            anon::Type::Variants(IdVec::from_vec(vec![
                anon::Type::Tuple(vec![]),
                anon::Type::Tuple(vec![
                    item,
                    anon::Type::Boxed(Box::new(anon::Type::Custom(tail))),
                ]),
            ]))
        };
        let g_list = |tail, item| {
            guard::Type::Variants(IdVec::from_vec(vec![
                guard::Type::Tuple(vec![]),
                guard::Type::Tuple(vec![
                    item,
                    guard::Type::Boxed(Box::new(guard::Type::Custom(tail))),
                ]),
            ]))
        };

        //  list0 = () + bool * rc list0
        let list0 = a_list(CustomTypeId(0), anon::Type::Bool);

        //  list1 = () + rc list0 * rc list1
        let list1 = a_list(
            CustomTypeId(1),
            anon::Type::Boxed(Box::new(anon::Type::Custom(CustomTypeId(0)))),
        );

        let customs = flat::CustomTypes {
            types: IdVec::from_vec(vec![
                flat::CustomTypeDef {
                    content: list0.clone(),
                    scc: flat::CustomTypeSccId(0),
                },
                flat::CustomTypeDef {
                    content: list1,
                    scc: flat::CustomTypeSccId(1),
                },
            ]),
            sccs: {
                let mut sccs = Sccs::new();
                sccs.push_cyclic_component(&[CustomTypeId(0)]);
                sccs.push_cyclic_component(&[CustomTypeId(1)]);
                sccs
            },
        };
        let kinds = IdVec::from_vec(vec![CanGuard::Yes, CanGuard::Yes]);

        //  guarded_list0 = () + bool * rc list0
        let guarded_list0 = guard(
            &customs,
            &kinds,
            GuardPhase::Structural,
            &anon::Type::Custom(CustomTypeId(0)),
        );
        let expected0 = g_list(CustomTypeId(0), guard::Type::Bool);
        assert_eq!(guarded_list0, expected0);

        //  guarded_list1 = () + rc (() + bool * rc list0) * rc list1
        let guarded_list1 = guard(
            &customs,
            &kinds,
            GuardPhase::Structural,
            &anon::Type::Custom(CustomTypeId(1)),
        );
        let expected1 = g_list(CustomTypeId(1), guard::Type::Boxed(Box::new(expected0)));
        assert_eq!(guarded_list1, expected1);
    }
}
