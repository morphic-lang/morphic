use crate::data::first_order_ast as first_ord;
use crate::data::mode_annot_ast2::{Mode, ModeData, Overlay, Path, SlotId, FUNC_BODY_PATH};
use crate::data::rc_annot_ast::{self as annot, RcOp, Selector};
use crate::data::rc_specialized_ast2 as rc;
use crate::util::instance_queue::InstanceQueue;
use crate::util::let_builder::{self, FromBindings};
use crate::util::local_context::LocalContext;
use crate::util::map_ext::{btree_map_refs, FnWrap, MapRef};
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{Count, IdVec};
use std::collections::BTreeMap;

impl FromBindings for rc::Expr {
    type LocalId = rc::LocalId;
    type Binding = (rc::Type, rc::Expr);

    fn from_bindings(bindings: Vec<Self::Binding>, ret: Self::LocalId) -> Self {
        rc::Expr::LetMany(bindings, ret)
    }
}

type LetManyBuilder = let_builder::LetManyBuilder<rc::Expr>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct TypeSpec {
    id: first_ord::CustomTypeId,
    subst: BTreeMap<SlotId, Mode>,
    tail_subst: BTreeMap<SlotId, Mode>,
}

// We only care about storage modes when lowering custom types, so we throw out any other modes
// to avoid duplicate specializations.
impl TypeSpec {
    fn new_head<'a>(
        customs: &annot::CustomTypes,
        id: first_ord::CustomTypeId,
        osub: impl MapRef<'a, SlotId, Mode>,
        tsub: impl MapRef<'a, SlotId, Mode>,
    ) -> Self {
        let head_mode = |slot| *osub.get(slot).unwrap_or_else(|| tsub.get(slot).unwrap());
        let subst = customs.types[id]
            .ty
            .iter_store(customs.view_types())
            .map(|slot| (*slot, head_mode(slot)))
            .collect::<BTreeMap<_, _>>();
        let tail_subst = customs.types[id]
            .ty
            .iter_store(customs.view_types())
            .map(|slot| (*slot, *tsub.get(slot).unwrap()))
            .collect::<BTreeMap<_, _>>();
        Self {
            id,
            subst,
            tail_subst,
        }
    }

    fn new_tail<'a>(
        customs: &annot::CustomTypes,
        id: first_ord::CustomTypeId,
        tsub: impl MapRef<'a, SlotId, Mode>,
    ) -> Self {
        let get_custom = FnWrap::wrap(|id| customs.types.get(id).map(|def| &def.ty));
        let subst = customs.types[id]
            .ty
            .iter_store(get_custom)
            .map(|slot| (*slot, *tsub.get(slot).unwrap()))
            .collect::<BTreeMap<_, _>>();
        let tail_subst = subst.clone();
        Self {
            id,
            subst,
            tail_subst,
        }
    }
}

#[derive(Clone, Debug)]
struct TypeInstances {
    queue: InstanceQueue<TypeSpec, rc::CustomTypeId>,
    provenance: IdVec<rc::CustomTypeId, first_ord::CustomTypeId>,
    resolved: IdVec<rc::CustomTypeId, rc::Type>,
}

impl TypeInstances {
    fn new() -> Self {
        Self {
            queue: InstanceQueue::new(),
            provenance: IdVec::new(),
            resolved: IdVec::new(),
        }
    }

    fn force(&mut self, customs: &annot::CustomTypes) {
        while let Some((id, spec)) = self.queue.pop_pending() {
            let ty = lower_custom_type(
                &mut self.queue,
                customs,
                &spec.subst,
                &spec.tail_subst,
                &customs.types[spec.id].ty,
            );

            let pushed_id1 = self.provenance.push(spec.id);
            let pushed_id2 = self.resolved.push(ty);
            debug_assert_eq!(pushed_id1, id);
            debug_assert_eq!(pushed_id2, id);
        }
    }

    fn resolve(&mut self, customs: &annot::CustomTypes, spec: TypeSpec) -> rc::CustomTypeId {
        let id = self.queue.resolve(spec);
        self.force(customs);
        id
    }

    fn lookup_resolved(&mut self, customs: &annot::CustomTypes, id: rc::CustomTypeId) -> &rc::Type {
        self.force(customs);
        &self.resolved[id]
    }

    fn finish(
        mut self,
        customs: &annot::CustomTypes,
    ) -> (
        IdVec<rc::CustomTypeId, first_ord::CustomTypeId>,
        IdVec<rc::CustomTypeId, rc::Type>,
    ) {
        self.force(customs);
        (self.provenance, self.resolved)
    }
}

fn lower_custom_type(
    insts: &mut InstanceQueue<TypeSpec, rc::CustomTypeId>,
    customs: &annot::CustomTypes,
    subst: &BTreeMap<SlotId, Mode>,
    tail_subst: &BTreeMap<SlotId, Mode>,
    ty: &ModeData<SlotId>,
) -> rc::Type {
    match ty {
        ModeData::Bool => rc::Type::Bool,
        ModeData::Num(n) => rc::Type::Num(*n),
        ModeData::Tuple(tys) => rc::Type::Tuple(
            tys.iter()
                .map(|ty| lower_custom_type(insts, customs, subst, tail_subst, ty))
                .collect(),
        ),
        ModeData::Variants(tys) => rc::Type::Variants(
            tys.map_refs(|_, ty| lower_custom_type(insts, customs, subst, tail_subst, ty)),
        ),
        ModeData::SelfCustom(id) => {
            let spec = TypeSpec::new_tail(customs, *id, tail_subst);
            rc::Type::Custom(insts.resolve(spec))
        }
        ModeData::Custom(id, osub, tsub) => {
            let osub_concrete = btree_map_refs(osub, |_, slot| subst[slot]);
            let tsub_concrete = tsub.map_refs(|_, slot| subst[slot]);
            let spec = TypeSpec::new_head(customs, *id, &osub_concrete, &tsub_concrete);
            rc::Type::Custom(insts.resolve(spec))
        }
        ModeData::Array(mode, _, item_ty) => rc::Type::Array(
            subst[mode],
            Box::new(lower_custom_type(
                insts, customs, subst, tail_subst, item_ty,
            )),
        ),
        ModeData::HoleArray(mode, _, item_ty) => rc::Type::HoleArray(
            subst[mode],
            Box::new(lower_custom_type(
                insts, customs, subst, tail_subst, item_ty,
            )),
        ),
        ModeData::Boxed(mode, _, item_ty) => rc::Type::Boxed(
            subst[mode],
            Box::new(lower_custom_type(
                insts, customs, subst, tail_subst, item_ty,
            )),
        ),
    }
}

fn lower_type(
    insts: &mut TypeInstances,
    customs: &annot::CustomTypes,
    ty: &annot::Type,
) -> rc::Type {
    match ty {
        annot::Type::Bool => rc::Type::Bool,
        annot::Type::Num(n) => rc::Type::Num(*n),
        annot::Type::Tuple(tys) => rc::Type::Tuple(
            tys.iter()
                .map(|ty| lower_type(insts, customs, ty))
                .collect(),
        ),
        annot::Type::Variants(tys) => {
            rc::Type::Variants(tys.map_refs(|_, ty| lower_type(insts, customs, ty)))
        }
        annot::Type::SelfCustom(_) => unreachable!(),
        annot::Type::Custom(id, osub, tsub) => {
            rc::Type::Custom(insts.resolve(customs, TypeSpec::new_head(customs, *id, osub, tsub)))
        }
        annot::Type::Array(mode, _, item_ty) => {
            rc::Type::Array(*mode, Box::new(lower_type(insts, customs, &*item_ty)))
        }
        annot::Type::HoleArray(mode, _, item_ty) => {
            rc::Type::HoleArray(*mode, Box::new(lower_type(insts, customs, &*item_ty)))
        }
        annot::Type::Boxed(mode, _, item_ty) => {
            rc::Type::Boxed(*mode, Box::new(lower_type(insts, customs, &*item_ty)))
        }
    }
}

#[derive(Clone, Debug)]
enum RcOpPlan {
    LeafOp,
    NoOp,
    TupleFields(BTreeMap<usize, RcOpPlan>),
    VariantCases(BTreeMap<first_ord::VariantId, RcOpPlan>),
    Custom(Box<RcOpPlan>),
}

impl RcOpPlan {
    fn from_sel(customs: &annot::CustomTypes, sel: &Selector) -> Self {
        match sel {
            Overlay::Bool => Self::NoOp,
            Overlay::Num(_) => Self::NoOp,
            Overlay::Tuple(fields) => {
                let mut plans = BTreeMap::new();
                for (idx, field) in fields.iter().enumerate() {
                    let plan = RcOpPlan::from_sel(customs, field);
                    if !matches!(plan, RcOpPlan::NoOp) {
                        plans.insert(idx, plan);
                    }
                }

                if plans.is_empty() {
                    Self::NoOp
                } else {
                    Self::TupleFields(plans)
                }
            }
            Overlay::Variants(variants) => {
                let mut plans = BTreeMap::new();
                for (variant_id, variant) in variants {
                    let plan = RcOpPlan::from_sel(customs, variant);
                    if !matches!(plan, RcOpPlan::NoOp) {
                        plans.insert(variant_id, plan);
                    }
                }

                if plans.is_empty() {
                    Self::NoOp
                } else {
                    Self::VariantCases(plans)
                }
            }
            // The only time we hit this case is when there is a recursive type whose recursive
            // occurrence is not guarded by a box. Currently, such a type is necessarily zero-sized,
            // but we would need to update this logic if we did not "cut" every edge of type SCCs
            // with boxes (e.g. if we inserted the minimal number of boxes to do cycle breaking).
            Overlay::SelfCustom(id) => {
                debug_assert!({
                    let get = FnWrap::wrap(|id| customs.types.get(id).map(|def| &def.ov));
                    customs.types[*id].ov.is_zero_sized(get)
                });
                Self::NoOp
            }
            Overlay::Custom(id, sub) => {
                let inner = customs.types[*id].ov.hydrate(sub);
                let plan = RcOpPlan::from_sel(customs, &inner);
                if matches!(plan, RcOpPlan::NoOp) {
                    Self::NoOp
                } else {
                    Self::Custom(Box::new(plan))
                }
            }
            Overlay::Array(drop) | Overlay::HoleArray(drop) | Overlay::Boxed(drop) => {
                if *drop {
                    Self::LeafOp
                } else {
                    Self::NoOp
                }
            }
        }
    }
}

/// The returned `LocalId` always refers to a binding of type `()` (the result of the final
/// retain/release operation). We propagate this outward to minimize the number of `let: () = ()`
/// bindings we have to generate, which makes the generated code slightly cleaner.
fn build_plan(
    customs: &annot::CustomTypes,
    insts: &mut TypeInstances,
    rc_op: RcOp,
    root: rc::LocalId,
    root_ty: &rc::Type,
    plan: &RcOpPlan,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    match plan {
        RcOpPlan::NoOp => builder.add_binding((rc::Type::Tuple(vec![]), rc::Expr::Tuple(vec![]))),

        RcOpPlan::LeafOp => builder.add_binding((
            rc::Type::Tuple(vec![]),
            rc::Expr::RcOp(rc_op, root_ty.clone(), root),
        )),

        RcOpPlan::TupleFields(plans) => {
            let rc::Type::Tuple(field_tys) = root_ty else {
                unreachable!()
            };

            plans
                .iter()
                .map(|(idx, plan)| {
                    let field_ty = &field_tys[*idx];
                    let field_local =
                        builder.add_binding((field_ty.clone(), rc::Expr::TupleField(root, *idx)));
                    build_plan(customs, insts, rc_op, field_local, field_ty, plan, builder)
                })
                .last()
                .unwrap()
        }

        RcOpPlan::VariantCases(plans) => {
            let rc::Type::Variants(variant_tys) = root_ty else {
                unreachable!()
            };

            let mut cases = Vec::new();
            for (variant_id, plan) in plans {
                let variant_ty = &variant_tys[variant_id];
                let cond = rc::Condition::Variant(*variant_id, Box::new(rc::Condition::Any));

                let mut case_builder = builder.child();
                let content_id = case_builder.add_binding((
                    variant_ty.clone(),
                    rc::Expr::UnwrapVariant(*variant_id, root),
                ));

                let unit = build_plan(
                    customs,
                    insts,
                    rc_op,
                    content_id,
                    variant_ty,
                    plan,
                    &mut case_builder,
                );

                cases.push((cond, case_builder.to_expr(unit)))
            }

            // For exhaustivity
            cases.push((rc::Condition::Any, rc::Expr::Tuple(vec![])));

            builder.add_binding((
                rc::Type::Tuple(vec![]),
                rc::Expr::Branch(root, cases, rc::Type::Tuple(vec![])),
            ))
        }

        RcOpPlan::Custom(plan) => {
            let rc::Type::Custom(custom_id) = root_ty else {
                unreachable!()
            };

            // `lookup_resolved` won't panic because we must have resolved this type when creating
            // the binding for the variable we are retaining/releasing
            let content_ty = insts.lookup_resolved(customs, *custom_id).clone();
            let content_id =
                builder.add_binding((content_ty.clone(), rc::Expr::UnwrapCustom(*custom_id, root)));
            build_plan(
                customs,
                insts,
                rc_op,
                content_id,
                &content_ty,
                plan,
                builder,
            )
        }
    }
}

#[derive(Clone, Debug)]
struct LocalInfo {
    ty: rc::Type,
    new_id: rc::LocalId,
}

fn lower_expr(
    funcs: &IdVec<annot::CustomFuncId, annot::FuncDef>,
    customs: &annot::CustomTypes,
    insts: &mut TypeInstances,
    ctx: &mut LocalContext<annot::LocalId, LocalInfo>,
    path: &Path,
    expr: &annot::Expr,
    ret_ty: &rc::Type,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    let new_expr = match expr {
        // The only interesting case...
        annot::Expr::RcOp(op, sel, arg) => {
            let plan = RcOpPlan::from_sel(customs, sel);
            let arg = ctx.local_binding(*arg);
            let unit = build_plan(customs, insts, *op, arg.new_id, &arg.ty, &plan, builder);
            rc::Expr::Local(unit)
        }

        annot::Expr::Local(local) => rc::Expr::Local(ctx.local_binding(*local).new_id),
        annot::Expr::Call(purity, func, arg) => {
            rc::Expr::Call(*purity, *func, ctx.local_binding(*arg).new_id)
        }
        annot::Expr::Branch(discrim, arms, ret_ty) => {
            let ret_ty = lower_type(insts, customs, ret_ty);
            let mut new_arms = Vec::new();
            for (cond, expr) in arms {
                let mut case_builder = builder.child();
                let final_local = lower_expr(
                    funcs,
                    customs,
                    insts,
                    ctx,
                    path,
                    expr,
                    &ret_ty,
                    &mut case_builder,
                );
                new_arms.push((cond.clone(), case_builder.to_expr(final_local)));
            }
            rc::Expr::Branch(ctx.local_binding(*discrim).new_id, new_arms, ret_ty)
        }
        annot::Expr::LetMany(bindings, ret) => {
            let final_local = ctx.with_scope(|ctx| {
                for (binding_ty, expr) in bindings {
                    let low_ty = lower_type(insts, customs, binding_ty);

                    let final_local =
                        lower_expr(funcs, customs, insts, ctx, path, expr, &low_ty, builder);
                    ctx.add_local(LocalInfo {
                        ty: low_ty,
                        new_id: final_local,
                    });
                }
                ctx.local_binding(*ret).new_id
            });

            // Note: Early return! We circumvent the usual return flow because we don't actually
            // want to create an expression directly corresponding to this 'let' block. The 'let'
            // block's bindings just get absorbed into the ambient `builder`.
            return final_local;
        }
        annot::Expr::Tuple(fields) => rc::Expr::Tuple(
            fields
                .iter()
                .map(|local| ctx.local_binding(*local).new_id)
                .collect(),
        ),
        annot::Expr::TupleField(tup, idx) => {
            rc::Expr::TupleField(ctx.local_binding(*tup).new_id, *idx)
        }
        annot::Expr::WrapVariant(variants, variant_id, content) => rc::Expr::WrapVariant(
            variants.map_refs(|_, ty| lower_type(insts, customs, ty)),
            *variant_id,
            ctx.local_binding(*content).new_id,
        ),
        annot::Expr::UnwrapVariant(variant_id, wrapped) => {
            rc::Expr::UnwrapVariant(*variant_id, ctx.local_binding(*wrapped).new_id)
        }
        annot::Expr::WrapBoxed(content, item_ty) => rc::Expr::WrapBoxed(
            ctx.local_binding(*content).new_id,
            lower_type(insts, customs, item_ty),
        ),
        annot::Expr::UnwrapBoxed(wrapped, item_ty) => rc::Expr::UnwrapBoxed(
            ctx.local_binding(*wrapped).new_id,
            lower_type(insts, customs, item_ty),
        ),
        annot::Expr::WrapCustom(_custom_id, content) => {
            let rc::Type::Custom(custom_id) = ret_ty else {
                unreachable!();
            };
            rc::Expr::WrapCustom(*custom_id, ctx.local_binding(*content).new_id)
        }
        annot::Expr::UnwrapCustom(_custom_id, wrapped) => {
            let info = ctx.local_binding(*wrapped);
            let rc::Type::Custom(custom_id) = &info.ty else {
                unreachable!();
            };
            rc::Expr::UnwrapCustom(*custom_id, info.new_id)
        }
        annot::Expr::Intrinsic(intr, arg) => {
            rc::Expr::Intrinsic(*intr, ctx.local_binding(*arg).new_id)
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Get(item_ty, arr, idx)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Get(
                lower_type(insts, customs, item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*idx).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Extract(item_ty, arr, idx)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Extract(
                lower_type(insts, customs, item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*idx).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Len(item_ty, arr)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Len(
                lower_type(insts, customs, item_ty),
                ctx.local_binding(*arr).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Push(item_ty, arr, item)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Push(
                lower_type(insts, customs, item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*item).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Pop(item_ty, arr)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Pop(
                lower_type(insts, customs, item_ty),
                ctx.local_binding(*arr).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Replace(item_ty, arr, idx)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Replace(
                lower_type(insts, customs, item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*idx).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(item_ty, arr, cap)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Reserve(
                lower_type(insts, customs, item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*cap).new_id,
            ))
        }
        annot::Expr::IoOp(annot::IoOp::Input) => rc::Expr::IoOp(rc::IoOp::Input),
        annot::Expr::IoOp(annot::IoOp::Output(local)) => {
            rc::Expr::IoOp(rc::IoOp::Output(ctx.local_binding(*local).new_id))
        }
        annot::Expr::Panic(ret_ty, msg) => rc::Expr::Panic(
            lower_type(insts, customs, ret_ty),
            ctx.local_binding(*msg).new_id,
        ),
        annot::Expr::ArrayLit(item_ty, items) => rc::Expr::ArrayLit(
            lower_type(insts, customs, item_ty),
            items
                .iter()
                .map(|local| ctx.local_binding(*local).new_id)
                .collect(),
        ),
        annot::Expr::BoolLit(lit) => rc::Expr::BoolLit(*lit),
        annot::Expr::ByteLit(lit) => rc::Expr::ByteLit(*lit),
        annot::Expr::IntLit(lit) => rc::Expr::IntLit(*lit),
        annot::Expr::FloatLit(lit) => rc::Expr::FloatLit(*lit),
    };

    builder.add_binding((ret_ty.clone(), new_expr))
}

fn lower_func(
    customs: &annot::CustomTypes,
    funcs: &IdVec<annot::CustomFuncId, annot::FuncDef>,
    insts: &mut TypeInstances,
    func: &annot::FuncDef,
) -> rc::FuncDef {
    let arg_type = lower_type(insts, customs, &func.arg_ty);
    let ret_type = lower_type(insts, customs, &func.ret_ty);

    let mut ctx = LocalContext::new();
    ctx.add_local(LocalInfo {
        ty: arg_type.clone(),
        new_id: rc::ARG_LOCAL,
    });

    let mut builder = LetManyBuilder::new(Count::from_value(1));
    let final_local = lower_expr(
        funcs,
        customs,
        insts,
        &mut ctx,
        &FUNC_BODY_PATH(),
        &func.body,
        &ret_type,
        &mut builder,
    );

    rc::FuncDef {
        purity: func.purity,
        arg_type,
        ret_type,
        body: builder.to_expr(final_local),
        profile_point: func.profile_point,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Strategy {
    Default,
    Trivial,
}

pub fn rc_specialize(
    program: annot::Program,
    _strategy: Strategy,
    progress: impl ProgressLogger,
) -> rc::Program {
    let mut progress = progress.start_session(Some(program.funcs.len()));

    let mut insts = TypeInstances::new();
    let mut funcs = IdVec::new();
    for (id, func) in &program.funcs {
        let new_func = lower_func(&program.custom_types, &program.funcs, &mut insts, &func);
        let pushed_id = funcs.push(new_func);
        debug_assert_eq!(pushed_id, id);
        progress.update(1);
    }

    progress.finish();

    let (provenance, types) = insts.finish(&program.custom_types);
    let custom_type_symbols = provenance.map_refs(|_, id| program.custom_type_symbols[id].clone());
    let custom_types = rc::CustomTypes { types, provenance };

    rc::Program {
        mod_symbols: program.mod_symbols,
        custom_types,
        custom_type_symbols,
        funcs,
        func_symbols: program.func_symbols,
        profile_points: program.profile_points,
        main: program.main,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::first_order_ast::NumType;

    #[test]
    fn test_spec_list() {
        use crate::data::mode_annot_ast2::SlotId;
        use crate::data::obligation_annot_ast as ob;
        use crate::util::map_ext::{map, set};
        use first_ord::CustomTypeId;

        // type List { Nil, Cons(Box((Array Int, List))) }
        let ty = ModeData::Variants(IdVec::from_vec(vec![
            ModeData::Tuple(vec![]),
            ModeData::Boxed(
                SlotId(0),
                Overlay::Tuple(vec![
                    Overlay::Array(SlotId(2)),
                    Overlay::SelfCustom(CustomTypeId(0)),
                ]),
                Box::new(ModeData::Tuple(vec![
                    ModeData::Array(
                        SlotId(1),
                        Overlay::Num(NumType::Int),
                        Box::new(ModeData::Num(NumType::Int)),
                    ),
                    ModeData::SelfCustom(CustomTypeId(0)),
                ])),
            ),
        ]));
        let ov = ty.unapply_overlay();
        let types = IdVec::from_vec(vec![ob::TypeDef {
            ty,
            ov,
            slot_count: Count::from_value(3),
            ov_slots: set![SlotId(0)],
        }]);
        let customs = annot::CustomTypes { types };

        let osub = map! [ SlotId(0) => Mode::Borrowed ];
        let tsub = IdVec::from_vec(vec![Mode::Owned, Mode::Owned, Mode::Owned]);
        let mut insts = TypeInstances::new();
        insts.resolve(
            &customs,
            TypeSpec::new_head(&customs, CustomTypeId(0), &osub, &tsub),
        );

        let expected_head = rc::Type::Variants(IdVec::from_vec(vec![
            rc::Type::Tuple(vec![]),
            rc::Type::Boxed(
                Mode::Borrowed,
                Box::new(rc::Type::Tuple(vec![
                    rc::Type::Array(Mode::Owned, Box::new(rc::Type::Num(NumType::Int))),
                    rc::Type::Custom(rc::CustomTypeId(1)),
                ])),
            ),
        ]));
        let expected_tail = rc::Type::Variants(IdVec::from_vec(vec![
            rc::Type::Tuple(vec![]),
            rc::Type::Boxed(
                Mode::Owned,
                Box::new(rc::Type::Tuple(vec![
                    rc::Type::Array(Mode::Owned, Box::new(rc::Type::Num(NumType::Int))),
                    rc::Type::Custom(rc::CustomTypeId(1)),
                ])),
            ),
        ]));

        assert_eq!(insts.resolved.len(), 2);
        assert_eq!(&insts.resolved[rc::CustomTypeId(0)], &expected_head);
        assert_eq!(&insts.resolved[rc::CustomTypeId(1)], &expected_tail);
    }
}
