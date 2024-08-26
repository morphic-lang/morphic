use crate::data::first_order_ast as first_ord;
use crate::data::mode_annot_ast2::{
    Mode, Path, ResModes, Shape, ShapeInner, SlotId, FUNC_BODY_PATH,
};
use crate::data::obligation_annot_ast as ob;
use crate::data::rc_annot_ast::{self as annot, RcOp, Selector};
use crate::data::rc_specialized_ast2 as rc;
use crate::util::instance_queue::InstanceQueue;
use crate::util::let_builder::{self, FromBindings};
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{Count, IdVec};
use std::collections::{BTreeMap, BTreeSet};

// TODO:
// - get rid of provenance (just do retain/release resolution)
// - collect the types to be specialized eagerly (if so far as "specialization" is still needed)

impl FromBindings for rc::Expr {
    type LocalId = rc::LocalId;
    type Binding = (rc::Type, rc::Expr);

    fn from_bindings(bindings: Vec<Self::Binding>, ret: Self::LocalId) -> Self {
        rc::Expr::LetMany(bindings, ret)
    }
}

type LetManyBuilder = let_builder::LetManyBuilder<rc::Expr>;

// We only care about storage modes when lowering custom types, so we throw out any other
// modes to avoid duplicate specializations.
fn prepare_subst(res: &IdVec<SlotId, ResModes<Mode>>) -> Vec<Mode> {
    res.values()
        .map(|modes| match modes {
            ResModes::Stack(mode) => *mode,
            ResModes::Heap(modes) => modes.storage,
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct TypeSpec {
    old_id: first_ord::CustomTypeId,
    res: Vec<Mode>,
}

impl TypeSpec {
    fn new<'a>(old_id: first_ord::CustomTypeId, res: IdVec<SlotId, ResModes<Mode>>) -> Self {
        Self {
            old_id,
            res: prepare_subst(&res),
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
            let ty = lower_type_impl(
                &mut self.queue,
                &customs.types[spec.old_id].content,
                &spec.res,
            );

            let pushed_id1 = self.provenance.push(spec.old_id);
            let pushed_id2 = self.resolved.push(ty);
            debug_assert_eq!(pushed_id1, id);
            debug_assert_eq!(pushed_id2, id);
        }
    }

    fn resolve(&mut self, _customs: &annot::CustomTypes, spec: TypeSpec) -> rc::CustomTypeId {
        self.queue.resolve(spec)
    }

    fn lower_type(&mut self, _customs: &annot::CustomTypes, ty: &ob::Type) -> rc::Type {
        lower_type_impl(&mut self.queue, &ty.shape, &prepare_subst(&ty.res))
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

fn lower_type_impl(
    insts: &mut InstanceQueue<TypeSpec, rc::CustomTypeId>,
    shape: &Shape,
    res: &[Mode],
) -> rc::Type {
    match &*shape.inner {
        ShapeInner::Bool => rc::Type::Bool,
        ShapeInner::Num(num_ty) => rc::Type::Num(*num_ty),
        ShapeInner::Tuple(shapes) => {
            // TODO: we have similar code in earlier inference phases
            let mut start = 0;
            let mut tys = Vec::with_capacity(shapes.len());
            for shape in shapes {
                let end = start + shape.num_slots;
                tys.push(lower_type_impl(insts, shape, &res[start..end]));
                start = end;
            }
            rc::Type::Tuple(tys)
        }
        ShapeInner::Variants(shapes) => {
            let mut start = 0;
            let mut tys = Vec::with_capacity(shapes.len());
            for shape in shapes.values() {
                let end = start + shape.num_slots;
                tys.push(lower_type_impl(insts, shape, &res[start..end]));
                start = end;
            }
            rc::Type::Variants(IdVec::from_vec(tys))
        }
        ShapeInner::Custom(id) | ShapeInner::SelfCustom(id) => {
            rc::Type::Custom(insts.resolve(TypeSpec {
                old_id: *id,
                res: res.iter().cloned().collect(),
            }))
        }
        ShapeInner::Array(shape) => {
            rc::Type::Array(res[0], Box::new(lower_type_impl(insts, shape, &res[1..])))
        }
        ShapeInner::HoleArray(shape) => {
            rc::Type::HoleArray(res[0], Box::new(lower_type_impl(insts, shape, &res[1..])))
        }
        ShapeInner::Boxed(shape) => {
            rc::Type::Boxed(res[0], Box::new(lower_type_impl(insts, shape, &res[1..])))
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
    fn from_sel_impl(
        customs: &annot::CustomTypes,
        true_: &BTreeSet<SlotId>,
        slots: (usize, usize),
        shape: &Shape,
    ) -> Self {
        match &*shape.inner {
            ShapeInner::Bool => Self::NoOp,
            ShapeInner::Num(_) => Self::NoOp,
            ShapeInner::Tuple(fields) => {
                let mut start = 0;
                let mut plans = BTreeMap::new();

                // TODO: we have similar code in earlier inference phases
                for (i, field) in fields.iter().enumerate() {
                    let end = start + field.num_slots;
                    let plan = RcOpPlan::from_sel_impl(customs, true_, (start, end), field);
                    if !matches!(plan, RcOpPlan::NoOp) {
                        plans.insert(i, plan);
                    }
                    start = end;
                }

                if plans.is_empty() {
                    Self::NoOp
                } else {
                    Self::TupleFields(plans)
                }
            }
            ShapeInner::Variants(variants) => {
                let mut start = 0;
                let mut plans = BTreeMap::new();

                for (i, variant) in variants {
                    let end = start + variant.num_slots;
                    let plan = RcOpPlan::from_sel_impl(customs, true_, (start, end), variant);
                    if !matches!(plan, RcOpPlan::NoOp) {
                        plans.insert(i, plan);
                    }
                    start = end;
                }

                if plans.is_empty() {
                    Self::NoOp
                } else {
                    Self::VariantCases(plans)
                }
            }
            // The only time we hit this case is when there is a recursive type whose recursive
            // occurrence is not guarded by a box. The type guarding pass ensures this only occurs
            // for zero-sized types, which require no non-trivial retain/release operations.
            ShapeInner::SelfCustom(_) => Self::NoOp,
            ShapeInner::Custom(id) => {
                let plan =
                    RcOpPlan::from_sel_impl(customs, true_, slots, &customs.types[*id].content);
                if matches!(plan, RcOpPlan::NoOp) {
                    Self::NoOp
                } else {
                    Self::Custom(Box::new(plan))
                }
            }
            ShapeInner::Array(_) | ShapeInner::HoleArray(_) | ShapeInner::Boxed(_) => {
                if true_.contains(&SlotId(slots.0)) {
                    Self::LeafOp
                } else {
                    Self::NoOp
                }
            }
        }
    }

    fn from_sel(customs: &annot::CustomTypes, sel: &Selector) -> Self {
        Self::from_sel_impl(customs, &sel.true_, (0, sel.shape.num_slots), &sel.shape)
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
    funcs: &IdVec<ob::CustomFuncId, annot::FuncDef>,
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
            let ret_ty = insts.lower_type(customs, ret_ty);
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
                    let low_ty = insts.lower_type(customs, binding_ty);

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
            variants.map_refs(|_, ty| insts.lower_type(customs, ty)),
            *variant_id,
            ctx.local_binding(*content).new_id,
        ),
        annot::Expr::UnwrapVariant(variant_id, wrapped) => {
            rc::Expr::UnwrapVariant(*variant_id, ctx.local_binding(*wrapped).new_id)
        }
        annot::Expr::WrapBoxed(content, item_ty) => rc::Expr::WrapBoxed(
            ctx.local_binding(*content).new_id,
            insts.lower_type(customs, item_ty),
        ),
        annot::Expr::UnwrapBoxed(wrapped, item_ty) => rc::Expr::UnwrapBoxed(
            ctx.local_binding(*wrapped).new_id,
            insts.lower_type(customs, item_ty),
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
                insts.lower_type(customs, item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*idx).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Extract(item_ty, arr, idx)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Extract(
                insts.lower_type(customs, item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*idx).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Len(item_ty, arr)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Len(
                insts.lower_type(customs, item_ty),
                ctx.local_binding(*arr).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Push(item_ty, arr, item)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Push(
                insts.lower_type(customs, item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*item).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Pop(item_ty, arr)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Pop(
                insts.lower_type(customs, item_ty),
                ctx.local_binding(*arr).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Replace(item_ty, arr, idx)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Replace(
                insts.lower_type(customs, item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*idx).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(item_ty, arr, cap)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Reserve(
                insts.lower_type(customs, item_ty),
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*cap).new_id,
            ))
        }
        annot::Expr::IoOp(annot::IoOp::Input) => rc::Expr::IoOp(rc::IoOp::Input),
        annot::Expr::IoOp(annot::IoOp::Output(local)) => {
            rc::Expr::IoOp(rc::IoOp::Output(ctx.local_binding(*local).new_id))
        }
        annot::Expr::Panic(ret_ty, msg) => rc::Expr::Panic(
            insts.lower_type(customs, ret_ty),
            ctx.local_binding(*msg).new_id,
        ),
        annot::Expr::ArrayLit(item_ty, items) => rc::Expr::ArrayLit(
            insts.lower_type(customs, item_ty),
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
    funcs: &IdVec<ob::CustomFuncId, annot::FuncDef>,
    insts: &mut TypeInstances,
    func: &annot::FuncDef,
) -> rc::FuncDef {
    let arg_type = insts.lower_type(customs, &func.arg_ty);
    let ret_type = insts.lower_type(customs, &func.ret_ty);

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
