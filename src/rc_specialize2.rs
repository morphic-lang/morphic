use crate::data::first_order_ast as first_ord;
use crate::data::mode_annot_ast2::{
    iter_shapes, Mode, Path, ResModes, Shape, ShapeInner, SlotId, FUNC_BODY_PATH,
};
use crate::data::obligation_annot_ast as ob;
use crate::data::rc_annot_ast::{self as annot, Selector};
use crate::data::rc_specialized_ast2::{self as rc, ModeScheme, ModeSchemeId};
use crate::util::collection_ext::VecExt;
use crate::util::instance_queue::InstanceQueue;
use crate::util::let_builder::{self, FromBindings};
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{Count, IdVec};
use std::collections::{BTreeMap, BTreeSet};

impl FromBindings for rc::Expr {
    type LocalId = rc::LocalId;
    type Binding = (rc::Type, rc::Expr);

    fn from_bindings(bindings: Vec<Self::Binding>, ret: Self::LocalId) -> Self {
        rc::Expr::LetMany(bindings, ret)
    }
}

type LetManyBuilder = let_builder::LetManyBuilder<rc::Expr>;

type ReleaseInstances = InstanceQueue<ReleaseSpec, ModeSchemeId>;

// We only care about storage modes when creating release plans. We throw out any other modes to
// avoid duplicate specializations.
fn prepare_resources(res: &[ResModes<Mode>]) -> Vec<Mode> {
    res.iter()
        .map(|modes| match modes {
            ResModes::Stack(mode) => *mode,
            ResModes::Heap(modes) => modes.storage,
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ReleaseSpec {
    custom_id: first_ord::CustomTypeId,
    res: Vec<Mode>,
}

impl ReleaseSpec {
    fn new<'a>(custom_id: first_ord::CustomTypeId, res: IdVec<SlotId, ResModes<Mode>>) -> Self {
        Self {
            custom_id,
            res: prepare_resources(res.as_slice()),
        }
    }
}

fn make_scheme_impl(
    insts: &mut ReleaseInstances,
    all_res: &[Mode],
    shape: &Shape,
    res: &[Mode],
) -> ModeScheme {
    match &*shape.inner {
        ShapeInner::Bool => ModeScheme::Bool,
        ShapeInner::Num(num_ty) => ModeScheme::Num(*num_ty),
        ShapeInner::Tuple(shapes) => ModeScheme::Tuple(
            iter_shapes(shapes, res)
                .map(|(shape, res)| make_scheme_impl(insts, all_res, shape, res))
                .collect(),
        ),
        ShapeInner::Variants(shapes) => ModeScheme::Variants(IdVec::from_vec(
            iter_shapes(shapes.as_slice(), res)
                .map(|(shape, res)| make_scheme_impl(insts, all_res, shape, res))
                .collect(),
        )),
        &ShapeInner::SelfCustom(custom_id) => {
            let scheme_id = insts.resolve(ReleaseSpec {
                custom_id,
                res: all_res.iter().cloned().collect(),
            });
            ModeScheme::Custom(scheme_id, custom_id)
        }
        &ShapeInner::Custom(custom_id) => {
            let scheme_id = insts.resolve(ReleaseSpec {
                custom_id,
                res: res.iter().cloned().collect(),
            });
            ModeScheme::Custom(scheme_id, custom_id)
        }
        ShapeInner::Array(shape) => {
            let inner = make_scheme_impl(insts, all_res, shape, &res[1..]);
            ModeScheme::Array(res[0], Box::new(inner))
        }
        ShapeInner::HoleArray(shape) => {
            let inner = make_scheme_impl(insts, all_res, shape, &res[1..]);
            ModeScheme::HoleArray(res[0], Box::new(inner))
        }
        ShapeInner::Boxed(shape) => {
            let inner = make_scheme_impl(insts, all_res, shape, &res[1..]);
            ModeScheme::Boxed(res[0], Box::new(inner))
        }
    }
}

fn make_scheme(insts: &mut ReleaseInstances, shape: &Shape, res: &[Mode]) -> ModeScheme {
    make_scheme_impl(insts, res, shape, res)
}

fn lower_type(shape: &Shape) -> rc::Type {
    match &*shape.inner {
        ShapeInner::Bool => rc::Type::Bool,
        ShapeInner::Num(num_ty) => rc::Type::Num(*num_ty),
        ShapeInner::Tuple(shapes) => rc::Type::Tuple(shapes.map_refs(|shape| lower_type(shape))),
        ShapeInner::Variants(shapes) => {
            rc::Type::Variants(shapes.map_refs(|_, shape| lower_type(shape)))
        }
        ShapeInner::Custom(id) | ShapeInner::SelfCustom(id) => rc::Type::Custom(*id),
        ShapeInner::Array(shape) => rc::Type::Array(Box::new(lower_type(shape))),
        ShapeInner::HoleArray(shape) => rc::Type::HoleArray(Box::new(lower_type(shape))),
        ShapeInner::Boxed(shape) => rc::Type::Boxed(Box::new(lower_type(shape))),
    }
}

#[derive(Clone, Debug)]
enum RcOpPlan {
    Custom(Box<RcOpPlan>),
    Tuple(BTreeMap<usize, RcOpPlan>),
    Variants(BTreeMap<first_ord::VariantId, RcOpPlan>),
    LeafOp,
    NoOp,
}

impl RcOpPlan {
    fn from_selector_impl(
        customs: &annot::CustomTypes,
        true_: &BTreeSet<SlotId>,
        slots: (usize, usize),
        shape: &Shape,
    ) -> Self {
        match &*shape.inner {
            ShapeInner::Bool => Self::NoOp,
            ShapeInner::Num(_) => Self::NoOp,
            ShapeInner::Tuple(shapes) => {
                let mut plans = BTreeMap::new();
                let mut start = 0;
                for (i, shape) in shapes.iter().enumerate() {
                    let end = start + shape.num_slots;
                    let plan = RcOpPlan::from_selector_impl(customs, true_, (start, end), shape);
                    if !matches!(plan, RcOpPlan::NoOp) {
                        plans.insert(i, plan);
                    }
                    start = end;
                }
                debug_assert_eq!(start, shape.num_slots);
                if plans.is_empty() {
                    Self::NoOp
                } else {
                    Self::Tuple(plans)
                }
            }
            ShapeInner::Variants(shapes) => {
                let mut plans = BTreeMap::new();
                let mut start = 0;
                for (i, shape) in shapes {
                    let end = start + shape.num_slots;
                    let plan = RcOpPlan::from_selector_impl(customs, true_, (start, end), shape);
                    if !matches!(plan, RcOpPlan::NoOp) {
                        plans.insert(i, plan);
                    }
                    start = end;
                }
                debug_assert_eq!(start, shape.num_slots);
                if plans.is_empty() {
                    Self::NoOp
                } else {
                    Self::Variants(plans)
                }
            }
            // The only time we hit this case is when there is a recursive type whose recursive
            // occurrence is not guarded by a box. The type guarding pass ensures this only occurs
            // for zero-sized types, which require no non-trivial retain/release operations.
            ShapeInner::SelfCustom(_) => Self::NoOp,
            ShapeInner::Custom(id) => {
                let plan = RcOpPlan::from_selector_impl(
                    customs,
                    true_,
                    slots,
                    &customs.types[*id].content,
                );
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

    fn from_selector(customs: &annot::CustomTypes, sel: &Selector) -> Self {
        Self::from_selector_impl(customs, &sel.true_, (0, sel.shape.num_slots), &sel.shape)
    }
}

/// The returned `LocalId` always refers to a binding of type `()` (the result of the final
/// retain/release operation). We propagate this outward to minimize the number of `let: () = ()`
/// bindings we have to generate, which makes the generated code slightly cleaner.
fn build_plan(
    customs: &annot::CustomTypes,
    insts: &mut ReleaseInstances,
    rc_op: annot::RcOp,
    root_id: rc::LocalId,
    root_shape: &Shape,
    root_res: &[ResModes<Mode>],
    plan: &RcOpPlan,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    match plan {
        RcOpPlan::NoOp => builder.add_binding((rc::Type::Tuple(vec![]), rc::Expr::Tuple(vec![]))),

        RcOpPlan::LeafOp => {
            let rc_op = match rc_op {
                annot::RcOp::Retain => rc::RcOp::Retain,
                annot::RcOp::Release => rc::RcOp::Release(make_scheme(
                    insts,
                    &root_shape,
                    &prepare_resources(root_res),
                )),
            };
            builder.add_binding((rc::Type::Tuple(vec![]), rc::Expr::RcOp(rc_op, root_id)))
        }

        RcOpPlan::Tuple(plans) => {
            let ShapeInner::Tuple(shapes) = &*root_shape.inner else {
                unreachable!()
            };

            plans
                .iter()
                .zip(iter_shapes(shapes, root_res))
                .map(|((idx, plan), (shape, res))| {
                    let field_local = builder
                        .add_binding((lower_type(shape), rc::Expr::TupleField(root_id, *idx)));
                    build_plan(
                        customs,
                        insts,
                        rc_op,
                        field_local,
                        shape,
                        res,
                        plan,
                        builder,
                    )
                })
                .last()
                .unwrap()
        }

        RcOpPlan::Variants(plans) => {
            let ShapeInner::Variants(shapes) = &*root_shape.inner else {
                unreachable!()
            };

            let mut cases = Vec::new();
            let iter = plans.iter().zip(iter_shapes(shapes.as_slice(), root_res));
            for ((variant_id, plan), (shape, res)) in iter {
                let cond = rc::Condition::Variant(*variant_id, Box::new(rc::Condition::Any));
                let variant_ty = lower_type(shape);

                let mut case_builder = builder.child();
                let content_id = case_builder.add_binding((
                    variant_ty.clone(),
                    rc::Expr::UnwrapVariant(*variant_id, root_id),
                ));

                let unit = build_plan(
                    customs,
                    insts,
                    rc_op,
                    content_id,
                    shape,
                    res,
                    plan,
                    &mut case_builder,
                );

                cases.push((cond, case_builder.to_expr(unit)))
            }

            // For exhaustivity
            cases.push((rc::Condition::Any, rc::Expr::Tuple(vec![])));

            builder.add_binding((
                rc::Type::Tuple(vec![]),
                rc::Expr::Branch(root_id, cases, rc::Type::Tuple(vec![])),
            ))
        }

        RcOpPlan::Custom(plan) => {
            let ShapeInner::Custom(custom_id) = &*root_shape.inner else {
                unreachable!()
            };

            let content = &customs.types[*custom_id].content;
            let content_id = builder.add_binding((
                lower_type(content),
                rc::Expr::UnwrapCustom(*custom_id, root_id),
            ));
            build_plan(
                customs, insts, rc_op, content_id, content, root_res, plan, builder,
            )
        }
    }
}

#[derive(Clone, Debug)]
struct LocalInfo {
    old_ty: ob::Type,
    new_ty: rc::Type,
    new_id: rc::LocalId,
}

fn lower_expr(
    funcs: &IdVec<ob::CustomFuncId, annot::FuncDef>,
    customs: &annot::CustomTypes,
    insts: &mut ReleaseInstances,
    ctx: &mut LocalContext<annot::LocalId, LocalInfo>,
    path: &Path,
    expr: &annot::Expr,
    ret_ty: &rc::Type,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    let new_expr = match expr {
        // The only interesting case...
        annot::Expr::RcOp(op, sel, arg) => {
            let plan = RcOpPlan::from_selector(customs, sel);
            let arg = ctx.local_binding(*arg);
            let unit = build_plan(
                customs,
                insts,
                *op,
                arg.new_id,
                &arg.old_ty.shape,
                arg.old_ty.res.as_slice(),
                &plan,
                builder,
            );
            rc::Expr::Local(unit)
        }

        annot::Expr::Local(local) => rc::Expr::Local(ctx.local_binding(*local).new_id),
        annot::Expr::Call(purity, func, arg) => {
            rc::Expr::Call(*purity, *func, ctx.local_binding(*arg).new_id)
        }
        annot::Expr::Branch(discrim, arms, ret_ty) => {
            let ret_ty = lower_type(&ret_ty.shape);
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
                    let low_ty = lower_type(&binding_ty.shape);

                    let final_local =
                        lower_expr(funcs, customs, insts, ctx, path, expr, &low_ty, builder);
                    ctx.add_local(LocalInfo {
                        old_ty: binding_ty.clone(),
                        new_ty: low_ty,
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
            variants.map_refs(|_, ty| lower_type(&ty.shape)),
            *variant_id,
            ctx.local_binding(*content).new_id,
        ),
        annot::Expr::UnwrapVariant(variant_id, wrapped) => {
            rc::Expr::UnwrapVariant(*variant_id, ctx.local_binding(*wrapped).new_id)
        }
        annot::Expr::WrapBoxed(content, item_ty) => rc::Expr::WrapBoxed(
            ctx.local_binding(*content).new_id,
            lower_type(&item_ty.shape),
        ),
        annot::Expr::UnwrapBoxed(wrapped, item_ty) => rc::Expr::UnwrapBoxed(
            ctx.local_binding(*wrapped).new_id,
            lower_type(&item_ty.shape),
        ),
        annot::Expr::WrapCustom(_custom_id, content) => {
            let rc::Type::Custom(custom_id) = ret_ty else {
                unreachable!();
            };
            rc::Expr::WrapCustom(*custom_id, ctx.local_binding(*content).new_id)
        }
        annot::Expr::UnwrapCustom(_custom_id, wrapped) => {
            let info = ctx.local_binding(*wrapped);
            let rc::Type::Custom(custom_id) = &info.new_ty else {
                unreachable!();
            };
            rc::Expr::UnwrapCustom(*custom_id, info.new_id)
        }
        annot::Expr::Intrinsic(intr, arg) => {
            rc::Expr::Intrinsic(*intr, ctx.local_binding(*arg).new_id)
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Get(item_ty, arr, idx)) => {
            let scheme = make_scheme(
                insts,
                &item_ty.shape,
                &prepare_resources(item_ty.res.as_slice()),
            );
            rc::Expr::ArrayOp(rc::ArrayOp::Get(
                scheme,
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*idx).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Extract(item_ty, arr, idx)) => {
            let scheme = make_scheme(
                insts,
                &item_ty.shape,
                &prepare_resources(item_ty.res.as_slice()),
            );
            rc::Expr::ArrayOp(rc::ArrayOp::Extract(
                scheme,
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*idx).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Len(item_ty, arr)) => {
            let scheme = make_scheme(
                insts,
                &item_ty.shape,
                &prepare_resources(item_ty.res.as_slice()),
            );
            rc::Expr::ArrayOp(rc::ArrayOp::Len(scheme, ctx.local_binding(*arr).new_id))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Push(item_ty, arr, item)) => {
            let scheme = make_scheme(
                insts,
                &item_ty.shape,
                &prepare_resources(item_ty.res.as_slice()),
            );
            rc::Expr::ArrayOp(rc::ArrayOp::Push(
                scheme,
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*item).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Pop(item_ty, arr)) => {
            let scheme = make_scheme(
                insts,
                &item_ty.shape,
                &prepare_resources(item_ty.res.as_slice()),
            );
            rc::Expr::ArrayOp(rc::ArrayOp::Pop(scheme, ctx.local_binding(*arr).new_id))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Replace(item_ty, arr, idx)) => {
            let scheme = make_scheme(
                insts,
                &item_ty.shape,
                &prepare_resources(item_ty.res.as_slice()),
            );
            rc::Expr::ArrayOp(rc::ArrayOp::Replace(
                scheme,
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*idx).new_id,
            ))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(item_ty, arr, cap)) => {
            let scheme = make_scheme(
                insts,
                &item_ty.shape,
                &prepare_resources(item_ty.res.as_slice()),
            );
            rc::Expr::ArrayOp(rc::ArrayOp::Reserve(
                scheme,
                ctx.local_binding(*arr).new_id,
                ctx.local_binding(*cap).new_id,
            ))
        }
        annot::Expr::IoOp(annot::IoOp::Input) => rc::Expr::IoOp(rc::IoOp::Input),
        annot::Expr::IoOp(annot::IoOp::Output(local)) => {
            rc::Expr::IoOp(rc::IoOp::Output(ctx.local_binding(*local).new_id))
        }
        annot::Expr::Panic(ret_ty, msg) => {
            rc::Expr::Panic(lower_type(&ret_ty.shape), ctx.local_binding(*msg).new_id)
        }
        annot::Expr::ArrayLit(item_ty, items) => {
            let scheme = make_scheme(
                insts,
                &item_ty.shape,
                &prepare_resources(item_ty.res.as_slice()),
            );
            rc::Expr::ArrayLit(
                scheme,
                items
                    .iter()
                    .map(|local| ctx.local_binding(*local).new_id)
                    .collect(),
            )
        }
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
    insts: &mut ReleaseInstances,
    func: &annot::FuncDef,
) -> rc::FuncDef {
    let arg_type = lower_type(&func.arg_ty.shape);
    let ret_type = lower_type(&func.ret_ty.shape);

    let mut ctx = LocalContext::new();
    ctx.add_local(LocalInfo {
        old_ty: func.arg_ty.clone(),
        new_ty: arg_type.clone(),
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

    let mut queue = ReleaseInstances::new();
    let mut funcs = IdVec::new();

    for (id, func) in &program.funcs {
        let new_func = lower_func(&program.custom_types, &program.funcs, &mut queue, &func);
        let pushed_id = funcs.push(new_func);
        debug_assert_eq!(pushed_id, id);
        progress.update(1);
    }

    progress.finish();

    let mut schemes = IdVec::new();
    while let Some((release_id, spec)) = queue.pop_pending() {
        let scheme = make_scheme(
            &mut queue,
            &program.custom_types.types[spec.custom_id].content,
            &spec.res,
        );
        let pushed_id = schemes.push(scheme);
        debug_assert_eq!(pushed_id, release_id);
    }

    let custom_types = rc::CustomTypes {
        types: program
            .custom_types
            .types
            .map_refs(|_, ty| lower_type(&ty.content)),
    };
    rc::Program {
        mod_symbols: program.mod_symbols,
        custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        func_symbols: program.func_symbols,
        schemes,
        profile_points: program.profile_points,
        main: program.main,
    }
}
