use crate::data::first_order_ast as first_ord;
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast::{enumerate_shapes, iter_shapes, Lt, Mode, ShapeInner, SlotId};
use crate::data::obligation_annot_ast::{self as ob, BindRes, CustomTypeId, Shape, ValueRes};
use crate::data::rc_annot_ast::{self as annot, Selector};
use crate::data::rc_specialized_ast::{self as rc, ModeScheme, ModeSchemeId};
use crate::pretty_print::utils::FuncRenderer;
use id_collections::{Count, IdVec};
use morphic_common::util::collection_ext::VecExt;
use morphic_common::util::instance_queue::InstanceQueue;
use morphic_common::util::iter::IterExt;
use morphic_common::util::let_builder::{self, BuildMatch};
use morphic_common::util::local_context::LocalContext;
use morphic_common::util::progress_logger::{ProgressLogger, ProgressSession};
use std::collections::BTreeSet;
use std::fmt;

type LetManyBuilder = let_builder::LetManyBuilder<rc::Expr>;
type ReleaseInstances = InstanceQueue<ReleaseSpec, ModeSchemeId>;

// We only care about storage modes when creating release plans. We throw out any other modes to
// avoid duplicate specializations.
fn prepare_value_res(res: &[ValueRes<Lt>]) -> Vec<Mode> {
    res.iter().map(|res| res.mode()).collect()
}

fn prepare_bind_res(res: &[BindRes<Lt>]) -> Vec<Mode> {
    res.iter().map(|res| res.mode()).collect()
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ReleaseSpec {
    custom_id: CustomTypeId,
    res: Vec<Mode>,
}

impl ReleaseSpec {
    fn new(custom_id: CustomTypeId, res: Vec<Mode>) -> Self {
        Self { custom_id, res }
    }

    fn make_scheme(
        &self,
        customs: &annot::CustomTypes,
        insts: &mut ReleaseInstances,
    ) -> ModeScheme {
        let custom = &customs.types[self.custom_id];
        let res = custom.subst_helper.do_subst(&self.res);
        make_scheme(insts, &custom.content, &res)
    }
}

fn make_scheme(insts: &mut ReleaseInstances, shape: &Shape, res: &[Mode]) -> ModeScheme {
    match &*shape.inner {
        ShapeInner::Bool => ModeScheme::Bool,
        ShapeInner::Num(num_ty) => ModeScheme::Num(*num_ty),
        ShapeInner::Tuple(shapes) => ModeScheme::Tuple(
            iter_shapes(shapes, res)
                .map(|(shape, res)| make_scheme(insts, shape, res))
                .collect(),
        ),
        ShapeInner::Variants(shapes) => ModeScheme::Variants(IdVec::from_vec(
            iter_shapes(shapes.as_slice(), res)
                .map(|(shape, res)| make_scheme(insts, shape, res))
                .collect(),
        )),
        &ShapeInner::SelfCustom(custom_id) => {
            let scheme_id =
                insts.resolve(ReleaseSpec::new(custom_id, res.iter().cloned().collect()));
            ModeScheme::Custom(scheme_id, custom_id)
        }
        &ShapeInner::Custom(custom_id) => {
            let scheme_id =
                insts.resolve(ReleaseSpec::new(custom_id, res.iter().cloned().collect()));
            ModeScheme::Custom(scheme_id, custom_id)
        }
        ShapeInner::Array(shape) => {
            let inner = make_scheme(insts, shape, &res[1..]);
            ModeScheme::Array(res[0], Box::new(inner))
        }
        ShapeInner::HoleArray(shape) => {
            let inner = make_scheme(insts, shape, &res[1..]);
            ModeScheme::HoleArray(res[0], Box::new(inner))
        }
        ShapeInner::Boxed(shape) => {
            let inner = make_scheme(insts, shape, &res[1..]);
            ModeScheme::Boxed(res[0], Box::new(inner))
        }
    }
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
    Tuple(Vec<RcOpPlan>),
    Variants(IdVec<first_ord::VariantId, RcOpPlan>),
    LeafOp,
    NoOp,
}

impl RcOpPlan {
    fn is_noop(&self) -> bool {
        matches!(self, RcOpPlan::NoOp)
    }
}

impl fmt::Display for RcOpPlan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RcOpPlan::Custom(plan) => write!(f, "Custom({})", plan),
            RcOpPlan::Tuple(plans) => {
                let elems = plans
                    .iter()
                    .map(|plan| plan.to_string())
                    .collect::<Vec<_>>();
                write!(f, "({})", elems.join(", "))
            }
            RcOpPlan::Variants(plans) => {
                let variants = plans
                    .values()
                    .map(|plan| plan.to_string())
                    .collect::<Vec<_>>();
                write!(f, "{{{}}}", variants.join(", "))
            }
            RcOpPlan::LeafOp => write!(f, "*"),
            RcOpPlan::NoOp => write!(f, "_"),
        }
    }
}

impl RcOpPlan {
    fn from_selector_impl(
        customs: &annot::CustomTypes,
        true_: &BTreeSet<SlotId>,
        start: usize,
        shape: &Shape,
        res: &[BindRes<Lt>],
    ) -> Self {
        match &*shape.inner {
            ShapeInner::Bool => Self::NoOp,
            ShapeInner::Num(_) => Self::NoOp,
            ShapeInner::Tuple(shapes) => {
                let plans = enumerate_shapes(shapes, res, start)
                    .map(|(shape, (start, _), res)| {
                        RcOpPlan::from_selector_impl(customs, true_, start, shape, res)
                    })
                    .collect::<Vec<_>>();

                if plans.iter().all(RcOpPlan::is_noop) {
                    Self::NoOp
                } else {
                    Self::Tuple(plans)
                }
            }
            ShapeInner::Variants(shapes) => {
                let plans = enumerate_shapes(shapes.as_slice(), res, start)
                    .map(|(shape, (start, _), res)| {
                        RcOpPlan::from_selector_impl(customs, true_, start, shape, res)
                    })
                    .collect::<Vec<_>>();

                if plans.iter().all(RcOpPlan::is_noop) {
                    Self::NoOp
                } else {
                    Self::Variants(IdVec::from_vec(plans))
                }
            }
            // The only time we hit this case is when there is a recursive type whose recursive
            // occurrence is not guarded by heap indirection. The type guarding pass ensures this
            // only occurs for zero-sized types, which require no non-trivial retain/release
            // operations.
            ShapeInner::SelfCustom(_) => Self::NoOp,
            ShapeInner::Custom(id) => {
                let plan = RcOpPlan::from_selector_impl(
                    customs,
                    true_,
                    start,
                    &customs.types[*id].content,
                    // We are on the stack. The custom is acyclic and the substitution is trivial.
                    res,
                );

                if plan.is_noop() {
                    Self::NoOp
                } else {
                    Self::Custom(Box::new(plan))
                }
            }
            ShapeInner::Array(_) | ShapeInner::HoleArray(_) | ShapeInner::Boxed(_) => {
                let mode = res[0].mode();
                if true_.contains(&SlotId(start)) && mode == Mode::Owned {
                    Self::LeafOp
                } else {
                    Self::NoOp
                }
            }
        }
    }

    fn from_selector(customs: &annot::CustomTypes, ty: &ob::BindType, sel: &Selector) -> Self {
        debug_assert_eq!(ty.shape(), &sel.shape);
        Self::from_selector_impl(customs, &sel.true_, 0, &sel.shape, ty.res().as_slice())
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
    root_res: &[BindRes<Lt>],
    plan: &RcOpPlan,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    match plan {
        RcOpPlan::NoOp => builder.add_binding(rc::Type::Tuple(vec![]), rc::Expr::Tuple(vec![])),

        RcOpPlan::LeafOp => {
            let scheme = make_scheme(insts, &root_shape, &prepare_bind_res(root_res));
            let rc_op = match rc_op {
                annot::RcOp::Retain => rc::RcOp::Retain,
                annot::RcOp::Release => rc::RcOp::Release,
            };
            builder.add_binding(
                rc::Type::Tuple(vec![]),
                rc::Expr::RcOp(scheme, rc_op, root_id),
            )
        }

        RcOpPlan::Tuple(plans) => {
            let ShapeInner::Tuple(shapes) = &*root_shape.inner else {
                unreachable!()
            };

            plans
                .iter()
                .enumerate()
                .zip(iter_shapes(shapes, root_res))
                .filter(|((_, plan), (_, _))| !plan.is_noop())
                .map(|((idx, plan), (shape, res))| {
                    let field_local =
                        builder.add_binding(lower_type(shape), rc::Expr::TupleField(root_id, idx));
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
                // When we construct plans, we propagate `NoOp`s such that we only generate a
                // `Tuple` plan if there is a non-trivial field plan.
                .unwrap()
        }

        RcOpPlan::Variants(plans) => {
            let ShapeInner::Variants(shapes) = &*root_shape.inner else {
                unreachable!()
            };

            let variant_data = plans
                .iter()
                .zip(iter_shapes(shapes.as_slice(), root_res))
                .collect::<Vec<_>>();
            let variant_data = IdVec::from_vec(variant_data);

            let cases = plans
                .iter()
                .zip_eq(shapes.values())
                .filter(|((_, plan), _)| !plan.is_noop())
                .map(|((variant_id, _), shape)| (variant_id, lower_type(shape)));

            rc::Expr::build_match(
                builder,
                root_id,
                cases,
                &rc::Type::Tuple(vec![]),
                || rc::Expr::Tuple(vec![]),
                |builder, variant_id, unwrapped| {
                    let ((_, plan), (shape, res)) = variant_data[variant_id];
                    build_plan(customs, insts, rc_op, unwrapped, shape, res, plan, builder)
                },
            )
        }

        RcOpPlan::Custom(plan) => {
            let ShapeInner::Custom(custom_id) = &*root_shape.inner else {
                unreachable!()
            };

            let custom = &customs.types[*custom_id];
            let content_id = builder.add_binding(
                lower_type(&custom.content),
                rc::Expr::UnwrapCustom(*custom_id, root_id),
            );
            build_plan(
                customs,
                insts,
                rc_op,
                content_id,
                // We are on the stack. The custom is acyclic and the substitution is trivial.
                &custom.content,
                root_res,
                plan,
                builder,
            )
        }
    }
}

#[derive(Clone, Debug)]
struct LocalInfo {
    old_ty: ob::BindType,
    new_ty: rc::Type,
    new_id: rc::LocalId,
}

fn new_id(ctx: &LocalContext<annot::LocalId, LocalInfo>, local: &annot::Occur) -> rc::LocalId {
    ctx.local_binding(local.id).new_id
}

fn lower_expr(
    funcs: &IdVec<ob::CustomFuncId, annot::FuncDef>,
    customs: &annot::CustomTypes,
    insts: &mut ReleaseInstances,
    ctx: &mut LocalContext<annot::LocalId, LocalInfo>,
    expr: &annot::Expr,
    ret_ty: &rc::Type,
    mut metadata: Metadata,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    let new_expr = match expr {
        // The only interesting case...
        annot::Expr::RcOp(op, sel, arg_id) => {
            let arg = ctx.local_binding(*arg_id);
            let plan = RcOpPlan::from_selector(customs, &arg.old_ty, sel);
            // println!(
            //     "%{}: {}",
            //     arg_id.0,
            //     ctx.local_binding(*arg_id).old_ty.display()
            // );
            // println!("{}", sel.display());
            // println!("{}", plan);

            metadata.add_comment(format!(
                "rc_specialize: {}: {plan}",
                match op {
                    annot::RcOp::Retain => "retain",
                    annot::RcOp::Release => "release",
                },
            ));

            let unit = build_plan(
                customs,
                insts,
                *op,
                arg.new_id,
                &arg.old_ty.shape(),
                arg.old_ty.res().as_slice(),
                &plan,
                builder,
            );
            rc::Expr::Local(unit)
        }

        annot::Expr::Local(local) => rc::Expr::Local(new_id(ctx, &local)),
        annot::Expr::Call(purity, func, arg) => rc::Expr::Call(*purity, *func, new_id(ctx, &arg)),
        annot::Expr::LetMany(bindings, ret) => {
            let final_local = ctx.with_scope(|ctx| {
                for (binding_ty, expr, metadata) in bindings {
                    let low_ty = lower_type(&binding_ty.shape());

                    let final_local = lower_expr(
                        funcs,
                        customs,
                        insts,
                        ctx,
                        expr,
                        &low_ty,
                        metadata.clone(),
                        builder,
                    );
                    ctx.add_local(LocalInfo {
                        old_ty: binding_ty.clone(),
                        new_ty: low_ty,
                        new_id: final_local,
                    });
                }
                new_id(ctx, &ret)
            });

            // Note: Early return! We circumvent the usual return flow because we don't actually
            // want to create an expression directly corresponding to this 'let' block. The 'let'
            // block's bindings just get absorbed into the ambient `builder`.
            return final_local;
        }
        annot::Expr::If(discrim, then_case, else_case) => {
            let then_case = {
                let mut case_builder = builder.child();
                let final_local = lower_expr(
                    funcs,
                    customs,
                    insts,
                    ctx,
                    then_case,
                    ret_ty,
                    Metadata::default(),
                    &mut case_builder,
                );
                case_builder.to_expr(final_local)
            };
            let else_case = {
                let mut case_builder = builder.child();
                let final_local = lower_expr(
                    funcs,
                    customs,
                    insts,
                    ctx,
                    else_case,
                    ret_ty,
                    Metadata::default(),
                    &mut case_builder,
                );
                case_builder.to_expr(final_local)
            };
            rc::Expr::If(
                new_id(ctx, &discrim),
                Box::new(then_case),
                Box::new(else_case),
            )
        }
        annot::Expr::CheckVariant(variant_id, variant) => {
            rc::Expr::CheckVariant(*variant_id, new_id(ctx, &variant))
        }
        annot::Expr::Unreachable(ty) => rc::Expr::Unreachable(lower_type(&ty.shape())),
        annot::Expr::Tuple(fields) => {
            rc::Expr::Tuple(fields.iter().map(|local| new_id(ctx, &local)).collect())
        }
        annot::Expr::TupleField(tup, idx) => rc::Expr::TupleField(new_id(ctx, &tup), *idx),
        annot::Expr::WrapVariant(variants, variant_id, content) => rc::Expr::WrapVariant(
            variants.map_refs(|_, ty| lower_type(&ty.shape())),
            *variant_id,
            new_id(ctx, &content),
        ),
        annot::Expr::UnwrapVariant(variant_id, wrapped) => {
            rc::Expr::UnwrapVariant(*variant_id, new_id(ctx, &wrapped))
        }
        annot::Expr::WrapBoxed(content, output_ty) => {
            let output_scheme = make_scheme(
                insts,
                &output_ty.shape(),
                &prepare_value_res(output_ty.res().as_slice()),
            );
            rc::Expr::WrapBoxed(new_id(ctx, &content), output_scheme)
        }
        annot::Expr::UnwrapBoxed(wrapped, output_ty) => {
            let input_scheme = make_scheme(
                insts,
                &wrapped.ty.shape(),
                &prepare_value_res(wrapped.ty.res().as_slice()),
            );
            let output_scheme = make_scheme(
                insts,
                &output_ty.shape(),
                &prepare_value_res(output_ty.res().as_slice()),
            );
            rc::Expr::UnwrapBoxed(new_id(ctx, &wrapped), input_scheme, output_scheme)
        }
        annot::Expr::WrapCustom(custom_id, content) => {
            rc::Expr::WrapCustom(*custom_id, new_id(ctx, &content))
        }
        annot::Expr::UnwrapCustom(custom_id, wrapped) => {
            rc::Expr::UnwrapCustom(*custom_id, new_id(ctx, &wrapped))
        }
        annot::Expr::Intrinsic(intr, arg) => rc::Expr::Intrinsic(*intr, new_id(ctx, &arg)),
        annot::Expr::ArrayOp(annot::ArrayOp::Get(arr, idx)) => {
            let scheme = make_scheme(
                insts,
                &arr.ty.shape(),
                &prepare_value_res(arr.ty.res().as_slice()),
            );
            rc::Expr::ArrayOp(
                scheme,
                rc::ArrayOp::Get(new_id(ctx, &arr), new_id(ctx, &idx)),
            )
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Extract(arr, idx)) => {
            let scheme = make_scheme(
                insts,
                &arr.ty.shape(),
                &prepare_value_res(arr.ty.res().as_slice()),
            );
            rc::Expr::ArrayOp(
                scheme,
                rc::ArrayOp::Extract(new_id(ctx, &arr), new_id(ctx, &idx)),
            )
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Len(arr)) => {
            let scheme = make_scheme(
                insts,
                &arr.ty.shape(),
                &prepare_value_res(arr.ty.res().as_slice()),
            );
            rc::Expr::ArrayOp(scheme, rc::ArrayOp::Len(new_id(ctx, &arr)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Push(arr, item)) => {
            let scheme = make_scheme(
                insts,
                &arr.ty.shape(),
                &prepare_value_res(arr.ty.res().as_slice()),
            );
            rc::Expr::ArrayOp(
                scheme,
                rc::ArrayOp::Push(new_id(ctx, &arr), new_id(ctx, &item)),
            )
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Pop(arr)) => {
            let scheme = make_scheme(
                insts,
                &arr.ty.shape(),
                &prepare_value_res(arr.ty.res().as_slice()),
            );
            rc::Expr::ArrayOp(scheme, rc::ArrayOp::Pop(new_id(ctx, &arr)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Replace(arr, idx)) => {
            let scheme = make_scheme(
                insts,
                &arr.ty.shape(),
                &prepare_value_res(arr.ty.res().as_slice()),
            );
            rc::Expr::ArrayOp(
                scheme,
                rc::ArrayOp::Replace(new_id(ctx, &arr), new_id(ctx, &idx)),
            )
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(arr, cap)) => {
            let scheme = make_scheme(
                insts,
                &arr.ty.shape(),
                &prepare_value_res(arr.ty.res().as_slice()),
            );
            rc::Expr::ArrayOp(
                scheme,
                rc::ArrayOp::Reserve(new_id(ctx, &arr), new_id(ctx, &cap)),
            )
        }
        annot::Expr::IoOp(annot::IoOp::Input) => rc::Expr::IoOp(rc::IoOp::Input),
        annot::Expr::IoOp(annot::IoOp::Output(local)) => {
            let scheme = make_scheme(
                insts,
                &local.ty.shape(),
                &prepare_value_res(local.ty.res().as_slice()),
            );
            rc::Expr::IoOp(rc::IoOp::Output(scheme, new_id(ctx, &local)))
        }
        annot::Expr::Panic(ret_ty, msg) => {
            let input_scheme = make_scheme(
                insts,
                &msg.ty.shape(),
                &prepare_value_res(msg.ty.res().as_slice()),
            );
            rc::Expr::Panic(lower_type(&ret_ty.shape()), input_scheme, new_id(ctx, &msg))
        }
        annot::Expr::ArrayLit(item_ty, items) => {
            let scheme = make_scheme(
                insts,
                &item_ty.shape(),
                &prepare_value_res(item_ty.res().as_slice()),
            );
            rc::Expr::ArrayLit(
                scheme,
                items.iter().map(|local| new_id(ctx, &local)).collect(),
            )
        }
        annot::Expr::BoolLit(lit) => rc::Expr::BoolLit(*lit),
        annot::Expr::ByteLit(lit) => rc::Expr::ByteLit(*lit),
        annot::Expr::IntLit(lit) => rc::Expr::IntLit(*lit),
        annot::Expr::FloatLit(lit) => rc::Expr::FloatLit(*lit),
    };

    builder.add_binding_with_metadata(ret_ty.clone(), new_expr, metadata.clone())
}

fn lower_func(
    customs: &annot::CustomTypes,
    _func_renderer: &FuncRenderer<ob::CustomFuncId>,
    funcs: &IdVec<ob::CustomFuncId, annot::FuncDef>,
    insts: &mut ReleaseInstances,
    func_id: ob::CustomFuncId,
) -> rc::FuncDef {
    // println!("---------------------------------");
    // println!(
    //     "func_id: {}, func: {}",
    //     func_id.0,
    //     func_renderer.render(func_id)
    // );

    let func = &funcs[func_id];
    let arg_type = lower_type(&func.arg_ty.shape());
    let ret_type = lower_type(&func.ret_ty.shape());

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
        &func.body,
        &ret_type,
        Metadata::default(),
        &mut builder,
    );
    // println!("+++++++++++++++++++++++++++++++++");

    rc::FuncDef {
        purity: func.purity,
        arg_type,
        ret_type,
        body: builder.to_expr(final_local),
        profile_point: func.profile_point,
    }
}

pub fn rc_specialize(program: annot::Program, progress: impl ProgressLogger) -> rc::Program {
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);
    let mut progress = progress.start_session(Some(program.funcs.len()));

    let mut queue = ReleaseInstances::new();
    let mut funcs = IdVec::new();

    let customs = &program.custom_types;

    for (func_id, _) in &program.funcs {
        let new_func = lower_func(customs, &func_renderer, &program.funcs, &mut queue, func_id);
        let pushed_id = funcs.push(new_func);
        debug_assert_eq!(pushed_id, func_id);
        progress.update(1);
    }

    progress.finish();

    let mut schemes = IdVec::new();
    while let Some((release_id, spec)) = queue.pop_pending() {
        let scheme = spec.make_scheme(customs, &mut queue);
        let pushed_id = schemes.push(scheme);
        debug_assert_eq!(pushed_id, release_id);
    }

    let custom_types = rc::CustomTypes {
        types: customs.types.map_refs(|_, ty| lower_type(&ty.content)),
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
