use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast2::{
    self as annot, Lt, LtParam, Mode, ModeParam, ModeSolution, Overlay,
};
use crate::data::rc_specialized_ast2 as rc;
use crate::util::iter::IterExt;
use crate::util::local_context;
use crate::util::progress_logger::ProgressLogger;
use id_collections::{id_type, Id, IdVec};
use std::collections::BTreeMap;

type AnnotExpr = annot::Expr<ModeSolution, Lt>;
type AnnotType = annot::Type<ModeSolution, Lt>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Status {
    Here,
    Gone,
}

type Sel = Overlay<Status>;
type StructLt = Overlay<annot::Lt>;

impl Sel {
    fn from_ty(ty: &AnnotType) -> Self {
        use Overlay as O;
        match ty {
            annot::Type::Bool => O::Bool,
            annot::Type::Num(num_ty) => O::Num(*num_ty),
            annot::Type::Tuple(field_tys) => O::Tuple(field_tys.iter().map(Sel::from_ty).collect()),
            annot::Type::Variants(variant_tys) => {
                O::Variants(variant_tys.map_refs(|_, ty| Sel::from_ty(ty)))
            }
            annot::Type::SelfCustom(id) => O::SelfCustom(*id),
            annot::Type::Custom(id, _, ov_sub) => O::Custom(*id, ov_sub.map_vals(|_| Status::Here)),
            annot::Type::Array(_, _, _, _) => O::Array(Status::Here),
            annot::Type::HoleArray(_, _, _, _) => O::HoleArray(Status::Here),
            annot::Type::Boxed(_, _, _, _) => O::Boxed(Status::Here),
        }
    }

    fn and_eq(&mut self, other: &Sel) {
        let compute_status = |lhs, rhs| match (lhs, rhs) {
            (Status::Here, Status::Here) => Status::Here,
            _ => Status::Gone,
        };

        use Overlay as O;
        match (self, other) {
            (O::Bool, O::Bool) => {}
            (O::Num(lhs), O::Num(rhs)) => {
                debug_assert_eq!(lhs, rhs);
            }
            (O::Tuple(lhs), O::Tuple(rhs)) => {
                for (lhs, rhs) in lhs.iter_mut().zip_eq(rhs) {
                    lhs.and_eq(rhs);
                }
            }
            (O::Variants(lhs), O::Variants(rhs)) => {
                for (lhs, rhs) in lhs.values_mut().zip_eq(rhs.values()) {
                    lhs.and_eq(rhs);
                }
            }
            (O::SelfCustom(lhs_id), O::SelfCustom(rhs_id)) => {
                debug_assert_eq!(lhs_id, rhs_id);
            }
            (O::Custom(lhs_id, lhs_inner), O::Custom(rhs_id, rhs_inner)) => {
                debug_assert_eq!(lhs_id, rhs_id);
                for (lhs, rhs) in lhs_inner.0.values_mut().zip_eq(rhs_inner.0.values()) {
                    *lhs = compute_status(*lhs, *rhs);
                }
            }
            (O::Array(lhs), O::Array(rhs))
            | (O::HoleArray(lhs), O::HoleArray(rhs))
            | (O::Boxed(lhs), O::Boxed(rhs)) => {
                *lhs = compute_status(*lhs, *rhs);
            }
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug)]
enum RcOpPlan {
    NoOp,
    LeafOp,
    OnTupleFields(BTreeMap<usize, RcOpPlan>),
    OnVariantCases(BTreeMap<first_ord::VariantId, RcOpPlan>),
    OnCustom(Box<RcOpPlan>),
}

impl RcOpPlan {
    fn from_sel(customs: &annot::CustomTypes, sel: &Sel) -> Self {
        use Overlay as O;
        match sel {
            O::Bool => Self::NoOp,
            O::Num(_) => Self::NoOp,
            O::Tuple(fields) => {
                let mut sub_plans = BTreeMap::new();
                for (idx, field) in fields.iter().enumerate() {
                    let sub_plan = RcOpPlan::from_sel(customs, field);
                    if !matches!(sub_plan, RcOpPlan::NoOp) {
                        sub_plans.insert(idx, sub_plan);
                    }
                }

                if sub_plans.is_empty() {
                    Self::NoOp
                } else {
                    Self::OnTupleFields(sub_plans)
                }
            }
            O::Variants(variants) => {
                let mut sub_plans = BTreeMap::new();
                for (variant_id, variant) in variants {
                    let sub_plan = RcOpPlan::from_sel(customs, variant);
                    if !matches!(sub_plan, RcOpPlan::NoOp) {
                        sub_plans.insert(variant_id, sub_plan);
                    }
                }

                if sub_plans.is_empty() {
                    Self::NoOp
                } else {
                    Self::OnVariantCases(sub_plans)
                }
            }
            // The only time we hit this case is when there is a recursive type whose recursive
            // occurrence is not guarded by a box. Currently, such a type is necessarily zero-sized,
            // but we would need to update this logic if we did not "cut" every edge of type SCCs
            // with boxes (e.g. if we inserted the minimal number of boxes to do cycle breaking).
            O::SelfCustom(_) => Self::NoOp,
            O::Custom(id, sub) => {
                let inner = sub.apply_to(&customs.types[*id].overlay);
                let sub_plan = RcOpPlan::from_sel(customs, &inner);
                if matches!(sub_plan, RcOpPlan::NoOp) {
                    Self::NoOp
                } else {
                    Self::OnCustom(Box::new(sub_plan))
                }
            }
            O::Array(status) | O::HoleArray(status) | O::Boxed(status) => match status {
                Status::Here => Self::LeafOp,
                Status::Gone => Self::NoOp,
            },
        }
    }
}

#[derive(Clone, Debug)]
struct LetManyBuilder {
    free_locals: usize,
    bindings: Vec<(rc::Type, rc::Expr)>,
}

impl LetManyBuilder {
    fn new(free_locals: usize) -> Self {
        LetManyBuilder {
            free_locals,
            bindings: Vec::new(),
        }
    }

    fn add_binding(&mut self, ty: rc::Type, rhs: rc::Expr) -> rc::LocalId {
        let binding_id = rc::LocalId(self.free_locals + self.bindings.len());
        self.bindings.push((ty, rhs));
        binding_id
    }

    fn to_expr(self, ret: rc::LocalId) -> rc::Expr {
        debug_assert!(ret.0 < self.free_locals + self.bindings.len());
        rc::Expr::LetMany(self.bindings, ret)
    }

    fn child(&self) -> LetManyBuilder {
        LetManyBuilder::new(self.free_locals + self.bindings.len())
    }
}

fn build_plan(
    customs: &rc::CustomTypes,
    rc_op: rc::RcOp,
    root: rc::LocalId,
    root_ty: &rc::Type,
    plan: &RcOpPlan,
    builder: &mut LetManyBuilder,
) {
    match plan {
        RcOpPlan::NoOp => {}

        RcOpPlan::LeafOp => {
            builder.add_binding(
                rc::Type::Tuple(vec![]),
                rc::Expr::RcOp(
                    rc_op,
                    rc::RcOpDebugInfo::MustPreserve,
                    root_ty.clone(),
                    root,
                ),
            );
        }

        RcOpPlan::OnTupleFields(sub_plans) => {
            let rc::Type::Tuple(field_tys) = root_ty else {
                unreachable!()
            };

            for (idx, sub_plan) in sub_plans {
                let field_ty = &field_tys[*idx];
                let field_local =
                    builder.add_binding(field_ty.clone(), rc::Expr::TupleField(root, *idx));
                build_plan(customs, rc_op, field_local, field_ty, sub_plan, builder);
            }
        }

        RcOpPlan::OnVariantCases(sub_plans) => {
            let rc::Type::Variants(variant_tys) = root_ty else {
                unreachable!()
            };

            let mut cases = Vec::new();
            for (variant_id, sub_plan) in sub_plans {
                let variant_ty = &variant_tys[variant_id];
                let cond = rc::Condition::Variant(*variant_id, Box::new(rc::Condition::Any));

                let mut case_builder = builder.child();
                let content_id = case_builder.add_binding(
                    variant_ty.clone(),
                    rc::Expr::UnwrapVariant(*variant_id, root),
                );
                build_plan(
                    customs,
                    rc_op,
                    content_id,
                    variant_ty,
                    sub_plan,
                    &mut case_builder,
                );

                // We need to return *something* from this branch arm, so we return a `()` value.
                //
                // TODO: Should we reuse the result of the generated RC op to make the generated
                // code for this case slightly easier to read?
                let unit_id =
                    case_builder.add_binding(rc::Type::Tuple(vec![]), rc::Expr::Tuple(vec![]));

                cases.push((cond, case_builder.to_expr(unit_id)))
            }
            cases.push((rc::Condition::Any, rc::Expr::Tuple(vec![])));

            builder.add_binding(
                rc::Type::Tuple(vec![]),
                rc::Expr::Branch(root, cases, rc::Type::Tuple(vec![])),
            );
        }

        RcOpPlan::OnCustom(sub_plan) => {
            let rc::Type::Custom(custom_id) = root_ty else {
                unreachable!()
            };

            let content_ty = &customs.types[custom_id].content;

            let content_id =
                builder.add_binding(content_ty.clone(), rc::Expr::UnwrapCustom(*custom_id, root));
            build_plan(customs, rc_op, content_id, content_ty, sub_plan, builder);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct TypeSpecInfo {
    custom_id: first_ord::CustomTypeId,
    subst: IdVec<ModeParam, Mode>,
    overlay_subst: BTreeMap<ModeParam, Mode>,
}

#[derive(Clone, Debug)]
struct Specs<I: Id, T, U> {
    mapping: BTreeMap<T, I>,
    data: IdVec<I, U>,
}

impl<I: Id, T: Clone + Eq + Ord, U> Specs<I, T, U> {
    fn new() -> Self {
        Specs {
            mapping: BTreeMap::new(),
            data: IdVec::new(),
        }
    }

    fn resolve(&mut self, spec: &T, f: impl FnOnce(&mut Self) -> U) -> I {
        match self.mapping.get(spec) {
            Some(&id) => id,
            None => {
                // We need to add an entry to the mapping before calling `f` because `f` might call
                // `resolve` for the same specialization again!
                let id = self.data.count().inc();
                self.mapping.insert(spec.clone(), id);

                let result = f(self);

                let new_id = self.data.push(result);
                debug_assert!(id == new_id);
                id
            }
        }
    }
}

fn lower_custom_ty_custom(
    specs: &mut Specs<rc::CustomTypeId, TypeSpecInfo, rc::Type>,
    customs: &annot::CustomTypes,
    subst: &IdVec<ModeParam, Mode>,
    overlay_subst: &BTreeMap<ModeParam, Mode>,
    custom_id: first_ord::CustomTypeId,
) -> rc::CustomTypeId {
    let spec = TypeSpecInfo {
        custom_id,
        subst: subst.clone(),
        overlay_subst: overlay_subst.clone(),
    };

    specs.resolve(&spec, |cache| {
        lower_custom_ty(
            cache,
            customs,
            subst,
            overlay_subst,
            &customs.types[custom_id].content,
        )
    })
}

fn lower_custom_ty(
    specs: &mut Specs<rc::CustomTypeId, TypeSpecInfo, rc::Type>,
    customs: &annot::CustomTypes,
    subst: &IdVec<ModeParam, Mode>,
    overlay_subst: &BTreeMap<ModeParam, Mode>,
    ty: &annot::Type<ModeParam, LtParam>,
) -> rc::Type {
    match ty {
        annot::Type::Bool => rc::Type::Bool,
        annot::Type::Num(num_ty) => rc::Type::Num(*num_ty),
        annot::Type::Tuple(field_tys) => rc::Type::Tuple(
            field_tys
                .iter()
                .map(|ty| lower_custom_ty(specs, customs, subst, overlay_subst, ty))
                .collect(),
        ),
        annot::Type::Variants(variant_tys) => rc::Type::Variants(
            variant_tys.map_refs(|_, ty| lower_custom_ty(specs, customs, subst, overlay_subst, ty)),
        ),
        annot::Type::SelfCustom(id) => {
            let tail_overlay_subst = overlay_subst
                .iter()
                .map(|(param, _)| (*param, subst[*param]))
                .collect();
            rc::Type::SelfCustom(lower_custom_ty_custom(
                specs,
                customs,
                subst,
                &tail_overlay_subst,
                *id,
            ))
        }
        annot::Type::Custom(id, other_subst, other_overlay_subst) => {
            let concrete_subst = other_subst.ms.map_refs(|_, param| subst[*param]);
            let concrete_overlay_subst = other_overlay_subst
                .0
                .iter()
                .map(|(param, _)| (*param, subst[*param]))
                .collect();
            rc::Type::Custom(lower_custom_ty_custom(
                specs,
                customs,
                &concrete_subst,
                &concrete_overlay_subst,
                *id,
            ))
        }
        annot::Type::Array(mode, _, ty, _) => rc::Type::Array(
            overlay_subst[mode],
            Box::new(lower_custom_ty(specs, customs, subst, overlay_subst, ty)),
        ),
        annot::Type::HoleArray(mode, _, ty, _) => rc::Type::HoleArray(
            overlay_subst[mode],
            Box::new(lower_custom_ty(specs, customs, subst, overlay_subst, ty)),
        ),
        annot::Type::Boxed(mode, _, ty, _) => rc::Type::Boxed(
            overlay_subst[mode],
            Box::new(lower_custom_ty(specs, customs, subst, overlay_subst, ty)),
        ),
    }
}

fn lower_ty<'a>(
    mapping: BTreeMap<TypeSpecInfo, rc::CustomTypeId>,
    rc_customs: &rc::CustomTypes,
    ty: &annot::Type<Mode, Lt>,
) -> rc::Type {
    match ty {
        annot::Type::Bool => rc::Type::Bool,
        annot::Type::Num(n) => rc::Type::Num(*n),
        annot::Type::Tuple(fields) => rc::Type::Tuple(
            fields
                .iter()
                .map(|field| lower_ty(mapping, rc_customs, field))
                .collect(),
        ),
        annot::Type::Variants(variants) => {
            rc::Type::Variants(variants.map_refs(|_, ty| lower_ty(mapping, rc_customs, ty)))
        }
        annot::Type::SelfCustom(_) => unreachable!(),
        annot::Type::Custom(id, tsub, osub) => {
            let spec = TypeSpecInfo {
                custom_id: *id,
                subst: tsub.ms.clone(),
                overlay_subst: osub.0.clone(),
            };
            rc::Type::Custom(mapping[&spec])
        }
        annot::Type::Array(mode, _, item_ty, _) => {
            rc::Type::Array(*mode, Box::new(lower_ty(mapping, rc_customs, item_ty)))
        }
        annot::Type::HoleArray(mode, _, item_ty, _) => {
            rc::Type::HoleArray(*mode, Box::new(lower_ty(mapping, rc_customs, item_ty)))
        }
        annot::Type::Boxed(mode, _, item_ty, _) => {
            rc::Type::Boxed(*mode, Box::new(lower_ty(mapping, rc_customs, item_ty)))
        }
    }
}

struct LocalInfo {
    ty: AnnotType,
    lt: StructLt,
    status: Sel,
    new_id: rc::LocalId,
}

struct CustomInfo<'a> {
    content: &'a rc::Type,
    new_id: rc::CustomTypeId,
}

type Context = local_context::LocalContext<flat::LocalId, LocalInfo>;

fn select_dups(
    spec_subst: &IdVec<ModeParam, Mode>,
    status: &Sel,
    src_ty: &AnnotType,
    dst_ty: &AnnotType,
    path: &annot::Path,
    lt_obligation: &StructLt,
) -> Sel {
    let compute_status = |old_status, src_mode, dst_mode, lt: &Lt| match (src_mode, dst_mode) {
        (_, Mode::Borrowed) => Status::Gone,
        (Mode::Borrowed, Mode::Owned) => Status::Here,
        (Mode::Owned, Mode::Owned) => {
            if lt.does_not_exceed(path) && old_status == Status::Here {
                Status::Gone
            } else {
                Status::Here
            }
        }
    };
    status
        .items()
        .zip(src_ty.overlay_items())
        .zip(dst_ty.overlay_items())
        .zip(lt_obligation.items())
        .map(
            &|id, (((statuses, src_modes), dst_modes), lts)| {
                annot::OverlaySubst(
                    statuses
                        .0
                        .iter()
                        .zip(src_modes.0.values())
                        .zip(dst_modes.0.values())
                        .zip(lts.0.values())
                        .map(|data| {
                            let ((((param, status), src_mode), dst_mode), lt) = data;
                            let src_mode = src_mode.lb.instantiate(spec_subst);
                            let dst_mode = dst_mode.lb.instantiate(spec_subst);
                            (*param, compute_status(*status, src_mode, dst_mode, lt))
                        })
                        .collect(),
                )
            },
            &|(((status, src_mode), dst_mode), lt)| {
                let src_mode = src_mode.lb.instantiate(spec_subst);
                let dst_mode = dst_mode.lb.instantiate(spec_subst);
                compute_status(*status, src_mode, dst_mode, lt)
            },
        )
        .collect_ov()
}

fn select_borrows(
    spec_subst: &IdVec<ModeParam, Mode>,
    selected_dups: &Sel,
    dst_ty: &AnnotType,
) -> Sel {
    let compute_status = |is_duped, dst_mode| match dst_mode {
        Mode::Borrowed => Status::Here,
        Mode::Owned => is_duped,
    };
    selected_dups
        .items()
        .zip(dst_ty.overlay_items())
        .map(
            &|id, (statuses, dst_modes)| {
                annot::OverlaySubst(
                    statuses
                        .0
                        .iter()
                        .zip(dst_modes.0.values())
                        .map(|((param, status), dst_mode)| {
                            let dst_mode = dst_mode.lb.instantiate(spec_subst);
                            (*param, compute_status(*status, dst_mode))
                        })
                        .collect(),
                )
            },
            &|(status, dst_mode)| {
                let dst_mode = dst_mode.lb.instantiate(spec_subst);
                compute_status(*status, dst_mode)
            },
        )
        .collect_ov()
}

fn specialize_occur<'a>(
    annot_customs: &annot::CustomTypes,
    rc_customs: &rc::CustomTypes,
    spec_subst: &IdVec<ModeParam, Mode>,
    ctx: &mut Context,
    path: &annot::Path,
    occur: &annot::Occur<ModeSolution, Lt>,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    let info = ctx.local_binding_mut(occur.id);
    let dups = select_dups(
        spec_subst,
        &info.status,
        &info.ty,
        &occur.ty,
        path,
        &info.lt,
    );
    let borrows = select_borrows(spec_subst, &dups, &occur.ty);

    build_plan(
        rc_customs,
        rc::RcOp::Retain,
        info.new_id,
        &lower_ty(customs, ty),
        &RcOpPlan::from_sel(annot_customs, &dups),
        builder,
    );

    info.status.and_eq(&borrows);
    info.new_id
}

fn specialize_expr<'a>(
    customs: &IdVec<first_ord::CustomTypeId, CustomInfo<'a>>,
    ctx: &mut Context,
    path: &annot::Path,
    expr: &AnnotExpr,
    ret_ty: &rc::Type,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    let get_id = |ctx: &Context, occur: &annot::Occur<_, _>| ctx.local_binding(occur.id).new_id;

    let new_expr = match expr {
        annot::Expr::Local(local) => rc::Expr::Local(get_id(ctx, local)),

        annot::Expr::Call(_, _, _) => todo!(),

        annot::Expr::Branch(_, _, _) => todo!(),

        annot::Expr::LetMany(_, _) => todo!(),

        annot::Expr::Tuple(fields) => {
            rc::Expr::Tuple(fields.iter().map(|field| get_id(ctx, field)).collect())
        }

        annot::Expr::TupleField(tup, idx) => rc::Expr::TupleField(get_id(ctx, tup), *idx),

        annot::Expr::WrapVariant(variant_tys, variant_id, content) => rc::Expr::WrapVariant(
            variant_tys.map_refs(|_, ty| lower_ty(customs, ty)),
            *variant_id,
            get_id(ctx, content),
        ),

        annot::Expr::UnwrapVariant(variant_id, wrapped) => {
            rc::Expr::UnwrapVariant(*variant_id, get_id(ctx, wrapped))
        }

        annot::Expr::WrapBoxed(content, item_ty) => {
            rc::Expr::WrapBoxed(get_id(ctx, content), lower_ty(customs, item_ty))
        }

        annot::Expr::UnwrapBoxed(wrapped, item_ty) => {
            rc::Expr::UnwrapBoxed(get_id(ctx, wrapped), lower_ty(customs, item_ty))
        }

        annot::Expr::WrapCustom(custom_id, content) => {
            rc::Expr::WrapCustom(customs[custom_id].new_id, get_id(ctx, content))
        }

        annot::Expr::UnwrapCustom(custom_id, wrapped) => {
            rc::Expr::UnwrapCustom(customs[custom_id].new_id, get_id(ctx, wrapped))
        }

        annot::Expr::Intrinsic(intr, arg) => rc::Expr::Intrinsic(*intr, get_id(ctx, arg)),

        annot::Expr::ArrayOp(annot::ArrayOp::Get(item_ty, arr, idx, ret_ty)) => {
            todo!()
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Extract(item_ty, arr, idx)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Extract(
                lower_ty(customs, item_ty),
                get_id(ctx, arr),
                get_id(ctx, idx),
            ))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Len(item_ty, arr)) => rc::Expr::ArrayOp(
            rc::ArrayOp::Len(lower_ty(customs, item_ty), get_id(ctx, arr)),
        ),

        annot::Expr::ArrayOp(annot::ArrayOp::Push(item_ty, arr, item)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Push(
                lower_ty(customs, item_ty),
                get_id(ctx, arr),
                get_id(ctx, item),
            ))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Pop(item_ty, arr)) => rc::Expr::ArrayOp(
            rc::ArrayOp::Pop(lower_ty(customs, item_ty), get_id(ctx, arr)),
        ),

        annot::Expr::ArrayOp(annot::ArrayOp::Replace(item_ty, arr, item)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Replace(
                lower_ty(customs, item_ty),
                get_id(ctx, arr),
                get_id(ctx, item),
            ))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(item_ty, arr, cap)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Reserve(
                lower_ty(customs, item_ty),
                get_id(ctx, arr),
                get_id(ctx, cap),
            ))
        }

        annot::Expr::IoOp(annot::IoOp::Input) => rc::Expr::IoOp(rc::IoOp::Input),

        annot::Expr::IoOp(annot::IoOp::Output(output)) => {
            rc::Expr::IoOp(rc::IoOp::Output(get_id(ctx, output)))
        }

        annot::Expr::Panic(ret_ty, msg) => {
            rc::Expr::Panic(lower_ty(customs, ret_ty), get_id(ctx, msg))
        }

        annot::Expr::ArrayLit(item_ty, items) => rc::Expr::ArrayLit(
            lower_ty(customs, item_ty),
            items.iter().map(|item| get_id(ctx, item)).collect(),
        ),

        annot::Expr::BoolLit(lit) => rc::Expr::BoolLit(*lit),

        annot::Expr::ByteLit(lit) => rc::Expr::ByteLit(*lit),

        annot::Expr::IntLit(lit) => rc::Expr::IntLit(*lit),

        annot::Expr::FloatLit(lit) => rc::Expr::FloatLit(*lit),
    };

    builder.add_binding(ret_ty.clone(), new_expr)
}

/// We want to deduplicate specializations w.r.t. their retains and releases. This happens in two
/// stages. First, we deduplicate w.r.t. modes and label specializations using `ModeSpecFuncId`.
#[id_type]
struct ModeSpecFuncId(usize);

pub fn rc_specialize(program: &annot::Program, progress: impl ProgressLogger) -> rc::Program {
    let mut progress = progress.start_session(Some(program.funcs.len()));

    todo!()
}
