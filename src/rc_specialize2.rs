use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::mode_annot_ast2::{
    self as annot, CollectOverlay, Lt, Mode, ModeData, ModeParam, ModeSolution, Overlay, SlotId,
};
use crate::data::purity::Purity;
use crate::data::rc_specialized_ast2 as rc;
use crate::util::instance_queue::InstanceQueue;
use crate::util::iter::IterExt;
use crate::util::local_context::LocalContext;
use crate::util::map_ext::Map;
use crate::util::progress_logger::ProgressLogger;
use id_collections::{id_type, IdVec};
use std::collections::BTreeMap;
use std::iter;

type AnnotExpr = annot::Expr<ModeSolution, Lt>;
type AnnotType = annot::Type<ModeSolution, Lt>;
type AnnotOverlay = annot::Overlay<ModeSolution>;
type AnnotModeData = annot::ModeData<ModeSolution>;
type AnnotLtData = annot::LtData<Lt>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MoveStatus {
    Absent,
    Present,
}

impl MoveStatus {
    fn or(&self, other: &Self) -> Self {
        match (self, other) {
            (MoveStatus::Absent, MoveStatus::Absent) => MoveStatus::Absent,
            _ => MoveStatus::Present,
        }
    }

    fn and(&self, other: &Self) -> Self {
        match (self, other) {
            (MoveStatus::Present, MoveStatus::Present) => MoveStatus::Present,
            _ => MoveStatus::Absent,
        }
    }
}

type Selector = Overlay<MoveStatus>;

impl Selector {
    fn or(&self, other: &Selector) -> Selector {
        self.iter()
            .zip_eq(other.iter())
            .map(|(s1, s2)| s1.or(s2))
            .collect_overlay(self)
    }

    fn and(&self, other: &Selector) -> Selector {
        self.iter()
            .zip_eq(other.iter())
            .map(|(s1, s2)| s1.and(s2))
            .collect_overlay(self)
    }
}

type StackLt = Overlay<Lt>;

impl StackLt {
    fn join(&self, other: &StackLt) -> StackLt {
        debug_assert_eq!(self.shape(), other.shape());
        self.iter()
            .zip_eq(other.iter())
            .map(|(lt1, lt2)| lt1.join(lt2))
            .collect_overlay(self)
    }
}

#[derive(Clone, Debug)]
enum Field<T> {
    TupleField(usize),
    VariantCase(first_ord::VariantId),
    Custom(first_ord::CustomTypeId, SlotId, T),
    Slot(T),
}

type TypeInst = annot::Type2<rc::CustomTypeId, Mode, Lt>;
type OverlayInst = annot::Overlay2<rc::CustomTypeId, Mode>;
type ModeDataInst = annot::ModeData2<rc::CustomTypeId, Mode>;
type LtDataInst = annot::LtData2<rc::CustomTypeId, Lt>;

// Having a new occur type for `InstExpr`s ensures we don't forget to process any occurrences during
// `annot_obligations`.
#[derive(Clone, Debug)]
struct OccurInst {
    pub id: flat::LocalId,
    pub ty: AnnotType,
}

#[derive(Clone, Debug)]
enum ArrayOp {
    Get(OccurInst, OccurInst, AnnotType),
    Extract(OccurInst, OccurInst),
    Len(OccurInst),
    Push(OccurInst, OccurInst),
    Pop(OccurInst),
    Replace(OccurInst, OccurInst),
    Reserve(OccurInst, OccurInst),
}

#[derive(Clone, Debug)]
enum IoOp {
    Input,
    Output(OccurInst),
}

/// An `annot::Expr` of `ModeSolutions`s can be transformed into an `ExprInst` by instantiating each
/// mode solution into a concrete mode and annotating each binding with its consequent stack
/// lifetime.
#[derive(Clone, Debug)]
enum ExprInst {
    Local(OccurInst),
    Call(Purity, first_ord::CustomFuncId, OccurInst),
    Branch(
        OccurInst,
        Vec<(annot::Condition<Mode, Lt>, ExprInst)>,
        AnnotType,
    ),
    LetMany(Vec<(AnnotType, StackLt, ExprInst)>, OccurInst),

    Tuple(Vec<OccurInst>),
    TupleField(OccurInst, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, AnnotType>,
        first_ord::VariantId,
        OccurInst,
    ),
    UnwrapVariant(first_ord::VariantId, OccurInst),
    WrapBoxed(OccurInst, AnnotType),
    UnwrapBoxed(OccurInst, AnnotType),
    WrapCustom(first_ord::CustomTypeId, OccurInst),
    UnwrapCustom(first_ord::CustomTypeId, OccurInst),

    Intrinsic(Intrinsic, OccurInst),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(AnnotType, OccurInst),

    ArrayLit(AnnotType, Vec<OccurInst>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

fn get_occur_obligation_for_slot(
    occur_path: &annot::Path,
    mode_src: Mode,
    mode_dst: Mode,
    lt_dst: &Lt,
) -> Lt {
    match (mode_src, mode_dst) {
        (Mode::Owned, Mode::Borrowed) => lt_dst.clone(),
        // Ultimately, any lifetime that does not exceed the scope of the binding will produce the
        // same result in `select_dups` (which is the only part of the pen-and-paper reification
        // algorithm that touches lifetime obligations), giving us a degree of freedom. In the
        // paper, we choose the lifetime strategically to aid in the proof of soundness. Here, our
        // choice is motivated by ensuring that lifetime obligations correspond to earliest possible
        // drop points.
        (Mode::Owned, Mode::Owned) => occur_path.as_lt(),
        (Mode::Borrowed, _) => Lt::Empty,
    }
}

fn get_occur_obligation(
    customs: &annot::CustomTypes,
    occur_path: &annot::Path,
    ty_src: &TypeInst,
    ty_dst: &TypeInst,
) -> StackLt {
    ty_src
        .modes()
        .iter_overlay()
        .zip_eq(ty_dst.modes().iter_overlay())
        .zip_eq(ty_dst.lts().iter_overlay(&customs.types))
        .map(|((mode_src, mode_dst), lt_dst)| {
            get_occur_obligation_for_slot(occur_path, *mode_src, *mode_dst, lt_dst)
        })
        .collect_overlay(&ty_src.modes().unapply_overlay())
}

fn instantiate_occur(
    insts: &mut TypeInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    occur: &annot::Occur<ModeSolution, Lt>,
) -> OccurInst {
    OccurInst {
        id: occur.id,
        ty: instantiate_modes(insts, inst_params, &occur.ty),
    }
}

fn instantiate_cond(
    insts: &mut TypeInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    cond: &annot::Condition<ModeSolution, Lt>,
) -> annot::Condition<Mode, Lt> {
    match cond {
        annot::Condition::Any => annot::Condition::Any,
        annot::Condition::Tuple(conds) => annot::Condition::Tuple(
            conds
                .iter()
                .map(|cond| instantiate_cond(insts, inst_params, cond))
                .collect(),
        ),
        annot::Condition::Variant(variant_id, cond) => annot::Condition::Variant(
            *variant_id,
            Box::new(instantiate_cond(insts, inst_params, cond)),
        ),
        annot::Condition::Boxed(cond, item_ty) => annot::Condition::Boxed(
            Box::new(instantiate_cond(insts, inst_params, cond)),
            instantiate_modes(insts, inst_params, item_ty),
        ),
        annot::Condition::Custom(custom_id, cond) => annot::Condition::Custom(
            *custom_id,
            Box::new(instantiate_cond(insts, inst_params, cond)),
        ),
        annot::Condition::BoolConst(lit) => annot::Condition::BoolConst(*lit),
        annot::Condition::ByteConst(lit) => annot::Condition::ByteConst(*lit),
        annot::Condition::IntConst(lit) => annot::Condition::IntConst(*lit),
        annot::Condition::FloatConst(lit) => annot::Condition::FloatConst(*lit),
    }
}

fn instantiate_expr(
    customs: &annot::CustomTypes,
    inst_params: &IdVec<ModeParam, Mode>,
    path: &annot::Path,
    ctx: &mut LocalContext<flat::LocalId, (AnnotType, StackLt)>,
    expr: annot::Expr<ModeSolution, Lt>,
) -> ExprInst {
    let handle_occur = |ctx: &mut LocalContext<_, (_, StackLt)>, occur: annot::Occur<_, _>| {
        let occur = instantiate_occur(inst_params, &occur);
        let (ty, lt) = ctx.local_binding_mut(occur.id);

        // We must update the lifetime obligation of the binding to reflect this occurrence.
        let obligation = get_occur_obligation(customs, path, &ty, &occur.ty);
        *lt = lt.join(&obligation);
        occur
    };

    match expr {
        annot::Expr::Local(occur) => ExprInst::Local(handle_occur(ctx, occur)),

        annot::Expr::Call(purity, func, arg) => {
            ExprInst::Call(purity, func, handle_occur(ctx, arg))
        }

        annot::Expr::Branch(cond, arms, ty) => {
            let new_cond = handle_occur(ctx, cond);
            let n = arms.len();
            let new_arms = arms
                .into_iter()
                .enumerate()
                .map(|(i, (cond, expr))| {
                    (
                        instantiate_cond(inst_params, &cond),
                        instantiate_expr(customs, inst_params, &path.par(i, n), ctx, expr),
                    )
                })
                .collect();
            ExprInst::Branch(new_cond, new_arms, ty)
        }

        // We use `with_scope` to express our intent. In fact, all the bindings we add are popped
        // from the context before we return.
        annot::Expr::LetMany(bindings, ret) => ctx.with_scope(|ctx| {
            let mut new_exprs = Vec::new();
            for (i, (ty, expr)) in bindings.into_iter().enumerate() {
                let ty = ty;
                let ov = ty.modes().unapply_overlay();
                let init_lt = ov.iter().map(|_| Lt::Empty).collect_overlay(&ov);

                let _ = ctx.add_local((ty, init_lt));
                let new_expr = instantiate_expr(customs, inst_params, &path.seq(i), ctx, expr);
                new_exprs.push(new_expr);
            }

            let mut new_bindings_rev = Vec::new();
            for expr in new_exprs.into_iter().rev() {
                let (_, (ty, obligation)) = ctx.pop_local();
                new_bindings_rev.push((ty, obligation, expr));
            }

            let new_bindings = {
                new_bindings_rev.reverse();
                new_bindings_rev
            };
            ExprInst::LetMany(new_bindings, handle_occur(ctx, ret))
        }),

        annot::Expr::Tuple(fields) => ExprInst::Tuple(
            fields
                .into_iter()
                .map(|occur| handle_occur(ctx, occur))
                .collect(),
        ),

        annot::Expr::TupleField(tup, idx) => ExprInst::TupleField(handle_occur(ctx, tup), idx),

        annot::Expr::WrapVariant(variants, variant, content) => {
            ExprInst::WrapVariant(variants, variant, handle_occur(ctx, content))
        }

        annot::Expr::UnwrapVariant(variant, content) => {
            ExprInst::UnwrapVariant(variant, handle_occur(ctx, content))
        }

        annot::Expr::WrapBoxed(content, ty) => ExprInst::WrapBoxed(handle_occur(ctx, content), ty),

        annot::Expr::UnwrapBoxed(content, ty) => {
            ExprInst::UnwrapBoxed(handle_occur(ctx, content), ty)
        }

        annot::Expr::WrapCustom(id, content) => {
            ExprInst::WrapCustom(id, handle_occur(ctx, content))
        }

        annot::Expr::UnwrapCustom(id, content) => {
            ExprInst::UnwrapCustom(id, handle_occur(ctx, content))
        }

        annot::Expr::Intrinsic(intrinsic, occur) => {
            ExprInst::Intrinsic(intrinsic, handle_occur(ctx, occur))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Get(arr, idx, ty)) => ExprInst::ArrayOp(ArrayOp::Get(
            handle_occur(ctx, arr),
            handle_occur(ctx, idx),
            ty,
        )),
        annot::Expr::ArrayOp(annot::ArrayOp::Extract(arr, idx)) => ExprInst::ArrayOp(
            ArrayOp::Extract(handle_occur(ctx, arr), handle_occur(ctx, idx)),
        ),
        annot::Expr::ArrayOp(annot::ArrayOp::Len(arr)) => {
            ExprInst::ArrayOp(ArrayOp::Len(handle_occur(ctx, arr)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Push(arr, item)) => ExprInst::ArrayOp(ArrayOp::Push(
            handle_occur(ctx, arr),
            handle_occur(ctx, item),
        )),
        annot::Expr::ArrayOp(annot::ArrayOp::Pop(arr)) => {
            ExprInst::ArrayOp(ArrayOp::Pop(handle_occur(ctx, arr)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Replace(arr, item)) => ExprInst::ArrayOp(
            ArrayOp::Replace(handle_occur(ctx, arr), handle_occur(ctx, item)),
        ),
        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(arr, cap)) => ExprInst::ArrayOp(
            ArrayOp::Reserve(handle_occur(ctx, arr), handle_occur(ctx, cap)),
        ),

        annot::Expr::IoOp(annot::IoOp::Input) => ExprInst::IoOp(IoOp::Input),
        annot::Expr::IoOp(annot::IoOp::Output(occur)) => {
            ExprInst::IoOp(IoOp::Output(handle_occur(ctx, occur)))
        }

        annot::Expr::Panic(ret_ty, occur) => ExprInst::Panic(ret_ty, handle_occur(ctx, occur)),
        annot::Expr::ArrayLit(ty, elems) => ExprInst::ArrayLit(
            ty,
            elems
                .into_iter()
                .map(|occur| handle_occur(ctx, occur))
                .collect(),
        ),

        annot::Expr::BoolLit(b) => ExprInst::BoolLit(b),
        annot::Expr::ByteLit(b) => ExprInst::ByteLit(b),
        annot::Expr::IntLit(i) => ExprInst::IntLit(i),
        annot::Expr::FloatLit(f) => ExprInst::FloatLit(f),
    }
}

/// Identifies a "payload" carrying field, e.g. an array or box
type FieldPath<T> = im_rc::Vector<Field<T>>;

fn get_field_data<T: Clone>(path: &FieldPath<T>) -> &T {
    match path.last().expect("expected non-empty field path") {
        Field::Custom(_, _, data) | Field::Slot(data) => data,
        _ => panic!("invalid field path: should end in custom or slot field"),
    }
}

fn set_present<T: Clone>(sel: &mut Selector, path: &FieldPath<T>) {
    let mut cursor = sel;
    for field in path.iter() {
        match field {
            Field::TupleField(i) => {
                let Overlay::Tuple(fields) = cursor else {
                    panic!("field path does not match selector");
                };
                cursor = &mut fields[*i];
            }
            Field::VariantCase(i) => {
                let Overlay::Variants(variants) = cursor else {
                    panic!("field path does not match selector");
                };
                cursor = &mut variants[*i];
            }
            Field::Custom(id, i, _) => {
                let Overlay::Custom(other_id, subst) = cursor else {
                    panic!("field path does not match selector");
                };
                debug_assert_eq!(id, other_id);
                subst.insert(*i, MoveStatus::Present);
            }
            Field::Slot(_) => match cursor {
                Overlay::Array(status) | Overlay::HoleArray(status) | Overlay::Boxed(status) => {
                    *status = MoveStatus::Present;
                }
                _ => panic!("field path does not match selector"),
            },
        }
    }
}

fn iterate_lt_fields<'a>(lt: &'a StackLt) -> Box<dyn Iterator<Item = FieldPath<&'a Lt>> + 'a> {
    fn iterate_lt_fields_impl<'a>(
        root: FieldPath<&'a Lt>,
        lt: &'a StackLt,
    ) -> Box<dyn Iterator<Item = FieldPath<&'a Lt>> + 'a> {
        match lt {
            Overlay::Bool => Box::new(iter::empty()),
            Overlay::Num(_) => Box::new(iter::empty()),
            Overlay::Tuple(fields) => {
                Box::new(fields.iter().enumerate().flat_map(move |(idx, lt)| {
                    let mut new_root = root.clone();
                    new_root.push_back(Field::TupleField(idx));
                    iterate_lt_fields_impl(new_root, lt)
                }))
            }
            Overlay::Variants(variants) => {
                Box::new(variants.iter().flat_map(move |(variant_id, lt)| {
                    let mut new_root = root.clone();
                    new_root.push_back(Field::VariantCase(variant_id));
                    iterate_lt_fields_impl(new_root, lt)
                }))
            }
            Overlay::SelfCustom(_) => Box::new(iter::empty()),
            Overlay::Custom(id, lts) => Box::new(lts.iter().map(move |(slot, lt)| {
                let mut leaf = root.clone();
                leaf.push_back(Field::Custom(*id, *slot, lt));
                leaf
            })),
            Overlay::Array(lt) | Overlay::HoleArray(lt) | Overlay::Boxed(lt) => {
                Box::new(iter::once({
                    let mut leaf = root.clone();
                    leaf.push_back(Field::Slot(lt));
                    leaf
                }))
            }
        }
    }
    iterate_lt_fields_impl(im_rc::Vector::new(), lt)
}

// TODO: should `InLetMany` and `InMatch` use a sparse or dense representation?
enum CandidateDrops {
    InBranch(BTreeMap<usize, Box<CandidateDrops>>),
    InLetMany(BTreeMap<usize, Box<CandidateDrops>>),
    Locals(BTreeMap<flat::LocalId, Selector>),
}

impl CandidateDrops {
    fn empty_locals() -> Self {
        CandidateDrops::Locals(BTreeMap::new())
    }

    fn empty_from_expr(expr: &ExprInst) -> Self {
        fn build(expr: &ExprInst) -> Option<CandidateDrops> {
            match expr {
                ExprInst::Branch(_, arms, _) => {
                    let mut drops = BTreeMap::new();
                    for (i, (_, expr)) in arms.iter().enumerate() {
                        if let Some(arm_drops) = build(expr) {
                            drops.insert(i, Box::new(arm_drops));
                        }
                    }
                    Some(CandidateDrops::InBranch(drops))
                }
                ExprInst::LetMany(bindings, _) => {
                    let mut drops = BTreeMap::new();
                    for (i, (_, _, expr)) in bindings.iter().enumerate() {
                        if let Some(binding_drops) = build(expr) {
                            drops.insert(i, Box::new(binding_drops));
                        }
                    }
                    Some(CandidateDrops::InLetMany(drops))
                }
                _ => None,
            }
        }
        build(expr).unwrap_or_else(|| Self::empty_locals())
    }

    // TODO: using `Selector`s here (as we've currently defined them) is quite inefficient. We
    // should use a data structure which can *sparsely* represent a subset of fields
    fn register_drops_for_binding_slot(
        &mut self,
        binding: flat::LocalId,
        slot: &Selector,
        obligation: &annot::LocalLt,
    ) {
        match obligation {
            annot::LocalLt::Final => {
                let CandidateDrops::Locals(self_locals) = self else {
                    panic!("structurally incompatible obligations");
                };
                self_locals
                    .entry(binding)
                    .and_modify(|self_slots| *self_slots = self_slots.or(slot))
                    .or_insert_with(|| slot.clone());
            }

            annot::LocalLt::Seq(arm, i) => {
                let CandidateDrops::InLetMany(self_arms) = self else {
                    panic!("structurally incompatible obligations");
                };
                let self_arm = self_arms
                    .entry(*i)
                    .or_insert_with(|| Box::new(CandidateDrops::empty_locals()));
                self_arm.register_drops_for_binding_slot(binding, slot, arm);
            }

            annot::LocalLt::Par(arms) => {
                let CandidateDrops::InBranch(self_arms) = self else {
                    panic!("structurally incompatible obligations");
                };
                for (i, arm) in arms.iter().enumerate() {
                    if let Some(arm) = arm {
                        let self_arm = self_arms
                            .entry(i)
                            .or_insert_with(|| Box::new(CandidateDrops::empty_locals()));
                        self_arm.register_drops_for_binding_slot(binding, slot, arm);
                    }
                }
            }
        }
    }

    fn register_drops_for_binding(
        &mut self,
        binding_path: &annot::Path,
        binding: flat::LocalId,
        binding_ty: &AnnotType,
        obligation: &StackLt,
    ) {
        let sel = binding_ty
            .modes()
            .iter_overlay()
            .map(|_| MoveStatus::Absent)
            .collect_overlay(&binding_ty.modes().unapply_overlay());

        for path in iterate_lt_fields(obligation) {
            let mut slot_sel = sel.clone();
            set_present(&mut slot_sel, &path);

            match get_field_data(&path) {
                // We don't need to do anything; the binding escapes into the caller's scope
                Lt::Join(_) => {}
                // The binding is unused; we can drop it immediately
                Lt::Empty => {
                    self.register_drops_for_binding_slot(
                        binding,
                        &slot_sel,
                        &binding_path.as_local_lt(),
                    );
                }
                Lt::Local(lt) => {
                    self.register_drops_for_binding_slot(binding, &slot_sel, &lt);
                }
            }
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
    fn from_sel(customs: &annot::CustomTypes, sel: &Selector) -> Self {
        match sel {
            Overlay::Bool => Self::NoOp,
            Overlay::Num(_) => Self::NoOp,
            Overlay::Tuple(fields) => {
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
            Overlay::Variants(variants) => {
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
            Overlay::SelfCustom(id) => {
                debug_assert!(customs.types[*id].ov.is_zero_sized_or_self(customs));
                Self::NoOp
            }
            Overlay::Custom(id, sub) => {
                let inner = customs.types[*id].ov.hydrate(sub);
                let sub_plan = RcOpPlan::from_sel(customs, &inner);
                if matches!(sub_plan, RcOpPlan::NoOp) {
                    Self::NoOp
                } else {
                    Self::OnCustom(Box::new(sub_plan))
                }
            }
            Overlay::Array(status) | Overlay::HoleArray(status) | Overlay::Boxed(status) => {
                match status {
                    MoveStatus::Present => Self::LeafOp,
                    MoveStatus::Absent => Self::NoOp,
                }
            }
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

type TypeInstances =
    InstanceQueue<(first_ord::CustomTypeId, IdVec<ModeParam, Mode>), rc::CustomTypeId>;
type FuncInstances =
    InstanceQueue<(first_ord::CustomFuncId, IdVec<ModeParam, Mode>), rc::CustomFuncId>;

fn lower_custom_ty(
    insts: &mut TypeInstances,
    inst_params: Option<&IdVec<ModeParam, Mode>>,
    ty: &ModeData<Mode>,
) -> rc::Type {
    match ty {
        ModeData::Bool => rc::Type::Bool,
        ModeData::Num(n) => rc::Type::Num(*n),
        ModeData::Tuple(fields) => rc::Type::Tuple(
            fields
                .iter()
                .map(|field| lower_custom_ty(insts, inst_params, field))
                .collect(),
        ),
        ModeData::Variants(variants) => {
            rc::Type::Variants(variants.map_refs(|_, ty| lower_custom_ty(insts, inst_params, ty)))
        }
        ModeData::SelfCustom(id) => {
            let params = inst_params.expect("self_params must be supplied when lowering customs");
            let spec = TypeSpec {
                id: *id,
                params: params.clone(),
            };
            rc::Type::SelfCustom(insts.resolve(spec))
        }
        ModeData::Custom(id, _, params) => {
            let spec = TypeSpec {
                id: *id,
                params: params.clone(),
            };
            rc::Type::Custom(insts.resolve(spec))
        }
        ModeData::Array(mode, _, item_ty) => rc::Type::Array(
            *mode,
            Box::new(lower_custom_ty(insts, inst_params, item_ty)),
        ),
        ModeData::HoleArray(mode, _, item_ty) => rc::Type::HoleArray(
            *mode,
            Box::new(lower_custom_ty(insts, inst_params, item_ty)),
        ),
        ModeData::Boxed(mode, _, item_ty) => rc::Type::Boxed(
            *mode,
            Box::new(lower_custom_ty(insts, inst_params, item_ty)),
        ),
    }
}

fn lower_ty(insts: &mut TypeInstances, ty: &ModeData<Mode>) -> rc::Type {
    lower_custom_ty(insts, None, ty)
}

fn select_slot_dups(
    path: &annot::Path,
    old_status: MoveStatus,
    src_mode: Mode,
    dst_mode: Mode,
    lt: &Lt,
) -> MoveStatus {
    match (src_mode, dst_mode) {
        (_, Mode::Borrowed) => MoveStatus::Absent,
        (Mode::Borrowed, Mode::Owned) => {
            panic!("borrowed to owned transitions should be prevented by the inferred constraints")
        }
        (Mode::Owned, Mode::Owned) => {
            if lt.does_not_exceed(path) && old_status == MoveStatus::Present {
                MoveStatus::Absent
            } else {
                MoveStatus::Present
            }
        }
    }
}

fn select_dups(
    path: &annot::Path,
    status: &Selector,
    src_ty: &TypeInst,
    dst_ty: &TypeInst,
    lt_obligation: &StackLt,
) -> Selector {
    status
        .iter()
        .zip_eq(src_ty.modes().iter_overlay())
        .zip_eq(dst_ty.modes().iter_overlay())
        .zip_eq(lt_obligation.iter())
        .map(|(((status, src_mode), dst_mode), lt)| {
            select_slot_dups(path, *status, *src_mode, *dst_mode, lt)
        })
        .collect_overlay(status)
}

fn select_slot_borrows(is_duped: MoveStatus, dst_mode: Mode) -> MoveStatus {
    match dst_mode {
        Mode::Borrowed => MoveStatus::Present,
        Mode::Owned => is_duped,
    }
}

fn select_borrows(selected_dups: &Selector, dst_ty: &TypeInst) -> Selector {
    selected_dups
        .iter()
        .zip_eq(dst_ty.modes().iter_overlay())
        .map(|(is_duped, dst_mode)| select_slot_borrows(*is_duped, *dst_mode))
        .collect_overlay(selected_dups)
}

fn select_owned(ty: &TypeInst) -> Selector {
    ty.modes()
        .iter_overlay()
        .map(|mode| match mode {
            Mode::Borrowed => MoveStatus::Absent,
            Mode::Owned => MoveStatus::Present,
        })
        .collect_overlay(&ty.modes().unapply_overlay())
}

#[derive(Clone, Debug)]
struct LocalInfo {
    annot_ty: AnnotType,
    rc_ty: rc::Type,
    obligation: StackLt,
    status: Selector,
    new_id: rc::LocalId,
}

#[derive(Clone, Copy, Debug)]
struct Customs<'a> {
    annot: &'a annot::CustomTypes,
    rc: &'a rc::CustomTypes,
    funcs: &'a IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    ty_map: &'a BTreeMap<TypeSpec, rc::CustomTypeId>,
    fn_map: &'a BTreeMap<FuncSpec, rc::CustomFuncId>,
}

fn final_slot_drop(
    binding_mode: Mode,
    is_final: MoveStatus,
    is_candidate: MoveStatus,
) -> MoveStatus {
    match binding_mode {
        Mode::Borrowed => MoveStatus::Absent,
        Mode::Owned => {
            if is_final == MoveStatus::Present {
                MoveStatus::Absent
            } else {
                is_candidate
            }
        }
    }
}

fn finalize_drops_custom(
    binding_ty: &AnnotType,
    is_final: &Selector,
    candidate_drops: &Selector,
) -> Selector {
    todo!()
}

fn finalize_drops(
    binding_ty: &AnnotType,
    is_final: &Selector,
    candidate_drops: &Selector,
) -> Selector {
    todo!()
}

fn build_drops(
    customs: Customs<'_>,
    locals: &BTreeMap<flat::LocalId, Selector>,
    ctx: &mut LocalContext<flat::LocalId, LocalInfo>,
    builder: &mut LetManyBuilder,
) {
    for (binding, candidate_drops) in locals {
        let info = ctx.local_binding_mut(*binding);
        let drops = finalize_drops(todo!(), todo!(), todo!());
        let plan = RcOpPlan::from_sel(customs.annot, &drops);

        build_plan(
            customs.rc,
            rc::RcOp::Release,
            info.new_id,
            &info.rc_ty,
            &plan,
            builder,
        );
    }
}

fn lower_occur(
    customs: Customs<'_>,
    ctx: &mut LocalContext<flat::LocalId, LocalInfo>,
    path: &annot::Path,
    occur: &OccurInst,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    let info = ctx.local_binding_mut(occur.id);
    let dups = select_dups(
        path,
        &info.status,
        &info.annot_ty,
        &occur.ty,
        &info.obligation,
    );

    let plan = RcOpPlan::from_sel(customs.annot, &dups);
    build_plan(
        customs.rc,
        rc::RcOp::Retain,
        info.new_id,
        &info.rc_ty,
        &plan,
        builder,
    );

    let borrows = select_borrows(&dups, &occur.ty);
    info.status = info.status.and(&borrows);
    info.new_id
}

fn lower_cond(
    customs: Customs<'_>,
    insts: &mut TypeInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    cond: &annot::Condition<Mode, Lt>,
) -> rc::Condition {
    match cond {
        annot::Condition::Any => rc::Condition::Any,
        annot::Condition::Tuple(conds) => rc::Condition::Tuple(
            conds
                .iter()
                .map(|cond| lower_cond(customs, insts, inst_params, cond))
                .collect(),
        ),
        annot::Condition::Variant(variant_id, cond) => rc::Condition::Variant(
            *variant_id,
            Box::new(lower_cond(customs, insts, inst_params, cond)),
        ),
        annot::Condition::Boxed(cond, item_ty) => rc::Condition::Boxed(
            Box::new(lower_cond(customs, insts, inst_params, cond)),
            lower_ty(insts, item_ty.modes()),
        ),
        annot::Condition::Custom(custom_id, cond) => {
            let new_id = insts.resolve(TypeSpec {
                id: *custom_id,
                params: inst_params.clone(),
            });
            rc::Condition::Custom(
                new_id,
                Box::new(lower_cond(customs, insts, inst_params, cond)),
            )
        }
        annot::Condition::BoolConst(lit) => rc::Condition::BoolConst(*lit),
        annot::Condition::ByteConst(lit) => rc::Condition::ByteConst(*lit),
        annot::Condition::IntConst(lit) => rc::Condition::IntConst(*lit),
        annot::Condition::FloatConst(lit) => rc::Condition::FloatConst(*lit),
    }
}

fn lower_expr(
    customs: Customs<'_>,
    type_insts: &mut TypeInstances,
    func_insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    ctx: &mut LocalContext<flat::LocalId, LocalInfo>,
    path: &annot::Path,
    expr: &ExprInst,
    ret_ty: &rc::Type,
    drops: Option<&CandidateDrops>,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    let new_expr = match expr {
        ExprInst::Local(local) => rc::Expr::Local(lower_occur(customs, ctx, path, local, builder)),

        ExprInst::Call(purity, func, arg) => {
            let call_params = customs.funcs[*func]
                .constrs
                .sig
                .map_refs(|_, solution| solution.instantiate(inst_params));
            let new_id = func_insts.resolve((*func, call_params));
            rc::Expr::Call(
                *purity,
                new_id,
                lower_occur(customs, ctx, path, arg, builder),
            )
        }

        ExprInst::Branch(discrim, branches, ret_ty) => {
            let Some(CandidateDrops::InBranch(drops)) = drops else {
                unreachable!()
            };

            let mut new_branches: Vec<(rc::Condition, _)> = Vec::new();
            let n = branches.len();
            let ret_ty = lower_ty(type_insts, ret_ty.modes());

            for (i, (cond, body)) in branches.iter().enumerate() {
                let mut case_builder = builder.child();
                let sub_drops = drops.get(&i).map(|x| &**x);

                let cond = lower_cond(customs, type_insts, inst_params, cond);
                let final_local = lower_expr(
                    customs,
                    type_insts,
                    func_insts,
                    inst_params,
                    ctx,
                    &path.par(i, n),
                    body,
                    &ret_ty,
                    sub_drops,
                    &mut case_builder,
                );

                if let Some(CandidateDrops::Locals(locals)) = sub_drops {
                    build_drops(customs, locals, ctx, &mut case_builder);
                }

                new_branches.push((cond, case_builder.to_expr(final_local)));
            }

            rc::Expr::Branch(
                lower_occur(customs, ctx, path, discrim, builder),
                new_branches,
                ret_ty,
            )
        }

        ExprInst::LetMany(bindings, ret) => {
            let final_local = ctx.with_scope(|ctx| {
                let Some(CandidateDrops::InLetMany(drops)) = drops else {
                    unreachable!()
                };

                let mut new_bindings = Vec::new();

                for (i, (ty, obligation, expr)) in bindings.iter().enumerate() {
                    let sub_drops = drops.get(&i).map(|x| &**x);
                    let rc_ty = lower_ty(type_insts, ty.modes());
                    let local = lower_expr(
                        customs,
                        type_insts,
                        func_insts,
                        inst_params,
                        ctx,
                        &path.seq(i),
                        expr,
                        &rc_ty,
                        sub_drops,
                        builder,
                    );

                    if let Some(CandidateDrops::Locals(locals)) = sub_drops {
                        build_drops(customs, locals, ctx, builder);
                    }

                    let ov = ty.modes().unapply_overlay();
                    let init_status = ov.iter().map(|_| MoveStatus::Present).collect_overlay(&ov);
                    ctx.add_local(LocalInfo {
                        annot_ty: ty.clone(),
                        rc_ty: rc_ty.clone(),
                        obligation: obligation.clone(),
                        status: init_status,
                        new_id: local,
                    });

                    new_bindings.push((rc_ty, local));
                }

                ctx.local_binding(ret.id).new_id
            });

            // Note: Early return!  We circumvent the usual return flow because we don't actually
            // want to create an expression directly corresponding to this 'let' block.  The 'let'
            // block's bindings just get absorbed into the ambient `builder`.
            return final_local;
        }

        ExprInst::Tuple(fields) => rc::Expr::Tuple(
            fields
                .iter()
                .map(|field| lower_occur(customs, ctx, path, field, builder))
                .collect(),
        ),

        ExprInst::TupleField(tup, idx) => {
            rc::Expr::TupleField(lower_occur(customs, ctx, path, tup, builder), *idx)
        }

        ExprInst::WrapVariant(variant_tys, variant_id, content) => rc::Expr::WrapVariant(
            variant_tys.map_refs(|_, ty| lower_ty(type_insts, ty.modes())),
            *variant_id,
            lower_occur(customs, ctx, path, content, builder),
        ),

        ExprInst::UnwrapVariant(variant_id, wrapped) => rc::Expr::UnwrapVariant(
            *variant_id,
            lower_occur(customs, ctx, path, wrapped, builder),
        ),

        ExprInst::WrapBoxed(content, item_ty) => rc::Expr::WrapBoxed(
            lower_occur(customs, ctx, path, content, builder),
            lower_ty(type_insts, item_ty.modes()),
        ),

        ExprInst::UnwrapBoxed(wrapped, item_ty) => rc::Expr::UnwrapBoxed(
            lower_occur(customs, ctx, path, wrapped, builder),
            lower_ty(type_insts, item_ty.modes()),
        ),

        ExprInst::WrapCustom(custom_id, content) => {
            let new_id = type_insts.resolve(TypeSpec {
                id: *custom_id,
                params: inst_params.clone(),
            });
            rc::Expr::WrapCustom(new_id, lower_occur(customs, ctx, path, content, builder))
        }

        ExprInst::UnwrapCustom(custom_id, wrapped) => {
            let new_id = type_insts.resolve(TypeSpec {
                id: *custom_id,
                params: inst_params.clone(),
            });
            rc::Expr::UnwrapCustom(new_id, lower_occur(customs, ctx, path, wrapped, builder))
        }

        ExprInst::Intrinsic(intr, arg) => {
            rc::Expr::Intrinsic(*intr, lower_occur(customs, ctx, path, arg, builder))
        }

        ExprInst::ArrayOp(ArrayOp::Get(arr, idx, ret_ty)) => {
            let info = ctx.local_binding_mut(arr.id);
            let plan = RcOpPlan::from_sel(customs.annot, &select_owned(ret_ty));
            build_plan(
                customs.rc,
                rc::RcOp::Retain,
                info.new_id,
                &info.rc_ty,
                &plan,
                builder,
            );
            rc::Expr::ArrayOp(rc::ArrayOp::Get(
                lower_ty(type_insts, arr.ty.unwrap_item_modes()),
                lower_occur(customs, ctx, path, arr, builder),
                lower_occur(customs, ctx, path, idx, builder),
            ))
        }

        ExprInst::ArrayOp(ArrayOp::Extract(arr, idx)) => rc::Expr::ArrayOp(rc::ArrayOp::Extract(
            lower_ty(type_insts, arr.ty.unwrap_item_modes()),
            lower_occur(customs, ctx, path, arr, builder),
            lower_occur(customs, ctx, path, idx, builder),
        )),

        ExprInst::ArrayOp(ArrayOp::Len(arr)) => rc::Expr::ArrayOp(rc::ArrayOp::Len(
            lower_ty(type_insts, arr.ty.unwrap_item_modes()),
            lower_occur(customs, ctx, path, arr, builder),
        )),

        ExprInst::ArrayOp(ArrayOp::Push(arr, item)) => rc::Expr::ArrayOp(rc::ArrayOp::Push(
            lower_ty(type_insts, item.ty.modes()),
            lower_occur(customs, ctx, path, arr, builder),
            lower_occur(customs, ctx, path, item, builder),
        )),

        ExprInst::ArrayOp(ArrayOp::Pop(arr)) => rc::Expr::ArrayOp(rc::ArrayOp::Pop(
            lower_ty(type_insts, arr.ty.unwrap_item_modes()),
            lower_occur(customs, ctx, path, arr, builder),
        )),

        ExprInst::ArrayOp(ArrayOp::Replace(arr, item)) => rc::Expr::ArrayOp(rc::ArrayOp::Replace(
            lower_ty(type_insts, item.ty.modes()),
            lower_occur(customs, ctx, path, arr, builder),
            lower_occur(customs, ctx, path, item, builder),
        )),

        ExprInst::ArrayOp(ArrayOp::Reserve(arr, cap)) => rc::Expr::ArrayOp(rc::ArrayOp::Reserve(
            lower_ty(type_insts, arr.ty.unwrap_item_modes()),
            lower_occur(customs, ctx, path, arr, builder),
            lower_occur(customs, ctx, path, cap, builder),
        )),

        ExprInst::IoOp(IoOp::Input) => rc::Expr::IoOp(rc::IoOp::Input),

        ExprInst::IoOp(IoOp::Output(output)) => rc::Expr::IoOp(rc::IoOp::Output(lower_occur(
            customs, ctx, path, output, builder,
        ))),

        ExprInst::Panic(ret_ty, msg) => rc::Expr::Panic(
            lower_ty(type_insts, ret_ty.modes()),
            lower_occur(customs, ctx, path, msg, builder),
        ),

        ExprInst::ArrayLit(item_ty, items) => rc::Expr::ArrayLit(
            lower_ty(type_insts, item_ty.modes()),
            items
                .iter()
                .map(|item| lower_occur(customs, ctx, path, item, builder))
                .collect(),
        ),

        ExprInst::BoolLit(lit) => rc::Expr::BoolLit(*lit),

        ExprInst::ByteLit(lit) => rc::Expr::ByteLit(*lit),

        ExprInst::IntLit(lit) => rc::Expr::IntLit(*lit),

        ExprInst::FloatLit(lit) => rc::Expr::FloatLit(*lit),
    };

    builder.add_binding(ret_ty.clone(), new_expr)
}

/// We want to deduplicate specializations w.r.t. their retains and releases. This happens in two
/// stages. First, we deduplicate w.r.t. modes and label specializations using `ModeSpecFuncId`.
#[id_type]
struct ModeSpecFuncId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Strategy {
    ElideOps,
    Trivial,
}

pub fn rc_specialize(program: annot::Program, progress: impl ProgressLogger) -> rc::Program {
    let mut progress = progress.start_session(Some(program.funcs.len()));

    let mut func_insts = FuncInstances::new();
    let mut type_insts = TypeInstances::new();

    let main_params = program.funcs[program.main]
        .constrs
        .sig
        .map_refs(|_, solution| solution.lb_const);
    let main = func_insts.resolve((program.main, main_params));

    // let mut funcs_resolved = IdVec::new();
    // let mut funcs_resolved_symbols = IdVec::new();

    while let Some((new_id, spec)) = func_insts.pop_pending() {
        let func = &program.funcs[spec.id];

        // We resolve function bodies in the same order they were enqueued
    }

    // let mut customs_resolved = BTreeMap::new();
    // let mut customs_resolved_symbols = BTreeMap::new();

    while let Some((new_id, spec)) = type_insts.pop_pending() {
        let ty = &program.custom_types.types[spec.id];

        // Analogous to the function case above
    }

    todo!()
}
