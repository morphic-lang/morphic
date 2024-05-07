use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::mode_annot_ast2::{
    self as annot, Lt, LtParam, Mode, ModeParam, MoveStatus, Overlay, Selector,
};
use crate::data::purity::Purity;
use crate::data::rc_specialized_ast2 as rc;
use crate::util::iter::IterExt;
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::ProgressLogger;
use id_collections::{id_type, Id, IdMap, IdVec};
use std::collections::BTreeMap;
use std::iter;

type AnnotExpr = annot::Expr<Mode, Lt>;
type AnnotType = annot::Type<Mode, Lt>;

type StructLt = Overlay<IdVec<LtParam, Lt>, Lt>;

impl StructLt {
    fn join_mut(&mut self, other: &StructLt) {
        self.update_with(
            other,
            |lhs, rhs| {
                for (lhs, rhs) in lhs.values_mut().zip_eq(rhs.values()) {
                    *lhs = lhs.join(rhs);
                }
            },
            |lhs, rhs| {
                *lhs = lhs.join(rhs);
            },
        );
    }
}

#[derive(Clone, Debug)]
enum Field<I, T> {
    TupleField(usize),
    VariantCase(first_ord::VariantId),
    Custom(first_ord::CustomTypeId, I, T),
    Slot(T),
}

// Identifies a "payload" carrying field, e.g. an array or box
type FieldPath<I, T> = im_rc::Vector<Field<I, T>>;

fn get_field_data<I: Clone, T: Clone>(path: &FieldPath<I, T>) -> &T {
    match path.last().expect("expected non-empty field path") {
        Field::Custom(_, _, data) | Field::Slot(data) => data,
        _ => panic!("invalid field path: should end in custom or slot field"),
    }
}

fn set_present(sel: &mut Selector, path: &FieldPath<LtParam, &Lt>) {
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
                subst[i] = MoveStatus::Present;
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

fn iterate_lt_fields<'a>(
    lt: &'a StructLt,
) -> Box<dyn Iterator<Item = FieldPath<LtParam, &'a Lt>> + 'a> {
    fn iterate_lt_fields_impl<'a>(
        root: FieldPath<LtParam, &'a Lt>,
        lt: &'a StructLt,
    ) -> Box<dyn Iterator<Item = FieldPath<LtParam, &'a Lt>> + 'a> {
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
            Overlay::Custom(id, lts) => Box::new(lts.iter().map(move |(param, lt)| {
                let mut leaf = root.clone();
                leaf.push_back(Field::Custom(*id, param, lt));
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

// Having a new occur type for `PreExpr`s ensures we don't forget to process any occurrences during
// `annot_obligations`.
#[derive(Clone, Debug)]
pub struct Occur {
    pub id: flat::LocalId,
    pub ty: AnnotType,
    pub is_final: Selector,
}

#[derive(Clone, Debug)]
pub enum ArrayOp {
    Get(AnnotType, Occur, Occur, AnnotType),
    Extract(AnnotType, Occur, Occur),
    Len(AnnotType, Occur),
    Push(AnnotType, Occur, Occur),
    Pop(AnnotType, Occur),
    Replace(AnnotType, Occur, Occur),
    Reserve(AnnotType, Occur, Occur),
}

#[derive(Clone, Debug)]
pub enum IoOp {
    Input,
    Output(Occur),
}

#[derive(Clone, Debug)]
pub enum PreExpr {
    Local(Occur),
    Call(Purity, first_ord::CustomFuncId, Occur),
    Branch(Occur, Vec<(annot::Condition<Mode, Lt>, PreExpr)>, AnnotType),
    LetMany(Vec<(AnnotType, StructLt, PreExpr)>, Occur),

    Tuple(Vec<Occur>),
    TupleField(Occur, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, AnnotType>,
        first_ord::VariantId,
        Occur,
    ),
    UnwrapVariant(first_ord::VariantId, Occur),
    WrapBoxed(Occur, AnnotType),
    UnwrapBoxed(Occur, AnnotType),
    WrapCustom(first_ord::CustomTypeId, Occur),
    UnwrapCustom(first_ord::CustomTypeId, Occur),

    Intrinsic(Intrinsic, Occur),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(AnnotType, Occur),

    ArrayLit(AnnotType, Vec<Occur>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

fn empty_struct_lt(ty: &AnnotType) -> StructLt {
    match ty {
        annot::Type::Bool => Overlay::Bool,
        annot::Type::Num(n) => Overlay::Num(*n),
        annot::Type::Tuple(fields) => Overlay::Tuple(fields.iter().map(empty_struct_lt).collect()),
        annot::Type::Variants(variants) => {
            Overlay::Variants(variants.map_refs(|_, ty| empty_struct_lt(ty)))
        }
        annot::Type::SelfCustom(id) => Overlay::SelfCustom(*id),
        annot::Type::Custom(id, tsub, _) => {
            Overlay::Custom(*id, tsub.lts.map_refs(|_, _| Lt::Empty))
        }
        annot::Type::Array(_, _, _, _) => Overlay::Array(Lt::Empty),
        annot::Type::HoleArray(_, _, _, _) => Overlay::HoleArray(Lt::Empty),
        annot::Type::Boxed(_, _, _, _) => Overlay::Boxed(Lt::Empty),
    }
}

fn get_occur_slot_obligation(
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

fn get_occur_obligation_custom(
    result: &mut IdMap<LtParam, Lt>,
    customs: &annot::CustomTypes,
    occur_path: &annot::Path,
    tsub_src: &annot::TypeSubst<Mode, Lt>,
    tsub_dst: &annot::TypeSubst<Mode, Lt>,
    ty: &annot::Type<ModeParam, LtParam>,
) {
    match ty {
        annot::Type::Bool => {}
        annot::Type::Num(_) => {}
        annot::Type::Tuple(fields) => {
            for field in fields {
                get_occur_obligation_custom(result, customs, occur_path, tsub_src, tsub_dst, field);
            }
        }
        annot::Type::Variants(variants) => {
            for (_, variant) in variants {
                get_occur_obligation_custom(
                    result, customs, occur_path, tsub_src, tsub_dst, variant,
                );
            }
        }
        annot::Type::SelfCustom(_) => {}
        annot::Type::Custom(_, tsub, _) => get_occur_obligation_custom(
            result,
            customs,
            occur_path,
            &tsub.map_vals(|m| tsub_src.ms[*m], |lt| tsub_src.lts[*lt].clone()),
            &tsub.map_vals(|m| tsub_src.ms[*m], |lt| tsub_src.lts[*lt].clone()),
            ty,
        ),
        annot::Type::Array(m, lt, _, _)
        | annot::Type::HoleArray(m, lt, _, _)
        | annot::Type::Boxed(m, lt, _, _) => {
            let obligation = get_occur_slot_obligation(
                occur_path,
                tsub_src.ms[*m],
                tsub_dst.ms[*m],
                &tsub_dst.lts[*lt],
            );
            result.insert(lt, obligation);
        }
    }
}

// TODO: the way we handle custom types here is incredibly ugly; we need some clean, efficient way
// to co-iterate the corresponding modes and lifetimes of a custom
fn get_occur_obligation(
    customs: &annot::CustomTypes,
    occur_path: &annot::Path,
    ty_src: &AnnotType,
    ty_dst: &AnnotType,
) -> StructLt {
    match (ty_src, ty_dst) {
        (annot::Type::Bool, annot::Type::Bool) => Overlay::Bool,
        (annot::Type::Num(n1), annot::Type::Num(n2)) if n1 == n2 => Overlay::Num(*n1),
        (annot::Type::Tuple(fields1), annot::Type::Tuple(fields2)) => Overlay::Tuple(
            fields1
                .iter()
                .zip_eq(fields2.iter())
                .map(|(ty1, ty2)| get_occur_obligation(customs, occur_path, ty1, ty2))
                .collect(),
        ),
        (annot::Type::Variants(variants1), annot::Type::Variants(variants2)) => {
            Overlay::Variants(IdVec::from_vec(
                variants1
                    .values()
                    .zip_eq(variants2.values())
                    .map(|(ty1, ty2)| get_occur_obligation(customs, occur_path, ty1, ty2))
                    .collect(),
            ))
        }
        (annot::Type::SelfCustom(id1), annot::Type::SelfCustom(id2)) if id1 == id2 => {
            Overlay::SelfCustom(*id1)
        }
        (annot::Type::Custom(id1, tsub1, _), annot::Type::Custom(id2, tsub2, _)) if id1 == id2 => {
            let mut lts = IdMap::new();
            get_occur_obligation_custom(
                &mut lts,
                customs,
                occur_path,
                tsub1,
                tsub2,
                &customs.types[*id1].content,
            );
            Overlay::Custom(*id1, lts.to_id_vec(tsub1.lts.count()))
        }
        (annot::Type::Array(m1, _, _, _), annot::Type::Array(m2, lt2, _, _)) => {
            Overlay::Array(get_occur_slot_obligation(occur_path, *m1, *m2, lt2))
        }
        (annot::Type::HoleArray(m1, _, _, _), annot::Type::HoleArray(m2, lt2, _, _)) => {
            Overlay::HoleArray(get_occur_slot_obligation(occur_path, *m1, *m2, lt2))
        }
        (annot::Type::Boxed(m1, _, _, _), annot::Type::Boxed(m2, lt2, _, _)) => {
            Overlay::Boxed(get_occur_slot_obligation(occur_path, *m1, *m2, lt2))
        }
        _ => unreachable!(),
    }
}

fn annot_obligations(
    customs: &annot::CustomTypes,
    path: &annot::Path,
    ctx: &mut LocalContext<flat::LocalId, (AnnotType, StructLt)>,
    expr: AnnotExpr,
) -> PreExpr {
    let handle_occur = |ctx: &mut LocalContext<_, (_, StructLt)>, occur: annot::Occur<_, _>| {
        let (ty, lt) = ctx.local_binding_mut(occur.id);

        // We must update the lifetime obligation of the binding to reflect this occurrence.
        let obligation = get_occur_obligation(customs, path, &ty, &occur.ty);
        lt.join_mut(&obligation);
        Occur {
            id: occur.id,
            ty: occur.ty,
            is_final: occur.is_final,
        }
    };

    match expr {
        annot::Expr::Local(occur) => PreExpr::Local(handle_occur(ctx, occur)),

        annot::Expr::Call(purity, func, arg) => PreExpr::Call(purity, func, handle_occur(ctx, arg)),

        annot::Expr::Branch(cond, arms, ty) => {
            let new_cond = handle_occur(ctx, cond);
            let n = arms.len();
            let new_arms = arms
                .into_iter()
                .enumerate()
                .map(|(i, (cond, expr))| {
                    (cond, annot_obligations(customs, &path.par(i, n), ctx, expr))
                })
                .collect();
            PreExpr::Branch(new_cond, new_arms, ty)
        }

        // We use `with_scope` to express our intent. In fact, all the bindings we add are popped
        // from the context before we return.
        annot::Expr::LetMany(bindings, ret) => ctx.with_scope(|ctx| {
            let mut new_exprs = Vec::new();
            for (i, (ty, expr)) in bindings.into_iter().enumerate() {
                let init = empty_struct_lt(&ty);
                let _ = ctx.add_local((ty, init));
                let new_expr = annot_obligations(customs, &path.seq(i), ctx, expr);
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
            PreExpr::LetMany(new_bindings, handle_occur(ctx, ret))
        }),

        annot::Expr::Tuple(fields) => PreExpr::Tuple(
            fields
                .into_iter()
                .map(|occur| handle_occur(ctx, occur))
                .collect(),
        ),

        annot::Expr::TupleField(tup, idx) => PreExpr::TupleField(handle_occur(ctx, tup), idx),

        annot::Expr::WrapVariant(variants, variant, content) => {
            PreExpr::WrapVariant(variants, variant, handle_occur(ctx, content))
        }

        annot::Expr::UnwrapVariant(variant, content) => {
            PreExpr::UnwrapVariant(variant, handle_occur(ctx, content))
        }

        annot::Expr::WrapBoxed(content, ty) => PreExpr::WrapBoxed(handle_occur(ctx, content), ty),

        annot::Expr::UnwrapBoxed(content, ty) => {
            PreExpr::UnwrapBoxed(handle_occur(ctx, content), ty)
        }

        annot::Expr::WrapCustom(id, content) => PreExpr::WrapCustom(id, handle_occur(ctx, content)),

        annot::Expr::UnwrapCustom(id, content) => {
            PreExpr::UnwrapCustom(id, handle_occur(ctx, content))
        }

        annot::Expr::Intrinsic(intrinsic, occur) => {
            PreExpr::Intrinsic(intrinsic, handle_occur(ctx, occur))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Get(item_ty, arr, idx, ty)) => PreExpr::ArrayOp(
            ArrayOp::Get(item_ty, handle_occur(ctx, arr), handle_occur(ctx, idx), ty),
        ),
        annot::Expr::ArrayOp(annot::ArrayOp::Extract(item_ty, arr, idx)) => PreExpr::ArrayOp(
            ArrayOp::Extract(item_ty, handle_occur(ctx, arr), handle_occur(ctx, idx)),
        ),
        annot::Expr::ArrayOp(annot::ArrayOp::Len(ty, arr)) => {
            PreExpr::ArrayOp(ArrayOp::Len(ty, handle_occur(ctx, arr)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Push(item_ty, arr, item)) => PreExpr::ArrayOp(
            ArrayOp::Push(item_ty, handle_occur(ctx, arr), handle_occur(ctx, item)),
        ),
        annot::Expr::ArrayOp(annot::ArrayOp::Pop(ty, arr)) => {
            PreExpr::ArrayOp(ArrayOp::Pop(ty, handle_occur(ctx, arr)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Replace(ty, arr, item)) => PreExpr::ArrayOp(
            ArrayOp::Replace(ty, handle_occur(ctx, arr), handle_occur(ctx, item)),
        ),
        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(ty, arr, cap)) => PreExpr::ArrayOp(
            ArrayOp::Reserve(ty, handle_occur(ctx, arr), handle_occur(ctx, cap)),
        ),

        annot::Expr::IoOp(annot::IoOp::Input) => PreExpr::IoOp(IoOp::Input),
        annot::Expr::IoOp(annot::IoOp::Output(occur)) => {
            PreExpr::IoOp(IoOp::Output(handle_occur(ctx, occur)))
        }

        annot::Expr::Panic(ty, occur) => PreExpr::Panic(ty, handle_occur(ctx, occur)),
        annot::Expr::ArrayLit(ty, elems) => PreExpr::ArrayLit(
            ty,
            elems
                .into_iter()
                .map(|occur| handle_occur(ctx, occur))
                .collect(),
        ),

        annot::Expr::BoolLit(b) => PreExpr::BoolLit(b),
        annot::Expr::ByteLit(b) => PreExpr::ByteLit(b),
        annot::Expr::IntLit(i) => PreExpr::IntLit(i),
        annot::Expr::FloatLit(f) => PreExpr::FloatLit(f),
    }
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

    fn from_expr(expr: &PreExpr) -> Self {
        fn from_expr_impl(expr: &PreExpr) -> Option<CandidateDrops> {
            match expr {
                PreExpr::Branch(_, arms, _) => {
                    let mut drops = BTreeMap::new();
                    for (i, (_, expr)) in arms.iter().enumerate() {
                        if let Some(arm_drops) = from_expr_impl(expr) {
                            drops.insert(i, Box::new(arm_drops));
                        }
                    }
                    Some(CandidateDrops::InBranch(drops))
                }
                PreExpr::LetMany(bindings, _) => {
                    let mut drops = BTreeMap::new();
                    for (i, (_, _, expr)) in bindings.iter().enumerate() {
                        if let Some(binding_drops) = from_expr_impl(expr) {
                            drops.insert(i, Box::new(binding_drops));
                        }
                    }
                    Some(CandidateDrops::InLetMany(drops))
                }
                _ => None,
            }
        }
        from_expr_impl(expr).unwrap_or_else(|| Self::empty_locals())
    }

    // TODO: using `Selector`s here (as we've currently defined them) is quite inefficient. We
    // should use a data structure which can *sparsely* represent a subset of fields
    fn register_binding_slot(
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
                if self_locals.contains_key(&binding) {
                    let self_slot = self_locals.get_mut(&binding).unwrap();
                    self_slot.or_eq(slot);
                } else {
                    self_locals.insert(binding, slot.clone());
                }
            }

            annot::LocalLt::Seq(arm, i) => {
                let CandidateDrops::InLetMany(self_arms) = self else {
                    panic!("structurally incompatible obligations");
                };
                let self_arm = self_arms
                    .entry(*i)
                    .or_insert_with(|| Box::new(CandidateDrops::empty_locals()));
                self_arm.register_binding_slot(binding, slot, arm);
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
                        self_arm.register_binding_slot(binding, slot, arm);
                    }
                }
            }
        }
    }

    fn register_binding(
        &mut self,
        binding_path: &annot::Path,
        binding: flat::LocalId,
        binding_ty: &AnnotType,
        obligation: &StructLt,
    ) {
        let sel = Selector::from_ty(binding_ty, MoveStatus::Absent);
        for path in iterate_lt_fields(obligation) {
            let mut slot_sel = sel.clone(); // TODO: don't clone here
            set_present(&mut slot_sel, &path);

            match get_field_data(&path) {
                // We don't need to do anything; the binding escapes into the caller's scope
                Lt::Join(_) => {}
                // The binding is unused; we can drop it immediately
                Lt::Empty => {
                    self.register_binding_slot(binding, &slot_sel, &binding_path.as_local_lt());
                }
                Lt::Local(lt) => {
                    self.register_binding_slot(binding, &slot_sel, &lt);
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
            Overlay::SelfCustom(_) => Self::NoOp,
            Overlay::Custom(id, sub) => {
                todo!();
                // let inner = sub.apply_to(&customs.types[*id].overlay);
                // let sub_plan = RcOpPlan::from_sel(customs, &inner);
                // if matches!(sub_plan, RcOpPlan::NoOp) {
                //     Self::NoOp
                // } else {
                //     Self::OnCustom(Box::new(sub_plan))
                // }
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

// TODO: make `subst` and `overlay_subst` references
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct TypeSpecInfo {
    id: first_ord::CustomTypeId,
    subst: IdVec<ModeParam, Mode>,
    overlay_subst: BTreeMap<ModeParam, Mode>,
}

// TODO: make `subst` and `overlay_subst` references
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FuncSpecInfo {
    id: first_ord::CustomFuncId,
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
        id: custom_id,
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
    mapping: &BTreeMap<TypeSpecInfo, rc::CustomTypeId>,
    ty: &annot::Type<Mode, Lt>,
) -> rc::Type {
    match ty {
        annot::Type::Bool => rc::Type::Bool,
        annot::Type::Num(n) => rc::Type::Num(*n),
        annot::Type::Tuple(fields) => rc::Type::Tuple(
            fields
                .iter()
                .map(|field| lower_ty(mapping, field))
                .collect(),
        ),
        annot::Type::Variants(variants) => {
            rc::Type::Variants(variants.map_refs(|_, ty| lower_ty(mapping, ty)))
        }
        annot::Type::SelfCustom(id) => unreachable!(),
        annot::Type::Custom(id, tsub, osub) => {
            let spec = TypeSpecInfo {
                id: *id,
                subst: tsub.ms.clone(),
                overlay_subst: osub.0.clone(),
            };
            rc::Type::Custom(mapping[&spec])
        }
        annot::Type::Array(mode, _, item_ty, _) => {
            rc::Type::Array(*mode, Box::new(lower_ty(mapping, item_ty)))
        }
        annot::Type::HoleArray(mode, _, item_ty, _) => {
            rc::Type::HoleArray(*mode, Box::new(lower_ty(mapping, item_ty)))
        }
        annot::Type::Boxed(mode, _, item_ty, _) => {
            rc::Type::Boxed(*mode, Box::new(lower_ty(mapping, item_ty)))
        }
    }
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
        (Mode::Borrowed, Mode::Owned) => MoveStatus::Present,
        (Mode::Owned, Mode::Owned) => {
            if lt.does_not_exceed(path) && old_status == MoveStatus::Present {
                MoveStatus::Absent
            } else {
                MoveStatus::Present
            }
        }
    }
}

fn select_dups_custom(
    result: &mut IdMap<LtParam, MoveStatus>,
    customs: &annot::CustomTypes,
    path: &annot::Path,
    status: &IdVec<LtParam, MoveStatus>,
    tsub_src: &annot::TypeSubst<Mode, Lt>,
    tsub_dst: &annot::TypeSubst<Mode, Lt>,
    lt_obligation: &IdVec<LtParam, Lt>,
    ty: &annot::Type<ModeParam, LtParam>,
) {
    match ty {
        annot::Type::Bool => {}
        annot::Type::Num(_) => {}
        annot::Type::Tuple(fields) => {
            for field in fields {
                select_dups_custom(
                    result,
                    customs,
                    path,
                    status,
                    tsub_src,
                    tsub_dst,
                    lt_obligation,
                    field,
                );
            }
        }
        annot::Type::Variants(variants) => {
            for (_, variant) in variants {
                select_dups_custom(
                    result,
                    customs,
                    path,
                    status,
                    tsub_src,
                    tsub_dst,
                    lt_obligation,
                    variant,
                );
            }
        }
        annot::Type::SelfCustom(_) => {}
        annot::Type::Custom(id, tsub, _) => {
            select_dups_custom(
                result,
                customs,
                path,
                &tsub.lts.map_refs(|_, lt| status[*lt].clone()),
                &tsub.map_vals(|m| tsub_src.ms[*m], |lt| tsub_src.lts[*lt].clone()),
                &tsub.map_vals(|m| tsub_dst.ms[*m], |lt| tsub_dst.lts[*lt].clone()),
                &tsub.lts.map_refs(|_, lt| lt_obligation[*lt].clone()),
                &customs.types[*id].content,
            );
        }
        annot::Type::Array(m, lt, _, _)
        | annot::Type::HoleArray(m, lt, _, _)
        | annot::Type::Boxed(m, lt, _, _) => {
            let dups = select_slot_dups(
                path,
                status[*lt],
                tsub_src.ms[*m],
                tsub_dst.ms[*m],
                &lt_obligation[*lt],
            );
            result.insert(lt, dups);
        }
    }
}

fn select_dups(
    customs: &annot::CustomTypes,
    path: &annot::Path,
    status: &Selector,
    src_ty: &AnnotType,
    dst_ty: &AnnotType,
    lt_obligation: &StructLt,
) -> Selector {
    use annot::Type as T;
    use Overlay as O;

    match (status, src_ty, dst_ty, lt_obligation) {
        (O::Bool, T::Bool, T::Bool, O::Bool) => O::Bool,

        (O::Num(n1), T::Num(n2), T::Num(n3), O::Num(n4)) if n1 == n2 && n1 == n3 && n1 == n4 => {
            O::Num(*n1)
        }

        (O::Tuple(fields1), T::Tuple(fields2), T::Tuple(fields3), O::Tuple(fields4)) => O::Tuple(
            fields1
                .iter()
                .zip_eq(fields2)
                .zip_eq(fields3)
                .zip_eq(fields4)
                .map(|(((dups, src), dst), lt)| select_dups(customs, path, dups, src, dst, lt))
                .collect(),
        ),

        (
            O::Variants(variants1),
            T::Variants(variants2),
            T::Variants(variants3),
            O::Variants(variants4),
        ) => O::Variants(IdVec::from_vec(
            variants1
                .values()
                .zip_eq(variants2.values())
                .zip_eq(variants3.values())
                .zip_eq(variants4.values())
                .map(|(((dups, src), dst), lt)| select_dups(customs, path, dups, src, dst, lt))
                .collect(),
        )),

        (O::SelfCustom(id1), T::SelfCustom(id2), T::SelfCustom(id3), O::SelfCustom(id4))
            if id1 == id2 && id1 == id3 && id1 == id4 =>
        {
            O::SelfCustom(*id1)
        }

        (
            O::Custom(id1, sub1),
            T::Custom(id2, sub2, _),
            T::Custom(id3, sub3, _),
            O::Custom(id4, sub4),
        ) if id1 == id2 && id1 == id3 && id1 == id4 => {
            let mut lts = IdMap::new();
            select_dups_custom(
                &mut lts,
                customs,
                path,
                sub1,
                sub2,
                sub3,
                sub4,
                &customs.types[*id2].content,
            );
            O::Custom(*id1, lts.to_id_vec(sub1.count()))
        }

        (O::Array(status), T::Array(msrc, _, _, _), T::Array(mdst, _, _, _), O::Array(lt)) => {
            O::Array(select_slot_dups(path, *status, *msrc, *mdst, lt))
        }

        (
            O::HoleArray(status),
            T::HoleArray(msrc, _, _, _),
            T::HoleArray(mdst, _, _, _),
            O::HoleArray(lt),
        ) => O::HoleArray(select_slot_dups(path, *status, *msrc, *mdst, lt)),

        (O::Boxed(status), T::Boxed(msrc, _, _, _), T::Boxed(mdst, _, _, _), O::Boxed(lt)) => {
            O::Boxed(select_slot_dups(path, *status, *msrc, *mdst, lt))
        }

        _ => unreachable!(),
    }
}

fn select_slot_borrows(is_duped: MoveStatus, dst_mode: Mode) -> MoveStatus {
    match dst_mode {
        Mode::Borrowed => MoveStatus::Present,
        Mode::Owned => is_duped,
    }
}

fn select_borrows_custom(
    result: &mut IdMap<LtParam, MoveStatus>,
    customs: &annot::CustomTypes,
    selected_dups: &IdVec<LtParam, MoveStatus>,
    tsub_dst: &annot::TypeSubst<Mode, Lt>,
    ty: &annot::Type<ModeParam, LtParam>,
) {
    match ty {
        annot::Type::Bool => {}
        annot::Type::Num(_) => {}
        annot::Type::Tuple(fields) => {
            for field in fields {
                select_borrows_custom(result, customs, selected_dups, tsub_dst, field);
            }
        }
        annot::Type::Variants(variants) => {
            for (_, variant) in variants {
                select_borrows_custom(result, customs, selected_dups, tsub_dst, variant);
            }
        }
        annot::Type::SelfCustom(_) => {}
        annot::Type::Custom(_, tsub, _) => select_borrows_custom(
            result,
            customs,
            &tsub.lts.map_refs(|_, lt| selected_dups[*lt]),
            &tsub.map_vals(|m| tsub_dst.ms[*m], |lt| tsub_dst.lts[*lt].clone()),
            ty,
        ),
        annot::Type::Array(m, lt, _, _)
        | annot::Type::HoleArray(m, lt, _, _)
        | annot::Type::Boxed(m, lt, _, _) => {
            let borrows = select_slot_borrows(selected_dups[*lt], tsub_dst.ms[*m]);
            result.insert(lt, borrows);
        }
    }
}

fn select_borrows(
    customs: &annot::CustomTypes,
    selected_dups: &Selector,
    dst_ty: &AnnotType,
) -> Selector {
    match (selected_dups, dst_ty) {
        (Overlay::Bool, annot::Type::Bool) => Overlay::Bool,
        (Overlay::Num(n1), annot::Type::Num(n2)) if n1 == n2 => Overlay::Num(*n1),
        (Overlay::Tuple(fields1), annot::Type::Tuple(fields2)) => Overlay::Tuple(
            fields1
                .iter()
                .zip_eq(fields2.iter())
                .map(|(dups, ty)| select_borrows(customs, dups, ty))
                .collect(),
        ),
        (Overlay::Variants(variants1), annot::Type::Variants(variants2)) => {
            Overlay::Variants(IdVec::from_vec(
                variants1
                    .values()
                    .zip_eq(variants2.values())
                    .map(|(dups, ty)| select_borrows(customs, dups, ty))
                    .collect(),
            ))
        }
        (Overlay::SelfCustom(id1), annot::Type::SelfCustom(id2)) if id1 == id2 => {
            Overlay::SelfCustom(*id1)
        }
        (Overlay::Custom(id1, sub1), annot::Type::Custom(id2, sub2, _)) if id1 == id2 => {
            let mut lts = IdMap::new();
            select_borrows_custom(&mut lts, customs, sub1, sub2, &customs.types[*id1].content);
            Overlay::Custom(*id1, lts.to_id_vec(sub1.count()))
        }
        (Overlay::Array(status), annot::Type::Array(m2, _, _, _)) => {
            Overlay::Array(select_slot_borrows(*status, *m2))
        }
        (Overlay::HoleArray(status), annot::Type::HoleArray(m2, _, _, _)) => {
            Overlay::HoleArray(select_slot_borrows(*status, *m2))
        }
        (Overlay::Boxed(status), annot::Type::Boxed(m2, _, _, _)) => {
            Overlay::Boxed(select_slot_borrows(*status, *m2))
        }
        _ => unreachable!(),
    }
}

/*

fn select_owned(ty: &AnnotType) -> Selector {
    match ty {
        AnnotType::Bool => Selector::Bool,
        AnnotType::Num(n) => Selector::Num(*n),
        AnnotType::Tuple(fields) => {
            Selector::Tuple(fields.iter().map(|field| select_owned(field)).collect())
        }
        AnnotType::Variants(variants) => {
            Selector::Variants(variants.map_refs(|_, ty| select_owned(ty)))
        }
        AnnotType::SelfCustom(id) => Selector::SelfCustom(*id),
        AnnotType::Custom(id, tsub, _) => Selector::Custom(
            *id,
            tsub.ms.map_refs(|_, mode| match mode {
                Mode::Borrowed => MoveStatus::Absent,
                Mode::Owned => MoveStatus::Present,
            }),
        ),
        AnnotType::Array(mode, _, item_ty, _) => {
            Selector::Array(*mode, Box::new(select_owned(item_ty)))
        }
        AnnotType::HoleArray(mode, _, item_ty, _) => {
            Selector::HoleArray(*mode, Box::new(select_owned(item_ty)))
        }
        AnnotType::Boxed(mode, _, item_ty, _) => {
            Selector::Boxed(*mode, Box::new(select_owned(item_ty)))
        }
    }
}

#[derive(Clone, Debug)]
struct LocalInfo {
    annot_ty: AnnotType,
    rc_ty: rc::Type,
    obligation: StructLt,
    status: Selector,
    new_id: rc::LocalId,
}

#[derive(Clone, Copy, Debug)]
struct Customs<'a> {
    annot: &'a annot::CustomTypes,
    rc: &'a rc::CustomTypes,
    ty_map: &'a BTreeMap<TypeSpecInfo, rc::CustomTypeId>,
    fn_map: &'a BTreeMap<FuncSpecInfo, rc::CustomFuncId>,
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

fn reify_occur(
    customs: Customs<'_>,
    ctx: &mut LocalContext<flat::LocalId, LocalInfo>,
    path: &annot::Path,
    occur: &Occur,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    let info = ctx.local_binding_mut(occur.id);
    let dups = select_dups(
        customs.annot,
        path,
        &info.status,
        &info.annot_ty,
        &occur.ty,
        &info.obligation,
    );
    let borrows = select_borrows(customs.annot, &dups, &occur.ty);

    build_plan(
        customs.rc,
        rc::RcOp::Retain,
        info.new_id,
        &lower_ty(customs.ty_map, &info.annot_ty),
        &RcOpPlan::from_sel(customs.annot, &dups),
        builder,
    );

    info.status.and_eq(&borrows);
    info.new_id
}

fn reify_cond(
    customs: Customs<'_>,
    spec_tsub: &IdVec<ModeParam, Mode>,
    spec_osub: &BTreeMap<ModeParam, Mode>,
    cond: &annot::Condition<Mode, Lt>,
) -> rc::Condition {
    match cond {
        annot::Condition::Any => rc::Condition::Any,
        annot::Condition::Tuple(conds) => rc::Condition::Tuple(
            conds
                .iter()
                .map(|cond| reify_cond(customs, spec_tsub, spec_osub, cond))
                .collect(),
        ),
        annot::Condition::Variant(variant_id, cond) => rc::Condition::Variant(
            *variant_id,
            Box::new(reify_cond(customs, spec_tsub, spec_osub, cond)),
        ),
        annot::Condition::Boxed(cond, item_ty) => rc::Condition::Boxed(
            Box::new(reify_cond(customs, spec_tsub, spec_osub, cond)),
            lower_ty(customs.ty_map, item_ty),
        ),
        annot::Condition::Custom(custom_id, cond) => {
            let new_id = customs.ty_map[&TypeSpecInfo {
                id: *custom_id,
                subst: spec_tsub.clone(),
                overlay_subst: spec_osub.clone(),
            }];

            rc::Condition::Custom(
                new_id,
                Box::new(reify_cond(customs, spec_tsub, spec_osub, cond)),
            )
        }
        annot::Condition::BoolConst(lit) => rc::Condition::BoolConst(*lit),
        annot::Condition::ByteConst(lit) => rc::Condition::ByteConst(*lit),
        annot::Condition::IntConst(lit) => rc::Condition::IntConst(*lit),
        annot::Condition::FloatConst(lit) => rc::Condition::FloatConst(*lit),
    }
}

fn reify_expr(
    customs: Customs<'_>,
    spec_tsub: &IdVec<ModeParam, Mode>,
    spec_osub: &BTreeMap<ModeParam, Mode>,
    ctx: &mut LocalContext<flat::LocalId, LocalInfo>,
    path: &annot::Path,
    expr: &PreExpr,
    ret_ty: &rc::Type,
    drops: Option<&CandidateDrops>,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    let new_expr = match expr {
        PreExpr::Local(local) => rc::Expr::Local(reify_occur(customs, ctx, path, local, builder)),

        PreExpr::Call(purity, func, arg) => {
            let new_id = customs.fn_map[&FuncSpecInfo {
                id: *func,
                subst: spec_tsub.clone(),
                overlay_subst: spec_osub.clone(),
            }];

            rc::Expr::Call(
                *purity,
                new_id,
                reify_occur(customs, ctx, path, arg, builder),
            )
        }

        PreExpr::Branch(discrim, branches, ret_ty) => {
            let Some(CandidateDrops::InBranch(drops)) = drops else {
                unreachable!()
            };

            let mut new_branches: Vec<(rc::Condition, _)> = Vec::new();
            let n = branches.len();
            let ret_ty = lower_ty(customs.ty_map, ret_ty);

            for (i, (cond, body)) in branches.iter().enumerate() {
                let mut case_builder = builder.child();
                let sub_drops = drops.get(&i).map(|x| &**x);

                let cond = reify_cond(customs, spec_tsub, spec_osub, cond);
                let final_local = reify_expr(
                    customs,
                    spec_tsub,
                    spec_osub,
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
                reify_occur(customs, ctx, path, discrim, builder),
                new_branches,
                ret_ty,
            )
        }

        PreExpr::LetMany(bindings, ret) => {
            let final_local = ctx.with_scope(|ctx| {
                let Some(CandidateDrops::InLetMany(drops)) = drops else {
                    unreachable!()
                };

                let mut new_bindings = Vec::new();

                for (i, (ty, obligation, expr)) in bindings.iter().enumerate() {
                    let sub_drops = drops.get(&i).map(|x| &**x);
                    let rc_ty = lower_ty(customs.ty_map, ty);
                    let local = reify_expr(
                        customs,
                        spec_tsub,
                        spec_osub,
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

                    ctx.add_local(LocalInfo {
                        annot_ty: ty.clone(),
                        rc_ty: rc_ty.clone(),
                        obligation: obligation.clone(),
                        status: Selector::from_ty(ty, MoveStatus::Present),
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

        PreExpr::Tuple(fields) => rc::Expr::Tuple(
            fields
                .iter()
                .map(|field| reify_occur(customs, ctx, path, field, builder))
                .collect(),
        ),

        PreExpr::TupleField(tup, idx) => {
            rc::Expr::TupleField(reify_occur(customs, ctx, path, tup, builder), *idx)
        }

        PreExpr::WrapVariant(variant_tys, variant_id, content) => rc::Expr::WrapVariant(
            variant_tys.map_refs(|_, ty| lower_ty(customs.ty_map, ty)),
            *variant_id,
            reify_occur(customs, ctx, path, content, builder),
        ),

        PreExpr::UnwrapVariant(variant_id, wrapped) => rc::Expr::UnwrapVariant(
            *variant_id,
            reify_occur(customs, ctx, path, wrapped, builder),
        ),

        PreExpr::WrapBoxed(content, item_ty) => rc::Expr::WrapBoxed(
            reify_occur(customs, ctx, path, content, builder),
            lower_ty(customs.ty_map, item_ty),
        ),

        PreExpr::UnwrapBoxed(wrapped, item_ty) => rc::Expr::UnwrapBoxed(
            reify_occur(customs, ctx, path, wrapped, builder),
            lower_ty(customs.ty_map, item_ty),
        ),

        PreExpr::WrapCustom(custom_id, content) => {
            let new_id = customs.ty_map[&TypeSpecInfo {
                id: *custom_id,
                subst: spec_tsub.clone(),
                overlay_subst: spec_osub.clone(),
            }];

            rc::Expr::WrapCustom(new_id, reify_occur(customs, ctx, path, content, builder))
        }

        PreExpr::UnwrapCustom(custom_id, wrapped) => {
            let new_id = customs.ty_map[&TypeSpecInfo {
                id: *custom_id,
                subst: spec_tsub.clone(),
                overlay_subst: spec_osub.clone(),
            }];

            rc::Expr::UnwrapCustom(new_id, reify_occur(customs, ctx, path, wrapped, builder))
        }

        PreExpr::Intrinsic(intr, arg) => {
            rc::Expr::Intrinsic(*intr, reify_occur(customs, ctx, path, arg, builder))
        }

        PreExpr::ArrayOp(ArrayOp::Get(item_ty, arr, idx, _)) => {
            todo!();
            rc::Expr::ArrayOp(rc::ArrayOp::Get(
                lower_ty(customs.ty_map, item_ty),
                reify_occur(customs, ctx, path, arr, builder),
                reify_occur(customs, ctx, path, idx, builder),
            ))
        }

        PreExpr::ArrayOp(ArrayOp::Extract(item_ty, arr, idx)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Extract(
                lower_ty(customs.ty_map, item_ty),
                reify_occur(customs, ctx, path, arr, builder),
                reify_occur(customs, ctx, path, idx, builder),
            ))
        }

        PreExpr::ArrayOp(ArrayOp::Len(item_ty, arr)) => rc::Expr::ArrayOp(rc::ArrayOp::Len(
            lower_ty(customs.ty_map, item_ty),
            reify_occur(customs, ctx, path, arr, builder),
        )),

        PreExpr::ArrayOp(ArrayOp::Push(item_ty, arr, item)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Push(
                lower_ty(customs.ty_map, item_ty),
                reify_occur(customs, ctx, path, arr, builder),
                reify_occur(customs, ctx, path, item, builder),
            ))
        }

        PreExpr::ArrayOp(ArrayOp::Pop(item_ty, arr)) => rc::Expr::ArrayOp(rc::ArrayOp::Pop(
            lower_ty(customs.ty_map, item_ty),
            reify_occur(customs, ctx, path, arr, builder),
        )),

        PreExpr::ArrayOp(ArrayOp::Replace(item_ty, arr, item)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Replace(
                lower_ty(customs.ty_map, item_ty),
                reify_occur(customs, ctx, path, arr, builder),
                reify_occur(customs, ctx, path, item, builder),
            ))
        }

        PreExpr::ArrayOp(ArrayOp::Reserve(item_ty, arr, cap)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Reserve(
                lower_ty(customs.ty_map, item_ty),
                reify_occur(customs, ctx, path, arr, builder),
                reify_occur(customs, ctx, path, cap, builder),
            ))
        }

        PreExpr::IoOp(IoOp::Input) => rc::Expr::IoOp(rc::IoOp::Input),

        PreExpr::IoOp(IoOp::Output(output)) => rc::Expr::IoOp(rc::IoOp::Output(reify_occur(
            customs, ctx, path, output, builder,
        ))),

        PreExpr::Panic(ret_ty, msg) => rc::Expr::Panic(
            lower_ty(customs.ty_map, ret_ty),
            reify_occur(customs, ctx, path, msg, builder),
        ),

        PreExpr::ArrayLit(item_ty, items) => rc::Expr::ArrayLit(
            lower_ty(customs.ty_map, item_ty),
            items
                .iter()
                .map(|item| reify_occur(customs, ctx, path, item, builder))
                .collect(),
        ),

        PreExpr::BoolLit(lit) => rc::Expr::BoolLit(*lit),

        PreExpr::ByteLit(lit) => rc::Expr::ByteLit(*lit),

        PreExpr::IntLit(lit) => rc::Expr::IntLit(*lit),

        PreExpr::FloatLit(lit) => rc::Expr::FloatLit(*lit),
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

*/
