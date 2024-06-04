use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::intrinsics::Intrinsic;
use crate::data::mode_annot_ast2::{
    self as annot, CollectOverlay, LocalLt, Lt, Mode, ModeData, ModeParam, ModeSolution, Overlay,
    Path, SlotId,
};
use crate::data::num_type::NumType;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::rc_specialized_ast2 as rc;
use crate::util::instance_queue::InstanceQueue;
use crate::util::iter::IterExt;
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{id_type, Count, IdVec};
use once_cell::sync::Lazy;
use std::collections::BTreeMap;
use std::iter;

//////////////////////////////////////////
/// TODO:
/// - Discard access mode when indexing type specializations
/// - Thread type and function symbols through specialization
//////////////////////////////////////////

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FuncSpec {
    old_id: first_ord::CustomFuncId,
    params: IdVec<ModeParam, Mode>,
}

type FuncInstances = InstanceQueue<FuncSpec, rc::CustomFuncId>;

mod lower_types {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub struct TypeSpecHead {
        pub old_id: first_ord::CustomTypeId,
        pub osub: BTreeMap<SlotId, Mode>,
        pub tsub: IdVec<SlotId, Mode>,
    }

    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct TypeSpecTail {
        old_id: first_ord::CustomTypeId,
        tsub: IdVec<SlotId, Mode>,
    }

    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum TypeSpec {
        Head(TypeSpecHead),
        Tail(TypeSpecTail),
    }

    // The way things are set up, we can't use a plain `InstanceQueue` for type specialization. The
    // problem is that we need to see the actual content of type specializations while emitting
    // `RcOpPlan`s to create bindings for unwrapped customs. This can't be easily circumvented because
    // head unrolling makes type specializations non-trivial in an annoying way. The two obvious
    // solutions are: (1) fill in the custom type table eagerly; (2) split lowering into two phases,
    // where the first phase creates plans but does not emit them. We opt for (1).
    #[derive(Clone, Debug)]
    pub struct TypeInstances {
        inner: InstanceQueue<TypeSpec, rc::CustomTypeId>,
        customs: IdVec<rc::CustomTypeId, rc::Type>,
        // custom_symbols: IdVec<rc::CustomTypeId, first_ord::CustomTypeSymbols>,
    }

    impl TypeInstances {
        pub fn new() -> Self {
            TypeInstances {
                inner: InstanceQueue::new(),
                customs: IdVec::new(),
            }
        }

        fn lower_custom_type_head(
            &mut self,
            customs: &annot::CustomTypes,
            custom_id: first_ord::CustomTypeId,
            osub: &BTreeMap<SlotId, Mode>,
            tsub: &IdVec<SlotId, Mode>,
        ) -> rc::Type {
            let custom = &customs.types[custom_id];
            let ty = custom.ty.modes().hydrate(tsub);
            let ov = custom.ov.hydrate(osub);

            let ty = ty.apply_overlay(&ov);
            lower_type_impl(customs, &mut self.inner, Some(tsub), &ty)
        }

        fn lower_custom_type_tail(
            &mut self,
            customs: &annot::CustomTypes,
            custom_id: first_ord::CustomTypeId,
            tsub: &IdVec<SlotId, Mode>,
        ) -> rc::Type {
            let ty = customs.types[custom_id].ty.modes().hydrate(&tsub);
            lower_type_impl(customs, &mut self.inner, Some(tsub), &ty)
        }

        fn force(&mut self, customs: &annot::CustomTypes) {
            while let Some((id, spec)) = self.inner.pop_pending() {
                let lowered_ty = match spec {
                    TypeSpec::Head(TypeSpecHead { old_id, osub, tsub }) => {
                        self.lower_custom_type_head(customs, old_id, &osub, &tsub)
                    }
                    TypeSpec::Tail(TypeSpecTail { old_id, tsub }) => {
                        self.lower_custom_type_tail(customs, old_id, &tsub)
                    }
                };
                let pushed_id = self.customs.push(lowered_ty);
                debug_assert_eq!(pushed_id, id);
            }
        }

        pub fn lower_type(&mut self, customs: &annot::CustomTypes, ty: &PreModeData) -> rc::Type {
            let ret_ty = lower_type_impl(&customs, &mut self.inner, None, ty);
            self.force(customs);
            ret_ty
        }

        pub fn resolve(
            &mut self,
            customs: &annot::CustomTypes,
            inst: TypeSpecHead,
        ) -> rc::CustomTypeId {
            let ret_id = self.inner.resolve(TypeSpec::Head(inst));
            self.force(customs);
            ret_id
        }

        pub fn lookup_resolved(&self, id: rc::CustomTypeId) -> &rc::Type {
            &self.customs[id]
        }

        pub fn into_customs(
            mut self,
            customs: &annot::CustomTypes,
        ) -> IdVec<rc::CustomTypeId, rc::Type> {
            self.force(customs);
            self.customs
        }
    }

    // It is very important that this function uses `InstanceQueue::resolve` rather than
    // `TypeInstances::resolve` to avoid infinite recursion.
    fn lower_type_impl(
        customs: &annot::CustomTypes,
        insts: &mut InstanceQueue<TypeSpec, rc::CustomTypeId>,
        self_tsub: Option<&IdVec<SlotId, Mode>>,
        ty: &PreModeData,
    ) -> rc::Type {
        match ty {
            PreModeData::Bool => rc::Type::Bool,
            PreModeData::Num(n) => rc::Type::Num(*n),
            PreModeData::Tuple(tys) => rc::Type::Tuple(
                tys.iter()
                    .map(|ty| lower_type_impl(customs, insts, self_tsub, ty))
                    .collect(),
            ),
            PreModeData::Variants(tys) => rc::Type::Variants(
                tys.map_refs(|_, ty| lower_type_impl(customs, insts, self_tsub, ty)),
            ),
            PreModeData::SelfCustom(id) => {
                let self_tsub = self_tsub
                    .expect("`self_tsub` must be provided when lowering a custom type body");
                let spec = TypeSpecTail {
                    old_id: *id,
                    tsub: self_tsub.clone(),
                };
                rc::Type::Custom(insts.resolve(TypeSpec::Tail(spec)))
            }
            PreModeData::Custom(id, osub, tsub) => {
                let spec = TypeSpecHead {
                    old_id: *id,
                    osub: osub.clone(),
                    tsub: tsub.clone(),
                };
                rc::Type::Custom(insts.resolve(TypeSpec::Head(spec)))
            }
            PreModeData::Array(mode, _, item_ty) => rc::Type::Array(
                *mode,
                Box::new(lower_type_impl(customs, insts, self_tsub, item_ty)),
            ),
            PreModeData::HoleArray(mode, _, item_ty) => rc::Type::HoleArray(
                *mode,
                Box::new(lower_type_impl(customs, insts, self_tsub, item_ty)),
            ),
            PreModeData::Boxed(mode, _, item_ty) => rc::Type::Boxed(
                *mode,
                Box::new(lower_type_impl(customs, insts, self_tsub, item_ty)),
            ),
        }
    }
}

use lower_types::*;

////////////////////////////////////////
// The first stage of this pass must annotate each binding with its "stack" lifetime. It is also
// convenient to specialize function calls here. We leave type specialization until a later stage
// because we need full `annot::Type`s to determine where retains and releases should be inserted.
////////////////////////////////////////

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

type AnnotExpr = annot::Expr<ModeSolution, Lt>;
type AnnotType = annot::Type<ModeSolution, Lt>;

type PreType = annot::Type<Mode, Lt>;
type PreModeData = annot::ModeData<Mode>;

#[derive(Clone, Debug)]
struct PreOccur {
    pub id: flat::LocalId,
    pub ty: PreType,
}

#[derive(Clone, Debug)]
enum ArrayOp {
    Get(PreOccur, PreOccur, PreType),
    Extract(PreOccur, PreOccur),
    Len(PreOccur),
    Push(PreOccur, PreOccur),
    Pop(PreOccur),
    Replace(PreOccur, PreOccur),
    Reserve(PreOccur, PreOccur),
}

#[derive(Clone, Debug)]
enum IoOp {
    Input,
    Output(PreOccur),
}

#[derive(Clone, Debug)]
enum PreExpr {
    Local(PreOccur),
    Call(Purity, rc::CustomFuncId, PreOccur),
    Branch(
        PreOccur,
        Vec<(annot::Condition<Mode, Lt>, PreExpr)>,
        PreType,
    ),
    LetMany(Vec<(PreType, StackLt, PreExpr)>, PreOccur),

    Tuple(Vec<PreOccur>),
    TupleField(PreOccur, usize),
    WrapVariant(
        IdVec<first_ord::VariantId, PreType>,
        first_ord::VariantId,
        PreOccur,
    ),
    UnwrapVariant(first_ord::VariantId, PreOccur),
    WrapBoxed(PreOccur, PreType),
    UnwrapBoxed(PreOccur, PreType),
    WrapCustom(
        first_ord::CustomTypeId,
        PreOccur, // The unwrapped argument value
        PreType,  // The wrapped return type (needed for lowering)
    ),
    UnwrapCustom(first_ord::CustomTypeId, PreOccur),

    Intrinsic(Intrinsic, PreOccur),
    ArrayOp(ArrayOp),
    IoOp(IoOp),
    Panic(PreType, PreOccur),

    ArrayLit(PreType, Vec<PreOccur>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]

struct PreFuncDef {
    pub purity: Purity,
    pub arg_type: PreType,
    pub arg_obligation: StackLt,
    pub ret_type: PreType,
    pub body: PreExpr,
    pub profile_point: Option<prof::ProfilePointId>,
}

fn get_occur_obligation_for_slot(
    occur_path: &Path,
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
    occur_path: &Path,
    ty_src: &PreType,
    ty_dst: &PreType,
) -> StackLt {
    ty_src
        .modes()
        .iter_overlay()
        .zip_eq(ty_dst.modes().iter_overlay())
        .zip_eq(ty_dst.lts().iter_overlay(customs))
        .map(|((mode_src, mode_dst), lt_dst)| {
            get_occur_obligation_for_slot(occur_path, *mode_src, *mode_dst, lt_dst)
        })
        .collect_overlay(&ty_src.modes().unapply_overlay())
}

fn instantiate_type(inst_params: &IdVec<ModeParam, Mode>, ty: &AnnotType) -> PreType {
    ty.map_modes(|solution| solution.lb.instantiate(inst_params))
}

fn instantiate_occur(
    inst_params: &IdVec<ModeParam, Mode>,
    occur: &annot::Occur<ModeSolution, Lt>,
) -> PreOccur {
    PreOccur {
        id: occur.id,
        ty: instantiate_type(inst_params, &occur.ty),
    }
}

fn instantiate_cond(
    inst_params: &IdVec<ModeParam, Mode>,
    cond: &annot::Condition<ModeSolution, Lt>,
) -> annot::Condition<Mode, Lt> {
    match cond {
        annot::Condition::Any => annot::Condition::Any,
        annot::Condition::Tuple(conds) => annot::Condition::Tuple(
            conds
                .iter()
                .map(|cond| instantiate_cond(inst_params, cond))
                .collect(),
        ),
        annot::Condition::Variant(variant_id, cond) => {
            annot::Condition::Variant(*variant_id, Box::new(instantiate_cond(inst_params, cond)))
        }
        annot::Condition::Boxed(cond, item_ty) => annot::Condition::Boxed(
            Box::new(instantiate_cond(inst_params, cond)),
            instantiate_type(inst_params, item_ty),
        ),
        annot::Condition::Custom(custom_id, cond) => {
            annot::Condition::Custom(*custom_id, Box::new(instantiate_cond(inst_params, cond)))
        }
        annot::Condition::BoolConst(lit) => annot::Condition::BoolConst(*lit),
        annot::Condition::ByteConst(lit) => annot::Condition::ByteConst(*lit),
        annot::Condition::IntConst(lit) => annot::Condition::IntConst(*lit),
        annot::Condition::FloatConst(lit) => annot::Condition::FloatConst(*lit),
    }
}

fn push_new_pre_binding(
    ctx: &mut LocalContext<flat::LocalId, (PreType, StackLt)>,
    ty: PreType,
) -> flat::LocalId {
    let ov = ty.modes().unapply_overlay();
    let init_lt = ov.iter().map(|_| Lt::Empty).collect_overlay(&ov);
    let binding_id = ctx.add_local((ty, init_lt));
    binding_id
}

fn instantiate_expr(
    customs: &annot::CustomTypes,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    path: &Path,
    ctx: &mut LocalContext<flat::LocalId, (PreType, StackLt)>,
    ret_ty: &PreType,
    expr: &AnnotExpr,
) -> PreExpr {
    let handle_occur = |ctx: &mut LocalContext<_, (_, StackLt)>, occur: &annot::Occur<_, _>| {
        let occur = instantiate_occur(inst_params, occur);
        let (ty, lt) = ctx.local_binding_mut(occur.id);

        // We must update the lifetime obligation of the binding to reflect this occurrence.
        let obligation = get_occur_obligation(customs, path, &ty, &occur.ty);
        *lt = lt.join(&obligation);
        occur
    };

    match expr {
        annot::Expr::Local(occur) => PreExpr::Local(handle_occur(ctx, occur)),

        annot::Expr::Call(purity, func_id, arg) => {
            let params = funcs[func_id]
                .constrs
                .sig
                .map_refs(|_, solution| solution.instantiate(inst_params));
            let new_func_id = insts.resolve(FuncSpec {
                old_id: *func_id,
                params: params,
            });
            PreExpr::Call(*purity, new_func_id, handle_occur(ctx, arg))
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
                        instantiate_expr(
                            customs,
                            funcs,
                            insts,
                            inst_params,
                            &path.par(i, n),
                            ctx,
                            ret_ty,
                            expr,
                        ),
                    )
                })
                .collect();
            PreExpr::Branch(new_cond, new_arms, instantiate_type(inst_params, &ty))
        }

        // We use `with_scope` to express our intent. In fact, all the bindings we add are popped
        // from the context before we return.
        annot::Expr::LetMany(bindings, ret) => ctx.with_scope(|ctx| {
            let mut new_exprs = Vec::new();
            for (i, (ty, expr)) in bindings.into_iter().enumerate() {
                let ty = instantiate_type(inst_params, &ty);
                let _ = push_new_pre_binding(ctx, ty.clone());
                let new_expr = instantiate_expr(
                    customs,
                    funcs,
                    insts,
                    inst_params,
                    &path.seq(i),
                    ctx,
                    &ty,
                    expr,
                );
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

        annot::Expr::TupleField(tup, idx) => PreExpr::TupleField(handle_occur(ctx, tup), *idx),

        annot::Expr::WrapVariant(variants, variant, content) => PreExpr::WrapVariant(
            variants.map_refs(|_, ty| instantiate_type(inst_params, ty)),
            *variant,
            handle_occur(ctx, content),
        ),

        annot::Expr::UnwrapVariant(variant, wrapped) => {
            PreExpr::UnwrapVariant(*variant, handle_occur(ctx, wrapped))
        }

        annot::Expr::WrapBoxed(content, ty) => PreExpr::WrapBoxed(
            handle_occur(ctx, content),
            instantiate_type(inst_params, &ty),
        ),

        annot::Expr::UnwrapBoxed(wrapped, ty) => PreExpr::UnwrapBoxed(
            handle_occur(ctx, wrapped),
            instantiate_type(inst_params, &ty),
        ),

        annot::Expr::WrapCustom(id, content) => {
            PreExpr::WrapCustom(*id, handle_occur(ctx, content), ret_ty.clone())
        }

        annot::Expr::UnwrapCustom(id, wrapped) => {
            PreExpr::UnwrapCustom(*id, handle_occur(ctx, wrapped))
        }

        annot::Expr::Intrinsic(intrinsic, occur) => {
            PreExpr::Intrinsic(*intrinsic, handle_occur(ctx, occur))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Get(arr, idx, ty)) => PreExpr::ArrayOp(ArrayOp::Get(
            handle_occur(ctx, arr),
            handle_occur(ctx, idx),
            instantiate_type(inst_params, &ty),
        )),
        annot::Expr::ArrayOp(annot::ArrayOp::Extract(arr, idx)) => PreExpr::ArrayOp(
            ArrayOp::Extract(handle_occur(ctx, arr), handle_occur(ctx, idx)),
        ),
        annot::Expr::ArrayOp(annot::ArrayOp::Len(arr)) => {
            PreExpr::ArrayOp(ArrayOp::Len(handle_occur(ctx, arr)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Push(arr, item)) => PreExpr::ArrayOp(ArrayOp::Push(
            handle_occur(ctx, arr),
            handle_occur(ctx, item),
        )),
        annot::Expr::ArrayOp(annot::ArrayOp::Pop(arr)) => {
            PreExpr::ArrayOp(ArrayOp::Pop(handle_occur(ctx, arr)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Replace(arr, item)) => PreExpr::ArrayOp(
            ArrayOp::Replace(handle_occur(ctx, arr), handle_occur(ctx, item)),
        ),
        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(arr, cap)) => PreExpr::ArrayOp(
            ArrayOp::Reserve(handle_occur(ctx, arr), handle_occur(ctx, cap)),
        ),

        annot::Expr::IoOp(annot::IoOp::Input) => PreExpr::IoOp(IoOp::Input),
        annot::Expr::IoOp(annot::IoOp::Output(occur)) => {
            PreExpr::IoOp(IoOp::Output(handle_occur(ctx, occur)))
        }

        annot::Expr::Panic(ret_ty, occur) => PreExpr::Panic(
            instantiate_type(inst_params, &ret_ty),
            handle_occur(ctx, occur),
        ),
        annot::Expr::ArrayLit(ty, elems) => PreExpr::ArrayLit(
            instantiate_type(inst_params, &ty),
            elems
                .into_iter()
                .map(|occur| handle_occur(ctx, occur))
                .collect(),
        ),

        annot::Expr::BoolLit(b) => PreExpr::BoolLit(*b),
        annot::Expr::ByteLit(b) => PreExpr::ByteLit(*b),
        annot::Expr::IntLit(i) => PreExpr::IntLit(*i),
        annot::Expr::FloatLit(f) => PreExpr::FloatLit(*f),
    }
}

fn instantiate_func(
    customs: &annot::CustomTypes,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    func_insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    id: first_ord::CustomFuncId,
) -> PreFuncDef {
    let func = &funcs[id];

    let mut context = LocalContext::new();
    let arg_ty = func.arg_ty.map_modes(|param| inst_params[param]);
    let arg_id = push_new_pre_binding(&mut context, arg_ty);
    debug_assert_eq!(arg_id, flat::ARG_LOCAL);

    let ret_type = func
        .ret_ty
        .map(|param| inst_params[param], |lt| Lt::var(lt.clone()));
    let body = instantiate_expr(
        customs,
        funcs,
        func_insts,
        inst_params,
        &annot::FUNC_BODY_PATH(),
        &mut context,
        &ret_type,
        &func.body,
    );

    let (_, (arg_type, arg_obligation)) = context.pop_local();
    PreFuncDef {
        purity: func.purity,
        arg_type,
        arg_obligation,
        ret_type,
        body,
        profile_point: func.profile_point,
    }
}

////////////////////////////////////////
// In the second stage of this pass, we specialize types (which is rather trivial) and insert
// retains and releases.
////////////////////////////////////////

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

#[derive(Clone, Debug)]
enum Field<T> {
    TupleField(usize),
    VariantCase(first_ord::VariantId),
    Custom(first_ord::CustomTypeId, SlotId, T),
    Slot(T),
}

/// Identifies a "payload" carrying field of a type, e.g. an array or box.
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

type LocalDrops = BTreeMap<flat::LocalId, Selector>;

/// The set of locations in an expression where variables' lifetimes end. This corresponds to the
/// set of drop points modulo where variables are moved.
///
/// Because the program is in ANF and occurences do not count toward lifetime obligations (only
/// accesses do), *local* lifetimes always end inside let many statements, except when a variable is
/// used along one branch of a match and unused along another.
///
/// In general, the empty lifetime can be interpreted as the path to the binding for drop purposes.
/// The exception is the function argument, which is the only variable not bound by a let many.
enum BodyDrops {
    Branch {
        // drops `before[i]` are executed before the body of the ith arm
        before: Vec<LocalDrops>,
        in_: Vec<Option<BodyDrops>>,
    },
    LetMany {
        // drops `after[i]` are executed after the ith binding
        after: Vec<LocalDrops>,
        in_: Vec<Option<BodyDrops>>,
    },
}

struct Drops {
    drop_immediately: Selector,
    body_drops: Option<BodyDrops>,
}

fn drop_skeleton(expr: &PreExpr) -> Option<BodyDrops> {
    match expr {
        PreExpr::Branch(_, arms, _) => {
            let before = arms.iter().map(|_| LocalDrops::new()).collect();
            let in_ = arms.iter().map(|(_, expr)| drop_skeleton(expr)).collect();
            Some(BodyDrops::Branch { before, in_ })
        }

        PreExpr::LetMany(bindings, _) => {
            let after = bindings.iter().map(|_| LocalDrops::new()).collect();
            let in_ = bindings
                .iter()
                .map(|(_, _, expr)| drop_skeleton(expr))
                .collect();
            Some(BodyDrops::LetMany { after, in_ })
        }

        _ => None,
    }
}

// TODO: using `Selector`s here (as we've currently defined them) is quite inefficient. We
// should use a data structure which can *sparsely* represent a subset of fields.
fn register_drops_for_slot(
    drops: &mut BodyDrops,
    binding: flat::LocalId,
    slot: &Selector,
    obligation: &LocalLt,
) {
    let register_to = |drops: &mut LocalDrops| {
        drops
            .entry(binding)
            .and_modify(|old_slots| *old_slots = old_slots.or(slot))
            .or_insert_with(|| slot.clone());
    };

    match obligation {
        LocalLt::Final => unreachable!(),

        LocalLt::Seq(obligation, idx) => {
            let BodyDrops::LetMany { after, in_ } = drops else {
                unreachable!()
            };

            if **obligation == LocalLt::Final {
                register_to(&mut after[*idx]);
            } else {
                let drops = in_[*idx].as_mut().unwrap();
                register_drops_for_slot(drops, binding, slot, obligation);
            }
        }

        LocalLt::Par(obligations) => {
            let BodyDrops::Branch { before, in_ } = drops else {
                unreachable!()
            };

            for (idx, obligation) in obligations.iter().enumerate() {
                if let Some(obligation) = obligation {
                    let drops = in_[idx].as_mut().unwrap();
                    register_drops_for_slot(drops, binding, slot, obligation);
                } else {
                    register_to(&mut before[idx]);
                }
            }
        }
    }
}

fn register_drops_for_binding(
    drops: &mut BodyDrops,
    binding_id: flat::LocalId,
    binding_ty: &PreType,
    binding_path: &Path,
    obligation: &StackLt,
) {
    let absent = Selector::from_const(&binding_ty.modes().unapply_overlay(), MoveStatus::Absent);
    let binding_path = Lazy::new(|| binding_path.as_local_lt());

    for path in iterate_lt_fields(obligation) {
        let mut slot = absent.clone();
        set_present(&mut slot, &path);
        match get_field_data(&path) {
            // We don't need to do anything since the binding escapes into the caller's scope.
            Lt::Join(_) => {}
            // The binding is unused, so we can drop it immediately.
            Lt::Empty => {
                register_drops_for_slot(drops, binding_id, &slot, &*binding_path);
            }
            Lt::Local(lt) => {
                register_drops_for_slot(drops, binding_id, &slot, lt);
            }
        }
    }
}

fn register_drops_for_expr(
    drops: &mut BodyDrops,
    mut num_locals: Count<flat::LocalId>,
    path: &Path,
    expr: &PreExpr,
) {
    match expr {
        PreExpr::Branch(_, arms, _) => {
            for (i, (_, expr)) in arms.iter().enumerate() {
                let path = path.par(i, arms.len());
                register_drops_for_expr(drops, num_locals, &path, expr);
            }
        }

        PreExpr::LetMany(bindings, _) => {
            for (i, (ty, obligation, sub_expr)) in bindings.iter().enumerate() {
                let path = path.seq(i);
                register_drops_for_expr(drops, num_locals, &path, sub_expr);

                // Only increment `num_locals` after recursing into `sub_expr`
                let binding_id = num_locals.inc();
                register_drops_for_binding(drops, binding_id, ty, &path, obligation);
            }
        }

        _ => {}
    }
}

fn drops_for_func(func: &PreFuncDef) -> Drops {
    let absent = Selector::from_const(&func.arg_type.modes().unapply_overlay(), MoveStatus::Absent);
    let mut drop_immediately = absent.clone();
    let mut body_drops = drop_skeleton(&func.body);

    for path in iterate_lt_fields(&func.arg_obligation) {
        let mut slot = absent.clone();
        set_present(&mut slot, &path);
        match get_field_data(&path) {
            Lt::Join(_) => {}
            Lt::Empty => {
                drop_immediately = drop_immediately.or(&slot);
            }
            Lt::Local(lt) => {
                let body_drops = body_drops.as_mut().unwrap();
                register_drops_for_slot(body_drops, flat::ARG_LOCAL, &slot, lt);
            }
        }
    }

    register_drops_for_expr(
        body_drops.as_mut().unwrap(),
        Count::from_value(1), // 1 to account for the function argument
        &annot::FUNC_BODY_PATH(),
        &func.body,
    );

    Drops {
        drop_immediately,
        body_drops,
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
                debug_assert!(customs.types[*id].ov.is_zero_sized(customs));
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
            Overlay::Array(status) | Overlay::HoleArray(status) | Overlay::Boxed(status) => {
                match status {
                    MoveStatus::Present => Self::LeafOp,
                    MoveStatus::Absent => Self::NoOp,
                }
            }
        }
    }
}

fn build_plan(
    customs: &annot::CustomTypes,
    insts: &mut TypeInstances,
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
                rc::Expr::RcOp(rc_op, root_ty.clone(), root),
            );
        }

        RcOpPlan::TupleFields(plans) => {
            let rc::Type::Tuple(field_tys) = root_ty else {
                unreachable!()
            };

            for (idx, plan) in plans {
                let field_ty = &field_tys[*idx];
                let field_local =
                    builder.add_binding(field_ty.clone(), rc::Expr::TupleField(root, *idx));
                build_plan(customs, insts, rc_op, field_local, field_ty, plan, builder);
            }
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
                let content_id = case_builder.add_binding(
                    variant_ty.clone(),
                    rc::Expr::UnwrapVariant(*variant_id, root),
                );

                build_plan(
                    customs,
                    insts,
                    rc_op,
                    content_id,
                    variant_ty,
                    plan,
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

            // For exhaustivity
            cases.push((rc::Condition::Any, rc::Expr::Tuple(vec![])));

            builder.add_binding(
                rc::Type::Tuple(vec![]),
                rc::Expr::Branch(root, cases, rc::Type::Tuple(vec![])),
            );
        }

        RcOpPlan::Custom(plan) => {
            let rc::Type::Custom(custom_id) = root_ty else {
                unreachable!()
            };

            let content_ty = insts.lookup_resolved(*custom_id).clone(); // appease the borrow checker
            let content_id =
                builder.add_binding(content_ty.clone(), rc::Expr::UnwrapCustom(*custom_id, root));
            build_plan(
                customs,
                insts,
                rc_op,
                content_id,
                &content_ty,
                plan,
                builder,
            );
        }
    }
}

fn select_slot_dups(path: &Path, src_mode: Mode, dst_mode: Mode, lt: &Lt) -> MoveStatus {
    match (src_mode, dst_mode) {
        (_, Mode::Borrowed) => MoveStatus::Absent,
        (Mode::Borrowed, Mode::Owned) => {
            panic!("borrowed to owned transitions should be prevented by the inferred constraints")
        }
        (Mode::Owned, Mode::Owned) => {
            if lt.does_not_exceed(path) {
                MoveStatus::Absent
            } else {
                MoveStatus::Present
            }
        }
    }
}

fn select_dups(
    path: &Path,
    src_ty: &PreType,
    dst_ty: &PreType,
    lt_obligation: &StackLt,
) -> Selector {
    src_ty
        .modes()
        .iter_overlay()
        .zip_eq(dst_ty.modes().iter_overlay())
        .zip_eq(lt_obligation.iter())
        .map(|((src_mode, dst_mode), lt)| select_slot_dups(path, *src_mode, *dst_mode, lt))
        .collect_overlay(lt_obligation)
}

fn select_owned(ty: &PreType) -> Selector {
    ty.modes()
        .iter_overlay()
        .map(|mode| match mode {
            Mode::Borrowed => MoveStatus::Absent,
            Mode::Owned => MoveStatus::Present,
        })
        .collect_overlay(&ty.modes().unapply_overlay())
}

#[derive(Clone, Debug)]
struct Local {
    old_ty: PreType,
    new_ty: rc::Type,
    new_id: rc::LocalId,
    obligation: StackLt,
}

// NB: for enlightenment, compare to `select_slot_dups`
fn finalize_slot_drop(path: &Path, lt: &Lt, is_candidate: MoveStatus) -> MoveStatus {
    match is_candidate {
        MoveStatus::Absent => MoveStatus::Absent,
        MoveStatus::Present => {
            if !matches!(lt, Lt::Empty) && lt.does_not_exceed(path) {
                MoveStatus::Absent
            } else {
                MoveStatus::Present
            }
        }
    }
}

fn finalize_drops(path: &Path, obligation: &StackLt, candidate_drops: &Selector) -> Selector {
    obligation
        .iter()
        .zip_eq(candidate_drops.iter())
        .map(|(lt, is_candidate)| finalize_slot_drop(path, lt, *is_candidate))
        .collect_overlay(obligation)
}

fn build_drops(
    customs: &annot::CustomTypes,
    insts: &mut TypeInstances,
    path: &Path,
    locals: &LocalDrops,
    ctx: &mut LocalContext<flat::LocalId, Local>,
    builder: &mut LetManyBuilder,
) {
    for (binding, candidate_drops) in locals {
        let local = ctx.local_binding_mut(*binding);
        let drops = finalize_drops(path, &local.obligation, candidate_drops);
        let plan = RcOpPlan::from_sel(customs, &drops);

        build_plan(
            &customs,
            insts,
            rc::RcOp::Release,
            local.new_id,
            &local.new_ty,
            &plan,
            builder,
        );
    }
}

fn lower_occur(
    customs: &annot::CustomTypes,
    insts: &mut TypeInstances,
    ctx: &mut LocalContext<flat::LocalId, Local>,
    path: &Path,
    occur: &PreOccur,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    let local = ctx.local_binding_mut(occur.id);
    let dups = select_dups(path, &local.old_ty, &occur.ty, &local.obligation);

    let plan = RcOpPlan::from_sel(customs, &dups);
    build_plan(
        customs,
        insts,
        rc::RcOp::Retain,
        local.new_id,
        &local.new_ty,
        &plan,
        builder,
    );

    local.new_id
}

fn lower_cond(
    customs: &annot::CustomTypes,
    insts: &mut TypeInstances,
    cond: &annot::Condition<Mode, Lt>,
    discrim: &rc::Type,
) -> rc::Condition {
    use annot::Condition as C;
    use rc::Type as T;
    match (cond, discrim) {
        (C::Any, _) => rc::Condition::Any,
        (C::Tuple(conds), T::Tuple(fields)) => rc::Condition::Tuple(
            conds
                .iter()
                .zip_eq(fields)
                .map(|(cond, field)| lower_cond(customs, insts, cond, field))
                .collect(),
        ),
        (C::Variant(variant_id, cond), T::Variants(variants)) => rc::Condition::Variant(
            *variant_id,
            Box::new(lower_cond(customs, insts, cond, &variants[*variant_id])),
        ),
        (C::Boxed(cond, item_ty), T::Boxed(_, content)) => rc::Condition::Boxed(
            Box::new(lower_cond(customs, insts, cond, content)),
            insts.lower_type(customs, item_ty.modes()),
        ),
        (C::Custom(_old_custom_id, cond), T::Custom(custom_id)) => {
            let content_ty = insts.lookup_resolved(*custom_id).clone(); // appease the borrow checker
            rc::Condition::Custom(
                *custom_id,
                Box::new(lower_cond(customs, insts, cond, &content_ty)),
            )
        }
        (C::BoolConst(lit), T::Bool) => rc::Condition::BoolConst(*lit),
        (C::ByteConst(lit), T::Num(NumType::Byte)) => rc::Condition::ByteConst(*lit),
        (C::IntConst(lit), T::Num(NumType::Int)) => rc::Condition::IntConst(*lit),
        (C::FloatConst(lit), T::Num(NumType::Float)) => rc::Condition::FloatConst(*lit),
        _ => unreachable!(),
    }
}

fn lower_expr(
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    customs: &annot::CustomTypes,
    insts: &mut TypeInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    ctx: &mut LocalContext<flat::LocalId, Local>,
    path: &Path,
    expr: &PreExpr,
    ret_ty: &rc::Type,
    drops: Option<&BodyDrops>,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    let new_expr = match expr {
        PreExpr::Local(local) => {
            rc::Expr::Local(lower_occur(customs, insts, ctx, path, local, builder))
        }

        PreExpr::Call(purity, func, arg) => rc::Expr::Call(
            *purity,
            *func,
            lower_occur(customs, insts, ctx, path, arg, builder),
        ),

        PreExpr::Branch(discrim, branches, ret_ty) => {
            let Some(BodyDrops::Branch { before, in_ }) = drops else {
                unreachable!()
            };

            let rc::Type::Variants(discrim_variants) =
                insts.lower_type(customs, discrim.ty.modes())
            else {
                unreachable!()
            };

            let mut new_branches: Vec<(rc::Condition, _)> = Vec::new();
            let n = branches.len();
            let ret_ty = insts.lower_type(customs, ret_ty.modes());

            for (i, ((cond, body), variant_ty)) in branches
                .iter()
                .zip_eq(discrim_variants.values())
                .enumerate()
            {
                let mut case_builder = builder.child();
                let case_path = path.par(i, n);
                let cond = lower_cond(customs, insts, cond, variant_ty);

                build_drops(
                    customs,
                    insts,
                    &case_path,
                    &before[i],
                    ctx,
                    &mut case_builder,
                );

                let final_local = lower_expr(
                    funcs,
                    customs,
                    insts,
                    inst_params,
                    ctx,
                    &case_path,
                    body,
                    &ret_ty,
                    in_[i].as_ref(),
                    &mut case_builder,
                );

                new_branches.push((cond, case_builder.to_expr(final_local)));
            }

            rc::Expr::Branch(
                lower_occur(customs, insts, ctx, path, discrim, builder),
                new_branches,
                ret_ty,
            )
        }

        PreExpr::LetMany(bindings, ret) => {
            let final_local = ctx.with_scope(|ctx| {
                let Some(BodyDrops::LetMany { after, in_ }) = drops else {
                    unreachable!()
                };

                let mut new_bindings = Vec::new();

                for (i, (ty, obligation, expr)) in bindings.iter().enumerate() {
                    let new_ty = insts.lower_type(customs, ty.modes());
                    let path = path.seq(i);

                    let local_id = lower_expr(
                        funcs,
                        customs,
                        insts,
                        inst_params,
                        ctx,
                        &path,
                        expr,
                        &new_ty,
                        in_[i].as_ref(),
                        builder,
                    );
                    let local = Local {
                        old_ty: ty.clone(),
                        new_ty: new_ty.clone(),
                        new_id: local_id,
                        obligation: obligation.clone(),
                    };

                    ctx.add_local(local);
                    new_bindings.push((new_ty, local_id));

                    build_drops(customs, insts, &path, &after[i], ctx, builder);
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
                .map(|field| lower_occur(customs, insts, ctx, path, field, builder))
                .collect(),
        ),

        PreExpr::TupleField(tup, idx) => {
            rc::Expr::TupleField(lower_occur(customs, insts, ctx, path, tup, builder), *idx)
        }

        PreExpr::WrapVariant(variant_tys, variant_id, content) => rc::Expr::WrapVariant(
            variant_tys.map_refs(|_, ty| insts.lower_type(customs, ty.modes())),
            *variant_id,
            lower_occur(customs, insts, ctx, path, content, builder),
        ),

        PreExpr::UnwrapVariant(variant_id, wrapped) => rc::Expr::UnwrapVariant(
            *variant_id,
            lower_occur(customs, insts, ctx, path, wrapped, builder),
        ),

        PreExpr::WrapBoxed(content, item_ty) => rc::Expr::WrapBoxed(
            lower_occur(customs, insts, ctx, path, content, builder),
            insts.lower_type(customs, item_ty.modes()),
        ),

        PreExpr::UnwrapBoxed(wrapped, item_ty) => rc::Expr::UnwrapBoxed(
            lower_occur(customs, insts, ctx, path, wrapped, builder),
            insts.lower_type(customs, item_ty.modes()),
        ),

        PreExpr::WrapCustom(custom_id, content, ret_ty) => {
            let ModeData::Custom(id, osub, tsub) = &ret_ty.modes() else {
                unreachable!()
            };

            debug_assert_eq!(id, custom_id);
            let spec = TypeSpecHead {
                old_id: *custom_id,
                osub: osub.clone(),
                tsub: tsub.clone(),
            };

            rc::Expr::WrapCustom(
                insts.resolve(customs, spec),
                lower_occur(customs, insts, ctx, path, content, builder),
            )
        }

        PreExpr::UnwrapCustom(custom_id, wrapped) => {
            let ModeData::Custom(id, osub, tsub) = &wrapped.ty.modes() else {
                unreachable!()
            };

            debug_assert_eq!(id, custom_id);
            let spec = TypeSpecHead {
                old_id: *custom_id,
                osub: osub.clone(),
                tsub: tsub.clone(),
            };

            rc::Expr::UnwrapCustom(
                insts.resolve(customs, spec),
                lower_occur(customs, insts, ctx, path, wrapped, builder),
            )
        }

        PreExpr::Intrinsic(intr, arg) => {
            rc::Expr::Intrinsic(*intr, lower_occur(customs, insts, ctx, path, arg, builder))
        }

        PreExpr::ArrayOp(ArrayOp::Get(arr, idx, ret_ty)) => {
            let local = ctx.local_binding_mut(arr.id);
            let plan = RcOpPlan::from_sel(customs, &select_owned(ret_ty));
            build_plan(
                &customs,
                insts,
                rc::RcOp::Retain,
                local.new_id,
                &local.new_ty,
                &plan,
                builder,
            );
            rc::Expr::ArrayOp(rc::ArrayOp::Get(
                insts.lower_type(customs, arr.ty.unwrap_item_modes()),
                lower_occur(customs, insts, ctx, path, arr, builder),
                lower_occur(customs, insts, ctx, path, idx, builder),
            ))
        }

        PreExpr::ArrayOp(ArrayOp::Extract(arr, idx)) => rc::Expr::ArrayOp(rc::ArrayOp::Extract(
            insts.lower_type(customs, arr.ty.unwrap_item_modes()),
            lower_occur(customs, insts, ctx, path, arr, builder),
            lower_occur(customs, insts, ctx, path, idx, builder),
        )),

        PreExpr::ArrayOp(ArrayOp::Len(arr)) => rc::Expr::ArrayOp(rc::ArrayOp::Len(
            insts.lower_type(customs, arr.ty.unwrap_item_modes()),
            lower_occur(customs, insts, ctx, path, arr, builder),
        )),

        PreExpr::ArrayOp(ArrayOp::Push(arr, item)) => rc::Expr::ArrayOp(rc::ArrayOp::Push(
            insts.lower_type(customs, item.ty.modes()),
            lower_occur(customs, insts, ctx, path, arr, builder),
            lower_occur(customs, insts, ctx, path, item, builder),
        )),

        PreExpr::ArrayOp(ArrayOp::Pop(arr)) => rc::Expr::ArrayOp(rc::ArrayOp::Pop(
            insts.lower_type(customs, arr.ty.unwrap_item_modes()),
            lower_occur(customs, insts, ctx, path, arr, builder),
        )),

        PreExpr::ArrayOp(ArrayOp::Replace(arr, item)) => rc::Expr::ArrayOp(rc::ArrayOp::Replace(
            insts.lower_type(customs, item.ty.modes()),
            lower_occur(customs, insts, ctx, path, arr, builder),
            lower_occur(customs, insts, ctx, path, item, builder),
        )),

        PreExpr::ArrayOp(ArrayOp::Reserve(arr, cap)) => rc::Expr::ArrayOp(rc::ArrayOp::Reserve(
            insts.lower_type(customs, arr.ty.unwrap_item_modes()),
            lower_occur(customs, insts, ctx, path, arr, builder),
            lower_occur(customs, insts, ctx, path, cap, builder),
        )),

        PreExpr::IoOp(IoOp::Input) => rc::Expr::IoOp(rc::IoOp::Input),

        PreExpr::IoOp(IoOp::Output(output)) => rc::Expr::IoOp(rc::IoOp::Output(lower_occur(
            customs, insts, ctx, path, output, builder,
        ))),

        PreExpr::Panic(ret_ty, msg) => rc::Expr::Panic(
            insts.lower_type(customs, ret_ty.modes()),
            lower_occur(customs, insts, ctx, path, msg, builder),
        ),

        PreExpr::ArrayLit(item_ty, items) => rc::Expr::ArrayLit(
            insts.lower_type(customs, item_ty.modes()),
            items
                .iter()
                .map(|item| lower_occur(customs, insts, ctx, path, item, builder))
                .collect(),
        ),

        PreExpr::BoolLit(lit) => rc::Expr::BoolLit(*lit),

        PreExpr::ByteLit(lit) => rc::Expr::ByteLit(*lit),

        PreExpr::IntLit(lit) => rc::Expr::IntLit(*lit),

        PreExpr::FloatLit(lit) => rc::Expr::FloatLit(*lit),
    };

    builder.add_binding(ret_ty.clone(), new_expr)
}

fn lower_func(
    customs: &annot::CustomTypes,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    insts: &mut TypeInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    func: &PreFuncDef,
) -> rc::FuncDef {
    let drops = drops_for_func(&func);

    let mut context = LocalContext::new();
    let _ = context.add_local(Local {
        old_ty: func.arg_type.clone(),
        new_ty: insts.lower_type(customs, &func.arg_type.modes()),
        new_id: rc::ARG_LOCAL,
        obligation: func.arg_obligation.clone(),
    });

    let mut builder = LetManyBuilder::new(1);

    {
        let plan = RcOpPlan::from_sel(customs, &drops.drop_immediately);
        build_plan(
            customs,
            insts,
            rc::RcOp::Release,
            rc::ARG_LOCAL,
            &context.local_binding(flat::ARG_LOCAL).new_ty,
            &plan,
            &mut builder,
        );
    }

    let ret_ty = insts.lower_type(customs, &func.ret_type.modes());
    let ret_local = lower_expr(
        funcs,
        customs,
        insts,
        inst_params,
        &mut context,
        &annot::FUNC_BODY_PATH(),
        &func.body,
        &ret_ty,
        drops.body_drops.as_ref(),
        &mut builder,
    );

    rc::FuncDef {
        purity: func.purity,
        arg_type: insts.lower_type(customs, &func.arg_type.modes()),
        ret_type: insts.lower_type(customs, &func.ret_type.modes()),
        body: builder.to_expr(ret_local),
        profile_point: func.profile_point,
    }
}

/// We want to deduplicate specializations w.r.t. their retains and releases. This happens in two
/// stages. First, we deduplicate w.r.t. modes and label specializations using `ModeSpecFuncId`.
#[id_type]
struct ModeSpecFuncId(usize);

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

    let mut func_insts = FuncInstances::new();
    let mut type_insts = TypeInstances::new();

    let main_params = program.funcs[program.main]
        .constrs
        .sig
        .map_refs(|_, solution| solution.lb_const);
    let main = func_insts.resolve(FuncSpec {
        old_id: program.main,
        params: main_params,
    });

    let mut funcs = IdVec::new();

    while let Some((new_id, spec)) = func_insts.pop_pending() {
        let instantaited = instantiate_func(
            &program.custom_types,
            &program.funcs,
            &mut func_insts,
            &spec.params,
            spec.old_id,
        );

        let lowered = lower_func(
            &program.custom_types,
            &program.funcs,
            &mut type_insts,
            &spec.params,
            &instantaited,
        );

        let pushed_id = funcs.push(lowered);
        debug_assert_eq!(new_id, pushed_id);
        progress.update(1);
    }

    progress.finish();

    let custom_types = rc::CustomTypes {
        types: type_insts.into_customs(&program.custom_types),
    };

    rc::Program {
        mod_symbols: program.mod_symbols,
        custom_types,
        funcs,
        profile_points: program.profile_points,
        main,
    }
}
