use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast2::CollectModeData;
use crate::data::mode_annot_ast2::{
    self as annot, CollectOverlay, Lt, LtData, Mode, ModeData, ModeParam, ModeSolution, Path,
};
use crate::data::obligation_annot_ast::{
    self as ob, ArrayOp, Condition, CustomFuncId, Expr, FuncDef, IoOp, Occur, StackLt, Type,
};
use crate::util::instance_queue::InstanceQueue;
use crate::util::iter::IterExt;
use crate::util::local_context;
use crate::util::progress_logger::ProgressLogger;
use crate::util::progress_logger::ProgressSession;
use id_collections::{IdMap, IdVec};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FuncSpec {
    old_id: first_ord::CustomFuncId,
    subst: IdVec<ModeParam, Mode>,
}

type FuncInstances = InstanceQueue<FuncSpec, CustomFuncId>;

fn get_slot_obligation(occur_path: &Path, src_mode: Mode, dst_mode: Mode, dst_lt: &Lt) -> Lt {
    match (src_mode, dst_mode) {
        (Mode::Owned, Mode::Borrowed) => dst_lt.clone(),
        _ => occur_path.as_lt(),
    }
}

fn get_occur_obligation(
    customs: &annot::CustomTypes,
    occur_path: &Path,
    src_modes: &ModeData<Mode>,
    dst_modes: &ModeData<Mode>,
    dst_lts: &LtData<Lt>,
) -> StackLt {
    src_modes
        .iter_stack(customs.view_modes())
        .zip_eq(dst_modes.iter_stack(customs.view_modes()))
        .zip_eq(dst_lts.iter_stack(&customs.types))
        .map(|((src_mode, dst_mode), dst_lt)| {
            get_slot_obligation(occur_path, *src_mode, *dst_mode, dst_lt)
        })
        .collect_overlay(&src_modes.unapply_overlay())
}

fn instantiate_type(
    inst_params: &IdVec<ModeParam, Mode>,
    ty: &annot::Type<ModeSolution, Lt>,
) -> Type {
    ty.modes()
        .iter()
        .map(|solution| solution.lb.instantiate(inst_params))
        .collect_mode_data(ty.modes())
}

fn instantiate_occur(
    inst_params: &IdVec<ModeParam, Mode>,
    occur: &annot::Occur<ModeSolution, Lt>,
) -> Occur {
    Occur {
        id: occur.id,
        ty: instantiate_type(inst_params, &occur.ty),
    }
}

fn instantiate_cond(
    inst_params: &IdVec<ModeParam, Mode>,
    cond: &annot::Condition<ModeSolution, Lt>,
) -> Condition {
    match cond {
        annot::Condition::Any => Condition::Any,
        annot::Condition::Tuple(conds) => Condition::Tuple(
            conds
                .iter()
                .map(|cond| instantiate_cond(inst_params, cond))
                .collect(),
        ),
        annot::Condition::Variant(variant_id, cond) => {
            Condition::Variant(*variant_id, Box::new(instantiate_cond(inst_params, cond)))
        }
        annot::Condition::Boxed(cond, item_ty) => Condition::Boxed(
            Box::new(instantiate_cond(inst_params, cond)),
            instantiate_type(inst_params, item_ty),
        ),
        annot::Condition::Custom(custom_id, cond) => {
            Condition::Custom(*custom_id, Box::new(instantiate_cond(inst_params, cond)))
        }
        annot::Condition::BoolConst(lit) => Condition::BoolConst(*lit),
        annot::Condition::ByteConst(lit) => Condition::ByteConst(*lit),
        annot::Condition::IntConst(lit) => Condition::IntConst(*lit),
        annot::Condition::FloatConst(lit) => Condition::FloatConst(*lit),
    }
}

type LocalContext = local_context::LocalContext<flat::LocalId, (ModeData<Mode>, StackLt)>;

fn add_unused_local(ctx: &mut LocalContext, ty: ModeData<Mode>) -> flat::LocalId {
    let ov = ty.unapply_overlay();
    let init_lt = ov.iter().map(|_| Lt::Empty).collect_overlay(&ov);
    let binding_id = ctx.add_local((ty, init_lt));
    binding_id
}

/// We use `escape_lts` to track the lifetime parameters that flow from the function's return type.
/// The way we currently consume lifetime obligations, all that matters is that the obligation is
/// some escaping lifetime, not the particular lifetime parameter. We could encode this at the type
/// level by having an obligation type distinct from `Lt`, but that approach has its own
/// inconveniences.
fn annot_expr(
    customs: &annot::CustomTypes,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    path: &Path,
    ctx: &mut LocalContext,
    expr: &annot::Expr<ModeSolution, Lt>,
    ret_ty: &ModeData<Mode>,
) -> Expr {
    let handle_occur =
        |ctx: &mut LocalContext, path: &Path, occur: &annot::Occur<ModeSolution, _>| {
            let occur_lts = occur.ty.lts();
            let occur = instantiate_occur(inst_params, occur);
            let (src_ty, src_lt) = ctx.local_binding_mut(occur.id);

            // We must update the lifetime obligation of the binding to reflect this occurrence.
            let obligation = get_occur_obligation(customs, path, src_ty, &occur.ty, occur_lts);
            *src_lt = src_lt.join(&obligation);
            occur
        };

    match expr {
        annot::Expr::Local(occur) => Expr::Local(handle_occur(ctx, path, occur)),

        annot::Expr::Call(purity, func_id, arg) => {
            let func = &funcs[*func_id];
            let arg = handle_occur(ctx, path, arg);

            let mut call_params = IdMap::new();
            for (param, value) in func.arg_ty.modes().iter().zip_eq(arg.ty.iter()) {
                call_params.insert(*param, *value);
            }
            for (param, value) in func.ret_ty.modes().iter().zip_eq(ret_ty.iter()) {
                call_params.insert(*param, *value);
            }

            let call_params = call_params.to_id_vec(func.constrs.sig.count());
            let call_subst = func
                .constrs
                .sig
                .map_refs(|_, solution| solution.instantiate(&call_params));

            let new_func_id = insts.resolve(FuncSpec {
                old_id: *func_id,
                subst: call_subst,
            });

            Expr::Call(*purity, new_func_id, arg)
        }

        annot::Expr::Branch(cond, arms, ty) => {
            let num_arms = arms.len();
            let new_arms = arms
                .into_iter()
                .enumerate()
                .map(|(i, (cond, expr))| {
                    (
                        instantiate_cond(inst_params, &cond),
                        annot_expr(
                            customs,
                            funcs,
                            insts,
                            inst_params,
                            &path.alt(i, num_arms),
                            ctx,
                            expr,
                            ret_ty,
                        ),
                    )
                })
                .collect();

            let new_cond = handle_occur(ctx, path, cond);
            Expr::Branch(new_cond, new_arms, instantiate_type(inst_params, &ty))
        }

        // We use `with_scope` to express our intent. In fact, all the bindings we add are popped
        // from the context before we return.
        annot::Expr::LetMany(bindings, ret) => ctx.with_scope(|ctx| {
            let mut new_exprs = Vec::new();
            for (i, (ty, expr)) in bindings.into_iter().enumerate() {
                let ret_ty = instantiate_type(inst_params, &ty);
                let new_expr = annot_expr(
                    customs,
                    funcs,
                    insts,
                    inst_params,
                    &path.seq(i),
                    ctx,
                    expr,
                    &ret_ty,
                );
                let _ = add_unused_local(ctx, ret_ty);
                new_exprs.push(new_expr);
            }

            let ret_occur = handle_occur(ctx, &path.seq(bindings.len()), ret);

            let mut new_bindings_rev = Vec::new();
            for expr in new_exprs.into_iter().rev() {
                let (_, (ty, obligation)) = ctx.pop_local();
                new_bindings_rev.push((ty, obligation, expr));
            }

            let new_bindings = {
                new_bindings_rev.reverse();
                new_bindings_rev
            };

            Expr::LetMany(new_bindings, ret_occur)
        }),

        annot::Expr::Tuple(fields) => {
            let mut fields_rev: Vec<_> = fields
                .into_iter()
                .enumerate()
                .rev()
                .map(|(i, occur)| handle_occur(ctx, &path.seq(i), occur))
                .collect();

            let fields = {
                fields_rev.reverse();
                fields_rev
            };

            Expr::Tuple(fields)
        }

        annot::Expr::TupleField(tup, idx) => Expr::TupleField(handle_occur(ctx, path, tup), *idx),

        annot::Expr::WrapVariant(variants, variant, content) => Expr::WrapVariant(
            variants.map_refs(|_, ty| instantiate_type(inst_params, ty)),
            *variant,
            handle_occur(ctx, path, content),
        ),

        annot::Expr::UnwrapVariant(variant, wrapped) => {
            Expr::UnwrapVariant(*variant, handle_occur(ctx, path, wrapped))
        }

        annot::Expr::WrapBoxed(content, ty) => Expr::WrapBoxed(
            handle_occur(ctx, path, content),
            instantiate_type(inst_params, &ty),
        ),

        annot::Expr::UnwrapBoxed(wrapped, ty) => Expr::UnwrapBoxed(
            handle_occur(ctx, path, wrapped),
            instantiate_type(inst_params, &ty),
        ),

        annot::Expr::WrapCustom(id, content) => {
            Expr::WrapCustom(*id, handle_occur(ctx, path, content))
        }

        annot::Expr::UnwrapCustom(id, wrapped) => {
            Expr::UnwrapCustom(*id, handle_occur(ctx, path, wrapped))
        }

        annot::Expr::Intrinsic(intrinsic, occur) => {
            Expr::Intrinsic(*intrinsic, handle_occur(ctx, path, occur))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Get(arr, idx, ty)) => {
            let idx = handle_occur(ctx, path, idx);
            let arr = handle_occur(ctx, path, arr);
            Expr::ArrayOp(ArrayOp::Get(arr, idx, instantiate_type(inst_params, &ty)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Extract(arr, idx)) => {
            let idx = handle_occur(ctx, path, idx);
            let arr = handle_occur(ctx, path, arr);
            Expr::ArrayOp(ArrayOp::Extract(arr, idx))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Len(arr)) => {
            Expr::ArrayOp(ArrayOp::Len(handle_occur(ctx, path, arr)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Push(arr, item)) => {
            let item = handle_occur(ctx, path, item);
            let arr = handle_occur(ctx, path, arr);
            Expr::ArrayOp(ArrayOp::Push(arr, item))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Pop(arr)) => {
            Expr::ArrayOp(ArrayOp::Pop(handle_occur(ctx, path, arr)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Replace(arr, item)) => {
            let item = handle_occur(ctx, path, item);
            let arr = handle_occur(ctx, path, arr);
            Expr::ArrayOp(ArrayOp::Replace(arr, item))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(arr, cap)) => {
            let cap = handle_occur(ctx, path, cap);
            let arr = handle_occur(ctx, path, arr);
            Expr::ArrayOp(ArrayOp::Reserve(arr, cap))
        }
        annot::Expr::IoOp(annot::IoOp::Input) => Expr::IoOp(IoOp::Input),
        annot::Expr::IoOp(annot::IoOp::Output(occur)) => {
            Expr::IoOp(IoOp::Output(handle_occur(ctx, path, occur)))
        }

        annot::Expr::Panic(ret_ty, occur) => Expr::Panic(
            instantiate_type(inst_params, &ret_ty),
            handle_occur(ctx, path, occur),
        ),
        annot::Expr::ArrayLit(ty, elems) => {
            let mut elems_rev: Vec<_> = elems
                .into_iter()
                .enumerate()
                .rev()
                .map(|(i, occur)| handle_occur(ctx, &path.seq(i), occur))
                .collect();

            let elems = {
                elems_rev.reverse();
                elems_rev
            };

            Expr::ArrayLit(instantiate_type(inst_params, &ty), elems)
        }

        annot::Expr::BoolLit(lit) => Expr::BoolLit(*lit),
        annot::Expr::ByteLit(lit) => Expr::ByteLit(*lit),
        annot::Expr::IntLit(lit) => Expr::IntLit(*lit),
        annot::Expr::FloatLit(lit) => Expr::FloatLit(*lit),
    }
}

fn annot_func(
    customs: &annot::CustomTypes,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    func_insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    id: first_ord::CustomFuncId,
) -> FuncDef {
    let func = &funcs[id];

    let mut ctx = LocalContext::new();
    let arg_ty = func.arg_ty.map_modes(|param| inst_params[param]);
    let arg_id = add_unused_local(&mut ctx, arg_ty.modes().clone());
    debug_assert_eq!(arg_id, flat::ARG_LOCAL);

    let ret_ty = func.ret_ty.map_modes(|param| inst_params[param]);

    let body = annot_expr(
        customs,
        funcs,
        func_insts,
        inst_params,
        &annot::FUNC_BODY_PATH(),
        &mut ctx,
        &func.body,
        ret_ty.modes(),
    );

    let (_, (_, arg_obligation)) = ctx.pop_local();
    FuncDef {
        purity: func.purity,
        arg_ty: arg_ty.into_modes(),
        ret_ty: ret_ty.into_modes(),
        arg_obligation,
        body,
        profile_point: func.profile_point,
    }
}

pub fn annot_obligations(program: annot::Program, progress: impl ProgressLogger) -> ob::Program {
    let mut progress = progress.start_session(Some(program.funcs.len()));
    let mut func_insts = FuncInstances::new();

    let main_params = program.funcs[program.main]
        .constrs
        .sig
        .map_refs(|_, solution| solution.lb_const);
    let main = func_insts.resolve(FuncSpec {
        old_id: program.main,
        subst: main_params,
    });

    let mut funcs = IdVec::new();
    let mut func_symbols = IdVec::new();
    while let Some((new_id, spec)) = func_insts.pop_pending() {
        let annot = annot_func(
            &program.custom_types,
            &program.funcs,
            &mut func_insts,
            &spec.subst,
            spec.old_id,
        );

        let pushed_id1 = funcs.push(annot);
        let pushed_id2 = func_symbols.push(program.func_symbols[spec.old_id].clone());
        debug_assert_eq!(pushed_id1, new_id);
        debug_assert_eq!(pushed_id2, new_id);
        progress.update(1);
    }

    progress.finish();

    let custom_types = ob::CustomTypes {
        types: IdVec::from_vec(
            program
                .custom_types
                .types
                .into_values()
                .map(|typedef| ob::TypeDef {
                    ty: typedef.ty.into_modes(),
                    ov: typedef.ov,
                    slot_count: typedef.slot_count,
                    ov_slots: typedef.ov_slots,
                })
                .collect(),
        ),
    };

    ob::Program {
        mod_symbols: program.mod_symbols,
        custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        profile_points: program.profile_points,
        func_symbols,
        main,
    }
}
