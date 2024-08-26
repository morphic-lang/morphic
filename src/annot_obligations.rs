use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast2::{
    self as annot, Interner, Lt, Mode, ModeParam, ModeSolution, Path, Res, ResModes, SlotId,
};
use crate::data::obligation_annot_ast::{
    self as ob, ArrayOp, CustomFuncId, Expr, FuncDef, IoOp, Occur, StackLt, Type,
};
use crate::pretty_print::utils::FuncRenderer;
use crate::util::instance_queue::InstanceQueue;
use crate::util::iter::IterExt;
use crate::util::local_context;
use crate::util::progress_logger::ProgressLogger;
use crate::util::progress_logger::ProgressSession;
use id_collections::IdVec;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FuncSpec {
    old_id: first_ord::CustomFuncId,
    subst: IdVec<ModeParam, Mode>,
}

type FuncInstances = InstanceQueue<FuncSpec, CustomFuncId>;

fn get_slot_obligation(
    interner: &Interner,
    occur_path: &Path,
    src_mode: Mode,
    dst_mode: Mode,
    dst_lt: &Lt,
) -> Lt {
    match (src_mode, dst_mode) {
        (Mode::Owned, Mode::Borrowed) => dst_lt.clone(),
        _ => occur_path.as_lt(interner),
    }
}

/// We need the instantiated mode solutions and lifetimes of the destination type. We end up getting
/// this data in a bit of an awkward format, where the (uninstantiated) mode solutions are stuck to
/// the lifetimes in `dst_lts`.
fn get_occur_obligation(
    interner: &Interner,
    customs: &annot::CustomTypes,
    occur_path: &Path,
    src: &Type,
    dst: &Type,
    dst_lts: &IdVec<SlotId, Res<ModeSolution, Lt>>,
) -> StackLt {
    debug_assert!(src.shape == dst.shape);
    let slots = src.shape.top_level_slots(customs.view_shapes());
    let data = slots.into_iter().map(|slot| {
        let obligation = get_slot_obligation(
            interner,
            occur_path,
            *src.res[slot].unwrap_stack(),
            *dst.res[slot].unwrap_stack(),
            &dst_lts[slot].lt,
        );
        (slot, obligation)
    });
    StackLt {
        shape: src.shape.clone(),
        data: data.collect(),
    }
}

fn instantiate_type_with<M, L>(ty: &annot::Type<M, L>, f: impl Fn(&M) -> Mode) -> Type {
    Type {
        shape: ty.shape.clone(),
        res: ty.res.map_refs(|_, res| res.modes.map(&f)),
    }
}

fn instantiate_type(
    inst_params: &IdVec<ModeParam, Mode>,
    ty: &annot::Type<ModeSolution, Lt>,
) -> Type {
    instantiate_type_with(ty, |solution| solution.lb.instantiate(inst_params))
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

type LocalContext = local_context::LocalContext<flat::LocalId, (Type, StackLt)>;

fn add_unused_local(
    customs: &annot::CustomTypes,
    ctx: &mut LocalContext,
    ty: &Type,
) -> flat::LocalId {
    let lt = StackLt {
        shape: ty.shape.clone(),
        data: ty
            .shape
            .top_level_slots(customs.view_shapes())
            .into_iter()
            .map(|slot| (slot, Lt::Empty))
            .collect(),
    };
    ctx.add_local((ty.clone(), lt))
}

fn annot_expr(
    interner: &Interner,
    customs: &annot::CustomTypes,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    func_renderer: &FuncRenderer<first_ord::CustomFuncId>,
    insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    path: &Path,
    ctx: &mut LocalContext,
    expr: &annot::Expr<ModeSolution, Lt>,
    ret_ty: &Type,
) -> Expr {
    let handle_occur =
        |ctx: &mut LocalContext, path: &Path, old_occur: &annot::Occur<ModeSolution, _>| {
            let occur = instantiate_occur(inst_params, old_occur);
            let (src_ty, src_lt) = ctx.local_binding_mut(occur.id);

            let obligation = get_occur_obligation(
                interner,
                customs,
                path,
                src_ty,
                &occur.ty,
                &old_occur.ty.res,
            );

            // We must update the lifetime obligation of the binding to reflect this occurrence.
            *src_lt = src_lt.join(interner, &obligation);

            occur
        };

    match expr {
        annot::Expr::Local(occur) => Expr::Local(handle_occur(ctx, path, occur)),

        annot::Expr::Call(purity, func_id, arg) => {
            let func = &funcs[*func_id];
            let arg = handle_occur(ctx, path, arg);

            // Mode inference solves for all functions in an SCC jointly and annotates each function
            // with the complete set of signature vairables for the SCC. Therefore, in general,
            // `arg.ty` and `ret_ty` constrain only a subset of the parameters. It suffices to let
            // the rest of the parameters be `Mode::Borrow`, which will ultimately result in them
            // being assigned their minimal solutions according to the signature constraints.
            let mut call_params =
                IdVec::from_count_with(func.constrs.sig.count(), |_| Mode::Borrowed);

            for (param, value) in func.arg_ty.iter_modes().zip_eq(arg.ty.res.values()) {
                match (param, value) {
                    (ResModes::Stack(param), ResModes::Stack(value)) => {
                        call_params[*param] = *value;
                    }
                    (ResModes::Heap(param), ResModes::Heap(value)) => {
                        call_params[param.access] = value.access;
                        call_params[param.storage] = value.storage;
                    }
                    _ => unreachable!(),
                }
            }
            for (param, value) in func.ret_ty.iter_modes().zip_eq(ret_ty.res.values()) {
                match (param, value) {
                    (ResModes::Stack(param), ResModes::Stack(value)) => {
                        call_params[*param] = *value;
                    }
                    (ResModes::Heap(param), ResModes::Heap(value)) => {
                        call_params[param.access] = value.access;
                        call_params[param.storage] = value.storage;
                    }
                    _ => unreachable!(),
                }
            }

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
                        cond.clone(),
                        annot_expr(
                            interner,
                            customs,
                            funcs,
                            func_renderer,
                            insts,
                            inst_params,
                            &path.seq(1).alt(i, num_arms),
                            ctx,
                            expr,
                            ret_ty,
                        ),
                    )
                })
                .collect();

            let new_cond = handle_occur(ctx, &path.seq(0), cond);
            Expr::Branch(new_cond, new_arms, instantiate_type(inst_params, &ty))
        }

        // We use `with_scope` to express our intent. In fact, all the bindings we add are popped
        // from the context before we return.
        annot::Expr::LetMany(bindings, ret) => ctx.with_scope(|ctx| {
            let mut new_exprs = Vec::new();
            for (i, (ty, expr)) in bindings.into_iter().enumerate() {
                let ret_ty = instantiate_type(inst_params, &ty);
                let new_expr = annot_expr(
                    interner,
                    customs,
                    funcs,
                    func_renderer,
                    insts,
                    inst_params,
                    &path.seq(i),
                    ctx,
                    expr,
                    &ret_ty,
                );
                let _ = add_unused_local(customs, ctx, &ret_ty);
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
            let fields = fields
                .into_iter()
                .enumerate()
                .map(|(i, occur)| handle_occur(ctx, &path.seq(i), occur))
                .collect();
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
            let elems = elems
                .into_iter()
                .enumerate()
                .map(|(i, occur)| handle_occur(ctx, &path.seq(i), occur))
                .collect();

            Expr::ArrayLit(instantiate_type(inst_params, &ty), elems)
        }

        annot::Expr::BoolLit(lit) => Expr::BoolLit(*lit),
        annot::Expr::ByteLit(lit) => Expr::ByteLit(*lit),
        annot::Expr::IntLit(lit) => Expr::IntLit(*lit),
        annot::Expr::FloatLit(lit) => Expr::FloatLit(*lit),
    }
}

fn annot_func(
    interner: &Interner,
    customs: &annot::CustomTypes,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    func_renderer: &FuncRenderer<first_ord::CustomFuncId>,
    func_insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    id: first_ord::CustomFuncId,
) -> FuncDef {
    let func = &funcs[id];

    let mut ctx = LocalContext::new();
    let arg_ty = instantiate_type_with(&func.arg_ty, |param| inst_params[*param]);
    let arg_id = add_unused_local(customs, &mut ctx, &arg_ty);
    debug_assert_eq!(arg_id, flat::ARG_LOCAL);

    let ret_ty = instantiate_type_with(&func.ret_ty, |param| inst_params[*param]);

    let body = annot_expr(
        interner,
        customs,
        funcs,
        func_renderer,
        func_insts,
        inst_params,
        &annot::FUNC_BODY_PATH(),
        &mut ctx,
        &func.body,
        &ret_ty,
    );

    let (_, (_, arg_obligation)) = ctx.pop_local();
    FuncDef {
        purity: func.purity,
        arg_ty,
        ret_ty,
        arg_obligation,
        body,
        profile_point: func.profile_point,
    }
}

pub fn annot_obligations(
    interner: &Interner,
    program: annot::Program,
    progress: impl ProgressLogger,
) -> ob::Program {
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

    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);
    while let Some((new_id, spec)) = func_insts.pop_pending() {
        let annot = annot_func(
            interner,
            &program.custom_types,
            &program.funcs,
            &func_renderer,
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
                .map(|typedef| ob::CustomTypeDef {
                    content: typedef.content.shape,
                    scc: typedef.scc,
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
