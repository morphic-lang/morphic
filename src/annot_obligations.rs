use crate::data::borrow_model as model;
use crate::data::first_order_ast::{self as first_ord};
use crate::data::flat_ast as flat;
use crate::data::guarded_ast as guard;
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast::{
    self as annot, iter_shapes, Lt, LtParam, Mode, ModeParam, ModeSolution, Path, Res, ResModes,
    ShapeInner, SlotId, TypeFo,
};
use crate::data::obligation_annot_ast::{
    self as ob, ArrayOp, CustomFuncId, CustomTypeId, Expr, FuncDef, IoOp, Occur, RetType, Shape,
    Type,
};
use crate::pretty_print::utils::FuncRenderer;
use crate::util::instance_queue::InstanceQueue;
use crate::util::iter::IterExt;
use crate::util::local_context;
use crate::util::progress_logger::ProgressLogger;
use crate::util::progress_logger::ProgressSession;
use id_collections::{Count, Id, IdMap, IdVec};
use id_graph_sccs::{find_components, Scc, SccKind, Sccs};
use std::collections::{BTreeMap, BTreeSet};

type Interner = annot::Interner<CustomTypeId>;

// --------------------
// Step 1: Mode solving
// --------------------
// Solve the mode constraints for concrete modes and perform monomorphization with respect to those
// mode choices.

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FuncSpec {
    old_id: first_ord::CustomFuncId,
    subst: IdVec<ModeParam, Mode>,
}

type FuncInstances = InstanceQueue<FuncSpec, CustomFuncId>;

fn solve_type(inst_params: &IdVec<ModeParam, Mode>, ty: &TypeFo<ModeSolution, Lt>) -> Type {
    let res = ty.res().map_refs(|_, res| {
        let modes = res.modes.map(|mode| mode.lb.instantiate(inst_params));
        let lt = res.lt.clone();
        Res { modes, lt }
    });
    Type::new(ty.shape().clone(), res)
}

fn solve_occur(
    inst_params: &IdVec<ModeParam, Mode>,
    occur: &annot::Occur<ModeSolution, Lt>,
) -> Occur {
    Occur {
        id: occur.id,
        ty: solve_type(inst_params, &occur.ty),
    }
}

fn solve_expr(
    interner: &Interner,
    customs: &annot::CustomTypes<first_ord::CustomTypeId, flat::CustomTypeSccId>,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    func_renderer: &FuncRenderer<first_ord::CustomFuncId>,
    insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    path: &Path,
    ctx: &mut LocalContext,
    expr: &annot::Expr<ModeSolution, Lt>,
    fut_ty: &Type,
) -> Expr {
    match expr {
        annot::Expr::Local(occur) => Expr::Local(solve_occur(inst_params, occur)),

        annot::Expr::Call(purity, func_id, arg) => {
            let func = &funcs[*func_id];
            let arg = solve_occur(inst_params, arg);

            // Mode inference solves for all functions in an SCC jointly and annotates each function
            // with the complete set of signature vairables for the SCC. Therefore, in general,
            // `arg.ty` and `ret_ty` constrain only a subset of the parameters. It suffices to let
            // the rest of the parameters be `Mode::Borrow`, which will ultimately result in them
            // being assigned their minimal solutions according to the signature constraints.
            let mut call_params =
                IdVec::from_count_with(func.constrs.sig.count(), |_| Mode::Borrowed);

            for (param, value) in func.arg_ty.iter_modes().zip_eq(arg.ty.iter_modes()) {
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
            for (param, value) in func.ret_ty.iter_modes().zip_eq(fut_ty.res().values()) {
                match (param, &value.modes) {
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

        // We use `with_scope` to express our intent. In fact, all the bindings we add are popped
        // from the context before we return.
        annot::Expr::LetMany(bindings, ret) => ctx.with_scope(|ctx| {
            let locals_offset = ctx.len();

            for (binding_ty, _, _) in bindings {
                let _ = ctx.add_local(LocalInfo {
                    ty: solve_type(inst_params, binding_ty),
                    metadata: Metadata::default(),
                });
            }

            let mut new_bindings_rev = Vec::new();
            for (i, (_, expr, metadata)) in bindings.into_iter().enumerate().rev() {
                let local = guard::LocalId(locals_offset + i);

                let ret_ty = ctx.local_binding(local).ty.clone();

                // Only retain the locals *strictly* before this binding.
                ctx.truncate(Count::from_value(local.0));

                let new_expr = solve_expr(
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

                new_bindings_rev.push((ret_ty, new_expr, metadata.clone()));
            }

            let ret_occur = solve_occur(inst_params, ret);

            let new_bindings = {
                new_bindings_rev.reverse();
                new_bindings_rev
            };

            Expr::LetMany(new_bindings, ret_occur)
        }),

        annot::Expr::If(discrim, then_case, else_case) => {
            let else_case = solve_expr(
                interner,
                customs,
                funcs,
                func_renderer,
                insts,
                inst_params,
                &path.seq(1).alt(1, 2),
                ctx,
                else_case,
                fut_ty,
            );
            let then_case = solve_expr(
                interner,
                customs,
                funcs,
                func_renderer,
                insts,
                inst_params,
                &path.seq(1).alt(0, 2),
                ctx,
                then_case,
                fut_ty,
            );
            let discrim = solve_occur(inst_params, discrim);
            Expr::If(discrim, Box::new(then_case), Box::new(else_case))
        }

        annot::Expr::CheckVariant(variant_id, variant) => {
            Expr::CheckVariant(*variant_id, solve_occur(inst_params, variant))
        }

        annot::Expr::Unreachable(ty) => Expr::Unreachable(solve_type(inst_params, ty)),

        annot::Expr::Tuple(fields) => {
            let mut fields_rev = fields
                .into_iter()
                .rev()
                .map(|occur| solve_occur(inst_params, occur))
                .collect::<Vec<_>>();
            let fields = {
                fields_rev.reverse();
                fields_rev
            };
            Expr::Tuple(fields)
        }

        annot::Expr::TupleField(tup, idx) => Expr::TupleField(solve_occur(inst_params, tup), *idx),

        annot::Expr::WrapVariant(variants, variant, content) => Expr::WrapVariant(
            variants.map_refs(|_, ty| solve_type(inst_params, ty)),
            *variant,
            solve_occur(inst_params, content),
        ),

        annot::Expr::UnwrapVariant(variant, wrapped) => {
            Expr::UnwrapVariant(*variant, solve_occur(inst_params, wrapped))
        }

        annot::Expr::WrapBoxed(content, output_ty) => Expr::WrapBoxed(
            solve_occur(inst_params, content),
            solve_type(inst_params, output_ty),
        ),

        annot::Expr::UnwrapBoxed(wrapped, output_ty) => Expr::UnwrapBoxed(
            solve_occur(inst_params, wrapped),
            solve_type(inst_params, output_ty),
        ),

        annot::Expr::WrapCustom(id, recipe, content) => {
            Expr::WrapCustom(*id, recipe.clone(), solve_occur(inst_params, content))
        }

        annot::Expr::UnwrapCustom(id, recipe, wrapped) => {
            Expr::UnwrapCustom(*id, recipe.clone(), solve_occur(inst_params, wrapped))
        }

        annot::Expr::Intrinsic(intr, arg) => {
            let ty = solve_type(&IdVec::new(), &arg.ty);
            Expr::Intrinsic(*intr, Occur { id: arg.id, ty })
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Get(arr, idx, ty)) => {
            let arr = solve_occur(inst_params, arr);
            let idx = solve_occur(inst_params, idx);
            let ty = solve_type(inst_params, ty);
            Expr::ArrayOp(ArrayOp::Get(arr, idx, ty))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Extract(arr, idx)) => {
            let arr = solve_occur(inst_params, arr);
            let idx = solve_occur(inst_params, idx);
            Expr::ArrayOp(ArrayOp::Extract(arr, idx))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Len(arr)) => {
            let arr = solve_occur(inst_params, arr);
            Expr::ArrayOp(ArrayOp::Len(arr))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Push(arr, item)) => {
            let arr = solve_occur(inst_params, arr);
            let item = solve_occur(inst_params, item);
            Expr::ArrayOp(ArrayOp::Push(arr, item))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Pop(arr)) => {
            let arr = solve_occur(inst_params, arr);
            Expr::ArrayOp(ArrayOp::Pop(arr))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Replace(hole, item)) => {
            let hole = solve_occur(inst_params, hole);
            let item = solve_occur(inst_params, item);
            Expr::ArrayOp(ArrayOp::Replace(hole, item))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(arr, cap)) => {
            let arr = solve_occur(inst_params, arr);
            let cap = solve_occur(inst_params, cap);
            Expr::ArrayOp(ArrayOp::Reserve(arr, cap))
        }

        annot::Expr::IoOp(annot::IoOp::Input) => Expr::IoOp(IoOp::Input),

        annot::Expr::IoOp(annot::IoOp::Output(arr)) => {
            let arr = solve_occur(inst_params, arr);
            Expr::IoOp(IoOp::Output(arr))
        }

        annot::Expr::Panic(ret_ty, msg) => {
            let ret_ty = solve_type(inst_params, ret_ty);
            let msg = solve_occur(inst_params, msg);
            Expr::Panic(ret_ty, msg)
        }

        annot::Expr::ArrayLit(item_ty, items) => {
            let item_ty = solve_type(inst_params, item_ty);
            let items = items
                .iter()
                .map(|item| solve_occur(inst_params, item))
                .collect();
            Expr::ArrayLit(item_ty, items)
        }

        annot::Expr::BoolLit(val) => Expr::BoolLit(*val),

        annot::Expr::ByteLit(val) => Expr::ByteLit(*val),

        annot::Expr::IntLit(val) => Expr::IntLit(*val),

        annot::Expr::FloatLit(val) => Expr::FloatLit(*val),
    }
}

fn solve_func(
    interner: &Interner,
    customs: &annot::CustomTypes<first_ord::CustomTypeId, flat::CustomTypeSccId>,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    func_renderer: &FuncRenderer<first_ord::CustomFuncId>,
    func_insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    id: first_ord::CustomFuncId,
) -> FuncDef {
    let func = &funcs[id];

    let mut ctx = LocalContext::new();
    let arg_id = ctx.add_local(LocalInfo {
        ty: Type::new(
            func.arg_ty.shape().clone(),
            func.arg_ty.res().map_refs(|_, res| Res {
                modes: res.modes.map(|mode| inst_params[*mode]),
                lt: res.lt.clone(),
            }),
        ),
        metadata: Metadata::default(),
    });

    debug_assert_eq!(arg_id, guard::ARG_LOCAL);

    let ret_ty = annot::Type::new(
        func.ret_ty.shape().clone(),
        func.ret_ty.res().map_refs(|_, res| {
            let modes = res.modes.map(|mode| inst_params[*mode]);
            let lt: LtParam = res.lt.clone();
            Res { modes, lt }
        }),
    );

    let body = solve_expr(
        interner,
        customs,
        funcs,
        func_renderer,
        func_insts,
        inst_params,
        &annot::FUNC_BODY_PATH(),
        &mut ctx,
        &func.body,
        &annot::wrap_lts(&ret_ty),
    );

    let (_, arg_info) = ctx.pop_local();
    FuncDef {
        purity: func.purity,
        arg_ty: arg_info.ty,
        ret_ty,
        body,
        profile_point: func.profile_point,
    }
}

pub fn solve_program(interner: &Interner, program: annot::Program) -> ob::Program {
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
        let solved = solve_func(
            interner,
            &program.custom_types,
            &program.funcs,
            &func_renderer,
            &mut func_insts,
            &spec.subst,
            spec.old_id,
        );

        let pushed_id1 = funcs.push(solved);
        let pushed_id2 = func_symbols.push(program.func_symbols[spec.old_id].clone());
        debug_assert_eq!(pushed_id1, new_id);
        debug_assert_eq!(pushed_id2, new_id);
    }

    ob::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        profile_points: program.profile_points,
        func_symbols,
        main,
    }
}

// ----------------------------------
// Step 2: Lifetime inference (again)
// ----------------------------------
// Perform flow analysis to recompute lifetimes, this time mediated by the concrete modes we have
// inferred.

struct Graph {
    nodes: IdVec<SlotId, Res<Mode, Lt>>,
    edges_in: IdVec<SlotId, BTreeSet<SlotId>>,
}

impl Graph {
    fn from_type_impl(
        customs: &ob::CustomTypes,
        seen: &mut BTreeSet<CustomTypeId>,
        edges_in: &mut IdVec<SlotId, BTreeSet<SlotId>>,
        container: Option<SlotId>,
        shape: &Shape,
        res: &[SlotId],
    ) {
        match &*shape.inner {
            ShapeInner::Bool | ShapeInner::Num(_) => {}
            ShapeInner::Tuple(shapes) => {
                for (shape, res) in iter_shapes(shapes, res) {
                    Self::from_type_impl(customs, seen, edges_in, container, shape, res);
                }
            }
            ShapeInner::Variants(shapes) => {
                for (shape, res) in iter_shapes(shapes.as_slice(), res) {
                    Self::from_type_impl(customs, seen, edges_in, container, shape, res);
                }
            }
            &ShapeInner::Custom(id) | &ShapeInner::SelfCustom(id) => {
                if !seen.contains(&id) {
                    seen.insert(id);
                    let custom = &customs.types[id];
                    Self::from_type_impl(
                        customs,
                        seen,
                        edges_in,
                        container,
                        &custom.content,
                        &custom.subst_helper.do_subst(res),
                    );
                }
            }
            ShapeInner::Array(shape) | ShapeInner::HoleArray(shape) | ShapeInner::Boxed(shape) => {
                if let Some(container) = container {
                    edges_in[container].insert(res[0]);
                }
                Self::from_type_impl(customs, seen, edges_in, Some(res[0]), shape, &res[1..]);
            }
        }
    }

    fn from_type(customs: &ob::CustomTypes, ty: &Type) -> Self {
        let mut edges_in = ty.res().map_refs(|_, _| BTreeSet::new());
        let identity = ty.res().count().into_iter().collect::<Vec<_>>();
        Self::from_type_impl(
            customs,
            &mut BTreeSet::new(),
            &mut edges_in,
            None,
            ty.shape(),
            &identity,
        );
        Self {
            nodes: ty.res().clone(),
            edges_in,
        }
    }

    fn fix(&mut self, interner: &Interner) {
        let collect_lifetimes = |graph: &Graph, scc: Scc<_>| {
            scc.nodes
                .iter()
                .map(|&node| graph.nodes[node].lt.clone())
                .collect::<Vec<_>>()
        };

        let sccs: Sccs<usize, _> = find_components(self.nodes.count(), |node| &self.edges_in[node]);
        for (_, scc) in &sccs {
            let mut old_lts = collect_lifetimes(self, scc);
            loop {
                for &dst in scc.nodes {
                    for &src in &self.edges_in[dst] {
                        let src_mode = self.nodes[src].modes.stack_or_access();
                        let dst_mode = self.nodes[dst].modes.stack_or_access();
                        if *src_mode == Mode::Owned && *dst_mode == Mode::Owned {
                            let new_lt = self.nodes[dst].lt.join(interner, &self.nodes[src].lt);
                            self.nodes[dst].lt = new_lt;
                        }
                    }
                }

                let new_lts = collect_lifetimes(self, scc);
                if old_lts.iter().zip_eq(&new_lts).all(|(old, new)| old == new) {
                    break;
                }

                old_lts = new_lts;
            }
        }
    }
}

fn propagate_spatial(interner: &Interner, customs: &ob::CustomTypes, ty: &Type) -> Type {
    let mut graph = Graph::from_type(customs, ty);
    graph.fix(interner);
    Type::new(ty.shape().clone(), graph.nodes)
}

fn should_propagate_temporal(src_mode: &ResModes<Mode>, dst_mode: &ResModes<Mode>) -> bool {
    let src_mode = src_mode.stack_or_access();
    let dst_mode = dst_mode.stack_or_access();
    match (src_mode, dst_mode) {
        (Mode::Owned, Mode::Borrowed) | (Mode::Borrowed, Mode::Borrowed) => true,
        (Mode::Owned, Mode::Owned) => false,
        (Mode::Borrowed, Mode::Owned) => unreachable!("impossible by construction"),
    }
}

fn propagate_temporal(
    interner: &Interner,
    occur_path: &Path,
    src_res: &Res<Mode, Lt>,
    dst_res: &Res<Mode, Lt>,
) -> Res<Mode, Lt> {
    let lt = if should_propagate_temporal(&src_res.modes, &dst_res.modes) {
        dst_res.lt.clone()
    } else {
        occur_path.as_lt(interner)
    };
    Res {
        modes: src_res.modes.clone(),
        lt: src_res.lt.join(interner, &lt),
    }
}

fn replace_lts<L1, L2, I: Id + 'static>(
    ty: &annot::Type<Mode, L1, I>,
    mut f: impl FnMut() -> L2,
) -> annot::Type<Mode, L2, I> {
    annot::Type::new(
        ty.shape().clone(),
        ty.res().map_refs(|_, res| res.map(Clone::clone, |_| f())),
    )
}

struct LocalInfo {
    ty: Type,
    metadata: Metadata,
}

type LocalContext = local_context::LocalContext<guard::LocalId, LocalInfo>;

fn create_occurs_from_model(
    sig: &model::Signature,
    interner: &Interner,
    _ctx: &mut LocalContext,
    path: &annot::Path,
    args: &[&Occur],
    ret: &Type,
) -> Vec<Occur> {
    assert!(args.len() >= sig.args.fixed.len());

    // Create a fresh occurrence for each function argument.
    let mut arg_occurs = args
        .iter()
        .map(|arg| {
            let ty = replace_lts(&arg.ty, || Lt::Empty);
            Occur { id: arg.id, ty }
        })
        .collect::<Vec<_>>();

    ///////////////////////////////////////
    // Step 1: Handle constraints which arise from model lifetime variables.
    ///////////////////////////////////////

    // Set up a mapping from model lifetimes to lifetimes.
    let mut get_ret: IdVec<model::ModelLt, Option<Res<Mode, Lt>>> =
        IdVec::from_count_with(sig.lt_count, |_| None);

    for (slot, model_res) in sig.ret.get_res(&ret.shape()) {
        if sig.unused_lts.contains(&model_res.lt) {
            panic!("unused model lifetimes cannot be supplied in return position");
        }

        // Update the lifetime mapping based on the return.
        let res = &ret.res()[slot];
        match &mut get_ret[model_res.lt] {
            entry @ None => *entry = Some(res.clone()),
            Some(_) => {
                panic!("a lifetime variable cannot appear more than once in a model return type");
            }
        }
    }

    let get_ret = get_ret;

    for (i, (arg, occur)) in sig.args.iter().zip(&mut arg_occurs).enumerate() {
        for (slot, model_res) in arg.get_res(&occur.ty.shape()) {
            let arg_res = &mut occur.ty.res_mut()[slot];

            // Substitute for model lifetimes using the mapping constructed from the return.
            arg_res.lt = if let Some(ret_res) = &get_ret[model_res.lt] {
                if should_propagate_temporal(&arg_res.modes, &ret_res.modes) {
                    ret_res.lt.clone()
                } else {
                    annot::arg_path(path, i, args.len()).as_lt(interner)
                }
            } else if sig.unused_lts.contains(&model_res.lt) {
                Lt::Empty
            } else {
                annot::arg_path(path, i, args.len()).as_lt(interner)
            };
        }
    }

    ///////////////////////////////////////
    // Step 2: Handle constraints which arise from repeated uses of the same model type variable.
    ///////////////////////////////////////

    // Accumulate the resources for each occurrence of each type variable.
    let mut vars = IdMap::new();
    for ((i, model), occur) in sig.args.iter().enumerate().zip(&arg_occurs) {
        model.extract_vars(
            |shape, res| Type::new(shape.clone(), IdVec::from_vec(res.to_vec())),
            model::VarOccurKind::Arg(i),
            &occur.ty.shape(),
            occur.ty.res().as_slice(),
            &mut vars,
        );
    }
    sig.ret.extract_vars(
        |shape, res| Type::new(shape.clone(), IdVec::from_vec(res.to_vec())),
        model::VarOccurKind::Ret,
        &ret.shape(),
        ret.res().as_slice(),
        &mut vars,
    );

    // At this point, it would seem natural to convert `vars` from an `IdMap` to an `IdVec`.
    // However, if the model signature has an empty variadic argument, then the `IdMap` will not
    // contain entries for any type variables which appear only in the type of that argument.

    for var_occurs in vars.values_mut() {
        // Propagate lifetimes from return occurrences of variables to argument occurrences of
        // variables.
        for ret in var_occurs.rets.iter() {
            for arg in var_occurs.args.iter_mut() {
                let loc = arg.loc;
                let arg_res =
                    &mut arg_occurs[loc.occur_idx].ty.res_mut().as_mut_slice()[loc.start..loc.end];

                for (arg_res, ret_res) in arg_res.iter_mut().zip_eq(ret.res().values()) {
                    if should_propagate_temporal(&arg_res.modes, &ret_res.modes) {
                        arg_res.lt = arg_res.lt.join(interner, &ret_res.lt);
                    }
                }
            }
        }
    }

    ///////////////////////////////////////
    // Step 3: Handle any explicit constraints (as given in the 'where' clause of the model).
    ///////////////////////////////////////

    for constr in &sig.constrs {
        match constr {
            model::Constr::Mode { .. } => {
                // Do nothing.
            }
            model::Constr::Lt { lhs, rhs } => {
                // We check when we construct a signature that any type variables that appear in
                // constraints also appear in the signature. This can only happen if there is an
                // empty variadic argument.
                if !vars.contains_key(lhs.type_var) || !vars.contains_key(rhs.type_var) {
                    continue;
                }

                let (lhs_vars, rhs_vars) = vars.get_pair_mut(lhs.type_var, rhs.type_var).unwrap();

                for ret in rhs_vars.rets.iter() {
                    for arg in lhs_vars.args.iter_mut() {
                        let loc = arg.loc;
                        let arg_res = &mut arg_occurs[loc.occur_idx].ty.res_mut().as_mut_slice()
                            [loc.start..loc.end];

                        for (arg_res, ret_res) in arg_res.iter_mut().zip_eq(ret.res().values()) {
                            if should_propagate_temporal(&arg_res.modes, &ret_res.modes) {
                                arg_res.lt = arg_res.lt.join(interner, &ret_res.lt);
                            }
                        }
                    }
                }
            }
        }
    }

    arg_occurs
}

fn propagate_occur(
    interner: &Interner,
    ctx: &mut LocalContext,
    path: &Path,
    local: guard::LocalId,
    ty: &Type,
) {
    let binding = ctx.local_binding_mut(local);

    let new_src_res = binding
        .ty
        .res()
        .values()
        .zip_eq(ty.res().values())
        .map(|(src_res, dst_res)| propagate_temporal(interner, path, src_res, dst_res))
        .collect::<Vec<_>>();

    binding.ty = Type::new(binding.ty.shape().clone(), IdVec::from_vec(new_src_res))
}

fn instantiate_model(
    sig: &model::Signature,
    interner: &Interner,
    ctx: &mut LocalContext,
    path: &annot::Path,
    args: &[&Occur],
    ret: &Type,
) -> Vec<Occur> {
    let occurs = create_occurs_from_model(sig, interner, ctx, path, args, ret);

    for (i, occur) in occurs.iter().enumerate() {
        propagate_occur(
            interner,
            ctx,
            &annot::arg_path(path, i, occurs.len()),
            occur.id,
            &occur.ty,
        );
    }

    occurs
}

#[derive(Clone, Copy, Debug)]
struct SignatureAssumptions<'a> {
    known_defs: &'a IdMap<CustomFuncId, FuncDef>,
    pending_args: &'a BTreeMap<CustomFuncId, Type>,
    pending_rets: &'a BTreeMap<CustomFuncId, RetType>,
}

impl SignatureAssumptions<'_> {
    fn sig_of(&self, id: CustomFuncId) -> (&Type, &RetType) {
        self.known_defs.get(id).map_or_else(
            || {
                let arg_type = self.pending_args.get(&id).unwrap();
                let ret_type = self.pending_rets.get(&id).unwrap();
                (arg_type, ret_type)
            },
            |def| (&def.arg_ty, &def.ret_ty),
        )
    }
}

fn handle_occur(
    interner: &Interner,
    ctx: &mut LocalContext,
    path: &Path,
    occur: guard::LocalId,
    use_ty: &Type,
) -> Occur {
    // Throw out the existing lifetimes; we are recomputing them. Keep the modes.
    propagate_occur(interner, ctx, path, occur, &use_ty);
    Occur {
        id: occur,
        ty: use_ty.clone(),
    }
}

fn annot_expr(
    interner: &Interner,
    customs: &ob::CustomTypes,
    sigs: SignatureAssumptions<'_>,
    func_renderer: &FuncRenderer<ob::CustomFuncId>,
    path: &Path,
    ctx: &mut LocalContext,
    expr: &Expr,
    fut_ty: &Type,
) -> Expr {
    match expr {
        Expr::Local(occur) => Expr::Local(handle_occur(interner, ctx, path, occur.id, fut_ty)),

        Expr::Call(purity, func_id, arg) => {
            let (arg_ty, ret_ty) = sigs.sig_of(*func_id);

            let lt_subst = annot::bind_lts(interner, &ret_ty, fut_ty);
            let arg_ty = annot::prepare_arg_type(interner, &path, arg_ty);

            // This `join_everywhere` reflects the fact that we assume that functions access all of
            // their arguments. We could be more precise here.
            let arg_ty = annot::join_everywhere(
                interner,
                &annot::subst_lts(interner, &arg_ty, &lt_subst),
                &path.as_lt(interner),
            );

            // println!(
            //     "calling {} with %{}",
            //     func_renderer.render(*func_id),
            //     arg.id.0,
            // );
            // println!("{}", arg_ty.display(),);
            // println!("{}", ctx.local_binding(arg.id).ty.display());
            let arg = handle_occur(interner, ctx, path, arg.id, &arg_ty);
            Expr::Call(*purity, *func_id, arg)
        }

        // We use `with_scope` to express our intent. In fact, all the bindings we add are popped
        // from the context before we return.
        Expr::LetMany(bindings, ret) => ctx.with_scope(|ctx| {
            let locals_offset = ctx.len();

            for (binding_ty, _, _) in bindings {
                let _ = ctx.add_local(LocalInfo {
                    ty: replace_lts(binding_ty, || Lt::Empty),
                    metadata: Metadata::default(),
                });
            }

            let ret_occur = handle_occur(interner, ctx, &path.seq(bindings.len()), ret.id, fut_ty);

            let mut new_bindings_rev = Vec::new();
            for (i, (_, expr, metadata)) in bindings.into_iter().enumerate().rev() {
                let local = guard::LocalId(locals_offset + i);

                let fut_ty = &ctx.local_binding(local).ty;
                let fut_ty = propagate_spatial(interner, customs, fut_ty);

                // Only retain the locals *strictly* before this binding.
                ctx.truncate(Count::from_value(local.0));

                let new_expr = annot_expr(
                    interner,
                    customs,
                    sigs,
                    func_renderer,
                    &path.seq(i),
                    ctx,
                    expr,
                    &fut_ty,
                );

                new_bindings_rev.push((fut_ty, new_expr, metadata.clone()));
            }

            let new_bindings = {
                new_bindings_rev.reverse();
                new_bindings_rev
            };

            Expr::LetMany(new_bindings, ret_occur)
        }),

        Expr::If(discrim, then_case, else_case) => {
            let else_case = annot_expr(
                interner,
                customs,
                sigs,
                func_renderer,
                &path.seq(1).alt(1, 2),
                ctx,
                else_case,
                fut_ty,
            );
            let then_case = annot_expr(
                interner,
                customs,
                sigs,
                func_renderer,
                &path.seq(1).alt(0, 2),
                ctx,
                then_case,
                fut_ty,
            );
            let discrim = handle_occur(
                interner,
                ctx,
                &path.seq(0),
                discrim.id,
                &Type::bool_(interner),
            );
            Expr::If(discrim, Box::new(then_case), Box::new(else_case))
        }

        Expr::CheckVariant(variant_id, variant) => {
            assert!(fut_ty.shape() == &Shape::bool_(interner));
            let variants_ty = &ctx.local_binding(variant.id).ty.clone(); // appease the borrow checker
            Expr::CheckVariant(
                *variant_id,
                handle_occur(interner, ctx, path, variant.id, variants_ty),
            )
        }

        Expr::Unreachable(ty) => Expr::Unreachable(ty.clone()),

        Expr::Tuple(fields) => {
            let fut_item_tys = annot::elim_tuple(fut_ty);
            let mut fields_rev = fields
                .into_iter()
                .zip_eq(fut_item_tys.iter())
                .enumerate()
                .rev()
                .map(|(i, (occur, item_ty))| {
                    handle_occur(interner, ctx, &path.seq(i), occur.id, item_ty)
                })
                .collect::<Vec<_>>();
            let fields = {
                fields_rev.reverse();
                fields_rev
            };
            Expr::Tuple(fields)
        }

        Expr::TupleField(tup, idx) => {
            let mut tuple_ty = replace_lts(&tup.ty, || Lt::Empty);
            let ShapeInner::Tuple(shapes) = &*tuple_ty.shape().inner else {
                panic!("expected `Tuple` type");
            };

            let (start, end) = annot::nth_res_bounds(shapes, *idx);
            tuple_ty.res_mut().as_mut_slice()[start..end].clone_from_slice(fut_ty.res().as_slice());

            let occur = handle_occur(interner, ctx, path, tup.id, &tuple_ty);
            Expr::TupleField(occur, *idx)
        }

        Expr::WrapVariant(_variants, variant_id, content) => {
            let fut_variant_tys = annot::elim_variants(fut_ty);
            let occur = handle_occur(
                interner,
                ctx,
                path,
                content.id,
                &fut_variant_tys[*variant_id],
            );
            Expr::WrapVariant(fut_variant_tys, *variant_id, occur)
        }

        Expr::UnwrapVariant(variant_id, wrapped) => {
            let mut variants_ty = replace_lts(&wrapped.ty, || Lt::Empty);
            let ShapeInner::Variants(shapes) = &*variants_ty.shape().inner else {
                panic!("expected `Variants` type");
            };

            let (start, end) = annot::nth_res_bounds(shapes.as_slice(), variant_id.to_index());
            variants_ty.res_mut().as_mut_slice()[start..end]
                .clone_from_slice(fut_ty.res().as_slice());

            let occur = handle_occur(interner, ctx, path, wrapped.id, &variants_ty);
            Expr::UnwrapVariant(*variant_id, occur)
        }

        Expr::WrapBoxed(content, _output_ty) => {
            let mut occurs =
                instantiate_model(&*model::box_new, interner, ctx, path, &[content], fut_ty);
            Expr::WrapBoxed(occurs.pop().unwrap(), fut_ty.clone())
        }

        Expr::UnwrapBoxed(wrapped, _output_ty) => {
            let mut occurs =
                instantiate_model(&*model::box_get, interner, ctx, path, &[wrapped], fut_ty);
            Expr::UnwrapBoxed(occurs.pop().unwrap(), fut_ty.clone())
        }

        Expr::WrapCustom(custom_id, recipe, unfolded) => {
            let fut_unfolded =
                annot::unfold(interner, &customs.types, &customs.sccs, recipe, fut_ty);
            let occur = handle_occur(interner, ctx, path, unfolded.id, &fut_unfolded);
            Expr::WrapCustom(*custom_id, recipe.clone(), occur)
        }

        Expr::UnwrapCustom(custom_id, recipe, folded) => {
            let fresh_folded = {
                let mut lt_count = Count::new();
                replace_lts(&ctx.local_binding(folded.id).ty, move || lt_count.inc())
            };

            let fresh_folded = {
                let fresh_unfolded = annot::unfold(
                    interner,
                    &customs.types,
                    &customs.sccs,
                    recipe,
                    &fresh_folded,
                );

                // Join the lifetimes in `fut_ty` which are identified under folding.
                let lt_subst = annot::bind_lts(interner, &fresh_unfolded, fut_ty);
                annot::subst_lts(interner, &annot::wrap_lts(&fresh_folded), &lt_subst)
            };

            let occur = handle_occur(interner, ctx, path, folded.id, &fresh_folded);
            Expr::UnwrapCustom(*custom_id, recipe.clone(), occur)
        }

        Expr::Intrinsic(intr, arg) => Expr::Intrinsic(*intr, arg.clone()),

        Expr::ArrayOp(ArrayOp::Get(arr, idx, _)) => {
            let occurs =
                instantiate_model(&*model::array_get, interner, ctx, path, &[arr, idx], fut_ty);
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Get(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
                fut_ty.clone(),
            ))
        }

        Expr::ArrayOp(ArrayOp::Extract(arr, idx)) => {
            let occurs = instantiate_model(
                &*model::array_extract,
                interner,
                ctx,
                path,
                &[arr, idx],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Extract(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        Expr::ArrayOp(ArrayOp::Len(arr)) => {
            let occurs = instantiate_model(&*model::array_len, interner, ctx, path, &[arr], fut_ty);
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Len(occurs.next().unwrap()))
        }

        Expr::ArrayOp(ArrayOp::Push(arr, item)) => {
            let occurs = instantiate_model(
                &*model::array_push,
                interner,
                ctx,
                path,
                &[arr, item],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Push(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        Expr::ArrayOp(ArrayOp::Pop(arr)) => {
            let occurs = instantiate_model(&*model::array_pop, interner, ctx, path, &[arr], fut_ty);
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Pop(occurs.next().unwrap()))
        }

        Expr::ArrayOp(ArrayOp::Replace(hole, item)) => {
            let occurs = instantiate_model(
                &*model::array_replace,
                interner,
                ctx,
                path,
                &[hole, item],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Replace(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        Expr::ArrayOp(ArrayOp::Reserve(arr, cap)) => {
            let occurs = instantiate_model(
                &*model::array_reserve,
                interner,
                ctx,
                path,
                &[arr, cap],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Reserve(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        Expr::IoOp(IoOp::Input) => {
            let _ = instantiate_model(&*model::io_input, interner, ctx, path, &[], fut_ty);
            Expr::IoOp(IoOp::Input)
        }

        Expr::IoOp(IoOp::Output(arr)) => {
            let occurs = instantiate_model(&*model::io_output, interner, ctx, path, &[arr], fut_ty);
            let mut occurs = occurs.into_iter();
            Expr::IoOp(IoOp::Output(occurs.next().unwrap()))
        }

        Expr::Panic(_ret_ty, msg) => {
            let occurs = instantiate_model(
                &*model::panic,
                interner,
                ctx,
                path,
                &[msg],
                &Type::unit(interner),
            );
            let mut occurs = occurs.into_iter();
            Expr::Panic(fut_ty.clone(), occurs.next().unwrap())
        }

        Expr::ArrayLit(_item_ty, items) => {
            let item_refs = items.iter().collect::<Vec<_>>();
            let occurs =
                instantiate_model(&*model::array_new, interner, ctx, path, &item_refs, fut_ty);
            let (_, ret_item_ty) = annot::elim_array(fut_ty);
            Expr::ArrayLit(ret_item_ty, occurs)
        }

        Expr::BoolLit(val) => Expr::BoolLit(*val),

        Expr::ByteLit(val) => Expr::ByteLit(*val),

        Expr::IntLit(val) => Expr::IntLit(*val),

        Expr::FloatLit(val) => Expr::FloatLit(*val),
    }
}

#[derive(Clone, Debug)]
struct SolverScc {
    func_args: BTreeMap<CustomFuncId, Type>,
    func_rets: BTreeMap<CustomFuncId, RetType>,
    func_bodies: BTreeMap<CustomFuncId, Expr>,
}

fn annot_scc(
    interner: &Interner,
    customs: &ob::CustomTypes,
    funcs: &IdVec<ob::CustomFuncId, FuncDef>,
    funcs_annot: &IdMap<ob::CustomFuncId, FuncDef>,
    func_renderer: &FuncRenderer<ob::CustomFuncId>,
    scc: Scc<ob::CustomFuncId>,
) -> SolverScc {
    match scc.kind {
        SccKind::Acyclic | SccKind::Cyclic => {
            // TODO: if the SCC is acyclic, we can skip lifetime fixed point iteration

            let mut next_lt = Count::new();

            let mut arg_tys = scc
                .nodes
                .iter()
                .map(|id| (*id, replace_lts(&funcs[id].arg_ty, || Lt::Empty)))
                .collect::<BTreeMap<_, _>>();

            let ret_tys = scc
                .nodes
                .iter()
                .map(|id| (*id, replace_lts(&funcs[id].ret_ty, || next_lt.inc())))
                .collect::<BTreeMap<_, _>>();

            let (new_arg_tys, bodies) = loop {
                let mut new_arg_tys = BTreeMap::new();
                let mut bodies = BTreeMap::new();
                let assumptions = SignatureAssumptions {
                    known_defs: funcs_annot,
                    pending_args: &arg_tys,
                    pending_rets: &ret_tys,
                };

                for id in scc.nodes {
                    // println!("annotating {}", func_renderer.render(id));
                    let func = &funcs[id];
                    let mut ctx = LocalContext::new();

                    let arg_id = ctx.add_local(LocalInfo {
                        ty: replace_lts(&func.arg_ty, || Lt::Empty),
                        metadata: Metadata::default(),
                    });
                    debug_assert_eq!(arg_id, guard::ARG_LOCAL);

                    let ret_ty = annot::wrap_lts(&ret_tys[id]);
                    let expr = annot_expr(
                        interner,
                        customs,
                        assumptions,
                        func_renderer,
                        &annot::FUNC_BODY_PATH(),
                        &mut ctx,
                        &func.body,
                        &ret_ty,
                    );
                    bodies.insert(*id, expr);

                    new_arg_tys.insert(
                        *id,
                        propagate_spatial(interner, customs, &ctx.local_binding(arg_id).ty),
                    );
                }

                if new_arg_tys
                    .values()
                    .zip_eq(arg_tys.values())
                    .all(|(new, old)| annot::lt_equiv(new, old))
                {
                    break (new_arg_tys, bodies);
                }

                arg_tys = new_arg_tys;
            };

            SolverScc {
                func_args: new_arg_tys,
                func_rets: ret_tys,
                func_bodies: bodies,
            }
        }
    }
}

fn add_func_deps(deps: &mut BTreeSet<ob::CustomFuncId>, expr: &Expr) {
    match expr {
        Expr::Call(_, other, _) => {
            deps.insert(*other);
        }
        Expr::If(_, then_case, else_case) => {
            add_func_deps(deps, then_case);
            add_func_deps(deps, else_case);
        }
        Expr::LetMany(bindings, _) => {
            for (_, rhs, _) in bindings {
                add_func_deps(deps, rhs);
            }
        }
        _ => {}
    }
}

fn annot_program(
    interner: &Interner,
    program: ob::Program,
    progress: impl ProgressLogger,
) -> ob::Program {
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);

    let func_sccs: Sccs<usize, _> = find_components(program.funcs.count(), |id| {
        let mut deps = BTreeSet::new();
        add_func_deps(&mut deps, &program.funcs[id].body);
        deps
    });

    let mut progress = progress.start_session(Some(program.funcs.len()));

    let mut funcs_annot = IdMap::new();
    for (_func_id, scc) in &func_sccs {
        let annotated = annot_scc(
            interner,
            &program.custom_types,
            &program.funcs,
            &funcs_annot,
            &func_renderer,
            scc,
        );

        for func_id in scc.nodes {
            let func = &program.funcs[func_id];
            funcs_annot.insert_vacant(
                *func_id,
                FuncDef {
                    purity: func.purity,
                    arg_ty: annotated.func_args[&func_id].clone(),
                    ret_ty: annotated.func_rets[&func_id].clone(),
                    body: annotated.func_bodies[&func_id].clone(),
                    profile_point: func.profile_point.clone(),
                },
            );
        }

        progress.update(scc.nodes.len());
    }

    let funcs = funcs_annot.to_id_vec(program.funcs.count());

    progress.finish();

    ob::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        profile_points: program.profile_points,
        func_symbols: program.func_symbols,
        main: program.main,
    }
}

pub fn annot_obligations(
    interner: &Interner,
    program: annot::Program,
    progress: impl ProgressLogger,
) -> ob::Program {
    let program = solve_program(interner, program);
    let program = annot_program(interner, program, progress);
    program
}
