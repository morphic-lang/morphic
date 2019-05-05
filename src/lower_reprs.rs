use crate::data::repr_annot_ast as in_ast;
use crate::data::repr_specialized_ast as out_ast;
use crate::util::with_scope;
use std::collections::{BTreeMap, VecDeque};

pub fn lower_reprs(program: in_ast::Program) -> out_ast::Program {
    let mut state = State {
        queue: VecDeque::new(),

        func_mapping: vec![BTreeMap::new(); program.funcs.len()],
        out_funcs: Vec::new(),

        type_mapping: vec![BTreeMap::new(); program.funcs.len()],
        out_types: Vec::new(),
    };

    state.lower_call(
        Context {
            env: &[],
            in_type_defs: &program.custom_types,
        },
        program.main,
        &[],
    );
    while let Some(pending) = state.queue.pop_front() {
        lower_func(
            Context {
                env: &pending.args,
                in_type_defs: &program.custom_types,
            },
            &mut state,
            pending.in_func,
            &program.funcs[pending.in_func.0],
        )
    }

    let main_args: &[_] = &[];
    let main = state
        .func_id_for(program.main, main_args)
        .expect("internal error: couldn't find main");

    out_ast::Program {
        custom_types: state.out_types.into_iter().map(Option::unwrap).collect(),
        funcs: state.out_funcs.into_iter().map(Option::unwrap).collect(),
        main: main,
    }
}

#[derive(Clone, Debug)]
struct PendingInstance {
    in_func: in_ast::CustomFuncId,
    args: Vec<out_ast::Repr>,
}

#[derive(Debug)]
struct State {
    func_mapping: Vec<BTreeMap<Vec<out_ast::Repr>, out_ast::CustomFuncId>>, // indexed by in_ast::CustomFuncId
    out_funcs: Vec<Option<out_ast::FuncDef>>, // indexed by out_ast::CustomFuncId

    type_mapping: Vec<BTreeMap<Vec<out_ast::Repr>, out_ast::CustomTypeId>>, // indexed by in_ast::CustomTypeId
    out_types: Vec<Option<out_ast::TypeDef>>, // indexed by out_ast::CustomFuncId

    queue: VecDeque<PendingInstance>,
}

impl State {
    fn add_pending(&mut self) -> out_ast::CustomFuncId {
        self.out_funcs.push(None);
        out_ast::CustomFuncId(self.out_funcs.len() - 1)
    }

    fn fresh_type(&mut self) -> out_ast::CustomTypeId {
        self.out_types.push(None);
        out_ast::CustomTypeId(self.out_types.len() - 1)
    }

    fn type_id_for(
        &self,
        ctx: Context,
        type_id: in_ast::CustomTypeId,
        args: &[in_ast::Solution],
    ) -> Option<out_ast::CustomTypeId> {
        let reprs = ctx.resolve_all(args);
        self.type_mapping[type_id.0].get(&reprs).cloned()
    }

    fn func_id_for(
        &self,
        in_func_id: in_ast::CustomFuncId,
        args: &[out_ast::Repr],
    ) -> Option<out_ast::CustomFuncId> {
        self.func_mapping[in_func_id.0].get(args).cloned()
    }

    fn lower_call(
        &mut self,
        ctx: Context,
        func: in_ast::CustomFuncId,
        args: &[in_ast::Solution],
    ) -> out_ast::CustomFuncId {
        let reprs = ctx.resolve_all(args);;
        if let Some(inst) = self.func_id_for(func, &reprs) {
            inst
        } else {
            let id = self.add_pending();
            self.func_mapping[func.0].insert(reprs.clone(), id);
            self.queue.push_back(PendingInstance {
                in_func: func,
                args: reprs,
            });
            id
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct Context<'a> {
    env: &'a [out_ast::Repr], // indexed by in_ast::RepParamId
    in_type_defs: &'a [in_ast::TypeDef<in_ast::RepParamId>], // indexed by in_ast::CustomTypeId
}

impl<'a> Context<'a> {
    fn resolve(&self, soln: in_ast::Solution) -> out_ast::Repr {
        match soln {
            in_ast::Solution::Shared => out_ast::Repr::Shared,
            in_ast::Solution::Unique => out_ast::Repr::Unique,
            in_ast::Solution::Var(repr_var) => self.env[repr_var.0],
        }
    }

    fn resolve_all(&self, solns: &[in_ast::Solution]) -> Vec<out_ast::Repr> {
        solns
            .iter()
            .map(|soln| self.resolve(*soln))
            .collect::<Vec<_>>()
    }

    fn repr_for(&self, param: in_ast::RepParamId) -> out_ast::Repr {
        self.env[param.0]
    }
}

fn lower_func(
    ctx: Context,
    state: &mut State,
    in_func_id: in_ast::CustomFuncId,
    func: &in_ast::FuncDef,
) {
    let out_arg_type = lower_type(ctx, state, &func.arg_type);
    let mut out_exprs = Vec::new();
    let mut out_types = Vec::new();
    let mut locals = vec![func.arg_type.clone()];
    for (expr, type_) in func.body.exprs.iter().zip(&func.body.types) {
        out_types.push(lower_type(ctx, state, type_));
        out_exprs.push(lower_expr(ctx, state, &mut locals, expr));
        locals.push(type_.clone());
    }
    let out_body = out_ast::Block {
        initial_idx: func.body.initial_idx,
        exprs: out_exprs,
        types: out_types,
        expr_ids: func.body.expr_ids.clone(),
    };
    let out_func_id = state.func_mapping[in_func_id.0][ctx.env];
    assert!(state.out_funcs[out_func_id.0].is_none());
    state.out_funcs[out_func_id.0] = Some(out_ast::FuncDef {
        arg_type: out_arg_type,
        body: out_body,
        unique_info: func.unique_info.clone(),
        ret_aliasing: func.ret_aliasing.clone(),
    });
}

fn lower_expr(
    ctx: Context,
    state: &mut State,
    locals: &mut Vec<in_ast::Type>,
    expr: &in_ast::Expr,
) -> out_ast::Expr {
    use in_ast::Expr as E;
    match expr {
        E::Term(term) => out_ast::Expr::Term(term.clone()),
        E::ArithOp(arith_op) => out_ast::Expr::ArithOp(arith_op.clone().into()),
        E::ArrayOp(array_op) => {
            use in_ast::ArrayOp as A;
            out_ast::Expr::ArrayOp(match array_op {
                A::Construct(item_t, repr_soln, items) => out_ast::ArrayOp::Construct(
                    Box::new(lower_type(ctx, state, item_t)),
                    ctx.resolve(*repr_soln),
                    items.clone(),
                ),
                A::Item(array, idx) => out_ast::ArrayOp::Item(array.clone(), idx.clone()),
                A::Len(array) => out_ast::ArrayOp::Len(array.clone()),
                A::Push(array, item) => out_ast::ArrayOp::Push(array.clone(), item.clone()),
                A::Pop(array) => out_ast::ArrayOp::Pop(array.clone()),
                A::Replace(hole, item) => out_ast::ArrayOp::Replace(hole.clone(), item.clone()),
            })
        }
        E::IOOp(in_ast::IOOp::Input(soln)) => {
            out_ast::Expr::IOOp(out_ast::IOOp::Input(ctx.resolve(*soln)))
        }
        E::IOOp(in_ast::IOOp::Output(term)) => {
            out_ast::Expr::IOOp(out_ast::IOOp::Output(term.clone()))
        }
        E::Ctor(in_type_id, solns, variant_id, arg) => out_ast::Expr::Ctor(
            state
                .type_id_for(ctx, *in_type_id, &solns)
                .expect("internal error: type should have already been instantiated"),
            *variant_id,
            arg.clone(),
        ),
        E::Tuple(items) => out_ast::Expr::Tuple(items.clone()),
        E::Local(local_id) => out_ast::Expr::Local(*local_id),
        E::Call(purity, in_func_id, arg, solns) => out_ast::Expr::Call(
            *purity,
            state.lower_call(ctx, *in_func_id, solns),
            arg.clone(),
        ),
        E::Match(matched_local, branches, result_type) => out_ast::Expr::Match(
            *matched_local,
            branches
                .iter()
                .map(|(pat, branch)| {
                    with_scope(locals, |sub_locals| {
                        let types = branch
                            .types
                            .iter()
                            .map(|t| lower_type(ctx, state, t))
                            .collect::<Vec<_>>();
                        sub_locals.extend_from_slice(&branch.types);
                        let exprs = branch
                            .exprs
                            .iter()
                            .map(|e| lower_expr(ctx, state, sub_locals, e))
                            .collect();
                        (
                            lower_pat(ctx, state, &sub_locals[matched_local.0], pat),
                            out_ast::Block {
                                initial_idx: branch.initial_idx,
                                exprs,
                                types,
                                expr_ids: branch.expr_ids.clone(),
                            },
                        )
                    })
                })
                .collect(),
            Box::new(lower_type(ctx, state, result_type)),
        ),
    }
}

fn lower_type(ctx: Context, state: &mut State, type_: &in_ast::Type) -> out_ast::Type {
    return lower_type_with(&|soln| ctx.resolve(soln), ctx.in_type_defs, state, type_);

    fn lower_type_with<Var>(
        resolve: &dyn Fn(Var) -> out_ast::Repr,
        in_type_defs: &[in_ast::TypeDef<in_ast::RepParamId>],
        state: &mut State,
        type_: &in_ast::Type<Var>,
    ) -> out_ast::Type
    where
        Var: Copy,
    {
        use in_ast::Type as T;
        match type_ {
            T::Bool => out_ast::Type::Prim(out_ast::Primitive::Bool),
            T::Int => out_ast::Type::Prim(out_ast::Primitive::Num(out_ast::NumType::Int)),
            T::Byte => out_ast::Type::Prim(out_ast::Primitive::Num(out_ast::NumType::Byte)),
            T::Float => out_ast::Type::Prim(out_ast::Primitive::Num(out_ast::NumType::Float)),
            T::Tuple(item_types) => out_ast::Type::Tuple(
                item_types
                    .iter()
                    .map(|t| lower_type_with(resolve, in_type_defs, state, t))
                    .collect(),
            ),
            T::Array(item_type, soln) => out_ast::Type::Array(
                Box::new(lower_type_with(resolve, in_type_defs, state, item_type)),
                resolve(*soln),
            ),
            T::HoleArray(item_type, soln) => out_ast::Type::HoleArray(
                Box::new(lower_type_with(resolve, in_type_defs, state, item_type)),
                resolve(*soln),
            ),
            T::Custom(in_type_id, solns) => {
                let args = solns.into_iter().cloned().map(resolve).collect::<Vec<_>>();
                if let Some(id) = state.type_mapping[in_type_id.0].get(&args) {
                    out_ast::Type::Custom(*id)
                } else {
                    let fresh = state.fresh_type();
                    state.type_mapping[in_type_id.0].insert(args.clone(), fresh);
                    assert!(state.out_types[fresh.0].is_none());
                    let resolve_arg = |in_ast::RepParamId(rep)| args[rep];
                    state.out_types[fresh.0] = Some(out_ast::TypeDef {
                        variants: in_type_defs[in_type_id.0]
                            .variants
                            .iter()
                            .map(|maybe_variant| {
                                maybe_variant.as_ref().map(|variant| {
                                    lower_type_with(&resolve_arg, in_type_defs, state, &variant)
                                })
                            })
                            .collect(),
                    });
                    out_ast::Type::Custom(fresh)
                }
            }
        }
    }
}

fn lower_pat(
    ctx: Context,
    state: &mut State,
    type_: &in_ast::Type,
    pat: &in_ast::Pattern,
) -> out_ast::Pattern {
    return lower_pat_with(
        &|soln| ctx.resolve(soln),
        ctx.in_type_defs,
        state,
        type_,
        pat,
    );

    fn lower_pat_with<Var>(
        resolve: &dyn Fn(Var) -> out_ast::Repr,
        in_type_defs: &[in_ast::TypeDef<in_ast::RepParamId>],
        state: &mut State,
        type_: &in_ast::Type<Var>,
        pat: &in_ast::Pattern,
    ) -> out_ast::Pattern
    where
        Var: Copy + std::fmt::Debug,
    {
        use in_ast::Pattern as P;
        use in_ast::Type as T;
        match (pat, type_) {
            (P::Any, _) => out_ast::Pattern::Any,
            (P::Tuple(items), T::Tuple(item_types)) => out_ast::Pattern::Tuple(
                items
                    .iter()
                    .zip(item_types)
                    .map(|(p, t)| lower_pat_with(resolve, in_type_defs, state, t, p))
                    .collect(),
            ),
            (P::Ctor(in_type_id, variant_id, arg_pat), T::Custom(t_type_id, solns)) => {
                assert_eq!(in_type_id, t_type_id);
                let args = solns.iter().map(|soln| resolve(*soln)).collect::<Vec<_>>();
                let out_type_id = state.type_mapping[in_type_id.0][&args];

                if let Some(arg_pat) = arg_pat {
                    let variant_t = in_type_defs[in_type_id.0].variants[variant_id.0]
                        .as_ref()
                        .unwrap();

                    let variant_resolve = move |in_ast::RepParamId(rep)| args[rep];
                    let lowered_arg =
                        lower_pat_with(&variant_resolve, in_type_defs, state, variant_t, arg_pat);
                    out_ast::Pattern::Ctor(out_type_id, *variant_id, Some(Box::new(lowered_arg)))
                } else {
                    out_ast::Pattern::Ctor(out_type_id, *variant_id, None)
                }
            }
            (P::BoolConst(v), _) => out_ast::Pattern::Const(out_ast::PrimVal::Bool(*v)),
            (P::IntConst(v), _) => out_ast::Pattern::Const(out_ast::PrimVal::Int(*v)),
            (P::FloatConst(v), _) => out_ast::Pattern::Const(out_ast::PrimVal::Float(*v)),
            (P::ByteConst(v), _) => out_ast::Pattern::Const(out_ast::PrimVal::Byte(*v)),
            (_, _) => panic!("mismatch between pattern {:?} and type {:?}", pat, type_),
        }
    }
}
