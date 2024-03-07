use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast::{CustomFuncId, CustomTypeId};
use crate::data::flat_ast::{self as flat, LocalId};
use crate::data::mode_annot_ast2::{
    self as annot, Lt, LtParam, ModeLteConstr, ModeParam, ModeTerm, Overlay,
};
use crate::util::graph::{self, Graph, Scc};
use crate::util::id_gen::IdGen;
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{id_type, Count, Id, IdMap, IdVec};
use std::collections::{BTreeMap, BTreeSet};

struct ConstrGraph {
    // a -> b means a <= b, i.e. if a is owned then b is owned
    inner: Graph<ModeParam>,
}

impl ConstrGraph {
    fn new() -> Self {
        Self {
            inner: Graph {
                edges_out: IdVec::new(),
            },
        }
    }

    fn add_constr(&mut self, constr: ModeLteConstr) {
        self.inner.edges_out[constr.0].push(constr.1);
    }

    fn add_lte(&mut self, a: ModeParam, b: ModeParam) {
        self.add_constr(ModeLteConstr(a, b));
    }

    fn add_eq(&mut self, a: ModeParam, b: ModeParam) {
        self.add_lte(a, b);
        self.add_lte(b, a);
    }

    fn solve(&self) -> IdVec<ModeVar, ModeTerm<ModeVar>> {
        let sccs = graph::acyclic_and_cyclic_sccs(&self.inner);

        let mut lower_bounds = IdMap::new();
        for scc in &sccs {
            todo!()
        }

        let len = lower_bounds.len();
        lower_bounds.to_id_vec(Count::from_value(len))
    }
}

struct ModeConstrs(Vec<ModeLteConstr>);

impl ModeConstrs {
    fn add_lte(&mut self, a: ModeParam, b: ModeParam) {
        self.0.push(ModeLteConstr(a, b));
    }

    fn add_eq(&mut self, a: ModeParam, b: ModeParam) {
        self.add_lte(a, b);
        self.add_lte(b, a);
    }
}

fn zero_counts<I: Id, J: Id>() -> (Count<I>, Count<J>) {
    (Count::new(), Count::new())
}

fn add_counts<I: Id>(a: Count<I>, b: Count<I>) -> Count<I> {
    Count::from_value(a.to_value() + b.to_value())
}

fn add_counts2<I: Id, J: Id>(
    a: (Count<I>, Count<J>),
    b: (Count<I>, Count<J>),
) -> (Count<I>, Count<J>) {
    (add_counts(a.0, b.0), add_counts(a.1, b.1))
}

fn count_params(
    customs: &IdMap<CustomTypeId, annot::CustomTypeDef>,
    t: &anon::Type,
) -> (Count<ModeParam>, Count<LtParam>) {
    match t {
        anon::Type::Bool => zero_counts(),
        anon::Type::Num(_) => zero_counts(),
        anon::Type::Tuple(ts) => ts
            .iter()
            .map(|t| count_params(customs, t))
            .fold(zero_counts(), add_counts2),
        anon::Type::Variants(ts) => ts
            .values()
            .map(|t| count_params(customs, t))
            .fold(zero_counts(), add_counts2),
        anon::Type::Custom(id) => match customs.get(id) {
            Some(typedef) => (typedef.num_mode_params, typedef.num_lt_params),
            // This is a typedef in the same SCC; the reference to it here contributes no additional
            // parameters to the entire SCC.
            None => zero_counts(),
        },
        anon::Type::Array(t) => count_params(customs, t),
        anon::Type::HoleArray(t) => count_params(customs, t),
        anon::Type::Boxed(t) => count_params(customs, t),
    }
}

fn parameterize(
    customs: &IdMap<CustomTypeId, annot::CustomTypeDef>,
    scc_num_mode_params: Count<ModeParam>,
    scc_num_lt_params: Count<LtParam>,
    mode_gen: &mut IdGen<ModeParam>,
    lt_gen: &mut IdGen<LtParam>,
    t: &anon::Type,
) -> annot::Type<ModeParam, LtParam> {
    match t {
        anon::Type::Bool => annot::Type::Bool,
        anon::Type::Num(num_type) => annot::Type::Num(*num_type),
        anon::Type::Tuple(ts) => annot::Type::Tuple(
            ts.iter()
                .map(|t| {
                    parameterize(
                        customs,
                        scc_num_mode_params,
                        scc_num_lt_params,
                        mode_gen,
                        lt_gen,
                        t,
                    )
                })
                .collect(),
        ),
        anon::Type::Variants(ts) => annot::Type::Variants(ts.map_refs(|_, t| {
            parameterize(
                customs,
                scc_num_mode_params,
                scc_num_lt_params,
                mode_gen,
                lt_gen,
                &t,
            )
        })),
        anon::Type::Custom(id) => match customs.get(id) {
            Some(typedef) => {
                let mode_subst =
                    IdVec::from_count_with(typedef.num_mode_params, |_| mode_gen.fresh());
                let lt_subst = IdVec::from_count_with(typedef.num_lt_params, |_| lt_gen.fresh());
                let overlay = IdVec::from_count_with(typedef.num_mode_params, |_| mode_gen.fresh());
                annot::Type::Custom {
                    id: *id,
                    mode_subst,
                    lt_subst,
                    overlay: Overlay::Custom(overlay),
                }
            }
            // This is a typedef in the same SCC, so we need to parameterize it by all the SCC parameters.
            None => {
                let mode_subst = IdVec::from_count_with(scc_num_mode_params, |id| id);
                let lt_subst = IdVec::from_count_with(scc_num_lt_params, |id| id);
                let overlay = IdVec::from_count_with(scc_num_mode_params, |id| id);
                annot::Type::Custom {
                    id: *id,
                    mode_subst,
                    lt_subst,
                    overlay: Overlay::Custom(overlay),
                }
            }
        },
        anon::Type::Array(t) => {
            let content = parameterize(
                customs,
                scc_num_mode_params,
                scc_num_lt_params,
                mode_gen,
                lt_gen,
                t,
            );
            annot::Type::Array {
                content: Box::new(content),
                mode: ModeTerm::var(mode_gen.fresh()),
                lt: Lt::var(lt_gen.fresh()),
                overlay: Overlay::Managed(mode_gen.fresh()),
            }
        }
        anon::Type::HoleArray(t) => {
            let content = parameterize(
                customs,
                scc_num_mode_params,
                scc_num_lt_params,
                mode_gen,
                lt_gen,
                t,
            );
            annot::Type::HoleArray {
                content: Box::new(content),
                mode: ModeTerm::var(mode_gen.fresh()),
                lt: Lt::var(lt_gen.fresh()),
                overlay: Overlay::Managed(mode_gen.fresh()),
            }
        }
        anon::Type::Boxed(t) => {
            let content = parameterize(
                customs,
                scc_num_mode_params,
                scc_num_lt_params,
                mode_gen,
                lt_gen,
                t,
            );
            annot::Type::Boxed {
                content: Box::new(content),
                mode: ModeTerm::var(mode_gen.fresh()),
                lt: Lt::var(lt_gen.fresh()),
                overlay: Overlay::Managed(mode_gen.fresh()),
            }
        }
    }
}

fn parameterize_custom_scc(
    typedefs: &IdVec<CustomTypeId, flat::CustomTypeDef>,
    parameterized: &IdMap<CustomTypeId, annot::CustomTypeDef>,
    scc: &Scc<CustomTypeId>,
) -> BTreeMap<CustomTypeId, annot::CustomTypeDef> {
    let (num_mode_params, num_lt_params) = scc
        .iter()
        .map(|id| count_params(parameterized, &typedefs[*id].content))
        .fold(zero_counts(), add_counts2);

    let mut mode_gen = IdGen::new();
    let mut lt_gen = IdGen::new();
    let to_populate = scc
        .iter()
        .map(|id| {
            (
                *id,
                annot::CustomTypeDef {
                    num_mode_params,
                    num_lt_params,
                    content: parameterize(
                        parameterized,
                        num_mode_params,
                        num_lt_params,
                        &mut mode_gen,
                        &mut lt_gen,
                        &typedefs[*id].content,
                    ),
                },
            )
        })
        .collect();

    debug_assert_eq!(num_mode_params, mode_gen.count());
    debug_assert_eq!(num_lt_params, lt_gen.count());
    to_populate
}

fn parameterize_customs(customs: &flat::CustomTypes) -> IdVec<CustomTypeId, annot::CustomTypeDef> {
    let mut parameterized = IdMap::new();
    for scc in customs.sccs.values() {
        let to_populate = parameterize_custom_scc(&customs.types, &parameterized, scc);

        debug_assert_eq!(
            to_populate.keys().collect::<BTreeSet<_>>(),
            scc.iter().collect::<BTreeSet<_>>()
        );

        for (id, typedef) in to_populate {
            parameterized.insert(id, typedef);
        }
    }
    parameterized.to_id_vec(customs.types.count())
}

fn add_func_deps(deps: &mut BTreeSet<CustomFuncId>, expr: &flat::Expr) {
    match expr {
        flat::Expr::Local(_) => {}

        flat::Expr::Call(_, other, _) => {
            deps.insert(*other);
        }

        flat::Expr::Branch(_, cases, _) => {
            for (_, body) in cases {
                add_func_deps(deps, body);
            }
        }

        flat::Expr::LetMany(bindings, _) => {
            for (_, rhs) in bindings {
                add_func_deps(deps, rhs);
            }
        }

        _ => {}
    }
}

fn func_dependency_graph(program: &flat::Program) -> Graph<CustomFuncId> {
    Graph {
        edges_out: program.funcs.map_refs(|_, func_def| {
            let mut deps = BTreeSet::new();
            add_func_deps(&mut deps, &func_def.body);
            deps.into_iter().collect()
        }),
    }
}

#[id_type]
struct LtVar(pub usize);

#[id_type]
struct ModeVar(pub usize);

type SolverType = annot::Type<ModeVar, LtVar>;

type SolverExpr = annot::Expr<ModeVar, LtVar>;

#[derive(Clone, Debug)]
struct PendingSig {
    arg: SolverType,
    ret: SolverType,
}

#[derive(Clone, Copy, Debug)]
struct GlobalContext<'a> {
    funcs_annot: &'a IdMap<CustomFuncId, annot::FuncDef>,
    sigs_pending: &'a BTreeMap<CustomFuncId, PendingSig>,
}

fn emit_occur_constrs(
    graph: &mut ConstrGraph,
    scope: annot::Path,
    t_ctx: &SolverType,
    t_fut: &SolverType,
) {
    todo!()
}

fn fresh_unused_type(
    typedefs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    t: &anon::Type,
) -> annot::Type<ModeVar, LtVar> {
    match t {
        anon::Type::Bool => annot::Type::Bool,
        anon::Type::Num(num_type) => annot::Type::Num(*num_type),
        anon::Type::Array(_) => todo!(),
        anon::Type::HoleArray(_) => todo!(),
        anon::Type::Tuple(_) => todo!(),
        anon::Type::Variants(_) => todo!(),
        anon::Type::Boxed(_) => todo!(),
        anon::Type::Custom(_) => todo!(),
    }
}

fn instantiate_expr(
    typedefs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    globals: GlobalContext,
    graph: &mut ConstrGraph,
    scopes: &mut LocalContext<LocalId, annot::Path>,
    locals: &mut LocalContext<LocalId, SolverType>,
    locals_fut: &mut LocalContext<LocalId, SolverType>,
    fut: &SolverType,
    expr: &flat::Expr,
    path: annot::Path,
) -> (SolverExpr, SolverType) {
    match expr {
        flat::Expr::Local(local) => {
            emit_occur_constrs(
                graph,
                scopes.local_binding(*local).clone(),
                locals.local_binding(*local),
                locals_fut.local_binding(*local),
            );
            (
                annot::Expr::Local(*local),
                locals.local_binding(*local).clone(),
            )
        }

        flat::Expr::Call(_, _, _) => todo!(),

        flat::Expr::Branch(discrim, cases, result) => {
            todo!()
        }

        flat::Expr::LetMany(bindings, final_local) => scopes.with_scope(|scopes| {
            locals.with_scope(|locals| {
                locals_fut.with_scope(|locals_fut| {
                    assert!(bindings.len() >= 1);
                    let prefix_len = bindings.len().saturating_sub(1);
                    for (t, _) in &bindings[..prefix_len] {
                        locals_fut.add_local(fresh_unused_type(typedefs, t));
                    }
                    locals_fut.add_local(fut.clone());

                    let end_of_scope = path.push_seq(bindings.len());
                    let bindings_inst = bindings
                        .iter()
                        .enumerate()
                        .rev()
                        .map(|(i, (_t, binding))| {
                            let (binding_inst, binding_t) = instantiate_expr(
                                typedefs,
                                globals,
                                graph,
                                scopes,
                                locals,
                                locals_fut,
                                fut,
                                binding,
                                path.push_seq(i),
                            );
                            scopes.add_local(end_of_scope.clone());
                            locals.add_local(binding_t.clone());
                            locals_fut.pop();
                            (binding_t, binding_inst)
                        })
                        .collect();
                    let expr_inst = annot::Expr::LetMany(bindings_inst, *final_local);
                    let ret_t = locals.local_binding(*final_local).clone();
                    (expr_inst, ret_t)
                })
            })
        }),

        flat::Expr::Tuple(items) => {
            let item_types = items
                .iter()
                .map(|item| locals.local_binding(*item).clone())
                .collect();
            (
                annot::Expr::Tuple(items.clone()),
                annot::Type::Tuple(item_types),
            )
        }

        flat::Expr::TupleField(tup, idx) => {
            let item_type = if let annot::Type::Tuple(item_types) = locals.local_binding(*tup) {
                item_types[*idx].clone()
            } else {
                unreachable!()
            };
            (annot::Expr::TupleField(*tup, *idx), item_type)
        }

        flat::Expr::WrapVariant(_, _, _) => todo!(),

        flat::Expr::UnwrapVariant(_, _) => todo!(),

        flat::Expr::WrapBoxed(_, _) => todo!(),

        flat::Expr::UnwrapBoxed(_, _) => todo!(),

        flat::Expr::WrapCustom(_, _) => todo!(),

        flat::Expr::UnwrapCustom(_, _) => todo!(),

        flat::Expr::Intrinsic(_, _) => todo!(),

        flat::Expr::ArrayOp(_) => todo!(),

        flat::Expr::IoOp(_) => todo!(),

        flat::Expr::Panic(_, _) => todo!(),

        flat::Expr::ArrayLit(_, _) => todo!(),

        flat::Expr::BoolLit(_) => todo!(),

        flat::Expr::ByteLit(_) => todo!(),

        flat::Expr::IntLit(_) => todo!(),

        flat::Expr::FloatLit(_) => todo!(),
    }
}
