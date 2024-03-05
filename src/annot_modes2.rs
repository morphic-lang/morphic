use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast::{CustomFuncId, CustomTypeId};
use crate::data::flat_ast::{self as flat, LocalId};
use crate::data::mode_annot_ast2::{
    self as annot, Lt, LtLocal, LtParam, LtVar, ModeConstr, ModeParam, ModeTerm, ModeVar,
    ParamCounts,
};
use crate::util::graph::{self, Scc};
use crate::util::id_gen::IdGen;
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{Count, IdMap, IdVec};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Add;

type SolverType = annot::Type<ModeVar, LtVar>;
type SolverExpr = annot::Expr<ModeVar, LtVar>;
type SigType = annot::Type<ModeParam, LtParam>;
type SigExpr = annot::Expr<ModeParam, LtParam>;

struct ModeConstrGraph {
    // a -> b means a <= b, i.e. if a is owned then b is owned
    inner: graph::Graph<ModeParam>,
    sig: BTreeSet<ModeVar>,
}

impl ModeConstrGraph {
    fn new() -> Self {
        Self {
            inner: graph::Graph {
                edges_out: IdVec::new(),
            },
            sig: BTreeSet::new(),
        }
    }

    fn add_constr(&mut self, constr: ModeConstr) {
        self.inner.edges_out[constr.0].push(constr.1);
    }

    fn mark_external(&mut self, var: ModeVar) {
        self.sig.insert(var);
    }

    fn find_lower_bounds(&self) -> IdVec<ModeVar, ModeTerm<ModeVar>> {
        let sccs = graph::acyclic_and_cyclic_sccs(&self.inner);

        let mut lower_bounds = IdMap::new();
        for scc in &sccs {
            todo!()
        }

        let len = lower_bounds.len();
        lower_bounds.to_id_vec(Count::from_value(len))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Phase {
    Stack,
    CyclicScc,
    Heap,
}

fn count_params(
    parameterized: &IdMap<CustomTypeId, annot::CustomTypeDef>,
    type_: &anon::Type,
    phase: Phase,
) -> annot::ParamCounts {
    let inc_counts = |content_type: &anon::Type| {
        let mut counts = count_params(parameterized, content_type, Phase::Heap);
        match phase {
            Phase::Stack => {
                let _ = counts.stack_mode_count.inc();
            }
            Phase::CyclicScc => {
                let _ = counts.stack_mode_count.inc();
                let _ = counts.storage_mode_count.inc();
                let _ = counts.access_mode_count.inc();
            }
            Phase::Heap => {
                let _ = counts.storage_mode_count.inc();
                let _ = counts.access_mode_count.inc();
            }
        }
        let _ = counts.lt_count.inc();
        counts
    };
    match type_ {
        anon::Type::Bool => Default::default(),
        anon::Type::Num(_) => Default::default(),
        anon::Type::Tuple(types) => types
            .iter()
            .map(|type_| count_params(parameterized, type_, phase))
            .fold(Default::default(), Add::add),
        anon::Type::Variants(types) => types
            .values()
            .map(|type_| count_params(parameterized, type_, phase))
            .fold(Default::default(), Add::add),
        anon::Type::Custom(id) => match parameterized.get(id) {
            Some(typedef) => typedef.num_params,
            // This is a typedef in the same SCC; the reference to it here contributes no additional
            // parameters to the entire SCC.
            None => Default::default(),
        },
        anon::Type::Array(content_type) => inc_counts(content_type),
        anon::Type::HoleArray(content_type) => inc_counts(content_type),
        anon::Type::Boxed(content_type) => inc_counts(content_type),
    }
}

struct ParamGens {
    stack_mode_gen: IdGen<ModeParam>,
    storage_mode_gen: IdGen<ModeParam>,
    access_mode_gen: IdGen<ModeParam>,
    lt_gen: IdGen<LtParam>,
}

impl ParamGens {
    fn new() -> Self {
        Self {
            stack_mode_gen: IdGen::new(),
            storage_mode_gen: IdGen::new(),
            access_mode_gen: IdGen::new(),
            lt_gen: IdGen::new(),
        }
    }

    fn count(&self) -> ParamCounts {
        ParamCounts {
            stack_mode_count: self.stack_mode_gen.count(),
            storage_mode_count: self.storage_mode_gen.count(),
            access_mode_count: self.access_mode_gen.count(),
            lt_count: self.lt_gen.count(),
        }
    }
}

fn parameterize(
    parameterized: &IdMap<CustomTypeId, annot::CustomTypeDef>,
    scc_num_params: ParamCounts,
    id_gens: &mut ParamGens,
    type_: &anon::Type,
    phase: Phase,
) -> SigType {
    let fresh_modes = |id_gens: &mut ParamGens| match phase {
        Phase::Stack => annot::ModeAnnot::Stack {
            stack: ModeTerm::var(id_gens.stack_mode_gen.fresh()),
        },
        Phase::CyclicScc => annot::ModeAnnot::CyclicScc {
            stack: ModeTerm::var(id_gens.stack_mode_gen.fresh()),
            storage: ModeTerm::var(id_gens.storage_mode_gen.fresh()),
            access: ModeTerm::var(id_gens.access_mode_gen.fresh()),
        },
        Phase::Heap => annot::ModeAnnot::Heap {
            storage: ModeTerm::var(id_gens.storage_mode_gen.fresh()),
            access: ModeTerm::var(id_gens.access_mode_gen.fresh()),
        },
    };
    match type_ {
        anon::Type::Bool => annot::Type::Bool,
        anon::Type::Num(num_type) => annot::Type::Num(*num_type),
        anon::Type::Tuple(types) => annot::Type::Tuple(
            types
                .iter()
                .map(|type_| parameterize(parameterized, scc_num_params, id_gens, type_, phase))
                .collect(),
        ),
        anon::Type::Variants(types) => annot::Type::Variants(types.map_refs(|_, type_| {
            parameterize(parameterized, scc_num_params, id_gens, type_, phase)
        })),
        anon::Type::Custom(id) => match parameterized.get(id) {
            Some(typedef) => {
                let stack_mode_subst =
                    IdVec::from_count_with(typedef.num_params.stack_mode_count, |_| {
                        id_gens.stack_mode_gen.fresh()
                    });
                let storage_mode_subst =
                    IdVec::from_count_with(typedef.num_params.storage_mode_count, |_| {
                        id_gens.storage_mode_gen.fresh()
                    });
                let access_mode_subst =
                    IdVec::from_count_with(typedef.num_params.access_mode_count, |_| {
                        id_gens.access_mode_gen.fresh()
                    });
                let lt_subst =
                    IdVec::from_count_with(typedef.num_params.lt_count, |_| id_gens.lt_gen.fresh());
                annot::Type::Custom {
                    id: *id,
                    stack_mode_subst,
                    storage_mode_subst,
                    access_mode_subst,
                    lt_subst,
                }
            }
            // This is a typedef in the same SCC, so we need to parameterize it by all the SCC parameters.
            None => {
                let stack_mode_subst =
                    IdVec::from_count_with(scc_num_params.stack_mode_count, |id| id);
                let storage_mode_subst =
                    IdVec::from_count_with(scc_num_params.storage_mode_count, |id| id);
                let access_mode_subst =
                    IdVec::from_count_with(scc_num_params.access_mode_count, |id| id);
                let lt_subst = IdVec::from_count_with(scc_num_params.lt_count, |id| id);
                annot::Type::Custom {
                    id: *id,
                    stack_mode_subst,
                    storage_mode_subst,
                    access_mode_subst,
                    lt_subst,
                }
            }
        },
        anon::Type::Array(content_type) => {
            let content_type = parameterize(
                parameterized,
                scc_num_params,
                id_gens,
                content_type,
                Phase::Heap,
            );
            annot::Type::Array(
                Box::new(content_type),
                fresh_modes(id_gens),
                id_gens.lt_gen.fresh(),
            )
        }
        anon::Type::HoleArray(content_type) => {
            let content_type = parameterize(
                parameterized,
                scc_num_params,
                id_gens,
                content_type,
                Phase::Heap,
            );
            annot::Type::HoleArray(
                Box::new(content_type),
                fresh_modes(id_gens),
                id_gens.lt_gen.fresh(),
            )
        }
        anon::Type::Boxed(content_type) => {
            let content_type = parameterize(
                parameterized,
                scc_num_params,
                id_gens,
                content_type,
                Phase::Heap,
            );
            annot::Type::Boxed(
                Box::new(content_type),
                fresh_modes(id_gens),
                id_gens.lt_gen.fresh(),
            )
        }
    }
}

fn parameterize_custom_scc(
    typedefs: &IdVec<CustomTypeId, flat::CustomTypeDef>,
    parameterized: &IdMap<CustomTypeId, annot::CustomTypeDef>,
    scc: &Scc<CustomTypeId>,
) -> BTreeMap<CustomTypeId, annot::CustomTypeDef> {
    let phase = match scc {
        Scc::Acyclic(_) => Phase::Stack,
        Scc::Cyclic(_) => Phase::CyclicScc,
    };

    let num_params: ParamCounts = scc
        .iter()
        .map(|id| count_params(parameterized, &typedefs[*id].content, phase))
        .fold(Default::default(), Add::add);

    let mut id_gens = ParamGens::new();
    let to_populate = scc
        .iter()
        .map(|id| {
            (
                *id,
                annot::CustomTypeDef {
                    num_params,
                    content: parameterize(
                        parameterized,
                        num_params,
                        &mut id_gens,
                        &typedefs[*id].content,
                        phase,
                    ),
                },
            )
        })
        .collect();

    debug_assert_eq!(num_params, id_gens.count());
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

fn constrain_modes(
    def_ctx: &IdMap<CustomFuncId, annot::FuncDef>,
    type_ctx: &mut LocalContext<LocalId, SolverType>,
    scope_ctx: &mut LocalContext<LocalId, Lt>,
    path: &mut LtLocal,
    expr: &flat::Expr,
    fut_type: &mut SolverType,
    constrs: &mut Vec<ModeConstr>,
) -> SolverExpr {
    todo!()
}

pub fn annot_modes(program: flat::Program, progress: impl ProgressLogger) -> annot::Program {
    let progress = progress.start_session(None);
    progress.finish();
    todo!()
}
