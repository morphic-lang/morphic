use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::id::ToPrimIntUnchecked;
use id_collections::{Count, Id, IdMap, IdVec};
use id_graph_sccs::{Scc, SccKind};
use std::collections::BTreeMap;

pub trait Signature {
    type Sig;
    fn signature(&self) -> &Self::Sig;
}

#[derive(Clone, Debug)]
pub struct SignatureAssumptions<'a, FuncId: Id + Ord, FuncDef: Signature> {
    known_defs: &'a IdMap<FuncId, FuncDef>,
    provisional_defs: Option<&'a BTreeMap<FuncId, FuncDef>>,
}

impl<'a, FuncId: Id + Ord, FuncDef: Signature> SignatureAssumptions<'a, FuncId, FuncDef> {
    pub fn sig_of(&self, func: &FuncId) -> Option<&'a FuncDef::Sig> {
        if let Some(func_def) = &self.known_defs.get(func) {
            return Some(func_def.signature());
        }
        if let Some(provisional_defs) = &self.provisional_defs {
            return Some(provisional_defs[func].signature());
        }
        None
    }
}

pub fn iterate_fixed_point<FuncId, FuncDef>(
    known_defs: &IdMap<FuncId, FuncDef>,
    annot_func: impl for<'a> Fn(&'a SignatureAssumptions<'a, FuncId, FuncDef>, &'a FuncId) -> FuncDef,
    scc: &Scc<FuncId>,
) -> BTreeMap<FuncId, FuncDef>
where
    FuncId: Id + Ord,
    FuncDef: Signature,
    FuncDef::Sig: Eq,
{
    match scc.kind {
        SccKind::Acyclic => {
            // This SCC consists of a single non-recursive function, which means that as a
            // performance optimization we can get away with only performing a single iteration of
            // abstract interpretation.

            let func = scc.nodes[0];

            let annotated_func_def = annot_func(
                &SignatureAssumptions {
                    known_defs,
                    provisional_defs: Some(&BTreeMap::new()),
                },
                &func,
            );

            let mut result = BTreeMap::new();
            result.insert(func.clone(), annotated_func_def);
            result
        }

        SccKind::Cyclic => {
            // This SCC consists of one or more (mutually) recursive functions, so we need to do the
            // full iterative fixed point computation.

            let mut defs = scc
                .nodes
                .iter()
                .map(|func| {
                    (
                        func.clone(),
                        annot_func(
                            &SignatureAssumptions {
                                known_defs,
                                provisional_defs: None,
                            },
                            func,
                        ),
                    )
                })
                .collect::<BTreeMap<_, _>>();

            loop {
                let mut prev_defs = BTreeMap::new();

                for func in scc.nodes {
                    let annotated_func_def = annot_func(
                        &SignatureAssumptions {
                            known_defs,
                            provisional_defs: Some(&defs),
                        },
                        func,
                    );
                    let prev_func_def = defs.insert(func.clone(), annotated_func_def).unwrap();
                    prev_defs.insert(func.clone(), prev_func_def);
                }

                if scc
                    .nodes
                    .iter()
                    .all(|func| defs[func].signature() == prev_defs[func].signature())
                {
                    return defs;
                }
            }
        }
    }
}

pub fn annot_all<FuncId, FuncDef, P: ProgressLogger>(
    func_count: Count<FuncId>,
    annot_func: impl for<'a> Fn(&'a SignatureAssumptions<'a, FuncId, FuncDef>, &'a FuncId) -> FuncDef,
    sccs: &[Scc<FuncId>],
    progress_logger: P,
) -> IdVec<FuncId, FuncDef>
where
    FuncId: Id + Ord,
    FuncDef: Signature,
    FuncDef::Sig: Eq,
{
    let mut annotated = IdMap::new();
    let num_funcs = func_count.to_value().to_usize_unchecked();
    let mut progress = progress_logger.start_session(Some(num_funcs));

    for scc in sccs {
        let annotated_defs = iterate_fixed_point(&annotated, &annot_func, scc);
        let def_count = annotated_defs.len();
        for (func, annotated_def) in annotated_defs {
            annotated.insert_vacant(func, annotated_def);
        }
        progress.update(def_count);
    }

    progress.finish();
    annotated.to_id_vec(func_count)
}
