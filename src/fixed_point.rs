use std::collections::BTreeMap;

use crate::util::graph::Scc;
use crate::util::id_type::Id;
use crate::util::id_vec::IdVec;

pub trait Signature {
    type Sig;
    fn signature(&self) -> &Self::Sig;
}

#[derive(Clone, Debug)]
pub struct SignatureAssumptions<'a, FuncId: Id + Ord, FuncDef: Signature> {
    known_defs: &'a IdVec<FuncId, Option<FuncDef>>,
    provisional_defs: Option<&'a BTreeMap<FuncId, FuncDef>>,
}

impl<'a, FuncId: Id + Ord, FuncDef: Signature> SignatureAssumptions<'a, FuncId, FuncDef> {
    pub fn sig_of(&self, func: &FuncId) -> Option<&'a FuncDef::Sig> {
        if let Some(func_def) = &self.known_defs[func] {
            Some(func_def.signature())
        } else if let Some(provisional_defs) = &self.provisional_defs {
            Some(provisional_defs[func].signature())
        } else {
            None
        }
    }
}

pub fn iterate_fixed_point<FuncId, FuncDef>(
    known_defs: &IdVec<FuncId, Option<FuncDef>>,
    annot_func: impl for<'a> Fn(&'a SignatureAssumptions<'a, FuncId, FuncDef>, &'a FuncId) -> FuncDef,
    scc: &Scc<FuncId>,
) -> BTreeMap<FuncId, FuncDef>
where
    FuncId: Id + Ord,
    FuncDef: Signature,
    FuncDef::Sig: Eq,
{
    match scc {
        Scc::Acyclic(func) => {
            // This SCC consists of a single non-recursive function, which means that as a
            // performance optimization we can get away with only performing a single iteration of
            // abstract interpretation.

            let annotated_func_def = annot_func(
                &SignatureAssumptions {
                    known_defs,
                    provisional_defs: Some(&BTreeMap::new()),
                },
                func,
            );

            let mut result = BTreeMap::new();
            result.insert(func.clone(), annotated_func_def);
            result
        }

        Scc::Cyclic(funcs) => {
            // This SCC consists of one or more (mutually) recursive functions, so we need to do the
            // full iterative fixed point computation.

            let mut defs = funcs
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
                let iterated_defs = funcs
                    .iter()
                    .map(|func| {
                        (
                            func.clone(),
                            annot_func(
                                &SignatureAssumptions {
                                    known_defs,
                                    provisional_defs: Some(&defs),
                                },
                                func,
                            ),
                        )
                    })
                    .collect::<BTreeMap<_, _>>();

                if funcs
                    .iter()
                    .all(|func| iterated_defs[func].signature() == defs[func].signature())
                {
                    return iterated_defs;
                }

                defs = iterated_defs;
            }
        }
    }
}

pub fn annot_all<FuncId, FuncDef>(
    num_funcs: usize,
    annot_func: impl for<'a> Fn(&'a SignatureAssumptions<'a, FuncId, FuncDef>, &'a FuncId) -> FuncDef,
    sccs: &[Scc<FuncId>],
) -> IdVec<FuncId, FuncDef>
where
    FuncId: Id + Ord,
    FuncDef: Signature,
    FuncDef::Sig: Eq,
{
    let mut annotated = IdVec::from_items((0..num_funcs).map(|_| None).collect());

    for scc in sccs {
        let annotated_defs = iterate_fixed_point(&annotated, &annot_func, scc);

        for (func, annotated_def) in annotated_defs {
            debug_assert!(annotated[&func].is_none());
            annotated[func] = Some(annotated_def);
        }
    }

    annotated.into_mapped(|_, func_def| func_def.unwrap())
}
