use std::borrow::Borrow;
use std::collections::BTreeMap;

use crate::data::first_order_ast as first_ord;
use crate::data::mono_ast as mono;
use crate::data::repr_specialized_ast as special;
use id_collections::{Id, IdVec};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct BaseName(String);

#[derive(Clone, Debug)]
struct DisambiguationTable<NameId> {
    name_counters: BTreeMap<BaseName, usize>,
    names_and_suffixes: BTreeMap<NameId, (BaseName, usize)>,
}

impl<NameId: Ord> DisambiguationTable<NameId> {
    fn new() -> Self {
        DisambiguationTable {
            name_counters: BTreeMap::new(),
            names_and_suffixes: BTreeMap::new(),
        }
    }

    fn register(&mut self, id: NameId, base_name: BaseName) {
        debug_assert!(!self.names_and_suffixes.contains_key(&id));
        let counter = self.name_counters.entry(base_name.clone()).or_insert(0);
        let suffix = *counter;
        *counter += 1;
        self.names_and_suffixes.insert(id, (base_name, suffix));
    }

    fn get_name(&self, id: impl Borrow<NameId>) -> &(BaseName, usize) {
        &self.names_and_suffixes[id.borrow()]
    }
}

#[derive(Clone, Debug)]
pub struct CustomTypeRenderer {
    table: DisambiguationTable<special::CustomTypeId>,
}

impl CustomTypeRenderer {
    pub fn from_symbols(
        custom_type_symbols: &IdVec<special::CustomTypeId, first_ord::CustomTypeSymbols>,
    ) -> Self {
        let mut table = DisambiguationTable::new();

        for (id, symbols) in custom_type_symbols {
            let base_name = match symbols {
                first_ord::CustomTypeSymbols::CustomType(custom) => {
                    BaseName(custom.type_name.0.clone())
                }

                first_ord::CustomTypeSymbols::ClosureType => BaseName("Closure".to_owned()),
            };

            table.register(id, base_name);
        }

        CustomTypeRenderer { table }
    }

    pub fn render(&self, custom_type: impl Borrow<special::CustomTypeId>) -> String {
        let (BaseName(base_name), suffix) = self.table.get_name(custom_type);
        debug_assert!(base_name.find(|c: char| c.is_whitespace()).is_none());
        format!("{}~{}", base_name, suffix)
    }
}

#[derive(Clone, Debug)]
pub struct FuncRenderer<FuncId> {
    table: DisambiguationTable<FuncId>,
}

fn mono_def_name(symbols: &mono::ValSymbols) -> String {
    match symbols {
        mono::ValSymbols::Wrapper(inner) => format!("{}.wrapper", inner.val_name.0),

        mono::ValSymbols::Normal(inner) => inner.val_name.0.clone(),
    }
}

impl<FuncId: Id + Ord> FuncRenderer<FuncId> {
    pub fn from_symbols(func_symbols: &IdVec<FuncId, first_ord::FuncSymbols>) -> Self {
        let mut table = DisambiguationTable::new();

        for (id, symbols) in func_symbols {
            let base_name = match symbols {
                first_ord::FuncSymbols::Global(mono_symbols) => {
                    BaseName(format!("{}.const", mono_def_name(mono_symbols)))
                }

                first_ord::FuncSymbols::Lam(lam_symbols) => {
                    BaseName(mono_def_name(&lam_symbols.lifted_from))
                }

                first_ord::FuncSymbols::MainWrapper => BaseName("main_wrapper".to_owned()),

                first_ord::FuncSymbols::Dispatch => BaseName("dispatch".to_owned()),
            };

            table.register(id, base_name);
        }

        FuncRenderer { table }
    }

    pub fn render(&self, func: impl Borrow<FuncId>) -> String {
        let (BaseName(base_name), suffix) = self.table.get_name(func);
        debug_assert!(base_name.find(|c: char| c.is_whitespace()).is_none());
        format!("{}#{}", base_name, suffix)
    }
}
