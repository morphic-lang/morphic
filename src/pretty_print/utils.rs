use crate::data::first_order_ast as first_ord;
use crate::data::metadata::Metadata;
use crate::data::mono_ast as mono;
use crate::data::tail_rec_ast as tail;
use id_collections::{Id, IdVec};
use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::io::{self, Write};

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
pub struct CustomTypeRenderer<TypeId> {
    table: DisambiguationTable<TypeId>,
}

impl<TypeId: Id> CustomTypeRenderer<TypeId> {
    pub fn from_symbols(custom_type_symbols: &IdVec<TypeId, first_ord::CustomTypeSymbols>) -> Self {
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

    pub fn render(&self, custom_type: impl Borrow<TypeId>) -> String {
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

fn first_ord_def_name(symbols: &first_ord::FuncSymbols) -> String {
    match symbols {
        first_ord::FuncSymbols::Global(mono_symbols) => {
            format!("{}.const", mono_def_name(mono_symbols))
        }

        first_ord::FuncSymbols::Lam(lam_symbols) => mono_def_name(&lam_symbols.lifted_from),

        first_ord::FuncSymbols::MainWrapper => "main_wrapper".to_owned(),

        first_ord::FuncSymbols::Dispatch => "dispatch".to_owned(),
    }
}

impl<FuncId: Id + Ord> FuncRenderer<FuncId> {
    pub fn from_symbols(func_symbols: &IdVec<FuncId, first_ord::FuncSymbols>) -> Self {
        let mut table = DisambiguationTable::new();

        for (id, symbols) in func_symbols {
            table.register(id, BaseName(first_ord_def_name(symbols)));
        }

        FuncRenderer { table }
    }

    pub fn render(&self, func: impl Borrow<FuncId>) -> String {
        let (BaseName(base_name), suffix) = self.table.get_name(func);
        debug_assert!(base_name.find(|c: char| c.is_whitespace()).is_none());
        format!("{}#{}", base_name, suffix)
    }
}

#[derive(Clone, Debug)]
pub struct TailFuncRenderer<FuncId> {
    table: DisambiguationTable<FuncId>,
}

impl<FuncId: Id + Ord> TailFuncRenderer<FuncId> {
    pub fn from_symbols(func_symbols: &IdVec<FuncId, tail::TailFuncSymbols>) -> Self {
        let mut table = DisambiguationTable::new();

        for (id, symbols) in func_symbols {
            let base_name = match symbols {
                tail::TailFuncSymbols::Acyclic(symbols) => BaseName(first_ord_def_name(symbols)),

                tail::TailFuncSymbols::Cyclic => BaseName("cyclic".to_owned()),
            };

            table.register(id, base_name);
        }

        TailFuncRenderer { table }
    }

    pub fn render(&self, func: impl Borrow<FuncId>) -> String {
        let (BaseName(base_name), suffix) = self.table.get_name(func);
        debug_assert!(base_name.find(|c: char| c.is_whitespace()).is_none());
        format!("{}#{}", base_name, suffix)
    }
}

/// Pretty print a metadata block. This function inserts a newline before, but not after, the
/// metadata because it may print nothing at all.
pub fn write_metadata(w: &mut dyn Write, indent: usize, metadata: &Metadata) -> io::Result<()> {
    for comment in &metadata.comments {
        write!(w, "\n{:indent$}// {}", "", comment, indent = indent)?;
    }
    Ok(())
}

pub fn write_delimited<T, I, J>(
    w: &mut dyn Write,
    elems: J,
    ldelim: &str,
    rdelim: &str,
    sep: &str,
    write_elem: impl Fn(&mut dyn Write, T) -> io::Result<()>,
) -> io::Result<()>
where
    I: ExactSizeIterator<Item = T>,
    J: IntoIterator<Item = T, IntoIter = I>,
{
    let mut elems = elems.into_iter();
    let len = elems.len();
    if len == 0 {
        write!(w, "{ldelim}{rdelim}")
    } else if len == 1 {
        write!(w, "{ldelim}")?;
        write_elem(w, elems.next().unwrap())?;
        write!(w, "{rdelim}")
    } else {
        write!(w, "{ldelim}")?;
        for _ in 0..len - 1 {
            let elem = elems.next().unwrap();
            write_elem(w, elem)?;
            write!(w, "{sep}")?;
        }
        write_elem(w, elems.next().unwrap())?;
        write!(w, "{rdelim}")
    }
}
