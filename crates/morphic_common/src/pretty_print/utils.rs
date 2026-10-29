use crate::config::MlVariant;
use crate::data::first_order_ast as first_ord;
use crate::data::metadata::Metadata;
use crate::data::mono_ast as mono;
use crate::data::num_type::{NumLit, NumType};
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

/// Writes a number literal as the IR dumps spell it: a `U8` as its character, an `I64` or `F64`
/// bare, and any other type with its name as a suffix.
pub fn write_num_lit(w: &mut dyn Write, lit: NumLit) -> io::Result<()> {
    match lit {
        NumLit::I8(val) => write!(w, "{}i8", val),
        NumLit::I16(val) => write!(w, "{}i16", val),
        NumLit::I32(val) => write!(w, "{}i32", val),
        NumLit::I64(val) => write!(w, "{}", val),
        NumLit::U8(val) => write!(w, "{:?}", val as char),
        NumLit::U16(val) => write!(w, "{}u16", val),
        NumLit::U32(val) => write!(w, "{}u32", val),
        NumLit::U64(val) => write!(w, "{}u64", val),
        NumLit::F32(val) => write!(w, "{}f32", val),
        NumLit::F64(val) => write!(w, "{}", val),
    }
}

/// The ML type that a number type compiles to, which the preludes' intrinsics are written
/// against.  OCaml has no unsigned or narrow integers, so `I8`, `I16` and `U16` are `int`s and
/// `U32` and `U64` are the bit patterns of an `int32` and an `int64`, and it has no 32-bit
/// float, so `F32` widens to `float`.
pub fn ml_num_type_name(variant: MlVariant, num_type: NumType) -> &'static str {
    match variant {
        MlVariant::OCaml => match num_type {
            NumType::I8 | NumType::I16 | NumType::U16 => "int",
            NumType::I32 | NumType::U32 => "int32",
            NumType::I64 | NumType::U64 => "int64",
            NumType::U8 => "char",
            NumType::F32 | NumType::F64 => "float",
        },
        MlVariant::Sml => match num_type {
            NumType::I8 => "Int8.int",
            NumType::I16 => "Int16.int",
            NumType::I32 => "Int32.int",
            NumType::I64 => "int",
            NumType::U8 => "char",
            NumType::U16 => "Word16.word",
            NumType::U32 => "Word32.word",
            NumType::U64 => "Word64.word",
            NumType::F32 => "Real32.real",
            NumType::F64 => "real",
        },
    }
}

/// Whether the OCaml spelling of a literal begins with a minus sign.  OCaml reads such a literal
/// as a prefix negation, which binds looser than an application does, so as an argument it needs
/// parentheses: `f (-1l)`, where `f -1l` is a subtraction.
pub fn ocaml_num_lit_is_negative(lit: NumLit) -> bool {
    match lit {
        NumLit::I8(val) => val < 0,
        NumLit::I16(val) => val < 0,
        NumLit::I32(val) => val < 0,
        NumLit::I64(val) => val < 0,
        NumLit::U8(_) | NumLit::U16(_) => false,
        // A `U32` or `U64` is spelled as the signed value with its bit pattern.
        NumLit::U32(val) => (val as i32) < 0,
        NumLit::U64(val) => (val as i64) < 0,
        NumLit::F32(val) => val.is_sign_negative(),
        NumLit::F64(val) => val.is_sign_negative(),
    }
}
