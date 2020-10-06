//! This module defines an AST for internal use within RC elision, in which functions may have
//! multiple "analysis versions," specialized with respect to (relevant subsets of) the aliasing and
//! mutation flags in their signatures.  This allows us to perform RC elision in the presence of
//! *concrete* aliasing graphs, rather than symbolic alias summaries.

use std::collections::BTreeMap;

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::mutation_annot_ast as mutation;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::event_set as event;
use crate::util::id_vec::IdVec;

id_type!(pub FuncVersionId);

/// The total order on this type is meaningful, with NoAlias < MayAlias.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConcreteAlias {
    NoAlias,
    MayAlias,
}

/// The total order on this type is meaningful, with NotUsed < MaybeUsed
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RetFate {
    NotUsed,
    MaybeUsed,
}

#[derive(Clone, Debug)]
pub struct FuncVersion {
    pub calls: IdVec<fate::CallId, (first_ord::CustomFuncId, FuncVersionId)>,
    pub aliases: BTreeMap<alias::AliasCondition, ConcreteAlias>,
    pub ret_fate: BTreeMap<alias::RetName, RetFate>,
}

#[derive(Clone, Debug)]
pub struct FuncDef {
    pub purity: Purity,
    pub arg_type: anon::Type,
    pub ret_type: anon::Type,
    pub alias_sig: alias::AliasSig,
    pub mutation_sig: mutation::MutationSig,
    pub arg_fate: BTreeMap<alias::ArgName, fate::ArgFieldFate>,
    // Every function's body occurs in a scope with exactly one free variable with index 0, holding
    // the argument.
    pub body: fate::Expr,
    pub occur_fates: IdVec<fate::OccurId, fate::Fate>,
    pub expr_annots: IdVec<fate::ExprId, fate::ExprAnnot>,
    pub let_block_end_events: IdVec<fate::LetBlockId, event::Horizon>,
    pub branch_block_end_events: IdVec<fate::BranchBlockId, event::Horizon>,
    pub versions: IdVec<FuncVersionId, FuncVersion>,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: IdVec<first_ord::CustomTypeId, anon::Type>,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<first_ord::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: first_ord::CustomFuncId,
}
