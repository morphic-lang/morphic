use im_rc::Vector;
use std::collections::BTreeMap;

use crate::data::alias_annot_ast as alias;
use crate::data::alias_specialized_ast as spec;
use crate::data::anon_sum_ast as anon;
use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as mutation;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::util::id_vec::IdVec;
use crate::util::inequality_graph::{ExternalVarId, Infimum, UpperBound};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum StackField {
    Field(usize),
    Variant(first_ord::VariantId),
    // Including 'CustomScc' in stack paths doesn't actually achieve much for RC elision, but it's
    // convenient for compatibility with the path format used for alias analysis.
    CustomScc(flat::CustomTypeSccId, first_ord::CustomTypeId),
    Custom(first_ord::CustomTypeId),
}

pub type StackPath = Vector<StackField>;

/// The ordering for modes is meaningful, and encodes a *subtyping relation* where owned values can
/// be converted to borrowed values, but not vice versa.  In other words, Owned < Borrowed.
///
/// Note that this is in some sense the opposite of the ordering convention used for superficially
/// similar flags elsewhere in the compiler.  Here, "greater is better", in the sense that borrowed
/// values achieve better runtime performance than owned values, and "lesser is more conservative",
/// in the sense that we could (roughly speaking) safely set the mode of every variable in the
/// program to `Owned` without affecting correctness.  Elsewhere in the compiler, the convention is
/// the other way around; in other analyses, "lesser is better", and "greater is more conservative".
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    Owned,
    Borrowed,
}

impl Infimum for Mode {
    fn min_mut(&mut self, other: &Self) {
        *self = (*self).min(*other);
    }

    fn greatest() -> Self {
        Mode::Borrowed
    }
}

#[derive(Clone, Debug)]
pub enum PathOccurMode {
    /// Represents a non-moving occurrence of a (path within a) variable, prior to its final move
    /// (or drop).
    ///
    /// After monomorphization with respect to modes:
    /// - When `src` is `Owned` and `dest` is `Borrowed`, an intermediate occurrence is a no-op.
    /// - When `src` is `Borrowed` and `dest` is `Borrowed`, an intermediate occurrence is a no-op.
    /// - When `src` is `Owned` and `dest` is `Owned`, an intermediate occurrence is a retain.
    /// - It is impossible for `src` to be `Borrowed` when `dest` is `Owned`.
    Intermediate {
        // Invariant: `src <= dest` (in symbolic constraint graph, not literally as Rust values)
        src: UpperBound<Mode>,
        dest: UpperBound<Mode>,
    },

    /// Represents a moving occurrence of a variable.  Every variable (or more accurately, every
    /// path within a variable) should have exactly one moving occurrence along each control flow
    /// path.  Drops count as moving occurrences.
    ///
    /// This always compiles to a no-op.
    Final,

    /// Unused occurrences should only occur strictly after moving occurrences.
    ///
    /// Intermediate occurrences should only occur strictly *before* moving occurrences.
    ///
    /// This always compiles to a no-op.
    Unused,
}

#[derive(Clone, Debug)]
pub struct OccurModes {
    pub path_modes: BTreeMap<StackPath, PathOccurMode>,
}

/// Represents an operation in which a subset of a value's paths are dropped, and the modes of those
/// dropped paths.
///
/// After monomorphization with respect to modes:
/// - When an `Owned` path is dropped, this compiles to a release.
/// - When a `Borrowed` path is dropped, this compiles to a no-op.
///
/// A drop counts as a move for the purposes of enforcing the constraint that every variable is
/// moved exactly once along each control flow path.
#[derive(Clone, Debug)]
pub struct DropModes {
    pub dropped_paths: BTreeMap<StackPath, UpperBound<Mode>>,
}

/// Represents an operation in which a subset of a value's paths might be retained, conditional on
/// the modes of those paths.
///
/// After monomorphization with respect to modes:
/// - When an `Owned` path appears, this compiles to a retain.
/// - When a `Borrowed` path appears, this compiles to a no-op.
#[derive(Clone, Debug)]
pub struct RetainModes {
    pub retained_paths: BTreeMap<StackPath, UpperBound<Mode>>,
}

#[derive(Clone, Debug)]
pub struct ModeAnnots {
    pub extern_constraints: IdVec<ExternalVarId, UpperBound<Mode>>,
    pub arg_modes: BTreeMap<alias::FieldPath, ExternalVarId>,
    pub ret_modes: BTreeMap<alias::FieldPath, ExternalVarId>,

    pub occur_modes: IdVec<fate::OccurId, OccurModes>,
    pub call_modes: IdVec<fate::CallId, IdVec<ExternalVarId, UpperBound<Mode>>>,

    /// Drop epilogues are used to drop otherwise-unmoved expressions at the end of a let block or
    /// branch arm.
    pub let_drop_epilogues: IdVec<fate::LetBlockId, Vec<(flat::LocalId, DropModes)>>,
    pub branch_drop_epilogues: IdVec<fate::BranchBlockId, Vec<(flat::LocalId, DropModes)>>,

    /// Drop epilogue for the argument at the end of the function body.
    pub arg_drop_epilogue: DropModes,

    /// Drop prologues are used to proactively drop otherwise-unmoved variables before mutating
    /// operations which could potentially invalidate them.
    pub drop_prologues: IdVec<fate::ExprId, Vec<(flat::LocalId, DropModes)>>,

    /// Retain epilogues are used to retain items obtained from 'get' operations on containers (e.g.
    /// `UnwrapBoxed`).
    pub retain_epilogues: IdVec<fate::RetainPointId, RetainModes>,
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
    pub versions: IdVec<spec::FuncVersionId, spec::FuncVersion>,
    pub modes: IdVec<spec::FuncVersionId, ModeAnnots>,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: flat::CustomTypes,
    pub custom_type_symbols: IdVec<first_ord::CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<first_ord::CustomFuncId, FuncDef>,
    pub func_symbols: IdVec<first_ord::CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: first_ord::CustomFuncId,
    pub main_version: spec::FuncVersionId,
}
