use super::constrain;
use super::mid_ast;
use super::unify::{self, ExprId};
use crate::annot_aliases::{FieldId, FieldPath, UniqueInfo};
use crate::util::constraint_graph::SolverVarId;
use im_rc::{vector, Vector};
use std::collections::{BTreeMap, BTreeSet};

pub type Name = (ExprId, FieldPath);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LastAccessTree {
    expr_id: ExprId,
    rest: BTreeMap<
        usize, // index into branch list of Match
        LastAccessTree,
    >,
}
impl LastAccessTree {
    fn singleton(ctx: &[(ExprId, usize)], final_expr_id: ExprId) -> Self {
        if ctx.len() == 0 {
            LastAccessTree {
                expr_id: final_expr_id,
                rest: BTreeMap::new(),
            }
        } else if ctx.len() == 1 {
            let mut rest = BTreeMap::new();
            rest.insert(
                ctx[0].1,
                LastAccessTree {
                    expr_id: final_expr_id,
                    rest: BTreeMap::new(),
                },
            );
            LastAccessTree {
                expr_id: ctx[0].0,
                rest,
            }
        } else {
            let mut rest = BTreeMap::new();
            rest.insert(
                ctx[0].1,
                LastAccessTree::singleton(&ctx[1..], final_expr_id),
            );
            LastAccessTree {
                expr_id: ctx[0].0,
                rest,
            }
        }
    }

    /// Returns whether the only access is at arg position.
    fn is_arg(&self) -> bool {
        if self.expr_id == ExprId::ARG {
            assert!(self.rest.is_empty());
            true
        } else {
            false
        }
    }

    /// The set of `LastAccessTree`s form a lattice; `join` computes the join (the
    /// least-upper-bound) of several points in the lattice, i.e. the `LastAccessTree`
    /// describing something that was accessed at every position named in `trees`.
    ///
    /// `trees` is mangled in the process.
    pub fn join(trees: &mut Vec<&LastAccessTree>) -> LastAccessTree {
        assert!(trees.len() > 0);
        let max_expr_id = trees.iter().map(|t| t.expr_id).max().unwrap();
        let mut i = 0;
        while i < trees.len() {
            if trees[i].expr_id < max_expr_id {
                trees.swap_remove(i);
            } else {
                i += 1;
            }
        }
        assert!(trees.len() > 0);
        if trees[0].rest.is_empty() {
            // The referenced ExprId is not a Match statement, so it is the final pointed to
            // All members of `trees` should be equal.
            trees[0].clone()
        } else {
            let mut result = LastAccessTree {
                expr_id: max_expr_id,
                rest: BTreeMap::new(),
            };
            let branches = trees
                .iter()
                .flat_map(|t| t.rest.keys())
                .collect::<BTreeSet<_>>();
            for branch in branches {
                result.rest.insert(
                    *branch,
                    LastAccessTree::join(
                        &mut trees.iter().filter_map(|t| t.rest.get(branch)).collect(),
                    ),
                );
            }
            result
        }
    }

    fn consider_access(&mut self, ctx: &[(ExprId, usize)], final_expr_id: ExprId) {
        let mut tree_node = self;
        for (i, &(expr_id, branch)) in ctx.iter().enumerate() {
            if tree_node.expr_id == expr_id {
                if let Some(tree_from_branch) = tree_node.rest.get_mut(&branch) {
                    tree_node = tree_from_branch;
                } else {
                    // The arguments provided to consider_access do not agree with self
                    // on whether expr_id is a Match statement.
                    unreachable!();
                }
            } else if tree_node.expr_id < expr_id {
                *tree_node = LastAccessTree::singleton(&ctx[i..], final_expr_id);
                return;
            }
        }
        if tree_node.expr_id < final_expr_id {
            *tree_node = LastAccessTree {
                expr_id: final_expr_id,
                rest: BTreeMap::new(),
            };
        }
    }

    pub fn is_used_after(&self, mut ctx: &[(ExprId, usize)], final_expr_id: ExprId) -> bool {
        let mut tree_node = self;
        while let Some((expr_id, branch)) = ctx.first() {
            if *expr_id < tree_node.expr_id {
                return true;
            }
            if *expr_id > tree_node.expr_id {
                return false;
            }
            if let Some(rest) = tree_node.rest.get(branch) {
                tree_node = rest;
                ctx = &ctx[1..];
            } else {
                // The given path disagrees with `self` about whether the
                // current location is a match statement
                unreachable!();
            }
        }
        tree_node.expr_id > final_expr_id
    }

    // TODO: remove code repetition w/ above function
    pub fn is_after(&self, mut ctx: &[(ExprId, usize)], final_expr_id: ExprId) -> bool {
        let mut tree_node = self;
        while let Some((expr_id, branch)) = ctx.first() {
            if *expr_id < tree_node.expr_id {
                return false;
            }
            if *expr_id > tree_node.expr_id {
                return true;
            }
            if let Some(rest) = tree_node.rest.get(branch) {
                tree_node = rest;
                ctx = &ctx[1..];
            } else {
                // The given path disagrees with `self` about whether the
                // current location is a match statement
                unreachable!();
            }
        }
        tree_node.expr_id > final_expr_id
    }
}

struct LastAccessesCursor {
    accesses: Vec<BTreeMap<FieldPath, LastAccessTree>>,
    // The following pairs are (ExprID of match statement, branch index)
    by_expr_id: Vec<Vec<(ExprId, usize)>>, // indexed by ExprId, describes which block that expr id is in
    ctx: Vec<(ExprId, usize)>,
}
impl LastAccessesCursor {
    fn in_branch_scope<F, R>(&mut self, match_expr_id: ExprId, branch_idx: usize, f: F) -> R
    where
        F: FnOnce(&mut LastAccessesCursor) -> R,
    {
        let original_len = self.ctx.len();
        self.ctx.push((match_expr_id, branch_idx));
        let result = f(self);
        self.ctx.truncate(original_len);
        result
    }

    fn consider_access(&mut self, (accessed_expr, accessed_path): &Name, at: ExprId) {
        if let Some(accesses) = self.accesses[accessed_expr.0].get_mut(accessed_path) {
            accesses.consider_access(&self.ctx, at);
        }
    }

    fn append_expr(&mut self, info: BTreeMap<FieldPath, LastAccessTree>) {
        self.accesses.push(info);
        self.by_expr_id.push(self.ctx.clone());
    }

    fn len(&self) -> usize {
        self.accesses.len()
    }

    fn last_expr_id(&self) -> ExprId {
        ExprId(self.len() - 1)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    args_used: BTreeSet<FieldPath>, // fields in argument that are ever used
    ret_aliases: BTreeSet<(FieldPath, FieldPath)>, // aliased paths in return value
}
impl Signature {
    pub fn new() -> Self {
        Signature {
            args_used: BTreeSet::new(),
            ret_aliases: BTreeSet::new(),
        }
    }
}

pub fn initialize_sigs_for_scc<'a>(
    scc_func_ids: impl Iterator<Item = &'a mid_ast::CustomFuncId>,
) -> BTreeMap<mid_ast::CustomFuncId, Signature> {
    scc_func_ids
        .map(|&func_id| (func_id, Signature::new()))
        .collect()
}

#[derive(Clone, Copy, Debug)]
pub struct Context<'a> {
    pub typedefs: &'a [mid_ast::TypeDef<mid_ast::RepParamId>], // indexed by CustomTypeId
    pub unique_infos: &'a [UniqueInfo],                        // indexed by CustomFuncId
    pub alias_sigs: &'a [Option<Signature>],                   // indexed by CustomFuncId
    pub scc_alias_sigs: &'a BTreeMap<mid_ast::CustomFuncId, Signature>,
}

impl<'a> Context<'a> {
    fn alias_sig_for(&self, func_id: mid_ast::CustomFuncId) -> &'a Signature {
        self.alias_sigs[func_id.0]
            .as_ref()
            .unwrap_or(&self.scc_alias_sigs[&func_id])
    }
}

pub fn alias_track_func(
    ctx: Context,
    body: &mid_ast::TypedBlock,
    id: mid_ast::CustomFuncId,
) -> (Signature, constrain::FuncInfo) {
    let mut name_adjacencies = Vec::new();
    let mut name_vars = Vec::new();
    let mut accesses_cursor = LastAccessesCursor {
        accesses: Vec::new(),
        by_expr_id: Vec::new(),
        ctx: Vec::new(),
    };
    // The function argument is expression zero
    initialize_expr(
        ctx.typedefs,
        &mut accesses_cursor,
        &mut name_adjacencies,
        &mut name_vars,
        ExprId::ARG,
        &body.types[0],
    );
    alias_track_block(
        ctx,
        &mut accesses_cursor,
        &mut name_adjacencies,
        &mut name_vars,
        &body,
    );

    let retval_expr_id = ExprId(name_adjacencies.len() - 1);

    // Returning something counts as accessing it
    for field in name_adjacencies[retval_expr_id.0].keys() {
        accesses_cursor.consider_access(&(retval_expr_id, field.clone()), retval_expr_id);
    }

    let retval_aliases = name_adjacencies[retval_expr_id.0]
        .iter()
        .flat_map(|(path, aliases)| {
            aliases.iter().filter_map(move |(expr, other_path)| {
                if *expr == retval_expr_id {
                    // Order them to prevent duplicates
                    Some(sorted_pair(path.clone(), other_path.clone()))
                } else {
                    None
                }
            })
        })
        .collect();

    let args_used = {
        let arg_accesses = &accesses_cursor.accesses[0];
        arg_accesses
            .keys()
            .filter(|field| arg_accesses[field].is_arg())
            .cloned()
            .collect::<BTreeSet<_>>()
    };

    (
        Signature {
            args_used,
            ret_aliases: retval_aliases,
        },
        constrain::FuncInfo::new(
            id,
            name_adjacencies,
            accesses_cursor.accesses,
            name_vars,
            accesses_cursor.by_expr_id,
        ),
    )
}

fn sorted_pair<T: Ord>(a: T, b: T) -> (T, T) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

// Track aliases in block. Appends all exprs to name_adjacencies without truncating
fn alias_track_block(
    ctx: Context,
    name_last_accesses: &mut LastAccessesCursor,
    name_adjacencies: &mut Vec<BTreeMap<FieldPath, BTreeSet<Name>>>, // indexed by ExprId
    name_vars: &mut Vec<BTreeMap<FieldPath, SolverVarId>>,           // indexed by ExprId
    block: &mid_ast::TypedBlock,
) {
    assert_eq!(name_last_accesses.len(), name_adjacencies.len());
    assert_eq!(name_last_accesses.len(), name_vars.len());
    for (i, (expr, type_)) in block.terms.iter().zip(&block.types).enumerate() {
        let cur_local_id = mid_ast::LocalId(block.initial_idx + i);
        let cur_expr_id = ExprId(name_adjacencies.len());
        assert_eq!(block.expr_id_of(cur_local_id), cur_expr_id);
        alias_track_expr(
            ctx,
            name_last_accesses,
            name_adjacencies,
            name_vars,
            &block.expr_ids,
            expr,
            cur_expr_id,
            &type_,
        );
    }
}

// Initializes last-accesses (for each name, one access at the point of creation),
// aliasing-edges (for each name, no aliases), and repr vars for names of a new
// expression of type `type_`.
fn initialize_expr(
    typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>], // indexed by CustomTypeId
    accesses: &mut LastAccessesCursor,
    name_adjacencies: &mut Vec<BTreeMap<FieldPath, BTreeSet<Name>>>, // indexed by ExprId
    name_vars: &mut Vec<BTreeMap<FieldPath, SolverVarId>>,           // indexed by ExprId
    cur_expr_id: ExprId,
    type_: &mid_ast::Type<SolverVarId>,
) {
    // Initialize the node for cur_expr_id in accesses and name_adjacencies
    let mut expr_name_vars = BTreeMap::new();
    let (name_paths, internal_edges) = get_names_in(typedefs, &mut expr_name_vars, type_);
    let mut expr_edges = BTreeMap::new();
    let mut expr_accesses = BTreeMap::new();
    for name in name_paths {
        expr_edges.insert(name.clone(), BTreeSet::new());
        expr_accesses.insert(
            name.clone(),
            LastAccessTree::singleton(&accesses.ctx, cur_expr_id),
        );
    }
    // Add internal edges to account for one level of type-folding-unrolling:
    for (a, b) in internal_edges {
        expr_edges
            .get_mut(&a)
            .unwrap()
            .insert((cur_expr_id, b.clone()));
        expr_edges
            .get_mut(&b)
            .unwrap()
            .insert((cur_expr_id, a.clone()));
    }
    name_adjacencies.push(expr_edges);
    accesses.append_expr(expr_accesses);
    name_vars.push(expr_name_vars);
}

// Appends data for `expr` to `accesses` and `name_adjacencies`, and updates
// each with accessing and aliasing information arising from `expr`.
fn alias_track_expr(
    ctx: Context,
    accesses: &mut LastAccessesCursor,
    name_adjacencies: &mut Vec<BTreeMap<FieldPath, BTreeSet<Name>>>,
    name_vars: &mut Vec<BTreeMap<FieldPath, SolverVarId>>,
    locals: &Vector<ExprId>, // indexed by LocalId
    expr: &mid_ast::TypedExpr,
    cur_expr_id: ExprId,                // id of `expr`
    type_: &mid_ast::Type<SolverVarId>, // type of `expr`
) {
    initialize_expr(
        ctx.typedefs,
        accesses,
        name_adjacencies,
        name_vars,
        cur_expr_id,
        type_,
    );

    match expr {
        mid_ast::Expr::Term(term) => {
            alias_field_to_term(name_adjacencies, locals, &(cur_expr_id, vector![]), term);
            update_term_accesses(accesses, locals, term);
        }
        mid_ast::Expr::ArithOp(arith_op) => match arith_op {
            mid_ast::ArithOp::IntOp(_, term1, term2)
            | mid_ast::ArithOp::ByteOp(_, term1, term2)
            | mid_ast::ArithOp::FloatOp(_, term1, term2)
            | mid_ast::ArithOp::IntCmp(_, term1, term2)
            | mid_ast::ArithOp::ByteCmp(_, term1, term2)
            | mid_ast::ArithOp::FloatCmp(_, term1, term2) => {
                update_term_accesses(accesses, locals, term1);
                update_term_accesses(accesses, locals, term2);
            }
            mid_ast::ArithOp::NegateInt(term)
            | mid_ast::ArithOp::NegateByte(term)
            | mid_ast::ArithOp::NegateFloat(term) => {
                update_term_accesses(accesses, locals, term);
            }
        },
        mid_ast::Expr::IOOp(mid_ast::IOOp::Input(_var)) => {
            // the array from input aliases nothing yet
        }
        mid_ast::Expr::IOOp(mid_ast::IOOp::Output(output_term)) => {
            update_term_accesses(accesses, locals, output_term);
        }
        mid_ast::Expr::ArrayOp(array_op) => match array_op {
            mid_ast::ArrayOp::Construct(_type, _var, item_terms) => {
                let items_name = (cur_expr_id, vector![FieldId::ArrayMembers]);
                let mut new_edges = Vec::new();
                for term in item_terms {
                    new_edges.push(compute_edges_from_aliasing_to_term(
                        name_adjacencies,
                        locals,
                        &items_name,
                        term,
                    ));
                    update_term_accesses(accesses, locals, term);
                }
                add_computed_edges(name_adjacencies, new_edges);
            }
            mid_ast::ArrayOp::Item(array_term, idx_term) => {
                update_term_accesses(accesses, locals, array_term);
                update_term_accesses(accesses, locals, idx_term);

                if let mid_ast::Term::Access(local_id, _actual, Some(array_field)) = array_term {
                    let mut new_edges = Vec::new();

                    let mut members_path = array_field.clone();
                    members_path.push_back(FieldId::ArrayMembers);
                    let original_array_members = (locals[local_id.0], &members_path);
                    // The returned item (in first tuple position) aliases
                    // array_term's members
                    let returned_item = (cur_expr_id, &vector![FieldId::Field(0)]);
                    new_edges.push(compute_edges_from_aliasing(
                        name_adjacencies,
                        original_array_members,
                        returned_item,
                        false,
                    ));
                    // The members of the HoleArray (in second tuple position) alias
                    // array_term's members
                    let new_array_members = (
                        cur_expr_id,
                        &vector![FieldId::Field(1), FieldId::ArrayMembers],
                    );
                    new_edges.push(compute_edges_from_aliasing(
                        name_adjacencies,
                        original_array_members,
                        new_array_members,
                        true,
                    ));

                    new_edges.push(conditionally_alias(
                        name_adjacencies,
                        original_array_members,
                        new_array_members,
                        returned_item,
                    ));

                    add_computed_edges(name_adjacencies, new_edges);
                } else {
                    // Any other Term is a compiler error
                    unreachable!()
                }
            }
            mid_ast::ArrayOp::Pop(array_term) => {
                update_term_accesses(accesses, locals, array_term);

                if let mid_ast::Term::Access(local_id, _, Some(array_field_path)) = array_term {
                    let mut new_edges = Vec::new();

                    let mut members_path = array_field_path.clone();
                    members_path.push_back(FieldId::ArrayMembers);
                    let original_array_members = (locals[local_id.0], &members_path);

                    // The members of the returned array (in first tuple position)
                    // alias the members of array_term
                    let new_array_members = (
                        cur_expr_id,
                        &vector![FieldId::Field(0), FieldId::ArrayMembers],
                    );
                    new_edges.push(compute_edges_from_aliasing(
                        name_adjacencies,
                        original_array_members,
                        new_array_members,
                        true,
                    ));

                    // The returned item (in the second tuple position) aliases the
                    // members of array_term
                    let returned_item = (cur_expr_id, &vector![FieldId::Field(1)]);
                    new_edges.push(compute_edges_from_aliasing(
                        name_adjacencies,
                        original_array_members,
                        returned_item,
                        false,
                    ));

                    new_edges.push(conditionally_alias(
                        name_adjacencies,
                        original_array_members,
                        new_array_members,
                        returned_item,
                    ));

                    add_computed_edges(name_adjacencies, new_edges);
                } else {
                    unreachable!();
                }
            }
            mid_ast::ArrayOp::Len(array_term) => {
                update_term_accesses(accesses, locals, array_term);
            }
            mid_ast::ArrayOp::Push(array_term, item_term)
            | mid_ast::ArrayOp::Replace(array_term, item_term) => {
                update_term_accesses(accesses, locals, array_term);
                update_term_accesses(accesses, locals, item_term);

                let mut new_edges = Vec::new();
                // The result's members alias the original array's members
                if let mid_ast::Term::Access(local_id, _, Some(array_path)) = array_term {
                    let mut array_members_path = array_path.clone();
                    array_members_path.push_back(FieldId::ArrayMembers);
                    new_edges.push(compute_edges_from_aliasing(
                        name_adjacencies,
                        (locals[local_id.0], &array_members_path),
                        (cur_expr_id, &vector![FieldId::ArrayMembers]),
                        true,
                    ));
                } else {
                    unreachable!();
                }
                // The result's members alias item_term
                // When item_term was already aliased in the original array, that alias
                // is copied here, creating a self-loop in the new array's members
                new_edges.push(compute_edges_from_aliasing_to_term(
                    name_adjacencies,
                    locals,
                    &(cur_expr_id, vector![FieldId::ArrayMembers]),
                    item_term,
                ));
                add_computed_edges(name_adjacencies, new_edges);
            }
        },
        mid_ast::Expr::Ctor(_type_id, _variant_id, None) => {
            // Nothing aliased or accessed
        }
        mid_ast::Expr::Ctor(_type_id, variant_id, Some(arg_term)) => {
            update_term_accesses(accesses, locals, arg_term);
            alias_field_to_term(
                name_adjacencies,
                locals,
                &(cur_expr_id, vector![FieldId::Variant(*variant_id)]),
                &arg_term,
            );
        }
        mid_ast::Expr::Tuple(item_terms) => {
            for (idx, item) in item_terms.iter().enumerate() {
                update_term_accesses(accesses, locals, &item);
                alias_field_to_term(
                    name_adjacencies,
                    locals,
                    &(cur_expr_id, vector![FieldId::Field(idx)]),
                    &item,
                );
            }
        }
        mid_ast::Expr::Local(local_id) => {
            alias_fields(
                name_adjacencies,
                (locals[local_id.0], &vector![]),
                (cur_expr_id, &vector![]),
            );
        }
        mid_ast::Expr::Call(_purity, func_id, arg_term, _) => {
            update_term_accesses(accesses, locals, arg_term);

            let alias_sig = ctx.alias_sig_for(*func_id);

            for sub_field in &alias_sig.args_used {
                update_term_field_accesses(accesses, locals, arg_term, sub_field);
            }

            // Before handling other aliasing, add aliases within return value
            for (path_a, path_b) in alias_sig.ret_aliases.iter() {
                name_adjacencies[cur_expr_id.0]
                    .entry(path_a.clone())
                    .or_default()
                    .insert((cur_expr_id, path_b.clone()));
                name_adjacencies[cur_expr_id.0]
                    .entry(path_b.clone())
                    .or_default()
                    .insert((cur_expr_id, path_a.clone()));
            }

            // Identify where parts of arg_term are aliased in the result
            apply_unique_info(
                name_adjacencies,
                locals,
                &ctx.unique_infos[func_id.0],
                arg_term,
                cur_expr_id,
            );
        }
        mid_ast::Expr::Match(_matched, branches, _result_type) => {
            let mut new_edges = Vec::new();
            for (branch_idx, (_pat, block)) in branches.iter().enumerate() {
                accesses.in_branch_scope(cur_expr_id, branch_idx, |sub_accesses| {
                    alias_track_block(ctx, sub_accesses, name_adjacencies, name_vars, block);
                    let branch_result = ExprId(name_adjacencies.len() - 1);
                    new_edges.push(compute_edges_from_aliasing(
                        name_adjacencies,
                        (branch_result, &vector![]),
                        (cur_expr_id, &vector![]),
                        true, // doesn't matter
                    ));
                });
            }
            add_computed_edges(name_adjacencies, new_edges);
        }
    };
}

// Computes the fields in `type_` at which there is a name. Differs from annot_aliases::get_names_in
// by including, for every recursive type in `type_`, one full layer of recursion, in order to
// facilitate alias graph construction (effectively, "unrolling" the type-folded name one step).
//
// Returns the names in `type_` and the edges between those that are aliased.
pub fn get_names_in(
    type_defs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
    name_vars: &mut BTreeMap<FieldPath, SolverVarId>, // indexed by ExprId
    type_: &mid_ast::Type<SolverVarId>,
) -> (Vec<FieldPath>, Vec<(FieldPath, FieldPath)>) {
    use im_rc::Vector;
    let mut names = Vec::new();
    let mut edges = Vec::new();
    add_names_from_type(
        type_defs,
        name_vars,
        &mut names,
        &mut edges,
        &mut BTreeMap::new(),
        &mut BTreeSet::new(),
        type_,
        Vector::new(),
    );
    return (names, edges);

    // Recursively appends paths to names in `type_` to `names`
    fn add_names_from_type(
        type_defs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
        name_vars: &mut BTreeMap<FieldPath, SolverVarId>, // indexed by ExprId
        names: &mut Vec<FieldPath>,
        edges: &mut Vec<(FieldPath, FieldPath)>,
        // `typedefs_on_path` maps types to the path at which they are found in the type
        typedefs_on_path: &mut BTreeMap<mid_ast::CustomTypeId, FieldPath>,
        typedefs_on_path_twice: &mut BTreeSet<mid_ast::CustomTypeId>,
        type_: &mid_ast::Type<SolverVarId>,
        prefix: FieldPath,
    ) {
        match type_ {
            mid_ast::Type::Bool
            | mid_ast::Type::Int
            | mid_ast::Type::Byte
            | mid_ast::Type::Float => {}
            mid_ast::Type::Array(item_type, var) | mid_ast::Type::HoleArray(item_type, var) => {
                // The array itself:
                names.push(prefix.clone());
                name_vars.insert(prefix.clone(), *var);
                // The names in elements of the array:
                let mut new_prefix = prefix.clone();
                new_prefix.push_back(FieldId::ArrayMembers);
                add_names_from_type(
                    type_defs,
                    name_vars,
                    names,
                    edges,
                    typedefs_on_path,
                    typedefs_on_path_twice,
                    item_type,
                    new_prefix,
                );
            }
            mid_ast::Type::Tuple(item_types) => {
                for (i, item_type) in item_types.iter().enumerate() {
                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(FieldId::Field(i));
                    add_names_from_type(
                        type_defs,
                        name_vars,
                        names,
                        edges,
                        typedefs_on_path,
                        typedefs_on_path_twice,
                        item_type,
                        new_prefix,
                    );
                }
            }
            mid_ast::Type::Custom(id, vars) => {
                let naming_nonrecursively = !typedefs_on_path.contains_key(id);
                let naming_second_layer =
                    typedefs_on_path.contains_key(id) && !typedefs_on_path_twice.contains(id);
                if naming_nonrecursively || naming_second_layer {
                    if naming_second_layer {
                        // Mark that we should not recursively traverse this type any deeper
                        typedefs_on_path_twice.insert(*id);
                        // Record that the current field aliases the ancestor of the same type
                        edges.push((typedefs_on_path.get(id).unwrap().clone(), prefix.clone()));
                    } else {
                        // Mark the path at which this type appears, for reference if it appears recursively
                        typedefs_on_path.insert(*id, prefix.clone());
                    }
                    for (i, variant) in type_defs[id.0].variants.iter().enumerate() {
                        if let Some(variant_type) = variant {
                            let mut variant_prefix = prefix.clone();
                            variant_prefix.push_back(FieldId::Variant(mid_ast::VariantId(i)));
                            add_names_from_type(
                                type_defs,
                                name_vars,
                                names,
                                edges,
                                typedefs_on_path,
                                typedefs_on_path_twice,
                                &unify::substitute_vars(type_defs, variant_type, vars),
                                variant_prefix,
                            );
                        }
                    }
                    if naming_second_layer {
                        typedefs_on_path_twice.remove(id);
                    } else {
                        // Remove if we added it
                        typedefs_on_path.remove(id);
                    }
                }
            }
        }
    }
}

fn apply_unique_info(
    name_adjacencies: &mut Vec<BTreeMap<FieldPath, BTreeSet<Name>>>, // indexed by ExprId
    locals: &Vector<ExprId>,                                         // indexed by LocalId
    ui: &UniqueInfo,
    arg: &mid_ast::Term,
    cur_expr_id: ExprId,
) {
    match arg {
        mid_ast::Term::Access(local_id, _, Some(field)) => {
            for alias in &ui.edges {
                alias_fields(
                    name_adjacencies,
                    (locals[local_id.0], &(field + &alias.arg_field)),
                    (cur_expr_id, &alias.ret_field),
                );
            }
        }
        mid_ast::Term::Access(_, _, None) => {
            unreachable!();
        }
        mid_ast::Term::BoolLit(_)
        | mid_ast::Term::IntLit(_)
        | mid_ast::Term::ByteLit(_)
        | mid_ast::Term::FloatLit(_) => {
            // Literals have no aliasing
        }
    }
}

fn update_term_accesses(
    accesses: &mut LastAccessesCursor,
    locals: &Vector<ExprId>, // indexed by LocalId
    term: &mid_ast::Term,
) {
    update_term_field_accesses(accesses, locals, term, &vector![]);
}

// Record accesses arising from accessing the `sub_field` field of `term`.
fn update_term_field_accesses(
    accesses: &mut LastAccessesCursor,
    locals: &Vector<ExprId>, // indexed by LocalId
    term: &mid_ast::Term,
    sub_field: &FieldPath,
) {
    let cur_expr_id = accesses.last_expr_id();
    match term {
        mid_ast::Term::Access(local_id, _, Some(pruned_base_field_path)) => {
            let field_path = pruned_base_field_path + sub_field;
            let referenced_expr = &mut accesses.accesses[locals[local_id.0].0];

            for i in 0..field_path.len() {
                if let Some(last_access) = referenced_expr.get_mut(&field_path.take(i)) {
                    last_access.consider_access(&accesses.ctx, cur_expr_id);
                }
            }
        }
        mid_ast::Term::Access(_, _, None) => unreachable!(),
        mid_ast::Term::BoolLit(_)
        | mid_ast::Term::IntLit(_)
        | mid_ast::Term::ByteLit(_)
        | mid_ast::Term::FloatLit(_) => {}
    }
}

/// Adds the necessary additional edges (in the aliasing graph in name_adjacencies)
/// when using a term in an expression.
/// Use means: the term `term` is going to occur in the position `prefix` in
/// the expression identified by `cur_expr_id`. `add_term_aliases` generates
/// the edges to add to `name_adjacencies` to represent this.
///
/// Note that this assumes that all field which are names in a given expression
/// have at least an empty set assigned in name_adjacencies.
fn alias_field_to_term(
    name_adjacencies: &mut [BTreeMap<FieldPath, BTreeSet<Name>>],
    locals: &Vector<ExprId>, // indexed by LocalId
    name: &Name,
    term: &mid_ast::Term,
) {
    let new_edges = compute_edges_from_aliasing_to_term(name_adjacencies, locals, name, term);
    add_computed_edges(name_adjacencies, vec![new_edges]);
}

#[must_use]
fn compute_edges_from_aliasing_to_term(
    name_adjacencies: &mut [BTreeMap<FieldPath, BTreeSet<Name>>],
    locals: &Vector<ExprId>, // indexed by LocalId
    (cur_expr_id, prefix): &Name,
    term: &mid_ast::Term,
) -> BTreeMap<ExprId, BTreeMap<FieldPath, BTreeSet<Name>>> {
    match term {
        mid_ast::Term::Access(referenced_local_id, _, Some(referenced_name_path)) => {
            compute_edges_from_aliasing(
                name_adjacencies,
                (locals[referenced_local_id.0], referenced_name_path),
                (*cur_expr_id, prefix),
                false,
            )
        }
        mid_ast::Term::BoolLit(_) | mid_ast::Term::IntLit(_) | mid_ast::Term::FloatLit(_) => {
            BTreeMap::new()
        }
        _ => unreachable!(),
    }
}

fn alias_fields(
    name_adjacencies: &mut [BTreeMap<FieldPath, BTreeSet<Name>>],
    prior: (ExprId, &FieldPath),
    new: (ExprId, &FieldPath),
) {
    let new_edges = compute_edges_from_aliasing(name_adjacencies, prior, new, true);
    add_computed_edges(name_adjacencies, vec![new_edges]);
}

fn add_computed_edges(
    name_adjacencies: &mut [BTreeMap<FieldPath, BTreeSet<Name>>],
    edge_maps_to_add: Vec<BTreeMap<ExprId, BTreeMap<FieldPath, BTreeSet<Name>>>>,
) {
    // Dump new edges from added_edges into name_adjacencies
    for edges_to_add in edge_maps_to_add {
        for (expr_id, edges_by_path) in edges_to_add.into_iter() {
            for (field_path, mut adjacent_names) in edges_by_path.into_iter() {
                name_adjacencies[expr_id.0]
                    .get_mut(&field_path)
                    .expect("found alias edge to name at uninitialized field path")
                    .append(&mut adjacent_names);
            }
        }
    }
}

// Creates aliases between `item` and `new_array_members` conditionally,
// adding a given edge if the name in `item` aliases the corresponding name
// in `original_array_members`. Used when inserting an element into an array
// that already contains alias(es) into it.
fn conditionally_alias(
    name_adjacencies: &[BTreeMap<FieldPath, BTreeSet<Name>>],
    original_array_members: (ExprId, &FieldPath),
    new_array_members: (ExprId, &FieldPath),
    item: (ExprId, &FieldPath),
) -> BTreeMap<ExprId, BTreeMap<FieldPath, BTreeSet<Name>>> {
    let mut added_edges: BTreeMap<ExprId, BTreeMap<FieldPath, BTreeSet<Name>>> = BTreeMap::new();

    let item_paths = name_adjacencies[(item.0).0]
        .iter()
        .filter(|(ref_path, _)| &ref_path.take(item.1.len()) == item.1);
    for (item_path, edges) in item_paths {
        let path_in_item = item_path.skip(item.1.len());
        let aliased_in_arr = edges.iter().any(|(expr, path)| {
            *expr == original_array_members.0
                && &path.take(original_array_members.1.len()) == original_array_members.1
                && path.skip(original_array_members.1.len()) == path_in_item
        });
        if aliased_in_arr {
            // If its aliased in the original array, alias it in the new array
            added_edges
                .entry(item.0)
                .or_default()
                .entry(item_path.clone())
                .or_default()
                .insert((new_array_members.0, new_array_members.1 + &path_in_item));
            added_edges
                .entry(new_array_members.0)
                .or_default()
                .entry(new_array_members.1 + &path_in_item)
                .or_default()
                .insert((item.0, item_path.clone()));
        }
    }

    added_edges
}

// Computes the edges to add to the graph to alias the two expressions.
fn compute_edges_from_aliasing(
    name_adjacencies: &[BTreeMap<FieldPath, BTreeSet<Name>>],
    prior: (ExprId, &FieldPath),
    new: (ExprId, &FieldPath),
    copy_toplevel_self_loops: bool,
) -> BTreeMap<ExprId, BTreeMap<FieldPath, BTreeSet<Name>>> {
    let (prior_expr, prior_path) = prior;
    let (new_expr, new_path) = new;

    let mut added_edges: BTreeMap<ExprId, BTreeMap<FieldPath, BTreeSet<Name>>> = BTreeMap::new();

    // Look at all sub-paths of the path being accessed
    let aliased_paths = name_adjacencies[prior_expr.0]
        .iter()
        .filter(|(ref_path, _)| ref_path.take(prior_path.len()) == *prior_path);
    for (ref_path, original_ref_edges) in aliased_paths {
        // NOTE: there is some redundant work being done here. As name_adjacencies
        // includes names in recursive types one level deep, fields in recursive
        // types will be handled twice each by this loop. It should be harmless.

        let ref_edges = {
            // Consider both the edges present in the original aliasing graph, and those
            // added in this call to `compute_edges_from_aliasing`.
            let mut ref_edges = original_ref_edges.clone();
            let edges_already_added = added_edges.get(&prior_expr).and_then(|e| e.get(&ref_path));
            if let Some(e) = edges_already_added {
                for edge in e {
                    ref_edges.insert(edge.clone());
                }
            }
            ref_edges
        };

        // ref_path is the full path into the referenced expression of some name
        // that is being copied. sub_path is that path *relative* to the path at
        // which `prior` and `new` are being aliased.
        let sub_path = ref_path.skip(prior_path.len());
        // Note: ref_path == prior_path + sub_path
        let here_path = new_path + &sub_path;

        // Mark "here" that the name aliases everything aliased by "there"
        let mut here_edges = ref_edges.clone();
        if ref_edges.contains(&(prior_expr, ref_path.clone()))
            && (!sub_path.is_empty() || copy_toplevel_self_loops)
        {
            // If "there" aliases "there" (i.e. if we find a self-loop), make a self-loop "here"
            here_edges.insert((new_expr, here_path.clone()));
        } else {
            // Mark "here" that the name aliases "there"
            here_edges.insert((prior_expr, ref_path.clone()));
        }
        added_edges
            .entry(new_expr)
            .or_insert_with(BTreeMap::new)
            .entry(here_path.clone())
            .or_insert_with(BTreeSet::new)
            .append(&mut here_edges);
        drop(here_edges); // emptied by previous statement

        // For every alias in ref_edges, mark that it is aliased
        // here (to make the edges undirected/bidirectional)
        for (other_expr, other_path) in ref_edges {
            added_edges
                .entry(other_expr)
                .or_insert_with(BTreeMap::new)
                .entry(other_path.clone())
                .or_insert_with(BTreeSet::new)
                .insert((new_expr, here_path.clone()));
        }

        // Mark there that the name is aliased here
        added_edges
            .entry(prior_expr)
            .or_insert_with(BTreeMap::new)
            .entry(ref_path.clone())
            .or_insert_with(BTreeSet::new)
            .insert((new_expr, new_path + ref_path));
    }
    added_edges
}
