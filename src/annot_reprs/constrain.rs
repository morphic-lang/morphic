use super::aliasing;
use super::mid_ast::{self, ExprId};
use super::out_ast::SharingPlace;
use crate::annot_aliases::FieldPath;
use crate::util::constraint_graph::{ConstraintGraph, EquivClass, EquivClasses, SolverVarId};
use im_rc::vector;
use std::collections::{BTreeMap, BTreeSet};

// TODO: move this into `mod aliasing`, with no `new` switched to private
// and other methods switched to public.
pub struct FuncInfo {
    pub id: mid_ast::CustomFuncId,
    // The following are indexed by `ExprId`
    aliases: Vec<BTreeMap<FieldPath, BTreeSet<aliasing::Name>>>,
    last_accesses: Vec<BTreeMap<FieldPath, aliasing::LastAccessTree>>,
    name_vars: Vec<BTreeMap<FieldPath, SolverVarId>>,
    paths_to_exprs: Vec<Vec<(ExprId, usize)>>,
}

impl FuncInfo {
    pub fn new(
        id: mid_ast::CustomFuncId,
        aliases: Vec<BTreeMap<FieldPath, BTreeSet<aliasing::Name>>>,
        last_accesses: Vec<BTreeMap<FieldPath, aliasing::LastAccessTree>>,
        name_vars: Vec<BTreeMap<FieldPath, SolverVarId>>,
        paths_to_exprs: Vec<Vec<(ExprId, usize)>>,
    ) -> Self {
        assert_eq!(aliases.len(), last_accesses.len());
        assert_eq!(aliases.len(), name_vars.len());
        assert_eq!(aliases.len(), paths_to_exprs.len());
        FuncInfo {
            id,
            last_accesses,
            aliases,
            name_vars,
            paths_to_exprs,
        }
    }

    /// Returns the variable which describes the representation of the given name
    fn repr_var_for(&self, (expr_id, path): &aliasing::Name) -> SolverVarId {
        *self.name_vars[expr_id.0].get(path).unwrap()
    }

    /// Compute the `LastAccessTree` representing the last uses of `name` (the last
    /// accesses to it or any name it aliases).
    fn last_uses_of(&self, name: &aliasing::Name) -> aliasing::LastAccessTree {
        // Collect the `LastAccessTree`s of the name and all names it aliases
        let mut access_trees = self
            .names_aliased_to(name)
            .iter()
            .map(|(expr, path)| &self.last_accesses[expr.0][path])
            .collect::<Vec<_>>();
        access_trees.push(&self.last_accesses[(name.0).0][&name.1]);
        return aliasing::LastAccessTree::join(&mut access_trees);
    }

    fn last_uses_of_arg(&self) -> BTreeMap<FieldPath, aliasing::LastAccessTree> {
        let arg_fields = self.last_accesses[0].keys().cloned();
        arg_fields
            .map(|path| (path.clone(), self.last_uses_of(&(ExprId::ARG, path))))
            .collect()
    }

    /// Determines whether `name` is used (i.e. if `name` or any name that
    /// aliases it may be accessed) after `at`.
    fn is_name_used_after(&self, name: &aliasing::Name, at: ExprId) -> bool {
        self.last_uses_of(name)
            .is_used_after(&self.paths_to_exprs[at.0], at)
    }

    /// Returns all the names that may-alias the given name.
    fn names_aliased_to(&self, (expr_id, path): &aliasing::Name) -> &BTreeSet<aliasing::Name> {
        &self.aliases[expr_id.0][path]
    }

    /// Returns the `ExprId` of the returned expression
    fn ret_expr(&self) -> ExprId {
        ExprId(self.aliases.len() - 1)
    }

    /// Checks whether the given names alias
    fn may_alias(&self, name_a: &aliasing::Name, name_b: &aliasing::Name) -> bool {
        self.names_aliased_to(name_a).contains(name_b)
    }

    /// If the given name is aliased to a field in the function argument or
    /// return value, `may_alias_external` returns the path in the argument or
    /// return val to which it is aliased. Otherwise, it returns None.
    fn external_names_aliased_to<'a>(
        &'a self,
        name: &aliasing::Name,
    ) -> impl Iterator<Item = (SharingPlace, &'a FieldPath)> {
        self.names_aliased_to(name)
            .iter()
            .filter_map(move |(other_expr, other_path)| {
                if *other_expr == ExprId::ARG {
                    Some((SharingPlace::Arg, other_path))
                } else if *other_expr == self.ret_expr() {
                    Some((SharingPlace::Ret, other_path))
                } else {
                    None
                }
            })
    }

    /// If the given name is aliased to a field in the function argument or
    /// return value, `may_alias_arg` returns the path in the argument to which
    /// it is aliased. Otherwise, it returns None.
    fn arg_names_aliased_to<'a>(
        &'a self,
        name: &aliasing::Name,
    ) -> impl Iterator<Item = &'a FieldPath> {
        self.external_names_aliased_to(name)
            .filter_map(|(place, path)| match place {
                SharingPlace::Arg => Some(path),
                SharingPlace::Ret => None,
            })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Context<'a> {
    pub constraint_sigs: &'a [Option<Signature>], // indexed by CustomFuncId
    pub equiv_classes: &'a EquivClasses,
    pub scc_sigs:
        &'a BTreeMap<mid_ast::CustomFuncId, BTreeMap<EquivClass, BTreeSet<mid_ast::Constraint>>>,
}

#[derive(Clone, Debug)]
pub struct Signature {
    params: Vec<BTreeSet<mid_ast::Constraint>>, // indexed by RepParamId
}

impl Signature {
    pub fn new(params: Vec<BTreeSet<mid_ast::Constraint>>) -> Self {
        Signature { params }
    }

    pub fn num_params(&self) -> usize {
        self.params.len()
    }

    pub fn into_params(self) -> Vec<BTreeSet<mid_ast::Constraint>> {
        self.params
    }

    fn is_empty(&self) -> bool {
        for constraints in &self.params {
            if !constraints.is_empty() {
                return false;
            }
        }
        true
    }
}

pub fn initialize_sigs_for_scc(
    equiv_classes: &EquivClasses,
    scc_funcs: &BTreeMap<mid_ast::CustomFuncId, mid_ast::FuncDef<()>>,
) -> BTreeMap<mid_ast::CustomFuncId, BTreeMap<EquivClass, BTreeSet<mid_ast::Constraint>>> {
    let mut scc_equiv_class_params = BTreeMap::new();
    for func in scc_funcs.values() {
        add_equiv_class_params(equiv_classes, &mut scc_equiv_class_params, &func.arg_type);
        add_equiv_class_params(equiv_classes, &mut scc_equiv_class_params, &func.ret_type);
    }
    let mut scc_sigs = BTreeMap::new();
    for func_id in scc_funcs.keys() {
        scc_sigs.insert(*func_id, scc_equiv_class_params.clone());
    }
    return scc_sigs;

    fn add_equiv_class_params(
        equiv_classes: &EquivClasses,
        params: &mut BTreeMap<EquivClass, BTreeSet<mid_ast::Constraint>>,
        type_: &mid_ast::Type<SolverVarId>,
    ) {
        use mid_ast::Type as T;
        match type_ {
            T::Bool | T::Int | T::Byte | T::Float => {}
            T::Array(item_t, var) | T::HoleArray(item_t, var) => {
                params.insert(equiv_classes.class(*var), BTreeSet::new());
                add_equiv_class_params(equiv_classes, params, item_t);
            }
            T::Tuple(item_types) => {
                for t in item_types {
                    add_equiv_class_params(equiv_classes, params, t);
                }
            }
            T::Custom(_id, vars) => {
                for v in vars {
                    params.insert(equiv_classes.class(*v), BTreeSet::new());
                }
            }
        }
    }
}

pub fn constrain_func(
    ctx: Context,
    graph: &mut ConstraintGraph<mid_ast::Constraint>,
    func: &FuncInfo,
    body: &mid_ast::TypedBlock,
) -> BTreeMap<EquivClass, BTreeSet<mid_ast::Constraint>> {
    let mut mutation_points = Vec::new();
    let _ = constrain_block(ctx, func, graph, &mut mutation_points, ExprId(1), &body);

    for (arg_path, arg_path_last_access) in func.last_uses_of_arg() {
        for (mutated_arg_path, mutation_loc) in &mutation_points {
            if arg_path_last_access.is_after(&func.paths_to_exprs[mutation_loc.0], *mutation_loc) {
                graph.require(
                    func.repr_var_for(&(ExprId::ARG, mutated_arg_path.clone())),
                    mid_ast::Constraint::SharedIfAliased(
                        arg_path.clone(),
                        mutated_arg_path.clone(),
                    ),
                );
            }
        }
    }
    let mut func_sig = BTreeMap::new();
    for equiv_class_param in ctx.scc_sigs[&func.id].keys() {
        func_sig.insert(*equiv_class_param, BTreeSet::new());
    }
    for (var_idx, var_constraints) in graph.var_constraints.iter().enumerate() {
        let equiv_class = ctx.equiv_classes.class(SolverVarId(var_idx));
        if let Some(constraints) = func_sig.get_mut(&equiv_class) {
            constraints.extend(var_constraints.requirements.iter().cloned());
        }
    }
    func_sig
}

/// Returns the next ExprId after the expressions in the given block
#[must_use]
fn constrain_block(
    ctx: Context,
    func: &FuncInfo,
    graph: &mut ConstraintGraph<mid_ast::Constraint>,
    arg_mutations: &mut Vec<(FieldPath, ExprId)>,
    initial_expr_id: ExprId,
    block: &mid_ast::TypedBlock,
) -> ExprId {
    let mut next_expr_id = initial_expr_id;
    for (expr, type_) in block.terms.iter().zip(block.types.iter()) {
        next_expr_id = constrain_expr(
            ctx,
            func,
            graph,
            arg_mutations,
            block,
            next_expr_id,
            expr,
            type_,
        );
    }
    next_expr_id
}

// Returns the `ExprId` of the next expression to be processed after the given `expr`.
#[must_use]
fn constrain_expr(
    ctx: Context,
    func: &FuncInfo,
    graph: &mut ConstraintGraph<mid_ast::Constraint>,
    arg_mutations: &mut Vec<(FieldPath, ExprId)>,
    block: &mid_ast::TypedBlock,
    expr_id: ExprId,
    expr: &mid_ast::TypedExpr,
    type_: &mid_ast::Type<SolverVarId>,
) -> ExprId {
    return match expr {
        mid_ast::Expr::IOOp(mid_ast::IOOp::Input(_))
        | mid_ast::Expr::IOOp(mid_ast::IOOp::Output(_)) => expr_id.next(),
        mid_ast::Expr::ArrayOp(array_op) => {
            match array_op {
                mid_ast::ArrayOp::Construct(..) => {}
                mid_ast::ArrayOp::Item(..) => {}
                mid_ast::ArrayOp::Len(_) => {}
                mid_ast::ArrayOp::Push(array_term, _item_term) => {
                    handle_array_mutated(
                        func,
                        graph,
                        arg_mutations,
                        block,
                        expr_id,
                        type_,
                        array_term,
                    );
                }
                mid_ast::ArrayOp::Pop(array_term) => {
                    handle_array_mutated(
                        func,
                        graph,
                        arg_mutations,
                        block,
                        expr_id,
                        type_,
                        array_term,
                    );
                }
                mid_ast::ArrayOp::Replace(hole_array_term, _item_term) => {
                    handle_array_mutated(
                        func,
                        graph,
                        arg_mutations,
                        block,
                        expr_id,
                        type_,
                        hole_array_term,
                    );
                }
            }
            expr_id.next()
        }
        // Call to a function outside the SCC
        mid_ast::Expr::Call(
            _purity,
            func_id,
            arg,
            Some(mid_ast::ReprParams::Determined(repr_vars)),
        ) => {
            if let Some(arg_name) = get_accessed_name(block, arg) {
                let sig = ctx.constraint_sigs[func_id.0].as_ref().unwrap();
                for (repr_var, constraint_set) in repr_vars.iter().zip(sig.params.iter()) {
                    for constraint in constraint_set {
                        apply_constraint_from_call(
                            func,
                            graph,
                            arg_mutations,
                            *repr_var,
                            constraint,
                            expr_id,
                            &arg_name,
                            &(expr_id, vector![]),
                        );
                    }
                }
            } else {
                assert!(ctx.constraint_sigs[func_id.0].as_ref().unwrap().is_empty())
            }
            expr_id.next()
        }
        // Call to a function in the SCC
        mid_ast::Expr::Call(_purity, func_id, arg, Some(mid_ast::ReprParams::Pending)) => {
            let callee_sig = ctx
                .scc_sigs
                .get(&func_id)
                .expect("function not present in SCC map");
            if let Some(arg_name) = get_accessed_name(block, arg) {
                for (equiv_class, constraints) in callee_sig {
                    let repr_var = ctx.equiv_classes.one_repr_var_of(*equiv_class);
                    for constraint in constraints {
                        apply_constraint_from_call(
                            func,
                            graph,
                            arg_mutations,
                            repr_var,
                            constraint,
                            expr_id,
                            &arg_name,
                            &(expr_id, vector![]),
                        );
                    }
                }
            } else {
                assert!(ctx.constraint_sigs[func_id.0].as_ref().unwrap().is_empty());
            }
            expr_id.next()
        }
        mid_ast::Expr::Call(_, _, _, None) => unreachable!(),
        mid_ast::Expr::Match(_matched_local, branches, _result_type) => {
            let mut next_expr_id = expr_id;
            for (_pat, branch) in branches {
                next_expr_id =
                    constrain_block(ctx, func, graph, arg_mutations, next_expr_id, branch);
            }
            next_expr_id
        }
        mid_ast::Expr::Term(_)
        | mid_ast::Expr::ArithOp(_)
        | mid_ast::Expr::Ctor(..)
        | mid_ast::Expr::Tuple(_)
        | mid_ast::Expr::Local(_) => expr_id.next(),
    };

    fn get_accessed_name(
        block: &mid_ast::TypedBlock,
        term: &mid_ast::Term,
    ) -> Option<(mid_ast::ExprId, FieldPath)> {
        if let mid_ast::Term::Access(local_id, _, Some(field)) = term {
            Some((block.expr_id_of(*local_id), field.clone()))
        } else if let mid_ast::Term::Access(_, _, None) = term {
            unreachable!()
        } else {
            None
        }
    }

    fn handle_array_mutated(
        func: &FuncInfo,
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        arg_mutations: &mut Vec<(FieldPath, ExprId)>,
        block: &mid_ast::TypedBlock,
        expr_id: ExprId,
        type_: &mid_ast::Type<SolverVarId>,
        array: &mid_ast::Term,
    ) {
        let original_array = get_accessed_name(block, array).expect("unexpected literal");
        let repr_var = match type_ {
            mid_ast::Type::Array(_, repr_var) => *repr_var,
            mid_ast::Type::HoleArray(_, repr_var) => *repr_var,
            _ => panic!("internal type error"),
        };
        apply_constraint_from_call(
            func,
            graph,
            arg_mutations,
            repr_var,
            &mid_ast::Constraint::SharedIfOutlivesCall(SharingPlace::Arg, vector![]),
            expr_id,
            &original_array,
            &(expr_id, vector![]),
        );
    }

    // When a function or builtin is called, generating `constraint` on `repr_var`,
    // `apply_constraint_from_call` generates the constraint(s) to apply to `repr_var`
    // in the scope of the calling function.
    // For every SharedIfOutlivesCall(Name) in which the Name aliases an argument,
    // the named argument and the expression ID that generated that constriant are
    // pushed to `arg_mutations` (for creating SharedIfAliased(...) constraints later).
    fn apply_constraint_from_call(
        func: &FuncInfo,
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        arg_mutations: &mut Vec<(FieldPath, ExprId)>,
        repr_var: SolverVarId,
        constraint: &mid_ast::Constraint,
        expr_id: ExprId, // id of expression that made the call
        arg_name: &aliasing::Name,
        ret_name: &aliasing::Name,
    ) {
        match constraint {
            mid_ast::Constraint::Shared => {
                graph.require(repr_var, mid_ast::Constraint::Shared);
            }
            mid_ast::Constraint::SharedIfOutlivesCall(place, sub_place_path) => {
                let constrained_name = {
                    let (constrained_expr, path) = match place {
                        SharingPlace::Arg => arg_name,
                        SharingPlace::Ret => ret_name,
                    };
                    (*constrained_expr, path + sub_place_path)
                };
                for outer_arg_path in func.arg_names_aliased_to(&constrained_name) {
                    arg_mutations.push((outer_arg_path.clone(), expr_id));
                }
                if func.is_name_used_after(&constrained_name, expr_id) {
                    graph.require(repr_var, mid_ast::Constraint::Shared);
                } else {
                    for (outer_place, outer_place_path) in
                        func.external_names_aliased_to(&constrained_name)
                    {
                        graph.require(
                            repr_var,
                            mid_ast::Constraint::SharedIfOutlivesCall(
                                outer_place,
                                outer_place_path.clone(),
                            ),
                        );
                    }
                }
            }
            mid_ast::Constraint::SharedIfAliased(sub_arg_path_a, sub_arg_path_b) => {
                let (name_a, name_b) = {
                    let (arg_expr, arg_path) = arg_name;
                    (
                        (*arg_expr, arg_path + sub_arg_path_a),
                        (*arg_expr, arg_path + sub_arg_path_b),
                    )
                };
                if func.may_alias(&name_a, &name_b) {
                    graph.require(repr_var, mid_ast::Constraint::Shared);
                } else {
                    for outer_arg_path_a in func.arg_names_aliased_to(&name_a) {
                        for outer_arg_path_b in func.arg_names_aliased_to(&name_b) {
                            // If both names are aliased to arguments (and not necessarily
                            // aliased locally), pass the buck
                            graph.require(
                                repr_var,
                                mid_ast::Constraint::SharedIfAliased(
                                    outer_arg_path_a.clone(),
                                    outer_arg_path_b.clone(),
                                ),
                            );
                        }
                    }
                }
            }
        }
    }
}
