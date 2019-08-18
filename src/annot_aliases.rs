use crate::data::first_order_ast as ast;
use crate::graph::{self, Graph};
use crate::util::id_vec::IdVec;
use im_rc::Vector;
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum FieldId {
    Variant(ast::VariantId),
    Field(usize),
    ArrayMembers,
}

// The nth item in a `FieldPath` is the nth "subscript" to take on some
// object to reach the field in question. An empty `FieldPath` refers to
// the object itself.
pub type FieldPath = Vector<FieldId>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AliasPair {
    pub arg_field: FieldPath,
    pub ret_field: FieldPath,
}

impl AliasPair {
    fn new(arg_field: FieldPath, ret_field: FieldPath) -> Self {
        AliasPair {
            arg_field,
            ret_field,
        }
    }

    // add_ret_context prepends a field to the `ret_field`, for when using
    // an AliasPair of a sub-structure to create one describing the super-structure.
    fn add_ret_context(&self, from: FieldId) -> Self {
        let mut new = self.clone();
        new.ret_field.push_front(from);
        new
    }

    fn rm_ret_context(&self, field: FieldId) -> Self {
        assert_eq!(self.ret_field[0], field);
        let mut new = self.clone();
        new.ret_field.pop_front();
        new
    }

    fn rm_context(&self, field: FieldId) -> Self {
        assert_eq!(self.arg_field[0], field);
        let mut new = self.clone();
        new.arg_field.pop_front();
        new
    }

    fn specify(&self, to: FieldId) -> Self {
        let mut new = self.clone();
        new.arg_field.push_back(to);
        new.ret_field.push_back(to);
        new
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UniqueInfo {
    pub edges: Vector<AliasPair>,
}

impl UniqueInfo {
    fn empty() -> UniqueInfo {
        UniqueInfo {
            edges: Vector::new(),
        }
    }

    fn add_ret_context(&self, field: FieldId) -> Self {
        UniqueInfo {
            edges: self
                .edges
                .iter()
                .map(|e| e.add_ret_context(field))
                .collect(),
        }
    }

    // *Assuming* that every edge starts from the field `field`, remove the
    // `field.` prefix from every edge
    fn rm_context(&self, field: FieldId) -> Self {
        UniqueInfo {
            edges: self.edges.iter().map(|e| e.rm_context(field)).collect(),
        }
    }

    // Filter edges for those starting with `field`, and remove `field` from those
    // edges in the result
    fn narrow_ret_context(&self, field: FieldId) -> Self {
        UniqueInfo {
            edges: self
                .edges
                .iter()
                .filter(|e| !e.ret_field.is_empty() && e.ret_field[0] == field)
                .map(|e| e.rm_ret_context(field))
                .collect(),
        }
    }

    fn one_field(&self, field: FieldId) -> Self {
        self.narrow_ret_context(field).add_ret_context(field)
    }

    fn set_ret_path(&self, ret_field: FieldPath) -> Self {
        UniqueInfo {
            edges: self
                .edges
                .iter()
                .map(|e| AliasPair {
                    arg_field: e.arg_field.clone(),
                    ret_field: ret_field.clone(),
                })
                .collect(),
        }
    }

    fn append(&mut self, other: UniqueInfo) {
        self.edges.append(other.edges.clone());
    }

    fn union(mut a: Self, b: Self) -> Self {
        a.edges.append(b.edges);
        a
    }

    fn add(&self, addition: AliasPair) -> Self {
        let mut new = self.clone();
        new.edges.push_back(addition);
        new
    }

    fn filter_ret_path(&self, other: FieldPath) -> Self {
        UniqueInfo {
            edges: self
                .edges
                .clone()
                .into_iter()
                .filter(|p| p.ret_field == other)
                .collect(),
        }
    }

    fn apply_to(&self, arg: &UniqueInfo) -> Self {
        let mut new = UniqueInfo::empty();
        for alias in self.edges.clone() {
            // wire together this alias with where the arg comes from
            new.append(
                arg.filter_ret_path(alias.arg_field)
                    .set_ret_path(alias.ret_field),
            );
        }
        new
    }
}

// A LocalId maps to its UniqueInfo in terms of the function argument
type Locals = Vec<UniqueInfo>;

fn bind_pattern_locals(
    locals: &mut Locals,
    func_infos: &[UniqueInfo],
    pattern: &ast::Pattern,
    rhs: UniqueInfo,
) {
    match pattern {
        ast::Pattern::Any(_) => {}
        ast::Pattern::Var(_) => {
            locals.push(rhs);
        }
        ast::Pattern::Tuple(patterns) => {
            for i in 0..patterns.len() {
                bind_pattern_locals(
                    locals,
                    func_infos,
                    &patterns[i],
                    rhs.narrow_ret_context(FieldId::Field(i)),
                );
            }
        }
        ast::Pattern::Ctor(_, _, None) => {}
        ast::Pattern::Ctor(_, variant_id, Some(arg_pattern)) => {
            bind_pattern_locals(
                locals,
                func_infos,
                &arg_pattern,
                rhs.narrow_ret_context(FieldId::Variant(*variant_id)),
            );
        }
        ast::Pattern::BoolConst(_) => {}
        ast::Pattern::ByteConst(_) => {}
        ast::Pattern::IntConst(_) => {}
        ast::Pattern::FloatConst(_) => {}
    }
}

fn annot_pattern(
    locals: &mut Locals,
    func_infos: &[UniqueInfo],
    pattern: &ast::Pattern,
    rhs: &ast::Expr,
    body: &ast::Expr,
) -> UniqueInfo {
    let initial_len = locals.len();
    let rhs_unique_info = annot_expression(locals, func_infos, rhs);
    bind_pattern_locals(locals, func_infos, pattern, rhs_unique_info);
    let result = annot_expression(locals, func_infos, body);
    locals.truncate(initial_len);
    result
}

// Compute how `expr` aliases the arguments to the containing function
fn annot_expression(
    locals: &mut Locals,
    func_infos: &[UniqueInfo],
    expr: &ast::Expr,
) -> UniqueInfo {
    match expr {
        ast::Expr::ArithOp(_) => UniqueInfo::empty(),
        ast::Expr::ArrayOp(ast::ArrayOp::Item(_, array, _)) => {
            let array_aliases = annot_expression(locals, func_infos, array);
            UniqueInfo::union(
                // The members of the array in the second entry of the returned tuple alias the
                // members of the given array
                array_aliases
                    .one_field(FieldId::ArrayMembers)
                    .add_ret_context(FieldId::Field(1)),
                // The item in the first entry of the returned tuple, aliases the given array's contents
                array_aliases
                    .one_field(FieldId::ArrayMembers)
                    .add_ret_context(FieldId::Field(0)),
            )
        }
        ast::Expr::ArrayOp(ast::ArrayOp::Pop(_type, array)) => {
            let array_aliases = annot_expression(locals, func_infos, array);
            UniqueInfo::union(
                // The members of the array in the first entry of the returned tuple alias the
                // members of the given array
                array_aliases
                    .one_field(FieldId::ArrayMembers)
                    .add_ret_context(FieldId::Field(0)),
                // The item in the second entry of the returned tuple, aliases the given array's contents
                array_aliases
                    .one_field(FieldId::ArrayMembers)
                    .add_ret_context(FieldId::Field(1)),
            )
        }
        ast::Expr::ArrayOp(ast::ArrayOp::Len(..)) => UniqueInfo::empty(),
        ast::Expr::ArrayOp(ast::ArrayOp::Push(_type, array, item))
        | ast::Expr::ArrayOp(ast::ArrayOp::Replace(_type, array, item)) => {
            let arr_aliases = annot_expression(locals, func_infos, array);
            let item_aliases = annot_expression(locals, func_infos, item);
            UniqueInfo::union(
                // the new array's members alias what the original array's members do
                arr_aliases.one_field(FieldId::ArrayMembers),
                // the new array's members alias what item aliases
                item_aliases.add_ret_context(FieldId::ArrayMembers),
            )
        }
        ast::Expr::ArrayOp(ast::ArrayOp::Concat(..)) => {
            // TODO: remove Concat
            unimplemented!()
        }
        ast::Expr::IOOp(_) => UniqueInfo::empty(),
        ast::Expr::Ctor(_id, variant_id, args) => match args {
            None => UniqueInfo::empty(),
            Some(args) => annot_expression(locals, func_infos, args)
                .add_ret_context(FieldId::Variant(*variant_id)),
        },
        ast::Expr::Local(ast::LocalId(id)) => locals[*id].clone(),
        ast::Expr::Tuple(elems) => {
            let mut info = UniqueInfo::empty();
            for i in 0..elems.len() {
                info = UniqueInfo::union(
                    info,
                    annot_expression(locals, func_infos, &elems[i])
                        .add_ret_context(FieldId::Field(i)),
                );
            }
            info
        }
        ast::Expr::Call(_purity, ast::CustomFuncId(func_id), arg) => {
            let arg_aliases = annot_expression(locals, func_infos, arg);
            func_infos[*func_id].apply_to(&arg_aliases)
        }
        ast::Expr::Match(matched_expr, cases, _type) => {
            let mut result = UniqueInfo::empty();
            for (pattern, body) in cases {
                result.append(annot_pattern(
                    locals,
                    func_infos,
                    pattern,
                    matched_expr,
                    body,
                ));
            }
            result
        }
        ast::Expr::Let(lhs, rhs, body) => annot_pattern(locals, func_infos, lhs, rhs, body),
        ast::Expr::ArrayLit(..) => UniqueInfo::empty(),
        ast::Expr::BoolLit(..) => UniqueInfo::empty(),
        ast::Expr::ByteLit(..) => UniqueInfo::empty(),
        ast::Expr::IntLit(..) => UniqueInfo::empty(),
        ast::Expr::FloatLit(..) => UniqueInfo::empty(),
    }
}

// Computes the fields in `type_` at which there is a name
fn get_names_in(
    type_defs: &IdVec<ast::CustomTypeId, ast::TypeDef>,
    type_: &ast::Type,
) -> Vec<FieldPath> {
    let mut names = Vec::new();
    add_names_from_type(
        type_defs,
        &mut names,
        &mut BTreeSet::new(),
        type_,
        Vector::new(),
    );
    return names;

    // Recursively appends paths to names in `type_` to `names`
    fn add_names_from_type(
        type_defs: &IdVec<ast::CustomTypeId, ast::TypeDef>,
        names: &mut Vec<FieldPath>,
        typedefs_on_path: &mut BTreeSet<ast::CustomTypeId>,
        type_: &ast::Type,
        prefix: FieldPath,
    ) {
        match type_ {
            ast::Type::Bool | ast::Type::Num(_) => {}
            ast::Type::Array(item_type) | ast::Type::HoleArray(item_type) => {
                // The array itself:
                names.push(prefix.clone());
                // The names in elements of the array:
                let mut new_prefix = prefix.clone();
                new_prefix.push_back(FieldId::ArrayMembers);
                add_names_from_type(type_defs, names, typedefs_on_path, item_type, new_prefix);
            }
            ast::Type::Tuple(item_types) => {
                for (i, item_type) in item_types.iter().enumerate() {
                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(FieldId::Field(i));
                    add_names_from_type(type_defs, names, typedefs_on_path, item_type, new_prefix);
                }
            }
            ast::Type::Custom(id) => {
                if !typedefs_on_path.contains(id) {
                    typedefs_on_path.insert(*id);
                    for (variant_id, variant) in &type_defs[id].variants {
                        if let Some(variant_type) = variant {
                            let mut variant_prefix = prefix.clone();
                            variant_prefix.push_back(FieldId::Variant(variant_id));
                            add_names_from_type(
                                type_defs,
                                names,
                                typedefs_on_path,
                                variant_type,
                                variant_prefix,
                            );
                        }
                    }
                    // Remove if we added it
                    typedefs_on_path.remove(id);
                }
            }
        }
    }
}

pub fn prune_field_path(
    type_defs: &IdVec<ast::CustomTypeId, ast::TypeDef>,
    type_: &ast::Type,
    path: &FieldPath,
) -> FieldPath {
    prune_field_path_with(
        move |type_id, variant_id| {
            type_defs[type_id].variants[variant_id]
                .as_ref()
                .map(Cow::Borrowed)
        },
        type_,
        path,
    )
}

/// Simplify FieldPaths such that two paths accessing the same *name* in a
/// recursive type have the same pruned path. E.g. once pruned,
/// `list = list.cdr = list.cdr.cdr = ...` and `list.car = list.cdr.car = ...`.
pub fn prune_field_path_with<
    'a,
    F: Fn(ast::CustomTypeId, ast::VariantId) -> Option<Cow<'a, ast::Type>>,
>(
    variant_for: F,
    type_: &'a ast::Type,
    path: &'a FieldPath,
) -> FieldPath {
    return prune_field_path_help(
        variant_for,
        type_,
        Vector::Empty,
        &mut BTreeMap::new(),
        path.clone(),
    );

    // Keeps track, in `customs`, of the indices in `front` which entered custom types,
    // so that paths involving recursive references can be pruned.
    fn prune_field_path_help<'a, 'b, F>(
        variant_for: F,
        type_: &'b ast::Type,
        mut front: FieldPath,
        customs: &mut BTreeMap<ast::CustomTypeId, usize>,
        mut path: FieldPath,
    ) -> FieldPath
    where
        F: Fn(ast::CustomTypeId, ast::VariantId) -> Option<Cow<'a, ast::Type>>,
    {
        if path.is_empty() {
            return front + path;
        }
        match (path[0], type_) {
            (FieldId::Variant(variant_id), ast::Type::Custom(type_id)) => {
                if let Some(idx) = customs.get(type_id) {
                    front.split_off(*idx);
                } else {
                    customs.insert(*type_id, front.len());
                }
                front.push_back(FieldId::Variant(variant_id));
                path.pop_front();
                if let Some(variant_type) = variant_for(*type_id, variant_id) {
                    prune_field_path_help(variant_for, variant_type.as_ref(), front, customs, path)
                } else {
                    debug_assert!(path.len() == 0);
                    front
                }
            }
            (FieldId::Field(field_idx), ast::Type::Tuple(item_types)) => {
                front.push_back(FieldId::Field(field_idx));
                path.pop_front();
                prune_field_path_help(variant_for, &item_types[field_idx], front, customs, path)
            }
            (FieldId::ArrayMembers, ast::Type::Array(item_type))
            | (FieldId::ArrayMembers, ast::Type::HoleArray(item_type)) => {
                front.push_back(FieldId::ArrayMembers);
                path.pop_front();
                prune_field_path_help(variant_for, &item_type, front, customs, path)
            }
            (_, _) => panic!(
                "internal error: field path {:?} mismatches type {:?} at first index",
                path, type_
            ),
        }
    }
}

// Does type-folding on the names in the unique info (see prune_field_path for more info)
fn prune_unique_info(
    type_defs: &IdVec<ast::CustomTypeId, ast::TypeDef>,
    func: &ast::FuncDef,
    ui: &UniqueInfo,
) -> UniqueInfo {
    let mut pruned_edges = Vector::new();
    for edge in &ui.edges {
        pruned_edges.push_back(AliasPair {
            arg_field: prune_field_path(type_defs, &func.arg_type, &edge.arg_field),
            ret_field: prune_field_path(type_defs, &func.ret_type, &edge.ret_field),
        })
    }
    UniqueInfo {
        edges: pruned_edges,
    }
}

fn annot_func(
    type_defs: &IdVec<ast::CustomTypeId, ast::TypeDef>,
    func: &ast::FuncDef,
    func_infos: &[UniqueInfo],
) -> UniqueInfo {
    let mut locals = Vec::new();
    // Compute the names in the arg
    let names = get_names_in(type_defs, &func.arg_type);
    let arg_unique_info = UniqueInfo {
        edges: names
            .into_iter()
            .map(|fp| AliasPair::new(fp.clone(), fp))
            .collect(),
    };
    bind_pattern_locals(&mut locals, func_infos, &func.arg, arg_unique_info);
    let messy_unique_info = annot_expression(&mut locals, func_infos, &func.body);
    prune_unique_info(type_defs, func, &messy_unique_info)
}

fn annot_scc(
    type_defs: &IdVec<ast::CustomTypeId, ast::TypeDef>,
    func_defs: &IdVec<ast::CustomFuncId, ast::FuncDef>,
    func_infos: &mut [UniqueInfo],
    scc: &[ast::CustomFuncId],
) {
    // Update the UniqueInfos for the SCC until we do a pass in which none of them change
    let mut scc_changed = true;
    while scc_changed {
        scc_changed = false;
        for id in scc {
            let newval = annot_func(&type_defs, &func_defs[id], func_infos);

            let oldval = &func_infos[id.0];
            if !scc_changed && newval.edges.iter().any(|edge| !oldval.edges.contains(edge)) {
                // Guard on scc_changed to avoid unnecessary comparisons
                scc_changed = true;
            }

            func_infos[id.0] = newval;
        }
    }
}

// `add_func_deps` traverses the expression tree and adds the `CustomFuncId` of every function used
// in it to `deps`.
fn add_func_deps(deps: &mut BTreeSet<ast::CustomFuncId>, expr: &ast::Expr) {
    match expr {
        ast::Expr::ArithOp(ast::ArithOp::Op(_num_type, _op, left, right)) => {
            add_func_deps(deps, left);
            add_func_deps(deps, right);
        }
        ast::Expr::ArithOp(ast::ArithOp::Cmp(_num_type, _cmp, left, right)) => {
            add_func_deps(deps, left);
            add_func_deps(deps, right);
        }
        ast::Expr::ArithOp(ast::ArithOp::Negate(_num_type, expr)) => {
            add_func_deps(deps, expr);
        }
        ast::Expr::ArrayOp(ast::ArrayOp::Item(_, array_expr, idx_expr)) => {
            add_func_deps(deps, array_expr);
            add_func_deps(deps, idx_expr);
        }
        ast::Expr::ArrayOp(ast::ArrayOp::Len(_, array_expr))
        | ast::Expr::ArrayOp(ast::ArrayOp::Pop(_, array_expr)) => {
            add_func_deps(deps, array_expr);
        }
        ast::Expr::ArrayOp(ast::ArrayOp::Push(_, array_expr, item_expr))
        | ast::Expr::ArrayOp(ast::ArrayOp::Replace(_, array_expr, item_expr)) => {
            add_func_deps(deps, array_expr);
            add_func_deps(deps, item_expr);
        }
        ast::Expr::ArrayOp(ast::ArrayOp::Concat(_, left_array_expr, right_array_expr)) => {
            add_func_deps(deps, left_array_expr);
            add_func_deps(deps, right_array_expr);
        }
        ast::Expr::IOOp(_) => {}
        ast::Expr::Ctor(_, _, None) => {}
        ast::Expr::Ctor(_, _, Some(expr)) => add_func_deps(deps, expr),
        ast::Expr::Local(_) => {}
        ast::Expr::Tuple(exprs) => {
            for expr in exprs {
                add_func_deps(deps, expr);
            }
        }
        ast::Expr::Call(_, func_id, arg_expr) => {
            deps.insert(*func_id);
            add_func_deps(deps, arg_expr);
        }
        ast::Expr::Match(matched_expr, cases, _) => {
            add_func_deps(deps, matched_expr);
            for (_, expr) in cases {
                add_func_deps(deps, expr);
            }
        }
        ast::Expr::Let(_, rhs, body) => {
            add_func_deps(deps, rhs);
            add_func_deps(deps, body);
        }
        ast::Expr::ArrayLit(_, exprs) => {
            for expr in exprs {
                add_func_deps(deps, expr);
            }
        }
        ast::Expr::BoolLit(_) => {}
        ast::Expr::ByteLit(_) => {}
        ast::Expr::IntLit(_) => {}
        ast::Expr::FloatLit(_) => {}
    }
}

pub fn func_dependency_graph(program: &ast::Program) -> Graph<ast::CustomFuncId> {
    Graph {
        edges_out: program.funcs.map(|_, funcdef| {
            let mut deps = BTreeSet::new();
            add_func_deps(&mut deps, &funcdef.body);
            deps.into_iter().collect()
        }),
    }
}

pub fn annot_aliases(program: &ast::Program) -> Vec<UniqueInfo> {
    let mut unique_infos = (0..program.funcs.len())
        .map(|_| UniqueInfo::empty())
        .collect::<Vec<_>>();

    for scc in graph::strongly_connected(&func_dependency_graph(program)) {
        annot_scc(
            &program.custom_types,
            &program.funcs,
            &mut unique_infos,
            &scc,
        );
    }

    unique_infos
}

// TODO: make these tests ignore order where it is irrelevant (e.g. edge lists)
#[cfg(test)]
mod test {
    use super::*;
    use crate::data::first_order_ast as ast;
    use im_rc::vector;
    use std::collections::BTreeSet;

    #[test]
    fn test_get_names_in() {
        fn set<T: Ord>(v: Vec<T>) -> BTreeSet<T> {
            use std::iter::FromIterator;
            BTreeSet::from_iter(v.into_iter())
        }
        let with_single_recursive_type = IdVec::from_items(vec![ast::TypeDef {
            variants: IdVec::from_items(vec![
                Some(ast::Type::Tuple(vec![
                    ast::Type::Array(Box::new(ast::Type::Num(ast::NumType::Byte))),
                    ast::Type::Custom(ast::CustomTypeId(0)),
                ])),
                Some(ast::Type::Num(ast::NumType::Byte)),
                Some(ast::Type::HoleArray(Box::new(ast::Type::Num(
                    ast::NumType::Byte,
                )))),
                None,
            ]),
        }]);
        let mapping: Vec<(
            IdVec<ast::CustomTypeId, ast::TypeDef>,
            ast::Type,
            BTreeSet<FieldPath>,
        )> = vec![
            // Types without names:
            (
                IdVec::new(),
                ast::Type::Tuple(vec![
                    ast::Type::Num(ast::NumType::Byte),
                    ast::Type::Num(ast::NumType::Float),
                ]),
                set(vec![]),
            ),
            (
                IdVec::from_items(vec![ast::TypeDef {
                    variants: IdVec::from_items(vec![
                        Some(ast::Type::Num(ast::NumType::Byte)),
                        None,
                    ]),
                }]),
                ast::Type::Tuple(vec![ast::Type::Custom(ast::CustomTypeId(0))]),
                set(vec![]),
            ),
            // Types with names, no typedefs:
            (
                IdVec::new(),
                ast::Type::Array(Box::new(ast::Type::Num(ast::NumType::Byte))),
                set(vec![vector![]]),
            ),
            (
                IdVec::new(),
                ast::Type::Array(Box::new(ast::Type::Array(Box::new(ast::Type::Num(
                    ast::NumType::Int,
                ))))),
                set(vec![vector![], vector![FieldId::ArrayMembers]]),
            ),
            // Recursive types:
            (
                IdVec::new(),
                ast::Type::Tuple(vec![
                    ast::Type::Num(ast::NumType::Float),
                    ast::Type::Array(Box::new(ast::Type::Tuple(vec![
                        ast::Type::Array(Box::new(ast::Type::Bool)),
                        ast::Type::Num(ast::NumType::Byte),
                        ast::Type::HoleArray(Box::new(ast::Type::Bool)),
                    ]))),
                ]),
                set(vec![
                    vector![FieldId::Field(1)],
                    vector![FieldId::Field(1), FieldId::ArrayMembers, FieldId::Field(0)],
                    vector![FieldId::Field(1), FieldId::ArrayMembers, FieldId::Field(2)],
                ]),
            ),
            (
                with_single_recursive_type.clone(),
                ast::Type::Custom(ast::CustomTypeId(0)),
                set(vec![
                    vector![FieldId::Variant(ast::VariantId(0)), FieldId::Field(0)],
                    vector![FieldId::Variant(ast::VariantId(2))],
                ]),
            ),
            (
                with_single_recursive_type.clone(),
                ast::Type::Array(Box::new(ast::Type::Custom(ast::CustomTypeId(0)))),
                set(vec![
                    vector![],
                    vector![
                        FieldId::ArrayMembers,
                        FieldId::Variant(ast::VariantId(0)),
                        FieldId::Field(0)
                    ],
                    vector![FieldId::ArrayMembers, FieldId::Variant(ast::VariantId(2))],
                ]),
            ),
        ];
        for (typedefs, type_, expected_names) in mapping {
            assert_eq!(set(get_names_in(&typedefs, &type_)), expected_names);
        }
    }

    #[test]
    pub fn test_without_aliasing() {
        let ex1 = ast::Expr::ArithOp(ast::ArithOp::Op(
            ast::NumType::Int,
            ast::BinOp::Mul,
            Box::new(ast::Expr::Local(ast::LocalId(0))),
            Box::new(ast::Expr::Local(ast::LocalId(0))),
        ));
        assert_eq!(
            annot_expression(&mut vec![], &[], &ex1),
            UniqueInfo::empty()
        );

        let ex2 = ast::Expr::ArrayLit(
            ast::Type::Array(Box::new(ast::Type::Num(ast::NumType::Int))),
            vec![ast::Expr::ArithOp(ast::ArithOp::Op(
                ast::NumType::Int,
                ast::BinOp::Add,
                Box::new(ast::Expr::IntLit(-10)),
                Box::new(ast::Expr::ArithOp(ast::ArithOp::Op(
                    ast::NumType::Int,
                    ast::BinOp::Mul,
                    Box::new(ast::Expr::IntLit(12)),
                    Box::new(ast::Expr::IntLit(2)),
                ))),
            ))],
        );
        assert_eq!(
            annot_expression(&mut vec![], &[], &ex2),
            UniqueInfo::empty()
        );
    }

    #[test]
    pub fn test_with_basic_array_aliasing() {
        let mut locals = vec![
            UniqueInfo {
                edges: vector![AliasPair::new(vector![FieldId::Field(0)], vector![])],
            },
            UniqueInfo {
                edges: vector![
                    AliasPair::new(
                        vector![FieldId::Field(0), FieldId::ArrayMembers],
                        vector![FieldId::Field(0)]
                    ),
                    AliasPair::new(vector![FieldId::Field(1)], vector![FieldId::Field(1)]),
                ],
            },
        ];
        let basic_aliasing = ast::Expr::Tuple(vec![
            ast::Expr::Local(ast::LocalId(0)),
            ast::Expr::Local(ast::LocalId(0)),
            ast::Expr::Local(ast::LocalId(1)),
        ]);
        assert_eq!(
            annot_expression(&mut locals, &[], &basic_aliasing),
            UniqueInfo {
                edges: vector![
                    AliasPair {
                        arg_field: vector![FieldId::Field(0)],
                        ret_field: vector![FieldId::Field(0)]
                    },
                    AliasPair {
                        arg_field: vector![FieldId::Field(0)],
                        ret_field: vector![FieldId::Field(1)]
                    },
                    AliasPair {
                        arg_field: vector![FieldId::Field(0), FieldId::ArrayMembers],
                        ret_field: vector![FieldId::Field(2), FieldId::Field(0)],
                    },
                    AliasPair {
                        arg_field: vector![FieldId::Field(1)],
                        ret_field: vector![FieldId::Field(2), FieldId::Field(1)],
                    }
                ]
            }
        );
    }
}
