use crate::data::first_order_ast as ast;
use crate::graph::{self, Graph};
use im_rc::{vector, Vector};
use std::collections::BTreeSet;

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
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
    arg_field: FieldPath,
    ret_field: FieldPath,
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

    fn rm_context(&self, field: FieldId) -> AliasPair {
        debug_assert!(self.arg_field[0] == field);
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
    edges: Vector<AliasPair>,
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
    fn narrow_context(&self, field: FieldId) -> Self {
        UniqueInfo {
            edges: self
                .edges
                .iter()
                .filter(|e| e.arg_field[0] == field)
                .map(|e| e.rm_context(field))
                .collect(),
        }
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

    fn union(&self, other: UniqueInfo) -> Self {
        let mut new = self.clone();
        new.edges.append(other.edges);
        new
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
                    rhs.narrow_context(FieldId::Field(i)),
                );
            }
        }
        ast::Pattern::Ctor(_, _, None) => {}
        ast::Pattern::Ctor(_, variant_id, Some(arg_pattern)) => {
            bind_pattern_locals(
                locals,
                func_infos,
                &arg_pattern,
                rhs.narrow_context(FieldId::Variant(*variant_id)),
            );
        }
        ast::Pattern::BoolConst(_) => {}
        ast::Pattern::IntConst(_) => {}
        ast::Pattern::FloatConst(_) => {}
        ast::Pattern::TextConst(_) => {}
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
        ast::Expr::ArrayOp(ast::ArrayOp::Item(_, array, _, wrapper)) => {
            // The holearray, in the second entry of the returned tuple, aliases the array
            let mut aliases =
                annot_expression(locals, func_infos, array).add_ret_context(FieldId::Field(1));
            aliases.append(
                // The item, in the first entry of the returned tuple, aliases the array contents
                aliases
                    .rm_context(FieldId::ArrayMembers)
                    .add_ret_context(FieldId::Field(0)),
            );
            if let Some((_, variant_id)) = wrapper {
                aliases.add_ret_context(FieldId::Variant(*variant_id));
            }
            aliases
        }
        ast::Expr::ArrayOp(ast::ArrayOp::Len(..)) => UniqueInfo::empty(),
        ast::Expr::ArrayOp(ast::ArrayOp::Push(..)) => UniqueInfo::empty(),
        ast::Expr::ArrayOp(ast::ArrayOp::Pop(..)) => UniqueInfo::empty(),
        ast::Expr::ArrayOp(ast::ArrayOp::Replace(_type, hole_array, item)) => {
            let arr_aliases = annot_expression(locals, func_infos, hole_array);
            let item_aliases = annot_expression(locals, func_infos, item);
            // the new array aliases what the hole-array did, and its members also alias what item aliases
            arr_aliases.union(item_aliases.add_ret_context(FieldId::ArrayMembers))
        }
        ast::Expr::Ctor(_id, variant_id, args) => match args {
            None => UniqueInfo::empty(),
            Some(args) => annot_expression(locals, func_infos, args)
                .add_ret_context(FieldId::Variant(*variant_id)),
        },
        ast::Expr::Local(ast::LocalId(id)) => locals[*id].clone(),
        ast::Expr::Tuple(elems) => {
            let mut info = UniqueInfo::empty();
            for i in 0..elems.len() {
                info = info.union(
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
        ast::Expr::IntLit(..) => UniqueInfo::empty(),
        ast::Expr::FloatLit(..) => UniqueInfo::empty(),
        ast::Expr::TextLit(..) => UniqueInfo::empty(),
    }
}

// Computes the `FieldPath`s in `type_` at which there is a name, and adds them to the end of `names`.
fn add_names_from_type(
    type_defs: &[ast::TypeDef],
    names: &mut Vec<FieldPath>,
    type_: &ast::Type,
    prefix: FieldPath,
) {
    // note that the empty FieldPath refers to the variable in question itself; i.e. if a value
    // contains a field `x` that is an array, it has a name `.x` but if a value *is* an array, then
    // the name is `.`, represented as an empty Vector.
    match type_ {
        ast::Type::Bool | ast::Type::Int | ast::Type::Float => {}
        ast::Type::Text => names.push(prefix),
        ast::Type::Array(item_type) | ast::Type::HoleArray(item_type) => {
            // The array itself:
            names.push(prefix.clone());
            // The names in elements of the array:
            let mut new_prefix = prefix.clone();
            new_prefix.push_back(FieldId::ArrayMembers);
            add_names_from_type(type_defs, names, item_type, new_prefix);
        }
        ast::Type::Tuple(item_types) => {
            for (i, item_type) in item_types.iter().enumerate() {
                let mut new_prefix = prefix.clone();
                new_prefix.push_back(FieldId::Field(i));
                add_names_from_type(type_defs, names, item_type, new_prefix);
            }
        }
        ast::Type::Custom(ast::CustomTypeId(id)) => {
            for (i, variant) in type_defs[*id].variants.iter().enumerate() {
                if let Some(variant_type) = variant {
                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(FieldId::Variant(ast::VariantId(i)));
                    add_names_from_type(type_defs, names, variant_type, new_prefix);
                }
            }
        }
    }
}

fn annot_func(
    type_defs: &[ast::TypeDef],
    func: &ast::FuncDef,
    func_infos: &[UniqueInfo],
) -> UniqueInfo {
    let mut locals = Vec::new();
    // Compute the names in the arg
    let mut names = vec![];
    add_names_from_type(type_defs, &mut names, &func.arg_type, vector![]);
    let arg_unique_info = UniqueInfo {
        edges: names
            .into_iter()
            .map(|fp| AliasPair::new(fp.clone(), fp))
            .collect(),
    };
    bind_pattern_locals(&mut locals, func_infos, &func.arg, arg_unique_info);
    annot_expression(&mut locals, func_infos, &func.body)
}

fn annot_scc(
    type_defs: &[ast::TypeDef],
    func_defs: &[ast::FuncDef],
    func_infos: &mut [UniqueInfo],
    scc: &[ast::CustomFuncId],
) {
    // Update the UniqueInfos for the SCC until we do a pass in which none of them change
    let mut scc_changed = true;
    while scc_changed {
        scc_changed = false;
        for ast::CustomFuncId(id) in scc {
            let newval = annot_func(&type_defs, &func_defs[*id], func_infos);

            if !scc_changed && newval != func_infos[*id] {
                // Guard on scc_changed to avoid unnecessary comparisons
                scc_changed = true;
            }

            func_infos[*id] = newval;
        }
    }
}

// `add_func_deps` traverses the expression tree and the `CustomFuncId` of every function used
// in it to `deps.
pub fn add_func_deps(deps: &mut BTreeSet<ast::CustomFuncId>, expr: &ast::Expr) {
    match expr {
        ast::Expr::ArithOp(ast::ArithOp::IntOp(_, left, right)) => {
            add_func_deps(deps, left);
            add_func_deps(deps, right);
        }
        ast::Expr::ArithOp(ast::ArithOp::FloatOp(_, left, right)) => {
            add_func_deps(deps, left);
            add_func_deps(deps, right);
        }
        ast::Expr::ArithOp(ast::ArithOp::IntCmp(_, left, right)) => {
            add_func_deps(deps, left);
            add_func_deps(deps, right);
        }
        ast::Expr::ArithOp(ast::ArithOp::FloatCmp(_, left, right)) => {
            add_func_deps(deps, left);
            add_func_deps(deps, right);
        }
        ast::Expr::ArithOp(ast::ArithOp::NegateInt(expr)) => add_func_deps(deps, expr),
        ast::Expr::ArithOp(ast::ArithOp::NegateFloat(expr)) => add_func_deps(deps, expr),
        ast::Expr::ArrayOp(ast::ArrayOp::Item(_, array_expr, idx_expr, _)) => {
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
        ast::Expr::IntLit(_) => {}
        ast::Expr::FloatLit(_) => {}
        ast::Expr::TextLit(_) => {}
    }
}

pub fn annot_aliases(program: &ast::Program) -> Vec<UniqueInfo> {
    let dep_graph = Graph {
        edges_out: program
            .funcs
            .iter()
            .map(|funcdef| {
                let mut deps = BTreeSet::new();
                add_func_deps(&mut deps, &funcdef.body);
                deps.iter()
                    .map(|&ast::CustomFuncId(id)| graph::NodeId(id))
                    .collect()
            })
            .collect(),
    };

    let mut unique_infos = (0..program.funcs.len())
        .map(|_| UniqueInfo::empty())
        .collect::<Vec<_>>();

    for scc in graph::strongly_connected(&dep_graph) {
        let scc_ids = scc
            .iter()
            .map(|&graph::NodeId(id)| ast::CustomFuncId(id))
            .collect::<Vec<_>>();
        annot_scc(
            &program.custom_types,
            &program.funcs,
            &mut unique_infos,
            &scc_ids,
        );
    }

    unique_infos
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    pub fn test_without_aliasing() {
        let ex1 = ast::Expr::ArithOp(ast::ArithOp::IntOp(
            ast::BinOp::Mul,
            Box::new(ast::Expr::Local(ast::LocalId(0))),
            Box::new(ast::Expr::Local(ast::LocalId(0))),
        ));
        assert_eq!(
            annot_expression(&mut vec![], &[], &ex1),
            UniqueInfo::empty()
        );

        let ex2 = ast::Expr::ArrayLit(
            ast::Type::Array(Box::new(ast::Type::Int)),
            vec![ast::Expr::ArithOp(ast::ArithOp::IntOp(
                ast::BinOp::Add,
                Box::new(ast::Expr::IntLit(-10)),
                Box::new(ast::Expr::ArithOp(ast::ArithOp::IntOp(
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
