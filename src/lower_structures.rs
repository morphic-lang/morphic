use crate::data::flat_ast as flat;
use crate::data::low_ast as low;
use crate::data::repr_specialized_ast_alt as special;
use crate::data::repr_unified_ast as unif;
use crate::util::graph::{self, Graph};
use crate::util::id_vec::IdVec;
use im_rc::OrdMap;
use im_rc::OrdSet;
use std::collections::BTreeSet;

fn lower_type(type_: &special::Type) -> low::Type {
    match type_ {
        special::Type::Bool => low::Type::Bool,
        special::Type::Num(num) => low::Type::Num(*num),
        special::Type::Array(rep, item_type) => {
            low::Type::Array(*rep, Box::new(lower_type(item_type)))
        }
        special::Type::HoleArray(rep, item_type) => {
            low::Type::HoleArray(*rep, Box::new(lower_type(item_type)))
        }
        special::Type::Tuple(types) => low::Type::Tuple(
            types
                .iter()
                .map(|item_type| lower_type(item_type))
                .collect(),
        ),
        special::Type::Variants(variants) => low::Type::Variants(IdVec::from_items(
            variants
                .items
                .iter()
                .map(|item_type| lower_type(item_type))
                .collect(),
        )),
        special::Type::Custom(id) => low::Type::Custom(*id),
    }
}

fn add_size_deps(type_: &special::Type, deps: &mut BTreeSet<special::CustomTypeId>) {
    match type_ {
        special::Type::Bool | special::Type::Num(_) => {}

        special::Type::Array(_, _) | special::Type::HoleArray(_, _) => {}

        special::Type::Tuple(items) => {
            for item in items {
                add_size_deps(item, deps)
            }
        }

        special::Type::Variants(variants) => {
            for (_, variant) in variants {
                add_size_deps(variant, deps)
            }
        }

        special::Type::Custom(custom) => {
            deps.insert(*custom);
        }
    }
}

#[derive(Clone, Debug)]
struct BoxInfo {
    scc: BTreeSet<special::CustomTypeId>,
}

fn find_box_infos(
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
) -> IdVec<special::CustomTypeId, BoxInfo> {
    let size_deps = Graph {
        edges_out: typedefs.map(|_, def| {
            let mut deps = BTreeSet::new();
            add_size_deps(def, &mut deps);
            deps.into_iter().collect()
        }),
    };

    let sccs = graph::strongly_connected(&size_deps);

    let mut maybe_box_infos = IdVec::from_items(vec![None; typedefs.len()]);

    for scc_vec in sccs {
        let scc: BTreeSet<_> = scc_vec.iter().cloned().collect();

        for custom_type in &scc {
            maybe_box_infos[custom_type] = Some(BoxInfo { scc: scc.clone() });
        }
    }

    maybe_box_infos.into_mapped(|_, value| value.unwrap())
}

fn needs_boxing(boxinfo: &BoxInfo, type_: &special::Type) -> bool {
    match type_ {
        special::Type::Bool => false,
        special::Type::Num(_num_type) => false,
        special::Type::Array(_rep, _item_type) => false,
        special::Type::HoleArray(_rep, _item_type) => false,
        special::Type::Tuple(types) => types
            .iter()
            .any(|item_type| needs_boxing(boxinfo, item_type)),
        special::Type::Variants(variants) => variants
            .iter()
            .any(|(_, item_type)| needs_boxing(boxinfo, item_type)),
        special::Type::Custom(id) => boxinfo.scc.contains(id),
    }
}

fn box_type(boxinfo: &BoxInfo, type_: &special::Type) -> low::Type {
    match type_ {
        special::Type::Variants(variants) => low::Type::Variants(IdVec::from_items(
            variants
                .items
                .iter()
                .map(|variant_type| box_type(boxinfo, variant_type))
                .collect(),
        )),
        _ => {
            if needs_boxing(boxinfo, type_) {
                low::Type::Boxed(Box::new(lower_type(type_)))
            } else {
                lower_type(type_)
            }
        }
    }
}

fn find_boxed_types(
    typedefs: &IdVec<special::CustomTypeId, special::Type>,
) -> (
    IdVec<special::CustomTypeId, low::Type>,
    IdVec<special::CustomTypeId, BoxInfo>,
) {
    let box_infos = find_box_infos(typedefs);

    (
        typedefs.map(|id, typedef| box_type(&box_infos[id], typedef)),
        box_infos,
    )
}

#[derive(Clone, Debug)]
struct MoveInfo {
    move_info: OrdMap<flat::LocalId, u64>,
}

#[derive(Clone, Debug)]
struct FutureUsageInfo {
    future_usages: OrdSet<flat::LocalId>,
}

#[derive(Clone, Debug)]
struct AnnotExpr {
    kind: AnnotExprKind,
    move_info: MoveInfo,
}

#[derive(Clone, Debug)]
enum AnnotExprKind {
    Branch(
        flat::LocalId,
        Vec<(special::Condition, AnnotExpr)>,
        special::Type,
    ),
    LetMany(
        Vec<(special::Type, AnnotExpr, FutureUsageInfo)>,
        flat::LocalId,
    ),
    Leaf(special::Expr),
}

fn annotate_expr(
    expr: special::Expr,
    future_usages: &FutureUsageInfo,
    ids_in_scope: usize,
) -> AnnotExpr {
    match expr {
        special::Expr::LetMany(exprs, final_local) => {
            let mut current_future_usages = future_usages.clone();
            current_future_usages.future_usages.insert(final_local);

            let mut let_move_info = MoveInfo {
                move_info: OrdMap::new(),
            };
            if final_local.0 < ids_in_scope {
                if !current_future_usages.future_usages.contains(&final_local) {
                    let_move_info.move_info.insert(final_local, 1);
                } else {
                    let_move_info.move_info.insert(final_local, 0);
                }
            }

            let mut new_bindings_reversed = Vec::new();

            for (index, (type_, binding)) in exprs.into_iter().enumerate().rev() {
                let annotated_binding =
                    annotate_expr(binding, &current_future_usages, ids_in_scope + index);

                let binding_move_info = annotated_binding.move_info.clone();

                new_bindings_reversed.push((
                    type_,
                    annotated_binding,
                    current_future_usages.clone(),
                ));

                for (var, _moves) in &binding_move_info.move_info {
                    if var.0 < ids_in_scope {
                        let entry = let_move_info.move_info.entry(*var).or_insert(0);
                        if !current_future_usages.future_usages.contains(var) {
                            *entry = 1;
                        }
                    }
                }
                for var in binding_move_info.move_info.keys() {
                    current_future_usages.future_usages.insert(*var);
                }

                current_future_usages
                    .future_usages
                    .remove(&flat::LocalId(index + ids_in_scope));
            }

            let mut new_bindings = new_bindings_reversed;
            new_bindings.reverse();

            AnnotExpr {
                kind: AnnotExprKind::LetMany(new_bindings, final_local),
                move_info: let_move_info,
            }
        }

        special::Expr::Branch(discrim, cases, res_type) => {
            let mut branch_move_info = MoveInfo {
                move_info: OrdMap::unit(discrim, 0),
            };
            if !future_usages.future_usages.contains(&discrim) {
                branch_move_info.move_info.insert(discrim, 1);
            }

            let mut new_cases = Vec::new();

            for (cond, body) in cases {
                let annotated_body = annotate_expr(body, future_usages, ids_in_scope);

                for (var, _move_count) in &annotated_body.move_info.move_info {
                    let entry = branch_move_info.move_info.entry(*var).or_insert(0);
                    if !future_usages.future_usages.contains(var) {
                        *entry = 1;
                    }
                }

                new_cases.push((cond, annotated_body));
            }

            AnnotExpr {
                move_info: branch_move_info,
                kind: AnnotExprKind::Branch(discrim, new_cases, res_type),
            }
        }

        _ => AnnotExpr {
            move_info: count_moves(&expr),
            kind: AnnotExprKind::Leaf(expr),
        },
    }
}

impl MoveInfo {
    fn add_borrow(&mut self, local_id: flat::LocalId) {
        self.move_info.entry(local_id).or_insert(0);
    }

    fn add_move(&mut self, local_id: flat::LocalId) {
        *self.move_info.entry(local_id).or_insert(0) += 1;
    }
}

fn count_moves(expr: &special::Expr) -> MoveInfo {
    let mut move_info = MoveInfo {
        move_info: OrdMap::new(),
    };

    match expr {
        special::Expr::Local(local_id) => move_info.add_move(*local_id),
        special::Expr::Call(_purity, _func_id, local_id) => move_info.add_move(*local_id),

        special::Expr::Tuple(local_ids) => {
            for local_id in local_ids {
                move_info.add_move(*local_id);
            }
        }
        special::Expr::TupleField(local_id, _index) => move_info.add_borrow(*local_id),
        special::Expr::WrapVariant(_variants, _variant_id, local_id) => {
            move_info.add_move(*local_id);
        }

        special::Expr::UnwrapVariant(_variant_id, local_id) => move_info.add_move(*local_id),
        special::Expr::WrapCustom(_type_id, local_id) => move_info.add_move(*local_id),
        special::Expr::UnwrapCustom(_type_id, local_id) => move_info.add_move(*local_id),

        special::Expr::ArithOp(arith_op) => match arith_op {
            flat::ArithOp::Op(_, _, local_id1, local_id2)
            | flat::ArithOp::Cmp(_, _, local_id1, local_id2) => {
                move_info.add_move(*local_id1);
                move_info.add_move(*local_id2);
            }
            flat::ArithOp::Negate(_num_type, local_id) => {
                move_info.add_move(*local_id);
            }
        },
        special::Expr::ArrayOp(_rep_choice, _item_type, array_op) => match array_op {
            unif::ArrayOp::Item(array_id, index_id) => {
                move_info.add_borrow(*array_id);
                move_info.add_move(*index_id);
            }
            unif::ArrayOp::Len(array_id) => {
                move_info.add_borrow(*array_id);
            }
            unif::ArrayOp::Push(array_id, item_id) => {
                move_info.add_move(*array_id);
                move_info.add_move(*item_id);
            }
            unif::ArrayOp::Pop(array_id) => {
                move_info.add_move(*array_id);
            }
            unif::ArrayOp::Replace(array_id, item_id) => {
                move_info.add_move(*array_id);
                move_info.add_move(*item_id);
            }
        },
        special::Expr::IoOp(_rep_choice, io_op) => match io_op {
            flat::IOOp::Input => {}
            flat::IOOp::Output(local_id) => {
                move_info.add_borrow(*local_id);
            }
        },

        special::Expr::ArrayLit(_rep_choice, _item_type, elem_ids) => {
            for elem_id in elem_ids {
                move_info.add_move(*elem_id);
            }
        }
        special::Expr::BoolLit(_)
        | special::Expr::ByteLit(_)
        | special::Expr::IntLit(_)
        | special::Expr::FloatLit(_) => {}

        special::Expr::LetMany(_, _) => unreachable![],
        special::Expr::Branch(_, _, _) => unreachable![],
    }

    move_info
}

// we need to add retain and releases
// every time we have a syntactic occurence of a variable, we need to add a retain
// we need to change branches to ifs
// we need to add boxing/unboxing in places

fn lower_structures(_program: special::Program) -> low::Program {
    todo![];
}
