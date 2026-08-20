use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use thiserror::Error;

#[derive(Clone, Debug, Error)]
pub enum Error {
    #[error(
        "the value `{name}` is used with polymorphic recursion: monomorphizing it would \
         require instantiating it at an unbounded number of distinct types"
    )]
    ValNonterminating { name: String },
    #[error(
        "the type `{name}` is used with polymorphic recursion: monomorphizing it would \
         require instantiating it at an unbounded number of distinct types"
    )]
    TypeNonterminating { name: String },
}

fn free_vars(ty: &res::Type, out: &mut BTreeSet<usize>) {
    match ty {
        res::Type::Var(res::TypeParamId(i)) => {
            out.insert(*i);
        }
        res::Type::App(_, args) => {
            for arg in args {
                free_vars(arg, out);
            }
        }
        res::Type::Tuple(items) => {
            for item in items {
                free_vars(item, out);
            }
        }
        res::Type::Func(_, arg, ret) => {
            free_vars(arg, out);
            free_vars(ret, out);
        }
    }
}

type Node<Id> = (Id, usize);
type Edge<Id> = (Node<Id>, Node<Id>);

fn add_application_edges<Id: Copy + Eq + std::hash::Hash>(
    edges: &mut HashMap<Node<Id>, Vec<Node<Id>>>,
    growing: &mut Vec<Edge<Id>>,
    source: Id,
    target: Id,
    args: &[res::Type],
) {
    for (j, arg) in args.iter().enumerate() {
        if let &res::Type::Var(res::TypeParamId(i)) = arg {
            edges.entry((source, i)).or_default().push((target, j));
        } else {
            let mut vars = BTreeSet::new();
            free_vars(arg, &mut vars);
            for i in vars {
                let edge = ((source, i), (target, j));
                edges.entry(edge.0).or_default().push(edge.1);
                growing.push(edge);
            }
        }
    }
}

fn find_growing_cycle<Id: Copy + Eq + std::hash::Hash>(
    edges: &HashMap<Node<Id>, Vec<Node<Id>>>,
    growing: &[Edge<Id>],
) -> Option<Id> {
    for &(from, to) in growing {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        visited.insert(to);
        queue.push_back(to);

        while let Some(node) = queue.pop_front() {
            if node == from {
                return Some(from.0);
            }
            if let Some(succs) = edges.get(&node) {
                for &succ in succs {
                    if visited.insert(succ) {
                        queue.push_back(succ);
                    }
                }
            }
        }
    }
    None
}

fn collect_global_calls<'a>(
    expr: &'a typed::Expr,
    out: &mut Vec<(res::CustomGlobalId, &'a [res::Type])>,
) {
    match expr {
        typed::Expr::Global(res::GlobalId::Custom(id), args) => out.push((*id, args.as_slice())),
        typed::Expr::Global(_, _) => {}
        typed::Expr::Local(_) => {}
        typed::Expr::Tuple(items) => {
            for item in items {
                collect_global_calls(item, out);
            }
        }
        typed::Expr::Lam(_, _, _, _, body, _) => collect_global_calls(body, out),
        typed::Expr::App(_, func, arg) => {
            collect_global_calls(func, out);
            collect_global_calls(arg, out);
        }
        typed::Expr::Match(discrim, cases, _) => {
            collect_global_calls(discrim, out);
            for (_, body) in cases {
                collect_global_calls(body, out);
            }
        }
        typed::Expr::LetMany(bindings, body) => {
            for (_, rhs) in bindings {
                collect_global_calls(rhs, out);
            }
            collect_global_calls(body, out);
        }
        typed::Expr::ArrayLit(_, items) => {
            for item in items {
                collect_global_calls(item, out);
            }
        }
        typed::Expr::ByteLit(_) | typed::Expr::IntLit(_) | typed::Expr::FloatLit(_) => {}
        typed::Expr::Span(_, _, content) => collect_global_calls(content, out),
    }
}

fn collect_type_applications<'a>(
    ty: &'a res::Type,
    out: &mut Vec<(res::CustomTypeId, &'a [res::Type])>,
) {
    match ty {
        res::Type::Var(_) => {}
        res::Type::App(res::TypeId::Custom(id), args) => {
            out.push((*id, args));
            for arg in args {
                collect_type_applications(arg, out);
            }
        }
        res::Type::App(_, args) => {
            for arg in args {
                collect_type_applications(arg, out);
            }
        }
        res::Type::Tuple(items) => {
            for item in items {
                collect_type_applications(item, out);
            }
        }
        res::Type::Func(_, arg, ret) => {
            collect_type_applications(arg, out);
            collect_type_applications(ret, out);
        }
    }
}

fn check_vals(program: &typed::Program) -> Result<(), Error> {
    let mut edges = HashMap::new();
    let mut growing = Vec::new();

    for (val_id, def) in &program.vals {
        let mut calls = Vec::new();
        collect_global_calls(&def.body, &mut calls);
        for (target, args) in calls {
            add_application_edges(&mut edges, &mut growing, val_id, target, args);
        }
    }

    if let Some(culprit) = find_growing_cycle(&edges, &growing) {
        return Err(Error::ValNonterminating {
            name: program.val_symbols[culprit].val_name.0.clone(),
        });
    }

    Ok(())
}

fn check_types(program: &typed::Program) -> Result<(), Error> {
    let mut edges = HashMap::new();
    let mut growing = Vec::new();

    for (type_id, typedef) in &program.custom_types {
        for variant in typedef.variants.values().flatten() {
            let mut applications = Vec::new();
            collect_type_applications(variant, &mut applications);
            for (target, args) in applications {
                add_application_edges(&mut edges, &mut growing, type_id, target, args);
            }
        }
    }

    if let Some(culprit) = find_growing_cycle(&edges, &growing) {
        return Err(Error::TypeNonterminating {
            name: program.custom_type_symbols[culprit].type_name.0.clone(),
        });
    }

    Ok(())
}

pub fn check_polymorphic_recursion(program: &typed::Program) -> Result<(), Error> {
    check_vals(program)?;
    check_types(program)?;
    Ok(())
}
