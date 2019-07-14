use failure::Fail;
use std::collections::BTreeMap;

use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use crate::util::id_vec::IdVec;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Relevance {
    Relevant,
    Irrelevant,
}

fn relevance(pat: &typed::Pattern) -> Relevance {
    match pat {
        typed::Pattern::Any(_) => Relevance::Relevant,
        typed::Pattern::Var(_) => Relevance::Relevant,

        typed::Pattern::Tuple(items) => {
            for item in items {
                if relevance(item) == Relevance::Irrelevant {
                    return Relevance::Irrelevant;
                }
            }
            Relevance::Relevant
        }

        typed::Pattern::Ctor(_, _, _, Some(content)) => relevance(content),

        typed::Pattern::Ctor(_, _, _, None) => Relevance::Relevant,

        typed::Pattern::ByteConst(_) => Relevance::Irrelevant,
        typed::Pattern::IntConst(_) => Relevance::Irrelevant,
        typed::Pattern::FloatConst(_) => Relevance::Irrelevant,
    }
}

#[derive(Clone, Copy, Debug)]
enum Decision {
    Any,
    PushTuple(usize),
    Ctor {
        id: res::TypeId,
        variant: res::VariantId,
        push_content: bool,
    },
    Pop,
}

fn flatten_to(pat: &typed::Pattern, target: &mut Vec<Decision>) {
    match pat {
        typed::Pattern::Any(_) => target.push(Decision::Any),
        typed::Pattern::Var(_) => target.push(Decision::Any),

        typed::Pattern::Tuple(items) => {
            target.push(Decision::PushTuple(items.len()));
            for item in items {
                flatten_to(item, target);
            }
            target.push(Decision::Pop);
        }

        &typed::Pattern::Ctor(id, _, variant, None) => {
            target.push(Decision::Ctor {
                id,
                variant,
                push_content: false,
            });
        }

        &typed::Pattern::Ctor(id, _, variant, Some(ref content)) => {
            target.push(Decision::Ctor {
                id,
                variant,
                push_content: true,
            });
            flatten_to(content, target);
            target.push(Decision::Pop);
        }

        typed::Pattern::IntConst(_)
        | typed::Pattern::ByteConst(_)
        | typed::Pattern::FloatConst(_) => panic!("Irrelevant patterns should have been skipped"),
    }
}

fn flatten_decisions(pat: &typed::Pattern) -> Vec<Decision> {
    let mut decisions = Vec::new();
    flatten_to(pat, &mut decisions);
    decisions
}

#[derive(Clone, Debug)]
pub enum Case {
    PushContent(DecisionTree),
    NoContentThen(DecisionTree),
}

#[derive(Clone, Debug)]
pub enum DecisionTree {
    End,
    Empty,
    AnyThen(Box<DecisionTree>),
    PushTuple(Box<DecisionTree>),
    Ctor {
        id: res::TypeId,
        cases: BTreeMap<res::VariantId, Case>,
        default: Box<DecisionTree>,
    },
    Pop(Box<DecisionTree>),
}

impl DecisionTree {
    fn new() -> Self {
        DecisionTree::Empty
    }

    fn add(&mut self, pat: &typed::Pattern) {
        match relevance(pat) {
            Relevance::Irrelevant => {}
            Relevance::Relevant => self.add_decisions(&flatten_decisions(pat)),
        }
    }

    fn add_decisions(&mut self, decisions: &[Decision]) {
        match (&mut *self, decisions.get(0)) {
            (DecisionTree::End, None) => {}
            (DecisionTree::End, Some(_)) => unreachable!(),

            (DecisionTree::Empty, None) => {
                *self = DecisionTree::End;
            }

            (_, None) => unreachable!(),

            (DecisionTree::Empty, Some(Decision::Any)) => {
                *self = DecisionTree::AnyThen(Box::new(DecisionTree::Empty));
                self.add_decisions(decisions); // Try again, now properly initialized
            }

            (DecisionTree::Empty, Some(&Decision::PushTuple(size))) => {
                let mut new_self = DecisionTree::Pop(Box::new(DecisionTree::Empty));
                for _ in 0..size {
                    new_self = DecisionTree::AnyThen(Box::new(new_self));
                }
                new_self = DecisionTree::PushTuple(Box::new(new_self));

                *self = new_self;

                self.add_decisions(decisions); // Try again, now properly initialized
            }

            (
                DecisionTree::Empty,
                Some(&Decision::Ctor {
                    id,
                    variant: _,
                    push_content: _,
                }),
            ) => {
                *self = DecisionTree::Ctor {
                    id,
                    cases: BTreeMap::new(),
                    default: Box::new(DecisionTree::Empty),
                };
                self.add_decisions(decisions); // Try again, now properly initialized
            }

            (DecisionTree::Empty, Some(Decision::Pop)) => unreachable!(),

            (DecisionTree::AnyThen(rest), Some(Decision::Any)) => {
                rest.add_decisions(&decisions[1..]);
            }

            (DecisionTree::AnyThen(rest), Some(&Decision::PushTuple(size))) => {
                // Temporarily replace with dummy value to obtain ownership.  The use of
                // DecisionTree::Empty here is not semantically meaningful.
                let rest_owned = std::mem::replace(rest, Box::new(DecisionTree::Empty));

                let mut new_self = DecisionTree::Pop(rest_owned);
                for _ in 0..size {
                    new_self = DecisionTree::AnyThen(Box::new(new_self));
                }
                new_self = DecisionTree::PushTuple(Box::new(new_self));

                *self = new_self;

                self.add_decisions(decisions); // Try again, now properly initialized
            }

            (
                DecisionTree::AnyThen(rest),
                Some(&Decision::Ctor {
                    id,
                    variant: _,
                    push_content: _,
                }),
            ) => {
                // Temporarily replace with dummy value to obtain ownership.  The use of
                // DecisionTree::Empty here is not semantically meaningful.
                let rest_owned = std::mem::replace(rest, Box::new(DecisionTree::Empty));

                *self = DecisionTree::Ctor {
                    id,
                    cases: BTreeMap::new(),
                    default: rest_owned,
                };

                self.add_decisions(decisions); // Try again, now properly initialized
            }

            (DecisionTree::AnyThen(_), Some(Decision::Pop)) => unreachable!(),

            (DecisionTree::PushTuple(inner), Some(Decision::Any)) => {
                inner.with_outer(1, &mut |rest| {
                    rest.add_decisions(&decisions[1..]);
                });
            }

            (DecisionTree::PushTuple(inner), Some(&Decision::PushTuple(_))) => {
                inner.add_decisions(&decisions[1..]);
            }

            (DecisionTree::PushTuple(_), Some(_)) => unreachable!(),

            (
                DecisionTree::Ctor {
                    id: _,
                    cases,
                    default,
                },
                Some(Decision::Any),
            ) => {
                for (_, case) in cases {
                    match case {
                        Case::NoContentThen(rest) => rest.add_decisions(&decisions[1..]),

                        Case::PushContent(inner) => {
                            inner.with_outer(1, &mut |rest| rest.add_decisions(&decisions[1..]))
                        }
                    }
                }

                default.add_decisions(&decisions[1..]);
            }

            (
                DecisionTree::Ctor { id, cases, default },
                Some(&Decision::Ctor {
                    id: ctor_id,
                    variant,
                    push_content,
                }),
            ) => {
                debug_assert_eq!(*id, ctor_id);

                let case = cases.entry(variant).or_insert_with(|| {
                    if push_content {
                        Case::PushContent(DecisionTree::AnyThen(Box::new(DecisionTree::Pop(
                            default.clone(),
                        ))))
                    } else {
                        Case::NoContentThen((**default).clone())
                    }
                });

                match (case, push_content) {
                    (Case::PushContent(inner), true) => {
                        inner.add_decisions(&decisions[1..]);
                    }

                    (Case::NoContentThen(rest), false) => {
                        rest.add_decisions(&decisions[1..]);
                    }

                    _ => unreachable!(),
                }
            }

            (DecisionTree::Ctor { .. }, Some(_)) => unreachable!(),

            (DecisionTree::Pop(outer), Some(Decision::Pop)) => {
                outer.add_decisions(&decisions[1..]);
            }

            (DecisionTree::Pop(_), Some(_)) => unreachable!(),
        }
    }

    fn with_outer<F>(&mut self, level: usize, body: &mut F)
    where
        F: for<'a> FnMut(&'a mut DecisionTree) -> (),
    {
        if level == 0 {
            body(self);
        } else {
            match self {
                DecisionTree::End => unreachable!(),

                DecisionTree::Empty => unreachable!(),

                DecisionTree::AnyThen(rest) => rest.with_outer(level, body),

                DecisionTree::PushTuple(inner) => inner.with_outer(level + 1, body),

                DecisionTree::Ctor {
                    id: _,
                    cases,
                    default,
                } => {
                    for (_, case) in cases {
                        match case {
                            Case::PushContent(inner) => inner.with_outer(level + 1, body),
                            Case::NoContentThen(rest) => rest.with_outer(level, body),
                        }
                    }

                    default.with_outer(level, body);
                }

                DecisionTree::Pop(outer) => {
                    outer.with_outer(level - 1, body);
                }
            }
        }
    }

    fn is_exhaustive(&self, custom_types: &IdVec<res::CustomTypeId, res::TypeDef>) -> bool {
        match self {
            DecisionTree::End => true,

            DecisionTree::Empty => false,

            DecisionTree::AnyThen(rest) => rest.is_exhaustive(custom_types),

            DecisionTree::PushTuple(inner) => inner.is_exhaustive(custom_types),

            DecisionTree::Ctor { id, cases, default } => {
                if cases.len() < num_variants(custom_types, *id) {
                    default.is_exhaustive(custom_types)
                } else {
                    cases.iter().all(|(_, case)| match case {
                        Case::PushContent(inner) => inner.is_exhaustive(custom_types),
                        Case::NoContentThen(rest) => rest.is_exhaustive(custom_types),
                    })
                }
            }

            DecisionTree::Pop(outer) => outer.is_exhaustive(custom_types),
        }
    }
}

fn num_variants(custom_types: &IdVec<res::CustomTypeId, res::TypeDef>, id: res::TypeId) -> usize {
    match id {
        res::TypeId::Bool => 2,
        res::TypeId::Custom(custom_id) => custom_types[custom_id].variants.len(),
        _ => unreachable!(),
    }
}

fn check_expr(
    custom_types: &IdVec<res::CustomTypeId, res::TypeDef>,
    expr: &typed::Expr,
) -> Result<(), ()> {
    match expr {
        typed::Expr::Global(_, _) => Ok(()),

        typed::Expr::Local(_) => Ok(()),

        typed::Expr::Tuple(items) => {
            for item in items {
                check_expr(custom_types, item)?;
            }
            Ok(())
        }

        typed::Expr::Lam(_purity, _arg_type, _ret_type, lhs, body) => {
            let mut tree = DecisionTree::new();
            tree.add(lhs);
            if !tree.is_exhaustive(custom_types) {
                return Err(());
            }

            check_expr(custom_types, body)?;

            Ok(())
        }

        typed::Expr::App(_, func, arg) => {
            check_expr(custom_types, func)?;
            check_expr(custom_types, arg)?;
            Ok(())
        }

        typed::Expr::Match(discrim, cases, _) => {
            check_expr(custom_types, discrim)?;

            let mut tree = DecisionTree::new();
            for (pat, _) in cases {
                tree.add(pat);
            }
            if !tree.is_exhaustive(custom_types) {
                return Err(());
            }

            for (_, body) in cases {
                check_expr(custom_types, body)?;
            }

            Ok(())
        }

        typed::Expr::Let(lhs, rhs, body) => {
            let mut tree = DecisionTree::new();
            tree.add(lhs);
            if !tree.is_exhaustive(custom_types) {
                return Err(());
            }

            check_expr(custom_types, rhs)?;
            check_expr(custom_types, body)?;

            Ok(())
        }

        typed::Expr::ArrayLit(_, items) => {
            for item in items {
                check_expr(custom_types, item)?;
            }
            Ok(())
        }

        typed::Expr::ByteLit(_) => Ok(()),

        typed::Expr::IntLit(_) => Ok(()),

        typed::Expr::FloatLit(_) => Ok(()),
    }
}

#[derive(Clone, Debug, Fail)]
#[fail(display = "Pattern match is non-exhaustive")]
pub struct Error(res::CustomGlobalId);

pub fn check_exhaustive(program: &typed::Program) -> Result<(), Error> {
    for (id, def) in &program.vals {
        check_expr(&program.custom_types, &def.body).map_err(|()| Error(id))?;
    }
    Ok(())
}
