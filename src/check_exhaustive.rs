use im_rc::{vector, Vector};
use std::collections::BTreeMap;

use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use crate::report_error::Report;
use crate::util::lines::lines;
use crate::{report_pattern, Errors};
use id_collections::IdVec;

#[derive(Clone, Debug)]
pub struct Error {
    not_covered: String,
}

impl Error {
    pub fn new(
        custom_type_symbols: &IdVec<res::CustomTypeId, res::TypeSymbols>,
        not_covered: report_pattern::Pattern,
    ) -> Self {
        Error {
            not_covered: report_pattern::render(custom_type_symbols, &not_covered),
        }
    }

    pub fn report(&self) -> Report {
        Report {
            title: "Non-Exhaustive Pattern Match".to_string(),
            message: Some(format!(
                lines![
                    "This pattern match doesn't cover the following case:",
                    "",
                    "    {}",
                ],
                &self.not_covered
            )),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Relevance {
    Relevant,
    Irrelevant,
}

fn relevance(pat: &typed::Pattern) -> Relevance {
    match &*pat.data {
        typed::PatternData::Any(_) => Relevance::Relevant,
        typed::PatternData::Var(_) => Relevance::Relevant,

        typed::PatternData::Tuple(items) => {
            for item in items {
                if relevance(&item) == Relevance::Irrelevant {
                    return Relevance::Irrelevant;
                }
            }
            Relevance::Relevant
        }

        typed::PatternData::Ctor(_, _, _, Some(content)) => relevance(&content),

        typed::PatternData::Ctor(_, _, _, None) => Relevance::Relevant,

        typed::PatternData::ByteConst(_) => Relevance::Irrelevant,
        typed::PatternData::IntConst(_) => Relevance::Irrelevant,
        typed::PatternData::FloatConst(_) => Relevance::Irrelevant,

        typed::PatternData::Error(_) => Relevance::Irrelevant,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Decision {
    Any,
    PushTuple(usize),
    Ctor {
        id: res::NominalType,
        variant: res::VariantId,
        push_content: bool,
    },
    Pop,
}

fn flatten_to(pat: &typed::Pattern, target: &mut Vec<Decision>) {
    match &*pat.data {
        typed::PatternData::Any(_) => target.push(Decision::Any),
        typed::PatternData::Var(_) => target.push(Decision::Any),

        typed::PatternData::Tuple(items) => {
            target.push(Decision::PushTuple(items.len()));
            for item in items {
                flatten_to(&item, target);
            }
            target.push(Decision::Pop);
        }

        &typed::PatternData::Ctor(id, _, variant, None) => {
            target.push(Decision::Ctor {
                id,
                variant,
                push_content: false,
            });
        }

        &typed::PatternData::Ctor(id, _, variant, Some(ref content)) => {
            target.push(Decision::Ctor {
                id,
                variant,
                push_content: true,
            });
            flatten_to(content, target);
            target.push(Decision::Pop);
        }

        typed::PatternData::IntConst(_)
        | typed::PatternData::ByteConst(_)
        | typed::PatternData::FloatConst(_)
        | typed::PatternData::Error(_) => panic!("Irrelevant patterns should have been skipped"),
    }
}

fn flatten_decisions(pat: &typed::Pattern) -> Vec<Decision> {
    let mut decisions = Vec::new();
    flatten_to(pat, &mut decisions);
    decisions
}

fn unflatten_decisions_from(
    decisions: &Vector<Decision>,
    pos: &mut usize,
) -> report_pattern::Pattern {
    debug_assert!(*pos < decisions.len());
    match &decisions[*pos] {
        Decision::Any => {
            *pos += 1;
            report_pattern::Pattern::Any
        }

        Decision::PushTuple(size) => {
            *pos += 1;
            let items = (0..*size)
                .map(|_| unflatten_decisions_from(decisions, pos))
                .collect();
            debug_assert_eq!(decisions[*pos], Decision::Pop);
            *pos += 1;
            report_pattern::Pattern::Tuple(items)
        }

        Decision::Ctor {
            id,
            variant,
            push_content,
        } => {
            *pos += 1;
            let content = if *push_content {
                let content = unflatten_decisions_from(decisions, pos);
                debug_assert_eq!(decisions[*pos], Decision::Pop);
                *pos += 1;
                Some(Box::new(content))
            } else {
                None
            };
            report_pattern::Pattern::Ctor(*id, *variant, content)
        }

        Decision::Pop => {
            println!("{:?}", decisions);
            unreachable!()
        }
    }
}

fn unflatten_decisions(decisions: &Vector<Decision>) -> report_pattern::Pattern {
    if decisions.is_empty() {
        report_pattern::Pattern::Any
    } else {
        let mut pos = 0;
        let pat = unflatten_decisions_from(decisions, &mut pos);
        debug_assert_eq!(pos, decisions.len());
        pat
    }
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
    PushTuple(usize, Box<DecisionTree>),
    Ctor {
        id: res::NominalType,
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
                new_self = DecisionTree::PushTuple(size, Box::new(new_self));

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
                new_self = DecisionTree::PushTuple(size, Box::new(new_self));

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

            (DecisionTree::PushTuple(_, inner), Some(Decision::Any)) => {
                inner.with_outer(1, &mut |rest| {
                    rest.add_decisions(&decisions[1..]);
                });
            }

            (DecisionTree::PushTuple(size, inner), Some(&Decision::PushTuple(decision_size))) => {
                debug_assert_eq!(*size, decision_size);
                inner.add_decisions(&decisions[1..]);
            }

            (DecisionTree::PushTuple(_, _), Some(_)) => unreachable!(),

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

                DecisionTree::PushTuple(_size, inner) => inner.with_outer(level + 1, body),

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

    fn check_exhaustive_rec(
        &self,
        errors: &mut Errors,
        custom_type_symbols: &IdVec<res::CustomTypeId, res::TypeSymbols>,
        custom_types: &IdVec<res::CustomTypeId, res::TypeDef>,
        path: Vector<Decision>,
    ) {
        match self {
            DecisionTree::End => {}

            DecisionTree::Empty => {
                errors.push(Error::new(custom_type_symbols, unflatten_decisions(&path)))
            }

            DecisionTree::AnyThen(rest) => rest.check_exhaustive_rec(
                errors,
                custom_type_symbols,
                custom_types,
                path + vector![Decision::Any],
            ),

            DecisionTree::PushTuple(size, inner) => inner.check_exhaustive_rec(
                errors,
                custom_type_symbols,
                custom_types,
                path + vector![Decision::PushTuple(*size)],
            ),

            DecisionTree::Ctor { id, cases, default } => {
                let id_num_variants = num_variants(custom_types, *id);
                if cases.len() < num_variants(custom_types, *id) {
                    let first_unhandled = (0..id_num_variants)
                        .map(res::VariantId)
                        .find(|variant| !cases.contains_key(variant))
                        .unwrap();

                    let has_content = match id {
                        res::NominalType::Custom(custom) => {
                            custom_types[custom].variants[first_unhandled].is_some()
                        }
                        res::NominalType::Bool => false,
                        _ => unreachable!(),
                    };

                    let unhandlded_decisions = if has_content {
                        vector![
                            Decision::Ctor {
                                id: *id,
                                variant: first_unhandled,
                                push_content: true
                            },
                            Decision::Any,
                            Decision::Pop
                        ]
                    } else {
                        vector![Decision::Ctor {
                            id: *id,
                            variant: first_unhandled,
                            push_content: false
                        }]
                    };

                    default.check_exhaustive_rec(custom_types, path + unhandlded_decisions)
                } else {
                    for (variant, case) in cases {
                        match case {
                            Case::PushContent(inner) => {
                                inner.check_exhaustive_rec(
                                    custom_types,
                                    path.clone()
                                        + vector![Decision::Ctor {
                                            id: *id,
                                            variant: *variant,
                                            push_content: true,
                                        }],
                                )?;
                            }
                            Case::NoContentThen(rest) => {
                                rest.check_exhaustive_rec(
                                    custom_types,
                                    path.clone()
                                        + vector![Decision::Ctor {
                                            id: *id,
                                            variant: *variant,
                                            push_content: false
                                        }],
                                )?;
                            }
                        }
                    }
                    Ok(())
                }
            }

            DecisionTree::Pop(outer) => {
                outer.check_exhaustive_rec(custom_types, path + vector![Decision::Pop])
            }
        }
    }

    fn check_exhaustive(
        &self,
        errors: &mut Errors,
        custom_type_symbols: &IdVec<res::CustomTypeId, res::TypeSymbols>,
        custom_types: &IdVec<res::CustomTypeId, res::TypeDef>,
    ) {
        self.check_exhaustive_rec(errors, custom_type_symbols, custom_types, vector![]);
    }
}

fn num_variants(
    custom_types: &IdVec<res::CustomTypeId, res::TypeDef>,
    id: res::NominalType,
) -> usize {
    match id {
        res::NominalType::Bool => 2,
        res::NominalType::Custom(custom_id) => custom_types[custom_id].variants.len(),
        _ => unreachable!(),
    }
}

fn check_irrefutable_pattern(
    errors: &mut Errors,
    custom_types: &IdVec<res::CustomTypeId, res::TypeDef>,
    pat: &typed::Pattern,
) {
    let mut tree = DecisionTree::new();
    tree.add(pat);
    tree.check_exhaustive(errors, custom_types);
}

fn check_expr(
    errors: &mut Errors,
    custom_types: &IdVec<res::CustomTypeId, res::TypeDef>,
    expr: &typed::Expr,
) {
    match &*expr.data {
        typed::ExprData::Global(_, _) => {}

        typed::ExprData::Local(_) => {}

        typed::ExprData::Tuple(items) => {
            for item in items {
                check_expr(errors, custom_types, &item);
            }
        }

        typed::ExprData::Lam(_purity, _arg_type, _ret_type, lhs, body, _prof_id) => {
            check_irrefutable_pattern(errors, custom_types, &lhs);
            check_expr(errors, custom_types, &body);
        }

        typed::ExprData::App(_, func, arg) => {
            check_expr(errors, custom_types, &func);
            check_expr(errors, custom_types, &arg);
        }

        typed::ExprData::Match(discrim, cases, _) => {
            check_expr(errors, custom_types, &discrim);

            let mut tree = DecisionTree::new();
            for (pat, _) in cases {
                tree.add(&pat);
            }
            tree.check_exhaustive(errors, custom_types);

            for (_, body) in cases {
                check_expr(errors, custom_types, &body);
            }
        }

        typed::ExprData::LetMany(bindings, body) => {
            for (lhs, rhs) in bindings {
                check_irrefutable_pattern(errors, custom_types, &lhs);
                check_expr(errors, custom_types, &rhs);
            }

            check_expr(errors, custom_types, &body);
        }

        typed::ExprData::ArrayLit(_, items) => {
            for item in items {
                check_expr(errors, custom_types, &item);
            }
        }

        typed::ExprData::ByteLit(_) => {}

        typed::ExprData::IntLit(_) => {}

        typed::ExprData::FloatLit(_) => {}

        typed::ExprData::Error(_) => {}
    }
}

pub fn check_exhaustive(program: &typed::Program, errors: &mut Errors) {
    for (id, def) in &program.vals {
        check_expr(errors, &program.custom_types, &def.body);
    }
}
