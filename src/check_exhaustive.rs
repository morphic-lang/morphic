use im_rc::{vector, Vector};
use std::collections::BTreeMap;
use std::io;

use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use crate::file_cache::FileCache;
use crate::report_error::{locate_path, locate_span, Locate};
use crate::report_pattern;
use id_collections::IdVec;

#[derive(Clone, Debug)]
struct RawErrorKind {
    not_covered: report_pattern::Pattern,
}

type RawError = Locate<RawErrorKind>;

#[derive(Clone, Debug)]
pub struct ErrorKind {
    not_covered: String,
}

pub type Error = Locate<ErrorKind>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    Root,
    CtorArg,
}

impl RawErrorKind {
    fn render(
        &self,
        custom_type_symbols: &IdVec<res::CustomTypeId, res::TypeSymbols>,
    ) -> ErrorKind {
        ErrorKind {
            not_covered: report_pattern::render(custom_type_symbols, &self.not_covered),
        }
    }
}

impl Error {
    pub fn report(&self, dest: &mut impl io::Write, files: &FileCache) -> io::Result<()> {
        self.report_with(dest, files, |err| {
            (
                "Non-Exhaustive Pattern Match",
                format!(
                    lines![
                        "This pattern match doesn't cover the following case:",
                        "",
                        "    {}",
                    ],
                    &err.not_covered
                ),
            )
        })
    }
}

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

        typed::Pattern::Span(_, _, content) => relevance(content),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

        typed::Pattern::Span(_, _, content) => flatten_to(content, target),
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
        custom_types: &IdVec<res::CustomTypeId, res::TypeDef>,
        path: Vector<Decision>,
    ) -> Result<(), Vector<Decision>> {
        match self {
            DecisionTree::End => Ok(()),

            DecisionTree::Empty => Err(path),

            DecisionTree::AnyThen(rest) => {
                rest.check_exhaustive_rec(custom_types, path + vector![Decision::Any])
            }

            DecisionTree::PushTuple(size, inner) => {
                inner.check_exhaustive_rec(custom_types, path + vector![Decision::PushTuple(*size)])
            }

            DecisionTree::Ctor { id, cases, default } => {
                let id_num_variants = num_variants(custom_types, *id);
                if cases.len() < num_variants(custom_types, *id) {
                    let first_unhandled = (0..id_num_variants)
                        .map(res::VariantId)
                        .find(|variant| !cases.contains_key(variant))
                        .unwrap();

                    let has_content = match id {
                        res::TypeId::Custom(custom) => {
                            custom_types[custom].variants[first_unhandled].is_some()
                        }
                        res::TypeId::Bool => false,
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
        custom_types: &IdVec<res::CustomTypeId, res::TypeDef>,
    ) -> Result<(), RawError> {
        self.check_exhaustive_rec(custom_types, vector![])
            .map_err(|decisions| {
                RawErrorKind {
                    not_covered: unflatten_decisions(&decisions),
                }
                .into()
            })
    }
}

fn num_variants(custom_types: &IdVec<res::CustomTypeId, res::TypeDef>, id: res::TypeId) -> usize {
    match id {
        res::TypeId::Bool => 2,
        res::TypeId::Custom(custom_id) => custom_types[custom_id].variants.len(),
        _ => unreachable!(),
    }
}

fn check_irrefutable_pattern(
    custom_types: &IdVec<res::CustomTypeId, res::TypeDef>,
    pat: &typed::Pattern,
) -> Result<(), RawError> {
    let mut tree = DecisionTree::new();
    tree.add(pat);
    tree.check_exhaustive(custom_types).map_err(|err| {
        if let typed::Pattern::Span(lo, hi, _) = pat {
            locate_span(*lo, *hi)(err)
        } else {
            err
        }
    })
}

fn check_expr(
    custom_types: &IdVec<res::CustomTypeId, res::TypeDef>,
    expr: &typed::Expr,
) -> Result<(), RawError> {
    match expr {
        typed::Expr::Global(_, _) => Ok(()),

        typed::Expr::Local(_) => Ok(()),

        typed::Expr::Tuple(items) => {
            for item in items {
                check_expr(custom_types, item)?;
            }
            Ok(())
        }

        typed::Expr::Lam(_purity, _arg_type, _ret_type, lhs, body, _prof_id) => {
            check_irrefutable_pattern(custom_types, lhs)?;
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
            tree.check_exhaustive(custom_types)?;

            for (_, body) in cases {
                check_expr(custom_types, body)?;
            }

            Ok(())
        }

        typed::Expr::LetMany(bindings, body) => {
            for (lhs, rhs) in bindings {
                check_irrefutable_pattern(custom_types, lhs)?;
                check_expr(custom_types, rhs)?;
            }

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

        typed::Expr::Span(lo, hi, content) => {
            check_expr(custom_types, content).map_err(locate_span(*lo, *hi))
        }
    }
}

pub fn check_exhaustive(program: &typed::Program) -> Result<(), Error> {
    for (id, def) in &program.vals {
        check_expr(&program.custom_types, &def.body)
            .map_err(locate_path(
                &program.mod_symbols[program.val_symbols[id].mod_].file,
            ))
            .map_err(|err| err.map(|raw_error| raw_error.render(&program.custom_type_symbols)))?;
    }
    Ok(())
}
