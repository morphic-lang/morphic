use std::collections::{BTreeMap, BTreeSet};
use std::iter::repeat_with;

use crate::data::closure_specialized_ast as special;
use crate::data::first_order_ast as first_ord;
use crate::data::intrinsics as intrs;
use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast::{self as res, ArrayOp, IoOp};
use crate::util::id_vec::IdVec;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum LeafFuncCase {
    Lam(special::LamId),
    Intrinsic(intrs::Intrinsic),
    ArrayOp(res::ArrayOp, special::Type),
    ArrayReplace(special::Type),
    IoOp(res::IoOp),
    Panic(special::Type),
    Ctor(special::CustomTypeId, res::VariantId),
}

fn add_rep_leaves(
    opaque_reps: &IdVec<special::OpaqueFuncRepId, special::FuncRep>,
    rep: &special::FuncRep,
    leaves: &mut BTreeSet<LeafFuncCase>,
) {
    for case in &rep.0 {
        match case {
            &special::FuncCase::Lam(lam) => {
                leaves.insert(LeafFuncCase::Lam(lam));
            }

            &special::FuncCase::Opaque(opaque) => {
                add_rep_leaves(opaque_reps, &opaque_reps[opaque], leaves);
            }

            &special::FuncCase::Intrinsic(intr) => {
                leaves.insert(LeafFuncCase::Intrinsic(intr));
            }

            special::FuncCase::ArrayOp(op, item_type) => {
                leaves.insert(LeafFuncCase::ArrayOp(*op, item_type.clone()));
            }

            special::FuncCase::ArrayReplace(item_type) => {
                leaves.insert(LeafFuncCase::ArrayReplace(item_type.clone()));
            }

            &special::FuncCase::IoOp(op) => {
                leaves.insert(LeafFuncCase::IoOp(op));
            }

            special::FuncCase::Panic(ret_type) => {
                leaves.insert(LeafFuncCase::Panic(ret_type.clone()));
            }

            &special::FuncCase::Ctor(custom, variant) => {
                leaves.insert(LeafFuncCase::Ctor(custom, variant));
            }
        }
    }
}

id_type!(LoweredClosureId);

id_type!(DispatchFuncId);

// We factor out this 'mapping' structure because its associated methods rely heavily on error-prone
// raw index manipulation, and we want to be able to able to reason about it independently of the
// rest of the algorithm.
#[derive(Clone, Debug)]
struct IdMapping {
    num_orig_custom_types: usize,
    num_orig_globals: usize,
    num_orig_lams: usize,
}

#[derive(Clone, Debug)]
struct ProgramParts {
    mod_symbols: IdVec<res::ModId, res::ModSymbols>,

    custom_types: IdVec<special::CustomTypeId, first_ord::TypeDef>,
    closures: IdVec<LoweredClosureId, first_ord::TypeDef>,

    custom_type_symbols: IdVec<special::CustomTypeId, mono::TypeSymbols>,

    globals: IdVec<special::CustomGlobalId, first_ord::FuncDef>,
    lam_bodies: IdVec<special::LamId, first_ord::FuncDef>,
    main: first_ord::FuncDef,
    dispatch_funcs: IdVec<DispatchFuncId, first_ord::FuncDef>,

    global_symbols: IdVec<special::CustomGlobalId, mono::ValSymbols>,
    lam_body_symbols: IdVec<special::LamId, lifted::LamSymbols>,

    profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
}

impl IdMapping {
    fn map_custom_type(&self, custom: special::CustomTypeId) -> first_ord::CustomTypeId {
        debug_assert!(custom.0 < self.num_orig_custom_types);
        first_ord::CustomTypeId(custom.0)
    }

    fn map_closure_type(&self, closure: LoweredClosureId) -> first_ord::CustomTypeId {
        first_ord::CustomTypeId(self.num_orig_custom_types + closure.0)
    }

    fn unmap_closure_type(&self, custom: first_ord::CustomTypeId) -> Option<LoweredClosureId> {
        if self.num_orig_custom_types <= custom.0 {
            Some(LoweredClosureId(custom.0 - self.num_orig_custom_types))
        } else {
            None
        }
    }

    fn map_global(&self, global: special::CustomGlobalId) -> first_ord::CustomFuncId {
        debug_assert!(global.0 < self.num_orig_globals);
        first_ord::CustomFuncId(global.0)
    }

    fn map_lam_body(&self, lam: special::LamId) -> first_ord::CustomFuncId {
        debug_assert!(lam.0 < self.num_orig_lams);
        first_ord::CustomFuncId(self.num_orig_globals + lam.0)
    }

    fn map_dispatch_func(&self, dispatch: DispatchFuncId) -> first_ord::CustomFuncId {
        first_ord::CustomFuncId(
            self.num_orig_globals + self.num_orig_lams + 1 /* for main */ + dispatch.0,
        )
    }

    fn assemble_program(&self, parts: ProgramParts) -> first_ord::Program {
        debug_assert_eq!(parts.custom_types.len(), self.num_orig_custom_types);
        debug_assert_eq!(parts.globals.len(), self.num_orig_globals);
        debug_assert_eq!(parts.lam_bodies.len(), self.num_orig_lams);

        let num_closures = parts.closures.items.len();

        let mut custom_types = parts.custom_types.items;
        custom_types.extend(parts.closures.items);

        let mut custom_type_symbols = parts
            .custom_type_symbols
            .into_mapped(|_, symbols| first_ord::CustomTypeSymbols::CustomType(symbols))
            .items;
        custom_type_symbols
            .extend(repeat_with(|| first_ord::CustomTypeSymbols::ClosureType).take(num_closures));

        let num_dispatch_funcs = parts.dispatch_funcs.len();

        let mut funcs = parts.globals.items;
        funcs.extend(parts.lam_bodies.items);
        funcs.push(parts.main);
        funcs.extend(parts.dispatch_funcs.items);

        let mut func_symbols = parts
            .global_symbols
            .into_mapped(|_, symbols| first_ord::FuncSymbols::Global(symbols))
            .items;
        func_symbols.extend(
            parts
                .lam_body_symbols
                .into_mapped(|_, symbols| first_ord::FuncSymbols::Lam(symbols))
                .items,
        );
        func_symbols.push(first_ord::FuncSymbols::MainWrapper);
        func_symbols
            .extend(repeat_with(|| first_ord::FuncSymbols::Dispatch).take(num_dispatch_funcs));

        first_ord::Program {
            mod_symbols: parts.mod_symbols,
            custom_types: IdVec::from_items(custom_types),
            custom_type_symbols: IdVec::from_items(custom_type_symbols),
            funcs: IdVec::from_items(funcs),
            func_symbols: IdVec::from_items(func_symbols),
            profile_points: parts.profile_points,
            main: first_ord::CustomFuncId(self.num_orig_globals + self.num_orig_lams),
        }
    }
}

#[derive(Clone, Debug)]
struct LoweredClosure {
    typedef: first_ord::TypeDef,
    case_variants: BTreeMap<LeafFuncCase, first_ord::VariantId>,
}

#[derive(Clone, Debug)]
struct Context<'a> {
    mapping: &'a IdMapping,
    program: &'a special::Program,

    lowered_ids: BTreeMap<BTreeSet<LeafFuncCase>, LoweredClosureId>,
    lowered_closures: IdVec<LoweredClosureId, Option<LoweredClosure>>,

    dispatch_ids: BTreeMap<LoweredClosureId, DispatchFuncId>,
    dispatch_funcs: IdVec<DispatchFuncId, first_ord::FuncDef>,

    dispatch_func_symbols: IdVec<DispatchFuncId, BTreeSet<LeafFuncCase>>,
}

#[derive(Clone, Debug)]
struct LocalIdMapping {
    num_captures: usize,
}

impl LocalIdMapping {
    fn map_capture(&self, capture: lifted::CaptureId) -> first_ord::LocalId {
        debug_assert!(capture.0 < self.num_captures);
        first_ord::LocalId(capture.0)
    }

    fn map_local(&self, local: lifted::LocalId) -> first_ord::LocalId {
        first_ord::LocalId(self.num_captures + local.0)
    }
}

// TODO: Add a termination checker for globals otherwise this pass causes undefined behavior for
// globals which panic or loop infinitely on evaluation
fn is_atomic(expr: &special::Expr) -> bool {
    match expr {
        special::Expr::App(Purity::Impure, _, _, _, _, _)
        | special::Expr::App(Purity::Pure, _, _, _, _, _)
        | special::Expr::Tuple(_)
        | special::Expr::Lam(_, _, _)
        | special::Expr::Match(_, _, _)
        | special::Expr::LetMany(_, _)
        | special::Expr::ArrayLit(_, _) => false,

        special::Expr::Intrinsic(_, _)
        | special::Expr::ArrayOp(_, _, _)
        | special::Expr::IoOp(_, _)
        | special::Expr::Panic(_, _)
        | special::Expr::NullaryCtor(_, _)
        | special::Expr::Ctor(_, _, _)
        | special::Expr::Global(_)
        | special::Expr::Local(_)
        | special::Expr::Capture(_)
        | special::Expr::BoolLit(_)
        | special::Expr::ByteLit(_)
        | special::Expr::IntLit(_)
        | special::Expr::FloatLit(_) => true,
    }
}

impl<'a> Context<'a> {
    fn new(mapping: &'a IdMapping, program: &'a special::Program) -> Self {
        Context {
            mapping,
            program,

            lowered_ids: BTreeMap::new(),
            lowered_closures: IdVec::new(),

            dispatch_ids: BTreeMap::new(),
            dispatch_funcs: IdVec::new(),

            dispatch_func_symbols: IdVec::new(),
        }
    }

    fn lower_env(&mut self, case: &LeafFuncCase) -> Option<first_ord::Type> {
        match case {
            LeafFuncCase::Lam(lam) => {
                let captures = &self.program.lams[lam].captures;

                let lowered_captures = captures
                    .iter()
                    .map(|(_, capture)| self.lower_type(capture))
                    .collect();

                Some(first_ord::Type::Tuple(lowered_captures))
            }
            LeafFuncCase::Intrinsic(_) => None,
            LeafFuncCase::ArrayOp(_, _) => None,
            LeafFuncCase::ArrayReplace(item_type) => Some(first_ord::Type::HoleArray(Box::new(
                self.lower_type(item_type),
            ))),
            LeafFuncCase::IoOp(_) => None,
            LeafFuncCase::Panic(_) => None,
            LeafFuncCase::Ctor(_, _) => None,
        }
    }

    fn lower_closure(&mut self, rep: &special::FuncRep) -> LoweredClosureId {
        let cases = {
            let mut cases = BTreeSet::new();
            add_rep_leaves(&self.program.opaque_reps, rep, &mut cases);
            cases
        };

        if let Some(&existing) = self.lowered_ids.get(&cases) {
            return existing;
        }

        let id = self.lowered_closures.push(None);
        self.lowered_ids.insert(cases.clone(), id);

        let mut variants = IdVec::new();
        let mut case_variants = BTreeMap::new();

        for (idx, case) in cases.into_iter().enumerate() {
            let variant_id = first_ord::VariantId(idx);

            {
                let pushed_id = variants.push(self.lower_env(&case));
                debug_assert_eq!(pushed_id, variant_id);
            }

            case_variants.insert(case, variant_id);
        }

        debug_assert!(self.lowered_closures[id].is_none());

        self.lowered_closures[id] = Some(LoweredClosure {
            typedef: first_ord::TypeDef { variants },
            case_variants,
        });

        id
    }

    fn make_dispatch_func(
        &mut self,
        lowered_id: LoweredClosureId,
        purity: Purity,
        arg_type: first_ord::Type,
        ret_type: first_ord::Type,
    ) -> DispatchFuncId {
        if let Some(&existing) = self.dispatch_ids.get(&lowered_id) {
            return existing;
        }

        let lowered = self.lowered_closures[lowered_id]
            .as_ref()
            .expect("Lowered closure definition should be completed by the time we query it")
            .clone();

        // Convenience functions to make programmatic AST generation a little less painful

        const fn local(idx: usize) -> first_ord::Expr {
            first_ord::Expr::Local(first_ord::LocalId(idx))
        }

        let func_rep_type = first_ord::Type::Custom(self.mapping.map_closure_type(lowered_id));

        static FUNC_REP_LOCAL: first_ord::Expr = local(0);
        static ARG_LOCAL: first_ord::Expr = local(1);
        static ENV_LOCAL: first_ord::Expr = local(2); // For use in match branch bodies; may not exist in all branches

        fn with_args(types: Vec<first_ord::Type>, body: first_ord::Expr) -> first_ord::Expr {
            first_ord::Expr::LetMany(
                vec![(
                    first_ord::Pattern::Tuple(
                        types.into_iter().map(first_ord::Pattern::Var).collect(),
                    ),
                    ARG_LOCAL.clone(),
                )],
                Box::new(body),
            )
        }

        let func = first_ord::FuncDef {
            purity,
            arg_type: first_ord::Type::Tuple(vec![func_rep_type.clone(), arg_type.clone()]),
            ret_type: ret_type.clone(),
            arg: first_ord::Pattern::Tuple(vec![
                // LocalId(0) is the closure representation
                first_ord::Pattern::Var(func_rep_type.clone()),
                // LocalId(1) is the main argument
                first_ord::Pattern::Var(arg_type.clone()),
            ]),
            body: first_ord::Expr::Match(
                Box::new(FUNC_REP_LOCAL.clone()),
                lowered
                    .case_variants
                    .iter()
                    .map(|(case, variant)| {
                        // If this is Some(...), then LocalId(2) is the environment
                        let env_pat = lowered.typedef.variants[variant]
                            .clone()
                            .map(first_ord::Pattern::Var);

                        let body = match case {
                            LeafFuncCase::Lam(lam) => {
                                debug_assert!(env_pat.is_some());

                                let lam_body_func = self.mapping.map_lam_body(*lam);

                                if self.program.lams[lam].captures.is_empty() {
                                    first_ord::Expr::Call(
                                        purity,
                                        lam_body_func,
                                        Box::new(ARG_LOCAL.clone()),
                                    )
                                } else {
                                    first_ord::Expr::Call(
                                        purity,
                                        lam_body_func,
                                        Box::new(first_ord::Expr::Tuple(vec![
                                            ENV_LOCAL.clone(), // Environment
                                            ARG_LOCAL.clone(), // Argument
                                        ])),
                                    )
                                }
                            }

                            LeafFuncCase::Intrinsic(intr) => {
                                debug_assert!(env_pat.is_none());

                                first_ord::Expr::Intrinsic(*intr, Box::new(ARG_LOCAL.clone()))
                            }

                            LeafFuncCase::ArrayOp(op, item_type) => {
                                let lowered_item_type = self.lower_type(item_type);

                                match op {
                                    ArrayOp::Get => {
                                        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Get(
                                            lowered_item_type,
                                            Box::new(local(2)), // Array
                                            Box::new(local(3)), // Index
                                        ))
                                    }

                                    ArrayOp::Extract => {
                                        let ret_parts =
                                            if let first_ord::Type::Tuple(ret_parts) = &ret_type {
                                                ret_parts
                                            } else {
                                                unreachable!()
                                            };

                                        debug_assert_eq!(ret_parts.len(), 2);

                                        let replacer_type = if let first_ord::Type::Custom(custom) =
                                            &ret_parts[1]
                                        {
                                            *custom
                                        } else {
                                            unreachable!()
                                        };

                                        let replacer_variant = self.case_variant(
                                            self.mapping.unmap_closure_type(replacer_type).unwrap(),
                                            &LeafFuncCase::ArrayReplace(item_type.clone()),
                                        );

                                        with_args(
                                            vec![
                                                first_ord::Type::Array(Box::new(
                                                    lowered_item_type.clone(),
                                                )),
                                                first_ord::Type::Num(first_ord::NumType::Int),
                                            ],
                                            first_ord::Expr::LetMany(
                                                vec![(
                                                    first_ord::Pattern::Tuple(vec![
                                                        // LocalId(4) is the returned item
                                                        first_ord::Pattern::Var(
                                                            lowered_item_type.clone(),
                                                        ),
                                                        // LocalId(5) is the hole array
                                                        first_ord::Pattern::Var(
                                                            first_ord::Type::HoleArray(Box::new(
                                                                lowered_item_type.clone(),
                                                            )),
                                                        ),
                                                    ]),
                                                    first_ord::Expr::ArrayOp(
                                                        first_ord::ArrayOp::Extract(
                                                            lowered_item_type,
                                                            Box::new(local(2)), // Array
                                                            Box::new(local(3)), // Index
                                                        ),
                                                    ),
                                                )],
                                                Box::new(first_ord::Expr::Tuple(vec![
                                                    local(4),
                                                    first_ord::Expr::Ctor(
                                                        replacer_type,
                                                        replacer_variant,
                                                        Some(Box::new(local(5))),
                                                    ),
                                                ])),
                                            ),
                                        )
                                    }

                                    ArrayOp::Len => {
                                        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Len(
                                            lowered_item_type,
                                            Box::new(ARG_LOCAL.clone()),
                                        ))
                                    }

                                    ArrayOp::Push => {
                                        with_args(
                                            vec![
                                                first_ord::Type::Array(Box::new(
                                                    lowered_item_type.clone(),
                                                )),
                                                lowered_item_type.clone(),
                                            ],
                                            first_ord::Expr::ArrayOp(first_ord::ArrayOp::Push(
                                                lowered_item_type,
                                                Box::new(local(2)), // Array
                                                Box::new(local(3)), // Item
                                            )),
                                        )
                                    }

                                    ArrayOp::Reserve => {
                                        with_args(
                                            vec![
                                                first_ord::Type::Array(Box::new(
                                                    lowered_item_type.clone(),
                                                )),
                                                first_ord::Type::Num(first_ord::NumType::Int),
                                            ],
                                            first_ord::Expr::ArrayOp(first_ord::ArrayOp::Reserve(
                                                lowered_item_type,
                                                Box::new(local(2)), // Array
                                                Box::new(local(3)), // Capacity
                                            )),
                                        )
                                    }

                                    ArrayOp::Pop => {
                                        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Pop(
                                            lowered_item_type,
                                            Box::new(ARG_LOCAL.clone()),
                                        ))
                                    }
                                }
                            }

                            LeafFuncCase::ArrayReplace(item_type) => {
                                debug_assert!(env_pat.is_some());

                                let lowered_item_type = self.lower_type(item_type);

                                first_ord::Expr::ArrayOp(first_ord::ArrayOp::Replace(
                                    lowered_item_type,
                                    Box::new(ENV_LOCAL.clone()), // Hole array (environment)
                                    Box::new(ARG_LOCAL.clone()), // Item (argument)
                                ))
                            }

                            LeafFuncCase::IoOp(op) => {
                                debug_assert!(env_pat.is_none());
                                debug_assert_eq!(purity, Purity::Impure);

                                match op {
                                    IoOp::Input => first_ord::Expr::IoOp(first_ord::IoOp::Input),
                                    IoOp::Output => first_ord::Expr::IoOp(first_ord::IoOp::Output(
                                        Box::new(ARG_LOCAL.clone()),
                                    )),
                                }
                            }

                            LeafFuncCase::Panic(ret_type) => {
                                debug_assert!(env_pat.is_none());

                                let lowered_ret_type = self.lower_type(ret_type);

                                first_ord::Expr::Panic(
                                    lowered_ret_type,
                                    Box::new(ARG_LOCAL.clone()),
                                )
                            }

                            LeafFuncCase::Ctor(custom, variant) => {
                                debug_assert!(env_pat.is_none());

                                first_ord::Expr::Ctor(
                                    self.mapping.map_custom_type(*custom),
                                    first_ord::VariantId(variant.0),
                                    // This constructor is necessarily non-nullary, because we are
                                    // calling it as a function
                                    Some(Box::new(ARG_LOCAL.clone())),
                                )
                            }
                        };

                        let pat = first_ord::Pattern::Ctor(
                            self.mapping.map_closure_type(lowered_id),
                            *variant,
                            env_pat.map(Box::new),
                        );

                        (pat, body)
                    })
                    .collect(),
                ret_type,
            ),
            profile_point: None,
        };

        let func_id = self.dispatch_funcs.push(func);
        self.dispatch_ids.insert(lowered_id, func_id);

        let _ = self.dispatch_func_symbols.push(
            lowered
                .case_variants
                .keys()
                .map(|case| case.clone())
                .collect(),
        );

        func_id
    }

    fn case_variant(&self, lowered: LoweredClosureId, case: &LeafFuncCase) -> first_ord::VariantId {
        self.lowered_closures[lowered]
            .as_ref()
            .expect("Lowered closure definition should be completed by the time we query it")
            .case_variants[case]
    }

    fn lower_type(&mut self, type_: &special::Type) -> first_ord::Type {
        match type_ {
            special::Type::Bool => first_ord::Type::Bool,
            special::Type::Byte => first_ord::Type::Num(first_ord::NumType::Byte),
            special::Type::Int => first_ord::Type::Num(first_ord::NumType::Int),
            special::Type::Float => first_ord::Type::Num(first_ord::NumType::Float),

            special::Type::Array(item_type) => {
                first_ord::Type::Array(Box::new(self.lower_type(item_type)))
            }

            special::Type::Tuple(items) => {
                first_ord::Type::Tuple(items.iter().map(|item| self.lower_type(item)).collect())
            }

            special::Type::Func(rep) => {
                let lowered_id = self.lower_closure(rep);
                first_ord::Type::Custom(self.mapping.map_closure_type(lowered_id))
            }

            &special::Type::Custom(custom) => {
                first_ord::Type::Custom(self.mapping.map_custom_type(custom))
            }
        }
    }

    fn lower_pattern(&mut self, pat: &special::Pattern) -> first_ord::Pattern {
        match pat {
            special::Pattern::Any(type_) => first_ord::Pattern::Any(self.lower_type(type_)),
            special::Pattern::Var(type_) => first_ord::Pattern::Var(self.lower_type(type_)),

            special::Pattern::Tuple(items) => first_ord::Pattern::Tuple(
                items.iter().map(|item| self.lower_pattern(item)).collect(),
            ),

            special::Pattern::Ctor(custom, variant, content) => first_ord::Pattern::Ctor(
                self.mapping.map_custom_type(*custom),
                first_ord::VariantId(variant.0),
                content
                    .as_ref()
                    .map(|content| Box::new(self.lower_pattern(content))),
            ),

            &special::Pattern::BoolConst(val) => first_ord::Pattern::BoolConst(val),
            &special::Pattern::ByteConst(val) => first_ord::Pattern::ByteConst(val),
            &special::Pattern::IntConst(val) => first_ord::Pattern::IntConst(val),
            &special::Pattern::FloatConst(val) => first_ord::Pattern::FloatConst(val),
        }
    }

    fn try_lower_app_simplified(
        &mut self,
        purity: Purity,
        rep: &special::FuncRep,
        func: &special::Expr,
        arg: &first_ord::Expr,
    ) -> Option<first_ord::Expr> {
        let func_expr_atomic = is_atomic(func);
        if !func_expr_atomic {
            return None;
        }

        let cases = {
            let mut cases = BTreeSet::new();
            add_rep_leaves(&self.program.opaque_reps, rep, &mut cases);
            cases
        };

        if cases.len() != 1 {
            return None;
        }

        let leaf = cases.into_iter().next().unwrap();

        match leaf {
            LeafFuncCase::Lam(lam_id) => {
                let has_captures = !self.program.lams[lam_id].captures.is_empty();
                if has_captures {
                    return None;
                }

                return Some(first_ord::Expr::Call(
                    purity,
                    self.mapping.map_lam_body(lam_id),
                    Box::new(arg.clone()),
                ));
            }
            LeafFuncCase::Intrinsic(intr) => {
                return Some(first_ord::Expr::Intrinsic(intr, Box::new(arg.clone())));
            }
            LeafFuncCase::ArrayOp(op, item_type) => {
                return match op {
                    res::ArrayOp::Get => match &arg {
                        first_ord::Expr::Tuple(args) => {
                            debug_assert_eq!(args.len(), 2);

                            Some(first_ord::Expr::ArrayOp(first_ord::ArrayOp::Get(
                                self.lower_type(&item_type),
                                Box::new(args[0].clone()),
                                Box::new(args[1].clone()),
                            )))
                        }

                        _ => None,
                    },
                    // TODO: optimize Extract
                    res::ArrayOp::Extract => None,
                    res::ArrayOp::Len => Some(first_ord::Expr::ArrayOp(first_ord::ArrayOp::Len(
                        self.lower_type(&item_type),
                        Box::new(arg.clone()),
                    ))),
                    res::ArrayOp::Push => match &arg {
                        first_ord::Expr::Tuple(args) => {
                            assert![args.len() == 2];

                            Some(first_ord::Expr::ArrayOp(first_ord::ArrayOp::Push(
                                self.lower_type(&item_type),
                                Box::new(args[0].clone()),
                                Box::new(args[1].clone()),
                            )))
                        }
                        _ => None,
                    },
                    res::ArrayOp::Pop => Some(first_ord::Expr::ArrayOp(first_ord::ArrayOp::Pop(
                        self.lower_type(&item_type),
                        Box::new(arg.clone()),
                    ))),
                    res::ArrayOp::Reserve => match &arg {
                        first_ord::Expr::Tuple(args) => {
                            assert![args.len() == 2];

                            Some(first_ord::Expr::ArrayOp(first_ord::ArrayOp::Reserve(
                                self.lower_type(&item_type),
                                Box::new(args[0].clone()),
                                Box::new(args[1].clone()),
                            )))
                        }
                        _ => None,
                    },
                };
            }
            // TODO: optimize ArrayReplace
            LeafFuncCase::ArrayReplace(_) => {}
            LeafFuncCase::IoOp(op) => match op {
                res::IoOp::Input => {
                    let arg_optimizable = match arg {
                        first_ord::Expr::Tuple(args) => {
                            assert![args.len() == 0];
                            true
                        }
                        first_ord::Expr::Local(_) => true,
                        _ => false,
                    };

                    if !arg_optimizable {
                        return None;
                    }
                    return Some(first_ord::Expr::IoOp(first_ord::IoOp::Input));
                }
                res::IoOp::Output => {
                    return Some(first_ord::Expr::IoOp(first_ord::IoOp::Output(Box::new(
                        arg.clone(),
                    ))));
                }
            },
            LeafFuncCase::Panic(ret_type) => {
                return Some(first_ord::Expr::Panic(
                    self.lower_type(&ret_type),
                    Box::new(arg.clone()),
                ));
            }
            LeafFuncCase::Ctor(type_id, variant_id) => {
                return Some(first_ord::Expr::Ctor(
                    self.mapping.map_custom_type(type_id),
                    first_ord::VariantId(variant_id.0),
                    Some(Box::new(arg.clone())),
                ));
            }
        }

        None
    }

    fn lower_expr(
        &mut self,
        local_mapping: &LocalIdMapping,
        expr: &special::Expr,
    ) -> first_ord::Expr {
        match expr {
            special::Expr::Intrinsic(intr, rep) => {
                let lowered_rep = self.lower_closure(rep);
                let intr_variant = self.case_variant(lowered_rep, &LeafFuncCase::Intrinsic(*intr));
                first_ord::Expr::Ctor(
                    self.mapping.map_closure_type(lowered_rep),
                    intr_variant,
                    None,
                )
            }

            special::Expr::ArrayOp(op, item_type, rep) => {
                let lowered_rep = self.lower_closure(rep);
                let op_variant =
                    self.case_variant(lowered_rep, &LeafFuncCase::ArrayOp(*op, item_type.clone()));
                first_ord::Expr::Ctor(self.mapping.map_closure_type(lowered_rep), op_variant, None)
            }

            special::Expr::IoOp(op, rep) => {
                let lowered_rep = self.lower_closure(rep);
                let op_variant = self.case_variant(lowered_rep, &LeafFuncCase::IoOp(*op));
                first_ord::Expr::Ctor(self.mapping.map_closure_type(lowered_rep), op_variant, None)
            }

            special::Expr::Panic(ret_type, rep) => {
                let lowered_rep = self.lower_closure(rep);
                let op_variant =
                    self.case_variant(lowered_rep, &LeafFuncCase::Panic(ret_type.clone()));
                first_ord::Expr::Ctor(self.mapping.map_closure_type(lowered_rep), op_variant, None)
            }

            &special::Expr::NullaryCtor(custom, variant) => first_ord::Expr::Ctor(
                self.mapping.map_custom_type(custom),
                first_ord::VariantId(variant.0),
                None,
            ),

            special::Expr::Ctor(custom, variant, rep) => {
                let lowered_rep = self.lower_closure(rep);
                let op_variant =
                    self.case_variant(lowered_rep, &LeafFuncCase::Ctor(*custom, *variant));
                first_ord::Expr::Ctor(self.mapping.map_closure_type(lowered_rep), op_variant, None)
            }

            &special::Expr::Global(global) => first_ord::Expr::Call(
                Purity::Pure,
                self.mapping.map_global(global),
                Box::new(first_ord::Expr::Tuple(vec![])),
            ),

            &special::Expr::Local(local) => first_ord::Expr::Local(local_mapping.map_local(local)),

            &special::Expr::Capture(capture) => {
                first_ord::Expr::Local(local_mapping.map_capture(capture))
            }

            special::Expr::Tuple(items) => first_ord::Expr::Tuple(
                items
                    .iter()
                    .map(|item| self.lower_expr(local_mapping, item))
                    .collect(),
            ),

            special::Expr::Lam(lam, rep, captures) => {
                let lowered_rep = self.lower_closure(rep);
                let op_variant = self.case_variant(lowered_rep, &LeafFuncCase::Lam(*lam));
                first_ord::Expr::Ctor(
                    self.mapping.map_closure_type(lowered_rep),
                    op_variant,
                    Some(Box::new(first_ord::Expr::Tuple(
                        captures
                            .iter()
                            .map(|(_, capture)| self.lower_expr(local_mapping, capture))
                            .collect(),
                    ))),
                )
            }

            special::Expr::App(purity, rep, func, arg, arg_type, ret_type) => {
                let lowered_arg = self.lower_expr(local_mapping, arg);

                if let Some(simplified_expr) =
                    self.try_lower_app_simplified(*purity, rep, func, &lowered_arg)
                {
                    return simplified_expr;
                };

                let lowered_rep = self.lower_closure(rep);

                let lowered_arg_type = self.lower_type(arg_type);
                let lowered_ret_type = self.lower_type(ret_type);

                let dispatch_func = self.make_dispatch_func(
                    lowered_rep,
                    *purity,
                    lowered_arg_type,
                    lowered_ret_type,
                );

                let lowered_func = self.lower_expr(local_mapping, func);

                first_ord::Expr::Call(
                    *purity,
                    self.mapping.map_dispatch_func(dispatch_func),
                    Box::new(first_ord::Expr::Tuple(vec![lowered_func, lowered_arg])),
                )
            }

            special::Expr::Match(discrim, cases, result_type) => first_ord::Expr::Match(
                Box::new(self.lower_expr(local_mapping, discrim)),
                cases
                    .iter()
                    .map(|(pat, body)| {
                        (
                            self.lower_pattern(pat),
                            self.lower_expr(local_mapping, body),
                        )
                    })
                    .collect(),
                self.lower_type(result_type),
            ),

            special::Expr::LetMany(bindings, body) => first_ord::Expr::LetMany(
                bindings
                    .iter()
                    .map(|(lhs, rhs)| {
                        (self.lower_pattern(lhs), self.lower_expr(local_mapping, rhs))
                    })
                    .collect(),
                Box::new(self.lower_expr(local_mapping, body)),
            ),

            special::Expr::ArrayLit(item_type, items) => first_ord::Expr::ArrayLit(
                self.lower_type(item_type),
                items
                    .iter()
                    .map(|item| self.lower_expr(local_mapping, item))
                    .collect(),
            ),

            &special::Expr::BoolLit(val) => first_ord::Expr::BoolLit(val),
            &special::Expr::ByteLit(val) => first_ord::Expr::ByteLit(val),
            &special::Expr::IntLit(val) => first_ord::Expr::IntLit(val),
            &special::Expr::FloatLit(val) => first_ord::Expr::FloatLit(val),
        }
    }

    fn lower_global(&mut self, val_def: &special::ValDef) -> first_ord::FuncDef {
        let lowered_type = self.lower_type(&val_def.type_);

        let lowered_body = self.lower_expr(&LocalIdMapping { num_captures: 0 }, &val_def.body);

        first_ord::FuncDef {
            purity: Purity::Pure,
            arg_type: first_ord::Type::Tuple(vec![]),
            ret_type: lowered_type,
            arg: first_ord::Pattern::Tuple(vec![]),
            body: lowered_body,
            profile_point: None,
        }
    }

    fn lower_lam_body(&mut self, lam_def: &special::LamDef) -> first_ord::FuncDef {
        let lowered_captures: Vec<_> = lam_def
            .captures
            .iter()
            .map(|(_, capture)| self.lower_type(capture))
            .collect();

        let lowered_arg = self.lower_type(&lam_def.arg);

        let lowered_ret = self.lower_type(&lam_def.ret);

        let lowered_arg_pat = self.lower_pattern(&lam_def.arg_pat);

        let lowered_body = self.lower_expr(
            &LocalIdMapping {
                num_captures: lam_def.captures.len(),
            },
            &lam_def.body,
        );

        if lowered_captures.is_empty() {
            first_ord::FuncDef {
                purity: lam_def.purity,
                arg_type: lowered_arg,
                ret_type: lowered_ret,
                arg: lowered_arg_pat,
                body: lowered_body,
                profile_point: lam_def.profile_point,
            }
        } else {
            let (captures_type, captures_pat) = (
                first_ord::Type::Tuple(lowered_captures.clone()),
                first_ord::Pattern::Tuple(
                    lowered_captures
                        .into_iter()
                        .map(first_ord::Pattern::Var)
                        .collect(),
                ),
            );

            first_ord::FuncDef {
                purity: lam_def.purity,
                arg_type: first_ord::Type::Tuple(vec![captures_type, lowered_arg]),
                ret_type: lowered_ret,
                arg: first_ord::Pattern::Tuple(vec![captures_pat, lowered_arg_pat]),
                body: lowered_body,
                profile_point: lam_def.profile_point,
            }
        }
    }

    fn lower_custom_type(&mut self, typedef: &special::TypeDef) -> first_ord::TypeDef {
        let lowered_variants: IdVec<res::VariantId, _> = typedef
            .variants
            .map(|_, variant| variant.as_ref().map(|content| self.lower_type(content)));

        first_ord::TypeDef {
            // Here we soft-transmute an IdVec indexed by res::VariantId to an IdVec indexed by
            // first_ord::VariantId.  This is not a reasonable operation in general, but here it is
            // perfectly fine, because we guarnatee that these indices coincide for first-order
            // types derived from pre-existing sum types.  The only reason we distinguish between
            // res::VariantId and first_ord::VariantId is that some sum types in the first-order AST
            // are not derived from pre-existing sum types at all, but are instead
            // internally-generated representations of defunctionalized closures.
            variants: IdVec::<first_ord::VariantId, _>::from_items(lowered_variants.items),
        }
    }

    fn lower_main(&mut self) -> first_ord::FuncDef {
        let main_rep =
            if let special::Type::Func(main_rep) = &self.program.vals[self.program.main].type_ {
                main_rep
            } else {
                unreachable!()
            };

        let main_lowered = self.lower_closure(main_rep);

        let main_dispatch = self.make_dispatch_func(
            main_lowered,
            Purity::Impure,
            first_ord::Type::Tuple(vec![]),
            first_ord::Type::Tuple(vec![]),
        );

        let main_wrapper_body = first_ord::Expr::Call(
            Purity::Impure,
            self.mapping.map_dispatch_func(main_dispatch),
            Box::new(first_ord::Expr::Tuple(vec![
                first_ord::Expr::Call(
                    Purity::Pure,
                    self.mapping.map_global(self.program.main),
                    Box::new(first_ord::Expr::Tuple(vec![])),
                ),
                first_ord::Expr::Tuple(vec![]),
            ])),
        );

        first_ord::FuncDef {
            purity: Purity::Impure,
            arg_type: first_ord::Type::Tuple(vec![]),
            ret_type: first_ord::Type::Tuple(vec![]),
            arg: first_ord::Pattern::Tuple(vec![]),
            body: main_wrapper_body,
            profile_point: None,
        }
    }
}

pub fn lower_closures(program: special::Program) -> first_ord::Program {
    let mapping = IdMapping {
        num_orig_custom_types: program.custom_types.len(),
        num_orig_globals: program.vals.len(),
        num_orig_lams: program.lams.len(),
    };

    let mut ctx = Context::new(&mapping, &program);

    let lowered_custom_types = program
        .custom_types
        .map(|_, typedef| ctx.lower_custom_type(typedef));

    let lowered_globals = program.vals.map(|_, val_def| ctx.lower_global(val_def));

    let lowered_global_symbols = program.val_symbols.clone();

    let lowered_lam_bodies = program.lams.map(|_, lam_def| ctx.lower_lam_body(lam_def));

    let lowered_lam_symbols = program.lam_symbols.clone();

    let lowered_main = ctx.lower_main();

    let lowered_closures = ctx
        .lowered_closures
        .map(|_, closure| closure.as_ref().unwrap().typedef.clone());

    let parts = ProgramParts {
        mod_symbols: program.mod_symbols.clone(),

        custom_types: lowered_custom_types,
        closures: lowered_closures,

        custom_type_symbols: program.custom_type_symbols.clone(),

        globals: lowered_globals,
        lam_bodies: lowered_lam_bodies,
        main: lowered_main,
        dispatch_funcs: ctx.dispatch_funcs,

        global_symbols: lowered_global_symbols,
        lam_body_symbols: lowered_lam_symbols,

        profile_points: program.profile_points,
    };

    mapping.assemble_program(parts)
}
