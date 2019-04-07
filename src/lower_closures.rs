use std::collections::{BTreeMap, BTreeSet};

use crate::data::closure_specialized_ast as special;
use crate::data::first_order_ast as first_ord;
use crate::data::lambda_lifted_ast as lifted;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp, IOOp};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum LeafFuncCase {
    Lam(special::LamId),
    ArithOp(Op),
    ArrayOp(ArrayOp, special::Type),
    ArrayReplace(special::Type),
    IOOp(IOOp),
    Ctor(special::CustomTypeId, res::VariantId),
}

fn add_rep_leaves(
    opaque_reps: &[special::FuncRep],
    rep: &special::FuncRep,
    leaves: &mut BTreeSet<LeafFuncCase>,
) {
    for case in &rep.0 {
        match case {
            &special::FuncCase::Lam(lam) => {
                leaves.insert(LeafFuncCase::Lam(lam));
            }

            &special::FuncCase::Opaque(opaque) => {
                add_rep_leaves(opaque_reps, &opaque_reps[opaque.0], leaves);
            }

            &special::FuncCase::ArithOp(op) => {
                leaves.insert(LeafFuncCase::ArithOp(op));
            }

            special::FuncCase::ArrayOp(op, item_type) => {
                leaves.insert(LeafFuncCase::ArrayOp(*op, item_type.clone()));
            }

            special::FuncCase::ArrayReplace(item_type) => {
                leaves.insert(LeafFuncCase::ArrayReplace(item_type.clone()));
            }

            &special::FuncCase::IOOp(op) => {
                leaves.insert(LeafFuncCase::IOOp(op));
            }

            &special::FuncCase::Ctor(custom, variant) => {
                leaves.insert(LeafFuncCase::Ctor(custom, variant));
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct LoweredClosureId(usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct DispatchFuncId(usize);

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
    custom_types: Vec<first_ord::TypeDef>, // Indexed by special::CustomTypeId
    lowered_closures: Vec<first_ord::TypeDef>, // Indexed by LoweredClosureId

    globals: Vec<first_ord::FuncDef>, // Indexed by special::CustomGlobalId
    lam_bodies: Vec<first_ord::FuncDef>, // Indexed by special::LamId
    dispatch_funcs: Vec<first_ord::FuncDef>, // Indexed by DispatchFuncId

    main: special::CustomGlobalId,
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
        first_ord::CustomFuncId(self.num_orig_globals + self.num_orig_lams + dispatch.0)
    }

    fn assemble_program(&self, parts: ProgramParts) -> first_ord::Program {
        debug_assert_eq!(parts.custom_types.len(), self.num_orig_custom_types);
        debug_assert_eq!(parts.globals.len(), self.num_orig_globals);
        debug_assert_eq!(parts.lam_bodies.len(), self.num_orig_lams);

        let mut custom_types = parts.custom_types;
        custom_types.extend(parts.lowered_closures);

        let mut funcs = parts.globals;
        funcs.extend(parts.lam_bodies);
        funcs.extend(parts.dispatch_funcs);

        // FIXME: Represent main as a function `proc () -> ()`, not a function `() -> (proc () -> ())`
        let main = self.map_global(parts.main);

        first_ord::Program {
            custom_types,
            funcs,
            main,
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
    lowered_closures: Vec<Option<LoweredClosure>>, // Indexed by LoweredClosureId

    dispatch_ids: BTreeMap<LoweredClosureId, DispatchFuncId>,
    dispatch_funcs: Vec<first_ord::FuncDef>,
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

impl<'a> Context<'a> {
    fn new(mapping: &'a IdMapping, program: &'a special::Program) -> Self {
        Context {
            mapping,
            program,

            lowered_ids: BTreeMap::new(),
            lowered_closures: Vec::new(),

            dispatch_ids: BTreeMap::new(),
            dispatch_funcs: Vec::new(),
        }
    }

    fn lower_env(&mut self, case: &LeafFuncCase) -> Option<first_ord::Type> {
        match case {
            LeafFuncCase::Lam(lam) => {
                let captures = &self.program.lams[lam.0].captures;

                let lowered_captures = captures
                    .iter()
                    .map(|capture| self.lower_type(capture))
                    .collect();

                Some(first_ord::Type::Tuple(lowered_captures))
            }

            LeafFuncCase::ArithOp(_) => None,

            LeafFuncCase::ArrayOp(_, _) => None,

            LeafFuncCase::ArrayReplace(item_type) => Some(first_ord::Type::HoleArray(Box::new(
                self.lower_type(item_type),
            ))),

            LeafFuncCase::IOOp(_) => None,

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

        let id = LoweredClosureId(self.lowered_closures.len());
        self.lowered_closures.push(None);
        self.lowered_ids.insert(cases.clone(), id);

        let mut variants = Vec::new();
        let mut case_variants = BTreeMap::new();

        for (idx, case) in cases.into_iter().enumerate() {
            variants.push(self.lower_env(&case));
            case_variants.insert(case, first_ord::VariantId(idx));
        }

        debug_assert!(self.lowered_closures[id.0].is_none());

        self.lowered_closures[id.0] = Some(LoweredClosure {
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

        let lowered = self.lowered_closures[lowered_id.0]
            .as_ref()
            .expect("Lowered closure definition should be completed by the time we query it")
            .clone();

        // Convenience functions to make programmatic AST generation a little less painful

        fn local(idx: usize) -> first_ord::Expr {
            first_ord::Expr::Local(first_ord::LocalId(idx))
        }

        fn with_args(types: Vec<first_ord::Type>, body: first_ord::Expr) -> first_ord::Expr {
            first_ord::Expr::Let(
                first_ord::Pattern::Tuple(types.into_iter().map(first_ord::Pattern::Var).collect()),
                Box::new(local(0)),
                Box::new(body),
            )
        }

        let func_rep_type = first_ord::Type::Custom(self.mapping.map_closure_type(lowered_id));

        let func_rep_local = local(0);
        let arg_local = local(1);
        let env_local = local(2); // For use in match branch bodies; may not exist in all branches

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
                Box::new(func_rep_local),
                lowered
                    .case_variants
                    .iter()
                    .map(|(case, variant)| {
                        // If this is Some(...), then LocalId(2) is the environment
                        let env_pat = lowered.typedef.variants[variant.0]
                            .clone()
                            .map(first_ord::Pattern::Var);

                        let body = match case {
                            LeafFuncCase::Lam(lam) => {
                                debug_assert!(env_pat.is_some());

                                let lam_body_func = self.mapping.map_lam_body(*lam);

                                first_ord::Expr::Call(
                                    purity,
                                    lam_body_func,
                                    Box::new(first_ord::Expr::Tuple(vec![
                                        env_local.clone(), // Environment
                                        arg_local.clone(), // Argument
                                    ])),
                                )
                            }

                            LeafFuncCase::ArithOp(op) => {
                                debug_assert!(env_pat.is_none());

                                use first_ord::Type::{Byte, Float, Int};

                                fn byte_binop(binop: first_ord::BinOp) -> first_ord::Expr {
                                    with_args(
                                        vec![Byte, Byte],
                                        first_ord::Expr::ArithOp(first_ord::ArithOp::ByteOp(
                                            binop,
                                            Box::new(local(2)),
                                            Box::new(local(3)),
                                        )),
                                    )
                                }

                                fn int_binop(binop: first_ord::BinOp) -> first_ord::Expr {
                                    with_args(
                                        vec![Int, Int],
                                        first_ord::Expr::ArithOp(first_ord::ArithOp::IntOp(
                                            binop,
                                            Box::new(local(2)),
                                            Box::new(local(3)),
                                        )),
                                    )
                                }

                                fn float_binop(binop: first_ord::BinOp) -> first_ord::Expr {
                                    with_args(
                                        vec![Float, Float],
                                        first_ord::Expr::ArithOp(first_ord::ArithOp::FloatOp(
                                            binop,
                                            Box::new(local(2)),
                                            Box::new(local(3)),
                                        )),
                                    )
                                }

                                fn byte_cmp(cmp: first_ord::Comparison) -> first_ord::Expr {
                                    with_args(
                                        vec![Byte, Byte],
                                        first_ord::Expr::ArithOp(first_ord::ArithOp::ByteCmp(
                                            cmp,
                                            Box::new(local(2)),
                                            Box::new(local(3)),
                                        )),
                                    )
                                }

                                fn int_cmp(cmp: first_ord::Comparison) -> first_ord::Expr {
                                    with_args(
                                        vec![Int, Int],
                                        first_ord::Expr::ArithOp(first_ord::ArithOp::IntCmp(
                                            cmp,
                                            Box::new(local(2)),
                                            Box::new(local(3)),
                                        )),
                                    )
                                }

                                fn float_cmp(cmp: first_ord::Comparison) -> first_ord::Expr {
                                    with_args(
                                        vec![Float, Float],
                                        first_ord::Expr::ArithOp(first_ord::ArithOp::FloatCmp(
                                            cmp,
                                            Box::new(local(2)),
                                            Box::new(local(3)),
                                        )),
                                    )
                                }

                                match op {
                                    Op::AddByte => byte_binop(first_ord::BinOp::Add),
                                    Op::SubByte => byte_binop(first_ord::BinOp::Sub),
                                    Op::MulByte => byte_binop(first_ord::BinOp::Mul),
                                    Op::DivByte => byte_binop(first_ord::BinOp::Div),
                                    Op::NegByte => first_ord::Expr::ArithOp(
                                        first_ord::ArithOp::NegateByte(Box::new(arg_local.clone())),
                                    ),

                                    Op::EqByte => byte_cmp(first_ord::Comparison::Equal),
                                    Op::LtByte => byte_cmp(first_ord::Comparison::Less),
                                    Op::LteByte => byte_cmp(first_ord::Comparison::LessEqual),

                                    Op::AddInt => int_binop(first_ord::BinOp::Add),
                                    Op::SubInt => int_binop(first_ord::BinOp::Sub),
                                    Op::MulInt => int_binop(first_ord::BinOp::Mul),
                                    Op::DivInt => int_binop(first_ord::BinOp::Div),
                                    Op::NegInt => first_ord::Expr::ArithOp(
                                        first_ord::ArithOp::NegateInt(Box::new(arg_local.clone())),
                                    ),

                                    Op::EqInt => int_cmp(first_ord::Comparison::Equal),
                                    Op::LtInt => int_cmp(first_ord::Comparison::Less),
                                    Op::LteInt => int_cmp(first_ord::Comparison::LessEqual),

                                    Op::AddFloat => float_binop(first_ord::BinOp::Add),
                                    Op::SubFloat => float_binop(first_ord::BinOp::Sub),
                                    Op::MulFloat => float_binop(first_ord::BinOp::Mul),
                                    Op::DivFloat => float_binop(first_ord::BinOp::Div),
                                    Op::NegFloat => {
                                        first_ord::Expr::ArithOp(first_ord::ArithOp::NegateFloat(
                                            Box::new(first_ord::Expr::Local(first_ord::LocalId(0))),
                                        ))
                                    }

                                    Op::EqFloat => float_cmp(first_ord::Comparison::Equal),
                                    Op::LtFloat => float_cmp(first_ord::Comparison::Less),
                                    Op::LteFloat => float_cmp(first_ord::Comparison::LessEqual),
                                }
                            }

                            LeafFuncCase::ArrayOp(op, item_type) => {
                                let lowered_item_type = self.lower_type(item_type);

                                match op {
                                    ArrayOp::Item => {
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
                                                first_ord::Type::Int,
                                            ],
                                            first_ord::Expr::ArrayOp(first_ord::ArrayOp::Item(
                                                lowered_item_type,
                                                Box::new(local(2)), // Array
                                                Box::new(local(3)), // Index
                                                Some((replacer_type, replacer_variant)),
                                            )),
                                        )
                                    }

                                    ArrayOp::Len => {
                                        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Len(
                                            lowered_item_type,
                                            Box::new(arg_local.clone()),
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

                                    ArrayOp::Pop => {
                                        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Pop(
                                            lowered_item_type,
                                            Box::new(arg_local.clone()),
                                        ))
                                    }

                                    ArrayOp::Concat => with_args(
                                        vec![
                                            first_ord::Type::Array(Box::new(
                                                lowered_item_type.clone(),
                                            )),
                                            first_ord::Type::Array(Box::new(
                                                lowered_item_type.clone(),
                                            )),
                                        ],
                                        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Concat(
                                            lowered_item_type,
                                            Box::new(local(2)), // First Array
                                            Box::new(local(3)), // Second Array
                                        )),
                                    ),
                                }
                            }

                            LeafFuncCase::ArrayReplace(item_type) => {
                                debug_assert!(env_pat.is_some());

                                let lowered_item_type = self.lower_type(item_type);

                                first_ord::Expr::ArrayOp(first_ord::ArrayOp::Replace(
                                    lowered_item_type,
                                    Box::new(env_local.clone()), // Hole array (environment)
                                    Box::new(arg_local.clone()), // Item (argument)
                                ))
                            }

                            LeafFuncCase::IOOp(op) => {
                                debug_assert!(env_pat.is_none());
                                debug_assert_eq!(purity, Purity::Impure);

                                match op {
                                    IOOp::Input => first_ord::Expr::IOOp(first_ord::IOOp::Input),
                                    IOOp::Output => first_ord::Expr::IOOp(first_ord::IOOp::Output(
                                        Box::new(arg_local.clone()),
                                    )),
                                }
                            }

                            LeafFuncCase::Ctor(custom, variant) => {
                                debug_assert!(env_pat.is_none());

                                first_ord::Expr::Ctor(
                                    self.mapping.map_custom_type(*custom),
                                    first_ord::VariantId(variant.0),
                                    // This constructor is necessarily non-nullary, because we are
                                    // calling it as a function
                                    Some(Box::new(arg_local.clone())),
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
        };

        let func_id = DispatchFuncId(self.dispatch_funcs.len());
        self.dispatch_funcs.push(func);
        self.dispatch_ids.insert(lowered_id, func_id);

        func_id
    }

    fn case_variant(&self, lowered: LoweredClosureId, case: &LeafFuncCase) -> first_ord::VariantId {
        self.lowered_closures[lowered.0]
            .as_ref()
            .expect("Lowered closure definition should be completed by the time we query it")
            .case_variants[case]
    }

    fn lower_type(&mut self, type_: &special::Type) -> first_ord::Type {
        match type_ {
            special::Type::Bool => first_ord::Type::Bool,
            special::Type::Byte => first_ord::Type::Byte,
            special::Type::Int => first_ord::Type::Int,
            special::Type::Float => first_ord::Type::Float,

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

    fn lower_expr(
        &mut self,
        local_mapping: &LocalIdMapping,
        expr: &special::Expr,
    ) -> first_ord::Expr {
        match expr {
            special::Expr::ArithOp(op, rep) => {
                let lowered_rep = self.lower_closure(rep);
                let op_variant = self.case_variant(lowered_rep, &LeafFuncCase::ArithOp(*op));
                first_ord::Expr::Ctor(self.mapping.map_closure_type(lowered_rep), op_variant, None)
            }

            special::Expr::ArrayOp(op, item_type, rep) => {
                let lowered_rep = self.lower_closure(rep);
                let op_variant =
                    self.case_variant(lowered_rep, &LeafFuncCase::ArrayOp(*op, item_type.clone()));
                first_ord::Expr::Ctor(self.mapping.map_closure_type(lowered_rep), op_variant, None)
            }

            special::Expr::IOOp(op, rep) => {
                let lowered_rep = self.lower_closure(rep);
                let op_variant = self.case_variant(lowered_rep, &LeafFuncCase::IOOp(*op));
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
                            .map(|capture| self.lower_expr(local_mapping, capture))
                            .collect(),
                    ))),
                )
            }

            special::Expr::App(purity, rep, func, arg, arg_type, ret_type) => {
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
                let lowered_arg = self.lower_expr(local_mapping, arg);

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

            special::Expr::Let(lhs, rhs, body) => first_ord::Expr::Let(
                self.lower_pattern(lhs),
                Box::new(self.lower_expr(local_mapping, rhs)),
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
        }
    }

    fn lower_lam_body(&mut self, lam_def: &special::LamDef) -> first_ord::FuncDef {
        let lowered_captures: Vec<_> = lam_def
            .captures
            .iter()
            .map(|capture| self.lower_type(capture))
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

        first_ord::FuncDef {
            purity: lam_def.purity,
            arg_type: lowered_arg,
            ret_type: lowered_ret,
            arg: first_ord::Pattern::Tuple(vec![
                first_ord::Pattern::Tuple(
                    lowered_captures
                        .into_iter()
                        .map(first_ord::Pattern::Var)
                        .collect(),
                ),
                lowered_arg_pat,
            ]),
            body: lowered_body,
        }
    }

    fn lower_custom_type(&mut self, typedef: &special::TypeDef) -> first_ord::TypeDef {
        let lowered_variants = typedef
            .variants
            .iter()
            .map(|variant| variant.as_ref().map(|content| self.lower_type(content)))
            .collect();

        first_ord::TypeDef {
            variants: lowered_variants,
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
        .iter()
        .map(|typedef| ctx.lower_custom_type(typedef))
        .collect();

    let lowered_globals = program
        .vals
        .iter()
        .map(|val_def| ctx.lower_global(val_def))
        .collect();

    let lowered_lam_bodies = program
        .lams
        .iter()
        .map(|lam_def| ctx.lower_lam_body(lam_def))
        .collect();

    let parts = ProgramParts {
        custom_types: lowered_custom_types,
        lowered_closures: ctx
            .lowered_closures
            .into_iter()
            .map(|closure| closure.unwrap().typedef)
            .collect(),

        globals: lowered_globals,
        lam_bodies: lowered_lam_bodies,
        dispatch_funcs: ctx.dispatch_funcs,

        main: program.main,
    };

    mapping.assemble_program(parts)
}
