use std::collections::{BTreeMap, BTreeSet};

use crate::data::closure_annot_ast as annot;
use crate::data::closure_specialized_ast as special;
use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::util::iter::try_zip_eq;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::IdVec;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Request<T> {
    head: T,
    params: IdVec<annot::RepParamId, special::FuncRep>,
}

#[derive(Clone, Debug)]
struct Context<'a> {
    orig: &'a annot::Program,

    template_instances: BTreeMap<Request<annot::TemplateId>, special::FuncRep>,
    type_instances: BTreeMap<Request<mono::CustomTypeId>, special::CustomTypeId>,
    lam_instances: BTreeMap<Request<lifted::LamId>, special::LamId>,
    val_instances: BTreeMap<Request<mono::CustomGlobalId>, special::CustomGlobalId>,

    custom_types: IdVec<special::CustomTypeId, Option<special::TypeDef>>,
    opaque_reps: IdVec<special::OpaqueFuncRepId, Option<special::FuncRep>>,
    vals: IdVec<special::CustomGlobalId, Option<special::ValDef>>,
    lams: IdVec<special::LamId, Option<special::LamDef>>,
}

fn populate<T>(opt: &mut Option<T>, val: T) {
    debug_assert!(opt.is_none());
    *opt = Some(val);
}

impl<'a> Context<'a> {
    fn new(orig: &'a annot::Program) -> Self {
        Context {
            orig,

            template_instances: BTreeMap::new(),
            type_instances: BTreeMap::new(),
            lam_instances: BTreeMap::new(),
            val_instances: BTreeMap::new(),

            custom_types: IdVec::new(),
            opaque_reps: IdVec::new(),
            vals: IdVec::new(),
            lams: IdVec::new(),
        }
    }

    fn resolve_template(&mut self, request: Request<annot::TemplateId>) -> special::FuncRep {
        if let Some(existing) = self.template_instances.get(&request) {
            return existing.clone();
        }

        let template = &self.orig.templates[request.head];

        match template.in_cycle {
            annot::InCycle::NoCycle => {
                let mut rep = special::FuncRep(BTreeSet::new());

                for requirement in &template.requirements {
                    self.resolve_requirement(requirement, &request.params, &mut rep);
                }

                self.template_instances.insert(request, rep.clone());

                rep
            }

            annot::InCycle::Cycle => {
                let opaque_id = self.opaque_reps.push(None);

                let external_rep = {
                    let mut external_rep = special::FuncRep(BTreeSet::new());
                    external_rep.0.insert(special::FuncCase::Opaque(opaque_id));
                    external_rep
                };

                self.template_instances
                    .insert(request.clone(), external_rep.clone());

                let mut internal_rep = special::FuncRep(BTreeSet::new());

                for requirement in &template.requirements {
                    self.resolve_requirement(requirement, &request.params, &mut internal_rep);
                }

                populate(&mut self.opaque_reps[opaque_id], internal_rep);

                external_rep
            }
        }
    }

    fn resolve_requirement(
        &mut self,
        requirement: &annot::Requirement,
        params: &IdVec<annot::RepParamId, special::FuncRep>,
        target_cases: &mut special::FuncRep,
    ) {
        match requirement {
            annot::Requirement::Lam(lam_id, lam_params) => {
                let resolved_lam_params =
                    lam_params.map_refs(|_, solution| self.resolve_solution(&solution, params));

                let resolved_lam = self.resolve_lam(Request {
                    head: *lam_id,
                    params: resolved_lam_params,
                });

                target_cases.0.insert(special::FuncCase::Lam(resolved_lam));
            }

            annot::Requirement::Template(template_id, template_params) => {
                let resolved_template_params = template_params
                    .map_refs(|_, solution| self.resolve_solution(&solution, params));

                let resolved_template = self.resolve_template(Request {
                    head: *template_id,
                    params: resolved_template_params,
                });

                target_cases.0.extend(resolved_template.0);
            }

            annot::Requirement::Intrinsic(intr) => {
                target_cases.0.insert(special::FuncCase::Intrinsic(*intr));
            }

            annot::Requirement::ArrayOp(op, item_type) => {
                let resolved_item_type = self.resolve_type(item_type, params);

                target_cases
                    .0
                    .insert(special::FuncCase::ArrayOp(*op, resolved_item_type));
            }

            annot::Requirement::ArrayReplace(item_type) => {
                let resolved_item_type = self.resolve_type(item_type, params);

                target_cases
                    .0
                    .insert(special::FuncCase::ArrayReplace(resolved_item_type));
            }

            annot::Requirement::IoOp(op) => {
                target_cases.0.insert(special::FuncCase::IoOp(*op));
            }

            annot::Requirement::Panic(ret_type) => {
                let resolved_ret_type = self.resolve_type(ret_type, params);

                target_cases
                    .0
                    .insert(special::FuncCase::Panic(resolved_ret_type));
            }

            annot::Requirement::Ctor(custom, type_params, variant) => {
                let resolved_type_params =
                    type_params.map_refs(|_, solution| self.resolve_solution(&solution, params));

                let resolved_custom = self.resolve_custom_type(Request {
                    head: *custom,
                    params: resolved_type_params,
                });

                target_cases
                    .0
                    .insert(special::FuncCase::Ctor(resolved_custom, *variant));
            }
        }
    }

    fn resolve_solution(
        &mut self,
        solution: &annot::Solution,
        params: &IdVec<annot::RepParamId, special::FuncRep>,
    ) -> special::FuncRep {
        match solution {
            annot::Solution::Param(param) => params[param].clone(),

            annot::Solution::MinSolutionTo(template_id, template_params) => {
                self.resolve_template(Request {
                    head: *template_id,
                    params: template_params.map_refs(|_, param| params[param].clone()),
                })
            }
        }
    }

    fn resolve_lam(&mut self, request: Request<lifted::LamId>) -> special::LamId {
        if let Some(existing) = self.lam_instances.get(&request) {
            return existing.clone();
        }

        let lam_id = self.lams.push(None);
        self.lam_instances.insert(request.clone(), lam_id);

        let lam = &self.orig.lams[request.head];

        debug_assert_eq!(lam.params.num_params(), request.params.len());

        let resolved_captures = lam
            .captures
            .map_refs(|_, capture| self.resolve_sig_type(&capture, &request.params));

        let resolved_arg = self.resolve_sig_type(&lam.arg, &request.params);

        let resolved_ret = self.resolve_sig_type(&lam.ret, &request.params);

        let resolved_arg_pat = self.resolve_pattern(&lam.arg_pat, &request.params);

        let resolved_body = self.resolve_expr(&lam.body, &request.params);

        let resolved_lam = special::LamDef {
            purity: lam.purity,
            captures: resolved_captures,
            arg: resolved_arg,
            ret: resolved_ret,
            arg_pat: resolved_arg_pat,
            profile_point: lam.profile_point,
            body: resolved_body,
        };

        populate(&mut self.lams[lam_id], resolved_lam);

        lam_id
    }

    fn resolve_type_generic<Rep, F>(
        &mut self,
        type_: &annot::Type<Rep>,
        resolve_rep: &mut F,
    ) -> special::Type
    where
        F: for<'b> FnMut(&'b mut Self, &'b Rep) -> special::FuncRep,
    {
        match type_ {
            annot::Type::Bool => special::Type::Bool,
            annot::Type::Byte => special::Type::Byte,
            annot::Type::Int => special::Type::Int,
            annot::Type::Float => special::Type::Float,

            annot::Type::Array(item_type) => {
                special::Type::Array(Box::new(self.resolve_type_generic(item_type, resolve_rep)))
            }

            annot::Type::Tuple(items) => special::Type::Tuple(
                items
                    .iter()
                    .map(|item| self.resolve_type_generic(item, resolve_rep))
                    .collect(),
            ),

            annot::Type::Func(_purity, rep, _arg, _ret) => {
                special::Type::Func(resolve_rep(self, rep))
            }

            annot::Type::Custom(custom, custom_params) => {
                let resolved_reps = custom_params.map_refs(|_, rep| resolve_rep(self, &rep));

                let resolved_custom = self.resolve_custom_type(Request {
                    head: *custom,
                    params: resolved_reps,
                });

                special::Type::Custom(resolved_custom)
            }
        }
    }

    fn resolve_type(
        &mut self,
        type_: &annot::Type<annot::Solution>,
        params: &IdVec<annot::RepParamId, special::FuncRep>,
    ) -> special::Type {
        self.resolve_type_generic(type_, &mut |ctx, solution| {
            ctx.resolve_solution(solution, params)
        })
    }

    fn resolve_sig_type(
        &mut self,
        type_: &annot::Type<annot::RepParamId>,
        params: &IdVec<annot::RepParamId, special::FuncRep>,
    ) -> special::Type {
        self.resolve_type_generic(type_, &mut |_, param| params[param].clone())
    }

    fn resolve_custom_type(
        &mut self,
        request: Request<mono::CustomTypeId>,
    ) -> special::CustomTypeId {
        if let Some(&existing) = self.type_instances.get(&request) {
            return existing;
        }

        let custom_id = self.custom_types.push(None);
        self.type_instances.insert(request.clone(), custom_id);

        let typedef = &self.orig.custom_types[request.head];

        debug_assert_eq!(typedef.num_params, request.params.len());

        let resolved_variants = typedef.variants.map_refs(|_, content| {
            content
                .as_ref()
                .map(|content| self.resolve_sig_type(content, &request.params))
        });

        let resolved_typedef = special::TypeDef {
            variants: resolved_variants,
        };

        populate(&mut self.custom_types[custom_id], resolved_typedef);

        custom_id
    }

    fn resolve_pattern(
        &mut self,
        pat: &annot::Pattern,
        params: &IdVec<annot::RepParamId, special::FuncRep>,
    ) -> special::Pattern {
        match pat {
            annot::Pattern::Any(type_) => special::Pattern::Any(self.resolve_type(type_, params)),

            annot::Pattern::Var(type_) => special::Pattern::Var(self.resolve_type(type_, params)),

            annot::Pattern::Tuple(items) => special::Pattern::Tuple(
                items
                    .iter()
                    .map(|item| self.resolve_pattern(item, params))
                    .collect(),
            ),

            annot::Pattern::Ctor(custom, custom_params, variant, content) => {
                let resolved_custom_params =
                    custom_params.map_refs(|_, solution| self.resolve_solution(&solution, params));

                let resolved_custom = self.resolve_custom_type(Request {
                    head: *custom,
                    params: resolved_custom_params,
                });

                let resolved_content = content
                    .as_ref()
                    .map(|content| Box::new(self.resolve_pattern(content, params)));

                special::Pattern::Ctor(resolved_custom, *variant, resolved_content)
            }

            &annot::Pattern::BoolConst(val) => special::Pattern::BoolConst(val),

            &annot::Pattern::ByteConst(val) => special::Pattern::ByteConst(val),

            &annot::Pattern::IntConst(val) => special::Pattern::IntConst(val),

            &annot::Pattern::FloatConst(val) => special::Pattern::FloatConst(val),
        }
    }

    fn resolve_expr(
        &mut self,
        expr: &annot::Expr,
        params: &IdVec<annot::RepParamId, special::FuncRep>,
    ) -> special::Expr {
        match expr {
            annot::Expr::Intrinsic(intr, solution) => {
                special::Expr::Intrinsic(*intr, self.resolve_solution(solution, params))
            }

            annot::Expr::ArrayOp(op, item_type, solution) => special::Expr::ArrayOp(
                *op,
                self.resolve_type(item_type, params),
                self.resolve_solution(solution, params),
            ),

            annot::Expr::IoOp(op, solution) => {
                special::Expr::IoOp(*op, self.resolve_solution(solution, params))
            }

            annot::Expr::Panic(ret_type, solution) => special::Expr::Panic(
                self.resolve_type(ret_type, params),
                self.resolve_solution(solution, params),
            ),

            annot::Expr::NullaryCtor(custom, custom_params, variant) => {
                let resolved_custom_params =
                    custom_params.map_refs(|_, solution| self.resolve_solution(&solution, params));

                let resolved_custom = self.resolve_custom_type(Request {
                    head: *custom,
                    params: resolved_custom_params,
                });

                special::Expr::NullaryCtor(resolved_custom, *variant)
            }

            annot::Expr::Ctor(custom, custom_params, variant, solution) => {
                let resolved_custom_params =
                    custom_params.map_refs(|_, solution| self.resolve_solution(&solution, params));

                let resolved_custom = self.resolve_custom_type(Request {
                    head: *custom,
                    params: resolved_custom_params,
                });

                let resolved_rep = self.resolve_solution(solution, params);

                special::Expr::Ctor(resolved_custom, *variant, resolved_rep)
            }

            annot::Expr::Global(val_id, val_params) => {
                let resolved_val_params =
                    val_params.map_refs(|_, solution| self.resolve_solution(&solution, params));

                let resolved_val_id = self.resolve_val(Request {
                    head: *val_id,
                    params: resolved_val_params,
                });

                special::Expr::Global(resolved_val_id)
            }

            &annot::Expr::Local(local) => special::Expr::Local(local),

            &annot::Expr::Capture(capture) => special::Expr::Capture(capture),

            annot::Expr::Tuple(items) => special::Expr::Tuple(
                items
                    .iter()
                    .map(|item| self.resolve_expr(item, params))
                    .collect(),
            ),

            annot::Expr::Lam(lam_id, lam_params, rep, captures) => {
                let resolved_lam_params =
                    lam_params.map_refs(|_, solution| self.resolve_solution(&solution, params));

                let resolved_lam_id = self.resolve_lam(Request {
                    head: *lam_id,
                    params: resolved_lam_params,
                });

                let resolved_rep = self.resolve_solution(rep, params);

                let resolved_captures =
                    captures.map_refs(|_, capture| self.resolve_expr(&capture, params));

                special::Expr::Lam(resolved_lam_id, resolved_rep, resolved_captures)
            }

            annot::Expr::App(purity, func_rep, func, arg, arg_type, ret_type) => {
                let resolved_func_rep = self.resolve_solution(func_rep, params);

                let resolved_func = self.resolve_expr(func, params);

                let resolved_arg = self.resolve_expr(arg, params);

                let resolved_arg_type = self.resolve_type(arg_type, params);

                let resolved_ret_type = self.resolve_type(ret_type, params);

                special::Expr::App(
                    *purity,
                    resolved_func_rep,
                    Box::new(resolved_func),
                    Box::new(resolved_arg),
                    resolved_arg_type,
                    resolved_ret_type,
                )
            }

            annot::Expr::Match(discrim, cases, result_type) => {
                let resolved_discrim = self.resolve_expr(discrim, params);

                let resolved_cases = cases
                    .iter()
                    .map(|(pat, body)| {
                        let resolved_pat = self.resolve_pattern(pat, params);
                        let resolved_body = self.resolve_expr(body, params);
                        (resolved_pat, resolved_body)
                    })
                    .collect();

                let resolved_result_type = self.resolve_type(result_type, params);

                special::Expr::Match(
                    Box::new(resolved_discrim),
                    resolved_cases,
                    resolved_result_type,
                )
            }

            annot::Expr::LetMany(bindings, body) => {
                let mut new_bindings = Vec::new();
                for (lhs, rhs) in bindings {
                    let resolved_lhs = self.resolve_pattern(lhs, params);

                    let resolved_rhs = self.resolve_expr(rhs, params);
                    new_bindings.push((resolved_lhs, resolved_rhs));
                }

                let resolved_body = self.resolve_expr(body, params);

                special::Expr::LetMany(new_bindings, Box::new(resolved_body))
            }

            annot::Expr::ArrayLit(item_type, items) => {
                let resolved_item_type = self.resolve_type(item_type, params);

                let resolved_items = items
                    .iter()
                    .map(|item| self.resolve_expr(item, params))
                    .collect();

                special::Expr::ArrayLit(resolved_item_type, resolved_items)
            }

            &annot::Expr::BoolLit(val) => special::Expr::BoolLit(val),

            &annot::Expr::ByteLit(val) => special::Expr::ByteLit(val),

            &annot::Expr::IntLit(val) => special::Expr::IntLit(val),

            &annot::Expr::FloatLit(val) => special::Expr::FloatLit(val),
        }
    }

    fn resolve_val(&mut self, request: Request<mono::CustomGlobalId>) -> special::CustomGlobalId {
        if let Some(&existing) = self.val_instances.get(&request) {
            return existing;
        }

        let val_id = self.vals.push(None);
        self.val_instances.insert(request.clone(), val_id);

        let val_def = &self.orig.vals[request.head];

        debug_assert_eq!(val_def.params.num_params(), request.params.len());

        let resolved_type = self.resolve_sig_type(&val_def.type_, &request.params);

        let resolved_body = self.resolve_expr(&val_def.body, &request.params);

        let resolved_val_def = special::ValDef {
            type_: resolved_type,
            body: resolved_body,
        };

        populate(&mut self.vals[val_id], resolved_val_def);

        val_id
    }
}

pub fn closure_specialize(
    program: annot::Program,
    progress: impl ProgressLogger,
) -> special::Program {
    let progress = progress.start_session(None);

    let mut ctx = Context::new(&program);

    let main_def = &program.vals[program.main];

    // TODO: Using an opaque representation to monomorphize every representation parameter in main's
    // SCC is a hack to avoid doing proper analysis of the dependencies among these representation
    // variables.  There should be some way to do this dependency analysis during the prior closure
    // annotation pass.

    let main_param_opaque_ids: IdVec<annot::RepParamId, _> = IdVec::from_vec(
        (0..main_def.params.num_params())
            .map(|_| ctx.opaque_reps.push(None))
            .collect(),
    );

    let main_param_opaque_reps = main_param_opaque_ids.map_refs(|_, opaque_id| {
        let mut param_rep = special::FuncRep(BTreeSet::new());
        param_rep.0.insert(special::FuncCase::Opaque(*opaque_id));
        param_rep
    });

    for (_, opaque_id, (template_id, template_params)) in
        try_zip_eq(&main_param_opaque_ids, &main_def.params.requirements)
            .expect("main_def.params.num_params() should equal main_def_params.requirements.len()")
    {
        let resolved_template_params =
            template_params.map_refs(|_, param| main_param_opaque_reps[param].clone());

        let rep = ctx.resolve_template(Request {
            head: *template_id,
            params: resolved_template_params,
        });

        populate(&mut ctx.opaque_reps[opaque_id], rep);
    }

    let resolved_main_id = ctx.resolve_val(Request {
        head: program.main,
        params: main_param_opaque_reps,
    });

    let mut type_origin = BTreeMap::new();
    for (request, type_id) in ctx.type_instances {
        let prev = type_origin.insert(type_id, request.head);
        debug_assert!(prev.is_none());
    }

    let mut lam_origin = BTreeMap::new();
    for (request, lam_id) in ctx.lam_instances {
        let prev = lam_origin.insert(lam_id, request.head);
        debug_assert!(prev.is_none());
    }

    let mut val_origin = BTreeMap::new();
    for (request, val_id) in ctx.val_instances {
        let prev = val_origin.insert(val_id, request.head);
        debug_assert!(prev.is_none());
    }

    let custom_type_symbols = ctx
        .custom_types
        .map_refs(|id, _| program.custom_type_symbols[type_origin.get(&id).unwrap()].clone());
    let val_symbols = ctx
        .vals
        .map_refs(|id, _| program.val_symbols[val_origin.get(&id).unwrap()].clone());
    let lam_symbols = ctx
        .lams
        .map_refs(|id, _| program.lam_symbols[lam_origin.get(&id).unwrap()].clone());

    progress.finish();

    special::Program {
        mod_symbols: program.mod_symbols.clone(),
        custom_types: ctx.custom_types.map(|_, typedef| typedef.unwrap()),
        custom_type_symbols,
        opaque_reps: ctx.opaque_reps.map(|_, rep| rep.unwrap()),
        vals: ctx.vals.map(|_, val_def| val_def.unwrap()),
        val_symbols,
        lams: ctx.lams.map(|_, lam_def| lam_def.unwrap()),
        lam_symbols,
        profile_points: program.profile_points,
        main: resolved_main_id,
    }
}

pub fn check_patterns(program: &special::Program) {
    for (lam_id, lam) in &program.lams {
        check_pattern(lam_id, &lam.arg_pat, &lam.arg);
    }

    fn check_pattern(i: special::LamId, pat: &special::Pattern, type_: &special::Type) {
        use special::Pattern as P;
        use special::Type as T;
        match (pat, type_) {
            (P::Any(_), _) => {}
            (P::Var(_), _) => {}
            (P::Tuple(items), T::Tuple(item_types)) => {
                assert_eq!(items.len(), item_types.len());
                for (p, t) in items.iter().zip(item_types) {
                    check_pattern(i, p, t);
                }
            }
            (P::Ctor(type_id, _, _), T::Custom(expected_type_id)) => {
                assert_eq!(type_id, expected_type_id);
            }
            (P::BoolConst(_), T::Bool) => {}
            (P::IntConst(_), T::Int) => {}
            (P::ByteConst(_), T::Byte) => {}
            (P::FloatConst(_), T::Float) => {}
            _ => {
                panic!("[{:?}] arg pattern didn't match argument type", i);
            }
        }
    }
}
