use std::collections::{BTreeMap, BTreeSet};

// this pass does 2 things:
// 1. for any 1 variant custom type, the custom type is removed and replaced with the variant
// 2. any type isomorphic to unit are stripped out within a tuple type
// 3. any tuple with one element is stripped
use crate::{
    data::{first_order_ast::*, intrinsics},
    intrinsic_config::intrinsic_sig,
    util::{
        graph::{self, Graph},
        id_vec::IdVec,
    },
};

struct Context<'a> {
    locals: Vec<Type>,
    prog: &'a Program,
    type_reduction: BTreeMap<CustomTypeId, Type>,
    current_local_id: BTreeMap<usize, Expr>,
    new_local: usize,
    old_local: usize,
    remove_type_cache: BTreeMap<CustomTypeId, Type>,
}
impl<'a> Context<'a> {
    pub fn is_unit(&mut self, t: &Type) -> bool {
        self.remove_type(t.clone()) == Type::Tuple(Vec::new())
    }

    pub fn remove_type(&mut self, t: Type) -> Type {
        match t {
            Type::Bool => Type::Bool,
            Type::Num(n) => Type::Num(n),
            Type::Array(type_) => Type::Array(Box::new(self.remove_type(*type_))),

            Type::HoleArray(type_) => Type::HoleArray(Box::new(self.remove_type(*type_))),
            Type::Tuple(types) => {
                let mut new_types = Vec::new();
                for type_ in types {
                    if self.is_unit(&type_) {
                        continue;
                    } else {
                        let new_type = self.remove_type(type_);
                        match new_type {
                            Type::Tuple(inside) => new_types.push(inside),
                            _ => new_types.push(vec![new_type]),
                        }
                    }
                }

                if new_types.concat().len() == 1 {
                    new_types.concat()[0].clone()
                } else {
                    Type::Tuple(new_types.concat())
                }
            }

            Type::Custom(type_id) => match self.remove_type_cache.get(&type_id) {
                Some(res) => res.clone(),
                None => {
                    let res = match self.type_reduction.get(&type_id) {
                        Some(t) => self.remove_type(t.clone()),
                        None => Type::Custom(type_id),
                    };
                    self.remove_type_cache.insert(type_id, res.clone());
                    res
                }
            },
        }
    }

    pub fn remove_expr(&mut self, e: Expr) -> Expr {
        match e {
            Expr::Intrinsic(intrinsic, expr) => {
                Expr::Intrinsic(intrinsic, Box::new(self.remove_expr(*expr)))
            }
            Expr::ArrayOp(array_op) => Expr::ArrayOp(match array_op {
                ArrayOp::Get(type_, x, y) => ArrayOp::Get(
                    self.remove_type(type_),
                    Box::new(self.remove_expr(*x)),
                    Box::new(self.remove_expr(*y)),
                ),
                ArrayOp::Extract(type_, x, y) => ArrayOp::Extract(
                    self.remove_type(type_),
                    Box::new(self.remove_expr(*x)),
                    Box::new(self.remove_expr(*y)),
                ),
                ArrayOp::Len(type_, x) => {
                    ArrayOp::Len(self.remove_type(type_), Box::new(self.remove_expr(*x)))
                }
                ArrayOp::Push(type_, x, y) => ArrayOp::Push(
                    self.remove_type(type_),
                    Box::new(self.remove_expr(*x)),
                    Box::new(self.remove_expr(*y)),
                ),

                ArrayOp::Pop(type_, x) => {
                    ArrayOp::Pop(self.remove_type(type_), Box::new(self.remove_expr(*x)))
                }

                ArrayOp::Replace(type_, x, y) => ArrayOp::Replace(
                    self.remove_type(type_),
                    Box::new(self.remove_expr(*x)),
                    Box::new(self.remove_expr(*y)),
                ),

                ArrayOp::Reserve(type_, x, y) => ArrayOp::Reserve(
                    self.remove_type(type_),
                    Box::new(self.remove_expr(*x)),
                    Box::new(self.remove_expr(*y)),
                ),
            }),
            Expr::IoOp(io_op) => Expr::IoOp({
                match io_op {
                    IoOp::Input => IoOp::Input,
                    IoOp::Output(x) => IoOp::Output(Box::new(self.remove_expr(*x))),
                }
            }),
            Expr::Panic(type_, expr) => {
                Expr::Panic(self.remove_type(type_), Box::new(self.remove_expr(*expr)))
            }
            Expr::Ctor(type_id, variant_id, arg) => match self.type_reduction.get(&type_id) {
                Some(_t) => {
                    arg.map_or_else(|| Expr::Tuple(Vec::new()), |arg| self.remove_expr(*arg))
                }
                None => Expr::Ctor(
                    type_id,
                    variant_id,
                    arg.map(|arg| Box::new(self.remove_expr(*arg))),
                ),
            },

            Expr::Local(id) => {
                if self.is_unit(&self.locals[id.0].clone()) {
                    Expr::Tuple(Vec::new())
                } else {
                    match self.current_local_id.get(&id.0) {
                        Some(t) => t.clone(),
                        None => Expr::ByteLit(255),
                    }
                }
            }
            Expr::Tuple(exprs) => {
                let mut new_exprs = Vec::new();
                for expr in exprs {
                    let expr_type = typecheck_expr(self, &expr);
                    if self.is_unit(&expr_type) {
                        continue;
                    } else {
                        let new_expr = self.remove_expr(expr);
                        new_exprs.push((self.remove_type(expr_type), new_expr));
                    }
                }

                if new_exprs.len() == 1 {
                    new_exprs.remove(0).1
                } else {
                    let mut new_cases = Vec::new();
                    let mut new_types = Vec::new();
                    let mut pats = Vec::new();
                    let mut num_vars = 0;

                    let mut result_arm = Vec::new();

                    for (expr_type, new_expr) in new_exprs {
                        new_types.push(expr_type.clone());
                        new_cases.push(new_expr);
                        match expr_type {
                            Type::Tuple(elem_types) => {
                                let mut subpattern = Vec::new();
                                for elem_type in elem_types {
                                    subpattern.push(Pattern::Var(elem_type));
                                    num_vars += 1;
                                }
                                pats.push(Pattern::Tuple(subpattern));
                            }
                            t => {
                                num_vars += 1;
                                pats.push(Pattern::Var(t));
                            }
                        }
                    }

                    let mut current_locals = self.old_local;
                    for _ in 0..num_vars {
                        result_arm.push(Expr::Local(LocalId(current_locals)));
                        current_locals += 1;
                    }

                    if result_arm.len() == new_cases.len() {
                        Expr::Tuple(new_cases)
                    } else {
                        Expr::Match(
                            Box::new(Expr::Tuple(new_cases)),
                            vec![(Pattern::Tuple(pats), Expr::Tuple(result_arm))],
                            self.remove_type(Type::Tuple(new_types)),
                        )
                    }
                    // match (f, g, h) with ((a b c) (d e) (f g)) -> (a b c d e f g)
                }
            }
            Expr::Call(purity, func_id, body) => {
                Expr::Call(purity, func_id, Box::new(self.remove_expr(*body)))
            }
            Expr::Match(arg, pats, type_) => {
                let arg_type = typecheck_expr(self, &arg);
                if self.is_unit(&arg_type) {
                    assert!(pats.len() == 1);
                    with_scope(self, |sub_ctx| {
                        bind_pattern(sub_ctx, &pats[0].0);
                        sub_ctx.remove_expr(pats[0].1.clone())
                    })
                } else {
                    Expr::Match(
                        Box::new(self.remove_expr(*arg)),
                        pats.iter()
                            .map(|(pat, expr)| {
                                with_scope(self, |sub_ctx| {
                                    bind_pattern(sub_ctx, pat);
                                    (
                                        sub_ctx.remove_pattern(pat.clone()),
                                        sub_ctx.remove_expr(expr.clone()),
                                    )
                                })
                            })
                            .collect(),
                        self.remove_type(type_),
                    )
                }
            }
            Expr::LetMany(bindings, result) => with_scope(self, |sub_ctx| {
                let mut new_bindings = Vec::new();
                for (lhs, rhs) in bindings {
                    let expr = sub_ctx.remove_expr(rhs);
                    bind_pattern(sub_ctx, &lhs);
                    new_bindings.push((sub_ctx.remove_pattern(lhs), expr));
                }

                Expr::LetMany(new_bindings, Box::new(sub_ctx.remove_expr(*result)))
            }),
            Expr::ArrayLit(item_type, elems) => Expr::ArrayLit(
                self.remove_type(item_type),
                elems
                    .iter()
                    .map(|item| self.remove_expr(item.clone()))
                    .collect(),
            ),
            Expr::BoolLit(b) => Expr::BoolLit(b),
            Expr::ByteLit(b) => Expr::ByteLit(b),
            Expr::IntLit(b) => Expr::IntLit(b),
            Expr::FloatLit(b) => Expr::FloatLit(b),
        }
    }

    pub fn remove_pattern(&mut self, p: Pattern) -> Pattern {
        fn pat_to_type(p: &Pattern) -> Type {
            match p {
                Pattern::Any(t) => t.clone(),
                Pattern::Var(t) => t.clone(),
                Pattern::Tuple(pats) => Type::Tuple(pats.iter().map(|x| pat_to_type(x)).collect()),
                Pattern::Ctor(type_id, _, _) => Type::Custom(*type_id),
                Pattern::BoolConst(_) => Type::Bool,
                Pattern::ByteConst(_) => Type::Num(NumType::Byte),
                Pattern::IntConst(_) => Type::Num(NumType::Int),
                Pattern::FloatConst(_) => Type::Num(NumType::Float),
            }
        }
        fn count_bindings(p: &Pattern) -> usize {
            match p {
                Pattern::Any(_) => 0,
                Pattern::Var(_) => 1,
                Pattern::Tuple(pats) => pats.iter().map(|pat| count_bindings(pat)).sum(),
                Pattern::Ctor(_, _, maybe_pat) => maybe_pat
                    .as_ref()
                    .map_or_else(|| 0, |pat| count_bindings(&pat)),
                Pattern::BoolConst(_) => 0,
                Pattern::ByteConst(_) => 0,
                Pattern::IntConst(_) => 0,
                Pattern::FloatConst(_) => 0,
            }
        }
        fn remove_pattern_rec(ctx: &mut Context, p: Pattern) -> Vec<Pattern> {
            if ctx.is_unit(&pat_to_type(&p)) {
                ctx.new_local += count_bindings(&p);
                return Vec::new();
            }

            let res = match p {
                Pattern::Any(t) => match ctx.remove_type(t) {
                    Type::Tuple(nested) => {
                        let mut n = Vec::new();
                        for nest in nested {
                            n.push(Pattern::Any(nest));
                        }
                        n
                    }
                    a => vec![Pattern::Any(a)],
                },
                Pattern::Var(t) => {
                    let real_type = ctx.remove_type(t.clone());
                    match real_type {
                        Type::Tuple(var_types) => {
                            let mut new_vars = Vec::new();
                            let mut result_vars = Vec::new();
                            for new_var_type in var_types {
                                new_vars.push(Pattern::Var(new_var_type));
                                result_vars.push(Expr::Local(LocalId(ctx.old_local)));
                                ctx.old_local += 1;
                            }
                            ctx.current_local_id
                                .insert(ctx.new_local, Expr::Tuple(result_vars));
                            ctx.new_local += 1;

                            new_vars
                        }
                        t => {
                            ctx.current_local_id
                                .insert(ctx.new_local, Expr::Local(LocalId(ctx.old_local)));
                            ctx.new_local += 1;
                            ctx.old_local += 1;
                            vec![Pattern::Var(ctx.remove_type(t))]
                        }
                    }
                }
                Pattern::Tuple(pats) => {
                    let mut new_pats = Vec::new();
                    for pat in pats {
                        new_pats.push(remove_pattern_rec(ctx, pat));
                    }
                    new_pats.concat()
                }
                Pattern::Ctor(type_id, variant_id, maybe_pattern) => {
                    if ctx.type_reduction.contains_key(&type_id) {
                        match maybe_pattern {
                            Some(pat) => remove_pattern_rec(ctx, *pat),
                            None => Vec::new(),
                        }
                    } else {
                        vec![Pattern::Ctor(
                            type_id,
                            variant_id,
                            maybe_pattern.map(|pat| Box::new(ctx.remove_pattern(*pat))),
                        )]
                    }
                }
                Pattern::BoolConst(b) => vec![Pattern::BoolConst(b)],
                Pattern::ByteConst(b) => vec![Pattern::ByteConst(b)],
                Pattern::IntConst(b) => vec![Pattern::IntConst(b)],
                Pattern::FloatConst(b) => vec![Pattern::FloatConst(b)],
            };
            res
        }
        let result = remove_pattern_rec(self, p);
        if result.len() == 0 {
            Pattern::Tuple(Vec::new())
        } else if result.len() == 1 {
            result[0].clone()
        } else {
            Pattern::Tuple(result)
        }
    }

    pub fn remove_func_def(&mut self, _id: CustomFuncId, def: FuncDef) -> FuncDef {
        let body = def.body;
        let arg = def.arg;
        let (new_pattern, new_body) = with_scope(self, |sub_ctx| {
            bind_pattern(sub_ctx, &arg);
            (sub_ctx.remove_pattern(arg), sub_ctx.remove_expr(body))
        });

        FuncDef {
            purity: def.purity,
            arg_type: self.remove_type(def.arg_type),
            ret_type: self.remove_type(def.ret_type),
            arg: new_pattern,
            body: new_body,
            profile_point: def.profile_point,
        }
    }
}

fn typecheck_expr(ctx: &mut Context, expr: &Expr) -> Type {
    use Expr as E;
    use Type as T;

    match expr {
        E::Intrinsic(intr, _v) => {
            fn trans_type(type_: &intrinsics::Type) -> Type {
                match type_ {
                    intrinsics::Type::Bool => T::Bool,
                    intrinsics::Type::Num(num_type) => T::Num(*num_type),
                    intrinsics::Type::Tuple(items) => {
                        T::Tuple(items.iter().map(trans_type).collect())
                    }
                }
            }

            let sig = intrinsic_sig(*intr);
            trans_type(&sig.ret)
        }
        E::ArrayOp(ArrayOp::Get(item_type, _array, _index)) => item_type.clone(),
        E::ArrayOp(ArrayOp::Extract(item_type, _array, _index)) => T::Tuple(vec![
            item_type.clone(),
            T::HoleArray(Box::new(item_type.clone())),
        ]),
        E::ArrayOp(ArrayOp::Len(_item_type, _array)) => T::Num(NumType::Int),
        E::ArrayOp(ArrayOp::Push(item_type, _array, _item)) => {
            let array_type = T::Array(Box::new(item_type.clone()));
            array_type
        }
        E::ArrayOp(ArrayOp::Pop(item_type, _array)) => {
            let array_type = T::Array(Box::new(item_type.clone()));
            T::Tuple(vec![array_type, item_type.clone()])
        }
        E::ArrayOp(ArrayOp::Replace(item_type, _hole_array, _item)) => {
            T::Array(Box::new(item_type.clone()))
        }
        E::ArrayOp(ArrayOp::Reserve(item_type, _array, _capacity)) => {
            let array_type = T::Array(Box::new(item_type.clone()));
            array_type
        }
        E::IoOp(IoOp::Input) => T::Array(Box::new(T::Num(NumType::Byte))),
        E::IoOp(IoOp::Output(_output)) => T::Tuple(vec![]),
        E::Panic(ret_type, _message) => ret_type.clone(),
        E::Ctor(type_id, _variant_id, _expr) => T::Custom(*type_id),
        E::Local(local_id) => ctx.locals[local_id.0].clone(),
        E::Tuple(items) => {
            let item_types = items.iter().map(|item| typecheck_expr(ctx, item)).collect();
            T::Tuple(item_types)
        }
        E::Call(_purity, func_id, _arg) => ctx.prog.funcs[func_id].ret_type.clone(),
        E::Match(_matched, branches, result_type) => {
            for (pattern, _body) in branches {
                with_scope(ctx, |sub_ctx| {
                    bind_pattern(sub_ctx, pattern);
                });
            }
            result_type.clone()
        }
        E::LetMany(bindings, body) => with_scope(ctx, |sub_ctx| {
            for (lhs, _rhs) in bindings {
                bind_pattern(sub_ctx, lhs);
            }
            typecheck_expr(sub_ctx, body)
        }),
        E::ArrayLit(item_type, _items) => T::Array(Box::new(item_type.clone())),
        E::BoolLit(_) => T::Bool,
        E::ByteLit(_) => T::Num(NumType::Byte),
        E::IntLit(_) => T::Num(NumType::Int),
        E::FloatLit(_) => T::Num(NumType::Float),
    }
}

fn bind_pattern(ctx: &mut Context, pattern: &Pattern) {
    use Pattern as P;
    match pattern {
        P::Any(_) => {}
        P::Var(t) => ctx.locals.push(t.clone()),
        P::Tuple(pats) => {
            for pat in pats.iter() {
                bind_pattern(ctx, pat);
            }
        }
        P::Ctor(_type_id, _variant_id, Some(arg_pat)) => {
            bind_pattern(ctx, arg_pat);
        }
        P::Ctor(_type_id, _variant_id, None) => {}
        P::BoolConst(_) | P::ByteConst(_) | P::IntConst(_) | P::FloatConst(_) => {}
    }
}

pub fn remove_unit(prog: &Program) -> Program {
    fn add_type_deps(deps: &mut BTreeSet<CustomTypeId>, type_: &Type) {
        match type_ {
            Type::Bool => {}
            Type::Num(_) => {}
            Type::Array(elem_type) => {
                add_type_deps(deps, elem_type);
            }
            Type::HoleArray(elem_type) => {
                add_type_deps(deps, elem_type);
            }
            Type::Tuple(elem_types) => {
                for elem_type in elem_types {
                    add_type_deps(deps, elem_type);
                }
            }
            Type::Custom(custom_type_id) => {
                deps.insert(*custom_type_id);
            }
        }
    }

    fn compute_reduction(
        prog: &Program,
        type_reduction: &mut BTreeMap<CustomTypeId, Type>,
        type_id: CustomTypeId,
        recursive_types: &BTreeSet<CustomTypeId>,
    ) -> Type {
        if let Some(t) = type_reduction.get(&type_id) {
            return t.clone();
        }

        let type_def = &prog.custom_types[type_id];
        if type_def.variants.len() == 1 && !recursive_types.contains(&type_id) {
            match &type_def.variants.items[0] {
                None => {
                    type_reduction.insert(type_id, Type::Tuple(Vec::new()));
                    return Type::Tuple(Vec::new());
                }
                Some(Type::Custom(new_type_id)) => {
                    let new_type =
                        compute_reduction(prog, type_reduction, *new_type_id, recursive_types);
                    type_reduction.insert(type_id, new_type.clone());
                    return new_type;
                }
                Some(t) => {
                    type_reduction.insert(type_id, t.clone());
                    return t.clone();
                }
            }
        }

        return Type::Custom(type_id);
    }

    let type_graph = Graph {
        edges_out: prog.custom_types.map(|_, type_def| {
            let mut deps = BTreeSet::new();
            for variant in &type_def.variants {
                match variant.1 {
                    Some(type_) => {
                        add_type_deps(&mut deps, &type_);
                    }
                    None => {}
                }
            }
            deps.into_iter().collect()
        }),
    };

    let type_sccs = graph::strongly_connected(&type_graph);

    let mut recursive_types = BTreeSet::new();

    for scc in type_sccs {
        if scc.len() > 1 {
            for component in scc {
                recursive_types.insert(component);
            }
        } else {
            if type_graph.edges_out[scc[0]].contains(&scc[0]) {
                recursive_types.insert(scc[0]);
            }
        }
    }

    let mut type_reduction = BTreeMap::new();
    for (type_id, _type_def) in &prog.custom_types {
        compute_reduction(&prog, &mut type_reduction, type_id, &recursive_types);
    }

    let mut ctx = Context {
        locals: Vec::new(),
        prog: &prog,
        type_reduction,
        current_local_id: BTreeMap::new(),
        new_local: 0,
        old_local: 0,
        remove_type_cache: BTreeMap::new(),
    };

    let prog = prog.clone();
    Program {
        mod_symbols: prog.mod_symbols,
        custom_types: prog.custom_types.into_mapped(|type_id, type_def| {
            if ctx.type_reduction.contains_key(&type_id) {
                TypeDef {
                    variants: IdVec::new(),
                }
            } else {
                TypeDef {
                    variants: type_def.variants.into_mapped(|_variant_id, variant_type| {
                        variant_type.map(|variant_type| ctx.remove_type(variant_type))
                    }),
                }
            }
        }),
        custom_type_symbols: prog.custom_type_symbols,
        funcs: prog
            .funcs
            .into_mapped(|func_id, func_def| ctx.remove_func_def(func_id, func_def)),
        func_symbols: prog.func_symbols,
        profile_points: prog.profile_points,
        main: prog.main,
    }
}

fn with_scope<R, F: for<'a> FnOnce(&'a mut Context) -> R>(ctx: &mut Context, func: F) -> R {
    let old_len = ctx.locals.len();
    let old_locals = ctx.old_local;
    let new_locals = ctx.new_local;
    let old_vars = ctx.current_local_id.clone();
    let result = func(ctx);
    assert!(ctx.locals.len() >= old_len);
    ctx.locals.truncate(old_len);
    ctx.old_local = old_locals;
    ctx.new_local = new_locals;
    ctx.current_local_id = old_vars;
    result
}
