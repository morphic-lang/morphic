use crate::data::kinded_ast as kinded;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use id_collections::IdVec;
use morphic_common::util::instance_queue::InstanceQueue;

/// A type with no type parameters left: every head is a constructor.  This is the form that
/// instantiation arguments take, and what the instance queues are keyed on.  Unlike a mono type it
/// may be a partial application such as `Result Int`, which is not the type of any expression:
/// a parameter of higher kind is instantiated with exactly such a term.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ClosedType {
    App(res::TypeId, Vec<ClosedType>),
    Tuple(Vec<ClosedType>),
    Func(Purity, Box<ClosedType>, Box<ClosedType>),
}

type InstArgs = IdVec<res::TypeParamId, ClosedType>;

type ValInstances = InstanceQueue<(res::CustomGlobalId, InstArgs), mono::CustomGlobalId>;

type TypeInstances = InstanceQueue<(res::CustomTypeId, InstArgs), mono::CustomTypeId>;

/// Substitutes closed types for the type parameters of `type_`.
fn subst_type(inst_args: &InstArgs, type_: &res::Type) -> ClosedType {
    match type_ {
        res::Type::App(res::TypeHead::Var(param), args) => {
            let mut result = inst_args[param].clone();

            if args.is_empty() {
                return result;
            }

            let subst_args = args.iter().map(|arg| subst_type(inst_args, arg));

            match &mut result {
                ClosedType::App(_, result_args) => {
                    result_args.extend(subst_args);
                    result
                }

                // Kind checking guarantees that a parameter applied to arguments is instantiated
                // with a (possibly partial) application, never with a tuple or function type.
                ClosedType::Tuple(_) | ClosedType::Func(_, _, _) => unreachable!(),
            }
        }

        res::Type::App(res::TypeHead::Ctor(id), args) => ClosedType::App(
            *id,
            args.iter().map(|arg| subst_type(inst_args, arg)).collect(),
        ),

        res::Type::Tuple(items) => ClosedType::Tuple(
            items
                .iter()
                .map(|item| subst_type(inst_args, item))
                .collect(),
        ),

        res::Type::Func(purity, arg, ret) => ClosedType::Func(
            *purity,
            Box::new(subst_type(inst_args, arg)),
            Box::new(subst_type(inst_args, ret)),
        ),
    }
}

struct Instantiator<'a> {
    typedefs: &'a IdVec<res::CustomTypeId, kinded::TypeDef>,
    val_insts: ValInstances,
    type_insts: TypeInstances,
}

impl<'a> Instantiator<'a> {
    fn arity(&self, id: res::TypeId) -> usize {
        match id {
            res::TypeId::Bool | res::TypeId::Byte | res::TypeId::Int | res::TypeId::Float => 0,
            res::TypeId::Array => 1,
            res::TypeId::Custom(custom) => self.typedefs[custom].param_kinds.len(),
        }
    }

    /// Whether a closed type has kind `Type`, i.e. is the type of some expression rather than a
    /// partial application.
    fn has_kind_type(&self, type_: &ClosedType) -> bool {
        match type_ {
            ClosedType::App(id, args) => args.len() == self.arity(*id),
            ClosedType::Tuple(_) | ClosedType::Func(_, _, _) => true,
        }
    }

    /// Registers the instances of custom types mentioned by a closed instantiation argument, so
    /// that mono ids are always assigned to the components of an instantiation before the
    /// instantiation itself.  Arguments of higher kind mention no complete instances.
    fn register_inst_arg(&mut self, arg: &ClosedType) {
        if self.has_kind_type(arg) {
            self.mono_type(arg);
        }
    }

    fn resolve_val_inst(
        &mut self,
        id: res::CustomGlobalId,
        args: InstArgs,
    ) -> mono::CustomGlobalId {
        for (_, arg) in &args {
            self.register_inst_arg(arg);
        }
        self.val_insts.resolve((id, args))
    }

    fn resolve_type_inst(&mut self, id: res::CustomTypeId, args: InstArgs) -> mono::CustomTypeId {
        for (_, arg) in &args {
            self.register_inst_arg(arg);
        }
        self.type_insts.resolve((id, args))
    }

    /// Converts a closed type of kind `Type` into its mono representation, registering any custom
    /// type instances it mentions.
    fn mono_type(&mut self, type_: &ClosedType) -> mono::Type {
        match type_ {
            ClosedType::App(res::TypeId::Bool, args) => {
                debug_assert!(args.is_empty());
                mono::Type::Bool
            }

            ClosedType::App(res::TypeId::Byte, args) => {
                debug_assert!(args.is_empty());
                mono::Type::Byte
            }

            ClosedType::App(res::TypeId::Int, args) => {
                debug_assert!(args.is_empty());
                mono::Type::Int
            }

            ClosedType::App(res::TypeId::Float, args) => {
                debug_assert!(args.is_empty());
                mono::Type::Float
            }

            ClosedType::App(res::TypeId::Array, args) => {
                debug_assert_eq!(args.len(), 1);
                mono::Type::Array(Box::new(self.mono_type(&args[0])))
            }

            ClosedType::App(res::TypeId::Custom(id), args) => {
                debug_assert_eq!(args.len(), self.arity(res::TypeId::Custom(*id)));
                let new_id = self.resolve_type_inst(*id, IdVec::from_vec(args.clone()));
                mono::Type::Custom(new_id)
            }

            ClosedType::Tuple(items) => {
                mono::Type::Tuple(items.iter().map(|item| self.mono_type(item)).collect())
            }

            ClosedType::Func(purity, arg, ret) => mono::Type::Func(
                *purity,
                Box::new(self.mono_type(arg)),
                Box::new(self.mono_type(ret)),
            ),
        }
    }

    fn resolve_type(&mut self, inst_args: &InstArgs, type_: &res::Type) -> mono::Type {
        self.mono_type(&subst_type(inst_args, type_))
    }

    fn resolve_inst_args(
        &self,
        inst_args: &InstArgs,
        args: &IdVec<res::TypeParamId, res::Type>,
    ) -> InstArgs {
        args.map_refs(|_param_id, arg| subst_type(inst_args, arg))
    }

    fn resolve_expr(&mut self, inst_args: &InstArgs, expr: &typed::Expr) -> mono::Expr {
        match expr {
            typed::Expr::Global(res::GlobalId::Intrinsic(intr), args) => {
                debug_assert!(args.is_empty());
                mono::Expr::Intrinsic(*intr)
            }

            typed::Expr::Global(res::GlobalId::ArrayOp(op), args) => {
                debug_assert_eq!(args.len(), 1);
                mono::Expr::ArrayOp(
                    *op,
                    self.resolve_type(inst_args, &args[res::TypeParamId(0)]),
                )
            }

            typed::Expr::Global(res::GlobalId::IoOp(op), args) => {
                debug_assert!(args.is_empty());
                mono::Expr::IoOp(*op)
            }

            typed::Expr::Global(res::GlobalId::Panic, args) => {
                debug_assert_eq!(args.len(), 1);
                mono::Expr::Panic(self.resolve_type(inst_args, &args[res::TypeParamId(0)]))
            }

            typed::Expr::Global(res::GlobalId::Ctor(res::TypeId::Bool, variant), args) => {
                debug_assert!(args.is_empty());

                let val = match variant {
                    res::VariantId(0) => false,
                    res::VariantId(1) => true,
                    res::VariantId(_) => unreachable!(),
                };

                mono::Expr::BoolLit(val)
            }

            typed::Expr::Global(res::GlobalId::Ctor(res::TypeId::Custom(id), variant), args) => {
                let args_resolved = self.resolve_inst_args(inst_args, args);
                let new_id = self.resolve_type_inst(*id, args_resolved);
                mono::Expr::Ctor(new_id, *variant)
            }

            typed::Expr::Global(res::GlobalId::Ctor(_, _), _) => unreachable!(),

            typed::Expr::Global(res::GlobalId::Custom(id), args) => {
                let args_resolved = self.resolve_inst_args(inst_args, args);
                let new_id = self.resolve_val_inst(*id, args_resolved);
                mono::Expr::Global(new_id)
            }

            &typed::Expr::Local(id) => mono::Expr::Local(id),

            typed::Expr::Tuple(items) => mono::Expr::Tuple(
                items
                    .iter()
                    .map(|item| self.resolve_expr(inst_args, item))
                    .collect(),
            ),

            typed::Expr::Lam(purity, arg_type, ret_type, pat, body, prof_id) => {
                let pat_resolved = self.resolve_pattern(inst_args, pat);
                let arg_type_resolved = self.resolve_type(inst_args, arg_type);
                let ret_type_resolved = self.resolve_type(inst_args, ret_type);
                let body_resolved = self.resolve_expr(inst_args, body);
                mono::Expr::Lam(
                    *purity,
                    arg_type_resolved,
                    ret_type_resolved,
                    pat_resolved,
                    Box::new(body_resolved),
                    *prof_id,
                )
            }

            typed::Expr::App(purity, func, arg) => {
                let func_resolved = self.resolve_expr(inst_args, func);
                let arg_resolved = self.resolve_expr(inst_args, arg);
                mono::Expr::App(*purity, Box::new(func_resolved), Box::new(arg_resolved))
            }

            typed::Expr::Match(discrim, cases, result_type) => {
                let discrim_resolved = self.resolve_expr(inst_args, discrim);

                let cases_resolved = cases
                    .iter()
                    .map(|(pat, body)| {
                        let pat_resolved = self.resolve_pattern(inst_args, pat);
                        let body_resolved = self.resolve_expr(inst_args, body);
                        (pat_resolved, body_resolved)
                    })
                    .collect();

                let result_resolved = self.resolve_type(inst_args, result_type);

                mono::Expr::Match(Box::new(discrim_resolved), cases_resolved, result_resolved)
            }

            typed::Expr::LetMany(bindings, body) => {
                let mut new_bindings = Vec::new();

                for (lhs, rhs) in bindings {
                    let lhs_resolved = self.resolve_pattern(inst_args, lhs);
                    let rhs_resolved = self.resolve_expr(inst_args, rhs);

                    new_bindings.push((lhs_resolved, rhs_resolved));
                }

                let body_resolved = self.resolve_expr(inst_args, body);

                mono::Expr::LetMany(new_bindings, Box::new(body_resolved))
            }

            typed::Expr::ArrayLit(type_, items) => {
                let type_resolved = self.resolve_type(inst_args, type_);
                let item_resolved = items
                    .iter()
                    .map(|item| self.resolve_expr(inst_args, item))
                    .collect();

                mono::Expr::ArrayLit(type_resolved, item_resolved)
            }

            &typed::Expr::ByteLit(val) => mono::Expr::ByteLit(val),
            &typed::Expr::IntLit(val) => mono::Expr::IntLit(val),
            &typed::Expr::FloatLit(val) => mono::Expr::FloatLit(val),

            typed::Expr::Span(_, _, content) => self.resolve_expr(inst_args, content),
        }
    }

    fn resolve_pattern(&mut self, inst_args: &InstArgs, pat: &typed::Pattern) -> mono::Pattern {
        match pat {
            typed::Pattern::Any(type_) => mono::Pattern::Any(self.resolve_type(inst_args, type_)),

            typed::Pattern::Var(type_) => mono::Pattern::Var(self.resolve_type(inst_args, type_)),

            typed::Pattern::Tuple(items) => {
                let items_resolved = items
                    .iter()
                    .map(|item| self.resolve_pattern(inst_args, item))
                    .collect();

                mono::Pattern::Tuple(items_resolved)
            }

            typed::Pattern::Ctor(res::TypeId::Bool, args, variant, None) => {
                debug_assert!(args.is_empty());

                let val = match variant {
                    res::VariantId(0) => false,
                    res::VariantId(1) => true,
                    _ => unreachable!(),
                };

                mono::Pattern::BoolConst(val)
            }

            typed::Pattern::Ctor(res::TypeId::Custom(id), args, variant, content) => {
                let args_resolved =
                    IdVec::from_vec(args.iter().map(|arg| subst_type(inst_args, arg)).collect());

                let content_resolved = if let Some(content) = content {
                    Some(Box::new(self.resolve_pattern(inst_args, content)))
                } else {
                    None
                };

                let new_id = self.resolve_type_inst(*id, args_resolved);

                mono::Pattern::Ctor(new_id, *variant, content_resolved)
            }

            typed::Pattern::Ctor(_, _, _, _) => unreachable!(),

            &typed::Pattern::ByteConst(val) => mono::Pattern::ByteConst(val),
            &typed::Pattern::IntConst(val) => mono::Pattern::IntConst(val),
            &typed::Pattern::FloatConst(val) => mono::Pattern::FloatConst(val),

            typed::Pattern::Span(_, _, content) => self.resolve_pattern(inst_args, content),
        }
    }

    fn resolve_val_def(&mut self, inst_args: &InstArgs, def: &typed::ValDef) -> mono::ValDef {
        debug_assert_eq!(inst_args.len(), def.scheme.param_kinds.len());

        let type_resolved = self.resolve_type(inst_args, &def.scheme.body);

        let body_resolved = self.resolve_expr(inst_args, &def.body);

        mono::ValDef {
            type_: type_resolved,
            body: body_resolved,
        }
    }

    fn resolve_typedef(
        &mut self,
        inst_args: &InstArgs,
        typedef: &kinded::TypeDef,
    ) -> mono::TypeDef {
        debug_assert_eq!(inst_args.len(), typedef.param_kinds.len());

        let variants_resolved = typedef.variants.map_refs(|_id, variant| {
            if let Some(variant) = variant {
                Some(self.resolve_type(inst_args, &variant))
            } else {
                None
            }
        });

        mono::TypeDef {
            variants: variants_resolved,
        }
    }
}

pub fn monomorphize(program: typed::Program) -> mono::Program {
    let mut inst = Instantiator {
        typedefs: &program.custom_types,
        val_insts: ValInstances::new(),
        type_insts: TypeInstances::new(),
    };

    let main_new_id = inst.resolve_val_inst(program.main, IdVec::new());

    let mut val_defs_resolved = IdVec::new();
    let mut val_defs_resolved_symbols = IdVec::new();

    while let Some((new_id, (orig_id, inst_args))) = inst.val_insts.pop_pending() {
        let def = &program.vals[orig_id];

        let def_resolved = inst.resolve_val_def(&inst_args, def);
        let def_resolved_symbols = mono::ValSymbols::Normal(mono::ValSymbolsInner {
            val_name: program.val_symbols[orig_id].val_name.clone(),
        });

        let pushed_val_id = val_defs_resolved.push(def_resolved);
        let pushed_val_symbols_id = val_defs_resolved_symbols.push(def_resolved_symbols);

        // We enqueue pending val defs to resolve in the order in which their ids are generated, so
        // this should always hold.  This allows us to insert resolved val defs at the appropriate
        // index simply by pushing them onto the end of the vector.
        assert_eq!(new_id, pushed_val_id);
        assert_eq!(new_id, pushed_val_symbols_id);
    }

    let mut typedefs_resolved = IdVec::new();
    let mut typedefs_resolved_symbols = IdVec::new();

    while let Some((new_id, (orig_id, inst_args))) = inst.type_insts.pop_pending() {
        let typedef = &program.custom_types[orig_id];

        let typedef_resolved = inst.resolve_typedef(&inst_args, typedef);

        let typedef_resolved_symbols = mono::TypeSymbols {
            type_name: program.custom_type_symbols[orig_id].type_name.clone(),
            variant_symbols: program.custom_type_symbols[orig_id].variant_symbols.clone(),
        };

        let pushed_type_id = typedefs_resolved.push(typedef_resolved);
        let pushed_type_symbols_id = typedefs_resolved_symbols.push(typedef_resolved_symbols);

        // These assertions are analogous to those in the val def case, described above
        assert_eq!(new_id, pushed_type_id);
        assert_eq!(new_id, pushed_type_symbols_id);
    }

    mono::Program {
        mod_symbols: program.mod_symbols.clone(),
        custom_types: typedefs_resolved,
        custom_type_symbols: typedefs_resolved_symbols,
        profile_points: program.profile_points,
        vals: val_defs_resolved,
        val_symbols: val_defs_resolved_symbols,
        main: main_new_id,
    }
}
