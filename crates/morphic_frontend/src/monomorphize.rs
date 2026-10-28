use crate::data::elaborated_ast as elab;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::data::solved_ast as solved;
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

/// A derivation with no givens left: every constraint is discharged by an impl, so the impl func a
/// trait func reference stands for is known.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ClosedDerivation {
    Impl(res::ImplId, InstArgs, InstDerivs),
}

type InstArgs = IdVec<res::TypeParamId, ClosedType>;

type InstDerivs = IdVec<res::TraitConstrId, ClosedDerivation>;

/// What identifies one monomorphic copy of a definition: a closed type per type parameter and a
/// closed derivation per trait constraint.  Two references at the same types but under different
/// impls yield different copies, which is what makes named, scoped impls coherent within a copy.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Instantiation {
    args: InstArgs,
    derivs: InstDerivs,
}

type ValInstances = InstanceQueue<(res::CustomGlobalId, Instantiation), mono::CustomGlobalId>;

type TypeInstances = InstanceQueue<(res::CustomTypeId, InstArgs), mono::CustomTypeId>;

/// Instantiates an elaborated type at closed types, giving a closed type.
///
/// The type's evidence does not survive.  A monomorphic type is a representation,
/// and a `Set Int` is represented the same way whichever `Ord Int` impl it was built under; type
/// checking has already kept values built under different impls apart.  What does depend on
/// evidence is which copy of a definition a reference calls, and that is keyed by the closed
/// derivations of its instantiation rather than by the types in it.
fn subst_type(inst_args: &InstArgs, type_: &elab::Type) -> ClosedType {
    match type_ {
        elab::Type::App(res::TypeHead::Var(param), args) => {
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

        elab::Type::App(res::TypeHead::Ctor(id), args) => ClosedType::App(
            *id,
            args.iter().map(|arg| subst_type(inst_args, arg)).collect(),
        ),

        elab::Type::Constrained(id, args, _) => ClosedType::App(
            res::TypeId::Custom(*id),
            args.iter().map(|arg| subst_type(inst_args, arg)).collect(),
        ),

        elab::Type::Tuple(items) => ClosedType::Tuple(
            items
                .iter()
                .map(|item| subst_type(inst_args, item))
                .collect(),
        ),

        elab::Type::Func(purity, arg, ret) => ClosedType::Func(
            *purity,
            Box::new(subst_type(inst_args, arg)),
            Box::new(subst_type(inst_args, ret)),
        ),
    }
}

struct Instantiator<'a> {
    typedefs: &'a IdVec<res::CustomTypeId, elab::TypeDef>,
    impls: &'a IdVec<res::CustomImplId, elab::ImplDef>,
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
        inst: Instantiation,
    ) -> mono::CustomGlobalId {
        for (_, arg) in &inst.args {
            self.register_inst_arg(arg);
        }
        self.val_insts.resolve((id, inst))
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

    fn resolve_type(&mut self, inst: &Instantiation, type_: &elab::Type) -> mono::Type {
        self.mono_type(&subst_type(&inst.args, type_))
    }

    /// Substitutes the current instantiation into a derivation, yielding a closed one.  A given
    /// becomes the derivation the instantiation supplies for it, and a superclass projection out
    /// of an impl derivation becomes that impl's stored superclass derivation, instantiated at
    /// the impl derivation's own arguments.
    fn subst_derivation(
        &self,
        inst: &Instantiation,
        deriv: &solved::Derivation,
    ) -> ClosedDerivation {
        match deriv {
            &solved::Derivation::Given(constr) => inst.derivs[constr].clone(),

            solved::Derivation::Impl(id, type_args, subs) => ClosedDerivation::Impl(
                *id,
                type_args.map_refs(|_, arg| subst_type(&inst.args, arg)),
                subs.map_refs(|_, sub| self.subst_derivation(inst, sub)),
            ),

            solved::Derivation::Super(inner, index) => {
                let ClosedDerivation::Impl(id, impl_args, impl_derivs) =
                    self.subst_derivation(inst, inner);
                match id {
                    // A builtin impl's superclass evidence is the builtin impl of the same type
                    // for the superclass.
                    res::ImplId::Builtin(builtin) => ClosedDerivation::Impl(
                        res::ImplId::Builtin(builtin.supers()[*index]),
                        IdVec::new(),
                        IdVec::new(),
                    ),
                    res::ImplId::Custom(custom) => {
                        let impl_inst = Instantiation {
                            args: impl_args,
                            derivs: impl_derivs,
                        };
                        self.subst_derivation(&impl_inst, &self.impls[custom].supers[*index])
                    }
                }
            }
        }
    }

    fn resolve_instantiation(
        &self,
        inst: &Instantiation,
        args: &IdVec<res::TypeParamId, elab::Type>,
        derivs: &IdVec<res::TraitConstrId, solved::Derivation>,
    ) -> Instantiation {
        Instantiation {
            args: args.map_refs(|_, arg| subst_type(&inst.args, arg)),
            derivs: derivs.map_refs(|_, deriv| self.subst_derivation(inst, deriv)),
        }
    }

    fn resolve_expr(&mut self, inst: &Instantiation, expr: &solved::Expr) -> mono::Expr {
        match expr {
            solved::Expr::Global(res::GlobalId::Intrinsic(intr), args, _) => {
                debug_assert!(args.is_empty());
                mono::Expr::Intrinsic(*intr)
            }

            solved::Expr::Global(res::GlobalId::ArrayOp(op), args, _) => {
                debug_assert_eq!(args.len(), 1);
                mono::Expr::ArrayOp(*op, self.resolve_type(inst, &args[res::TypeParamId(0)]))
            }

            solved::Expr::Global(res::GlobalId::IoOp(op), args, _) => {
                debug_assert!(args.is_empty());
                mono::Expr::IoOp(*op)
            }

            solved::Expr::Global(res::GlobalId::Panic, args, _) => {
                debug_assert_eq!(args.len(), 1);
                mono::Expr::Panic(self.resolve_type(inst, &args[res::TypeParamId(0)]))
            }

            solved::Expr::Global(res::GlobalId::Ctor(res::TypeId::Bool, variant), args, _) => {
                debug_assert!(args.is_empty());

                let val = match variant {
                    res::VariantId(0) => false,
                    res::VariantId(1) => true,
                    res::VariantId(_) => unreachable!(),
                };

                mono::Expr::BoolLit(val)
            }

            solved::Expr::Global(
                res::GlobalId::Ctor(res::TypeId::Custom(id), variant),
                args,
                _,
            ) => {
                let args_resolved = args.map_refs(|_, arg| subst_type(&inst.args, arg));
                let new_id = self.resolve_type_inst(*id, args_resolved);
                mono::Expr::Ctor(new_id, *variant)
            }

            solved::Expr::Global(res::GlobalId::Ctor(_, _), _, _) => unreachable!(),

            // A trait func stands for the corresponding func of whichever impl discharges the
            // trait constraint, instantiated at that impl's arguments and evidence followed by
            // the func's own.
            solved::Expr::TraitFunc(_, func, trait_inst) => {
                let ClosedDerivation::Impl(impl_id, impl_args, impl_derivs) =
                    self.subst_derivation(inst, &trait_inst.trait_deriv);
                let impl_def = match impl_id {
                    // A builtin impl's func is the intrinsic implementing it, so the operators
                    // on builtin types compile exactly as before there were traits.
                    res::ImplId::Builtin(builtin) => {
                        return mono::Expr::Intrinsic(builtin.func_intrinsic(*func));
                    }
                    res::ImplId::Custom(custom) => &self.impls[custom],
                };
                let layout = impl_def.func_layout();

                let callee_inst = Instantiation {
                    args: layout.params(
                        impl_args,
                        trait_inst
                            .func_args
                            .map_refs(|_, arg| subst_type(&inst.args, arg)),
                    ),
                    derivs: layout.constrs(
                        impl_derivs,
                        trait_inst
                            .func_derivs
                            .map_refs(|_, deriv| self.subst_derivation(inst, deriv)),
                    ),
                };

                let new_id = self.resolve_val_inst(impl_def.funcs[*func], callee_inst);
                mono::Expr::Global(new_id)
            }

            solved::Expr::Global(res::GlobalId::Custom(id), args, derivs) => {
                let callee_inst = self.resolve_instantiation(inst, args, derivs);
                let new_id = self.resolve_val_inst(*id, callee_inst);
                mono::Expr::Global(new_id)
            }

            &solved::Expr::Local(id) => mono::Expr::Local(id),

            solved::Expr::Tuple(items) => mono::Expr::Tuple(
                items
                    .iter()
                    .map(|item| self.resolve_expr(inst, item))
                    .collect(),
            ),

            solved::Expr::Lam(purity, arg_type, ret_type, pat, body, prof_id) => {
                let pat_resolved = self.resolve_pattern(inst, pat);
                let arg_type_resolved = self.resolve_type(inst, arg_type);
                let ret_type_resolved = self.resolve_type(inst, ret_type);
                let body_resolved = self.resolve_expr(inst, body);
                mono::Expr::Lam(
                    *purity,
                    arg_type_resolved,
                    ret_type_resolved,
                    pat_resolved,
                    Box::new(body_resolved),
                    *prof_id,
                )
            }

            solved::Expr::App(purity, func, arg) => {
                let func_resolved = self.resolve_expr(inst, func);
                let arg_resolved = self.resolve_expr(inst, arg);
                mono::Expr::App(*purity, Box::new(func_resolved), Box::new(arg_resolved))
            }

            solved::Expr::Match(discrim, cases, result_type) => {
                let discrim_resolved = self.resolve_expr(inst, discrim);

                let cases_resolved = cases
                    .iter()
                    .map(|(pat, body)| {
                        let pat_resolved = self.resolve_pattern(inst, pat);
                        let body_resolved = self.resolve_expr(inst, body);
                        (pat_resolved, body_resolved)
                    })
                    .collect();

                let result_resolved = self.resolve_type(inst, result_type);

                mono::Expr::Match(Box::new(discrim_resolved), cases_resolved, result_resolved)
            }

            solved::Expr::LetMany(bindings, body) => {
                let mut new_bindings = Vec::new();

                for (lhs, rhs) in bindings {
                    let lhs_resolved = self.resolve_pattern(inst, lhs);
                    let rhs_resolved = self.resolve_expr(inst, rhs);

                    new_bindings.push((lhs_resolved, rhs_resolved));
                }

                let body_resolved = self.resolve_expr(inst, body);

                mono::Expr::LetMany(new_bindings, Box::new(body_resolved))
            }

            solved::Expr::ArrayLit(type_, items) => {
                let type_resolved = self.resolve_type(inst, type_);
                let item_resolved = items
                    .iter()
                    .map(|item| self.resolve_expr(inst, item))
                    .collect();

                mono::Expr::ArrayLit(type_resolved, item_resolved)
            }

            &solved::Expr::ByteLit(val) => mono::Expr::ByteLit(val),
            &solved::Expr::IntLit(val) => mono::Expr::IntLit(val),
            &solved::Expr::FloatLit(val) => mono::Expr::FloatLit(val),

            solved::Expr::Span(_, _, content) => self.resolve_expr(inst, content),
        }
    }

    fn resolve_pattern(&mut self, inst: &Instantiation, pat: &solved::Pattern) -> mono::Pattern {
        match pat {
            solved::Pattern::Any(type_) => mono::Pattern::Any(self.resolve_type(inst, type_)),

            solved::Pattern::Var(type_) => mono::Pattern::Var(self.resolve_type(inst, type_)),

            solved::Pattern::Tuple(items) => {
                let items_resolved = items
                    .iter()
                    .map(|item| self.resolve_pattern(inst, item))
                    .collect();

                mono::Pattern::Tuple(items_resolved)
            }

            solved::Pattern::Ctor(res::TypeId::Bool, args, variant, None) => {
                debug_assert!(args.is_empty());

                let val = match variant {
                    res::VariantId(0) => false,
                    res::VariantId(1) => true,
                    _ => unreachable!(),
                };

                mono::Pattern::BoolConst(val)
            }

            solved::Pattern::Ctor(res::TypeId::Custom(id), args, variant, content) => {
                let args_resolved =
                    IdVec::from_vec(args.iter().map(|arg| subst_type(&inst.args, arg)).collect());

                let content_resolved = if let Some(content) = content {
                    Some(Box::new(self.resolve_pattern(inst, content)))
                } else {
                    None
                };

                let new_id = self.resolve_type_inst(*id, args_resolved);

                mono::Pattern::Ctor(new_id, *variant, content_resolved)
            }

            solved::Pattern::Ctor(_, _, _, _) => unreachable!(),

            &solved::Pattern::ByteConst(val) => mono::Pattern::ByteConst(val),
            &solved::Pattern::IntConst(val) => mono::Pattern::IntConst(val),
            &solved::Pattern::FloatConst(val) => mono::Pattern::FloatConst(val),

            solved::Pattern::Span(_, _, content) => self.resolve_pattern(inst, content),
        }
    }

    fn resolve_val_def(&mut self, inst: &Instantiation, def: &solved::ValDef) -> mono::ValDef {
        debug_assert_eq!(inst.args.len(), def.scheme.param_kinds.len());
        debug_assert_eq!(inst.derivs.len(), def.scheme.trait_constrs.len());

        let type_resolved = self.resolve_type(inst, &def.scheme.body);

        let body_resolved = self.resolve_expr(inst, &def.body);

        mono::ValDef {
            type_: type_resolved,
            body: body_resolved,
        }
    }

    fn resolve_typedef(&mut self, inst_args: &InstArgs, typedef: &elab::TypeDef) -> mono::TypeDef {
        debug_assert_eq!(inst_args.len(), typedef.param_kinds.len());

        let inst = Instantiation {
            args: inst_args.clone(),
            derivs: IdVec::new(),
        };

        let variants_resolved = typedef.variants.map_refs(|_id, variant| {
            if let Some(variant) = variant {
                Some(self.resolve_type(&inst, variant))
            } else {
                None
            }
        });

        mono::TypeDef {
            variants: variants_resolved,
        }
    }
}

pub fn monomorphize(program: solved::Program) -> mono::Program {
    let mut inst = Instantiator {
        typedefs: &program.custom_types,
        impls: &program.impls,
        val_insts: ValInstances::new(),
        type_insts: TypeInstances::new(),
    };

    let main_new_id = inst.resolve_val_inst(
        program.main,
        Instantiation {
            args: IdVec::new(),
            derivs: IdVec::new(),
        },
    );

    let mut val_defs_resolved = IdVec::new();
    let mut val_defs_resolved_symbols = IdVec::new();

    while let Some((new_id, (orig_id, instantiation))) = inst.val_insts.pop_pending() {
        let def = &program.vals[orig_id];

        let def_resolved = inst.resolve_val_def(&instantiation, def);
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
