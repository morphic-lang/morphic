//! The traits the operators desugar to, and their impls for the builtin types.
//!
//! `+` means `Add`'s `add`, `=` means `PartialEq`'s `eq`, `!` means `Not`'s `not`, and so on, so
//! that a user impl of a builtin trait gives its type the operator.  The impls for the builtin
//! types map each func to the corresponding intrinsic and are in scope in every module unless a
//! declared or imported impl of the same name covers one up.  Like Rust's, `Eq` and `Ord` are
//! markers with no funcs: they refine `PartialEq` and `PartialOrd`, which `Float` has but they do
//! not; and `Not` is logical not for `Bool` and bitwise not for `Int`.

use crate::data::elaborated_ast as elab;
use crate::data::elaborated_ast::Derivation;
use crate::data::intrinsics::Intrinsic;
use crate::data::kinded_ast::Kind;
use crate::data::num_type::NumType;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::data::resolved_ast::{SuperId, TraitFuncId, TraitId, TypeId, TypeParamId};
use id_collections::{Count, IdVec};
use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BuiltinTrait {
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Add,
    Sub,
    Mul,
    Div,
    Neg,
    Not,
}

impl BuiltinTrait {
    pub const ALL: [BuiltinTrait; 10] = [
        BuiltinTrait::PartialEq,
        BuiltinTrait::Eq,
        BuiltinTrait::PartialOrd,
        BuiltinTrait::Ord,
        BuiltinTrait::Add,
        BuiltinTrait::Sub,
        BuiltinTrait::Mul,
        BuiltinTrait::Div,
        BuiltinTrait::Neg,
        BuiltinTrait::Not,
    ];

    pub fn name(self) -> &'static str {
        match self {
            BuiltinTrait::PartialEq => "PartialEq",
            BuiltinTrait::Eq => "Eq",
            BuiltinTrait::PartialOrd => "PartialOrd",
            BuiltinTrait::Ord => "Ord",
            BuiltinTrait::Add => "Add",
            BuiltinTrait::Sub => "Sub",
            BuiltinTrait::Mul => "Mul",
            BuiltinTrait::Div => "Div",
            BuiltinTrait::Neg => "Neg",
            BuiltinTrait::Not => "Not",
        }
    }

    pub fn from_name(name: &str) -> Option<BuiltinTrait> {
        BuiltinTrait::ALL
            .into_iter()
            .find(|trait_| trait_.name() == name)
    }

    /// Every builtin trait has one parameter, of kind `Type`.
    pub fn num_params() -> Count<TypeParamId> {
        Count::from_value(1)
    }

    pub fn supers(self) -> &'static [BuiltinTrait] {
        match self {
            BuiltinTrait::Eq => &[BuiltinTrait::PartialEq],
            BuiltinTrait::PartialOrd => &[BuiltinTrait::PartialEq],
            BuiltinTrait::Ord => &[BuiltinTrait::Eq, BuiltinTrait::PartialOrd],
            BuiltinTrait::PartialEq
            | BuiltinTrait::Add
            | BuiltinTrait::Sub
            | BuiltinTrait::Mul
            | BuiltinTrait::Div
            | BuiltinTrait::Neg
            | BuiltinTrait::Not => &[],
        }
    }

    pub fn funcs(self) -> &'static [BuiltinTraitFunc] {
        match self {
            BuiltinTrait::PartialEq => &[BuiltinTraitFunc::Eq],
            BuiltinTrait::PartialOrd => &[
                BuiltinTraitFunc::Lt,
                BuiltinTraitFunc::Lte,
                BuiltinTraitFunc::Gt,
                BuiltinTraitFunc::Gte,
            ],
            BuiltinTrait::Add => &[BuiltinTraitFunc::Add],
            BuiltinTrait::Sub => &[BuiltinTraitFunc::Sub],
            BuiltinTrait::Mul => &[BuiltinTraitFunc::Mul],
            BuiltinTrait::Div => &[BuiltinTraitFunc::Div],
            BuiltinTrait::Neg => &[BuiltinTraitFunc::Neg],
            BuiltinTrait::Not => &[BuiltinTraitFunc::Not],
            BuiltinTrait::Eq | BuiltinTrait::Ord => &[],
        }
    }

    /// The trait as resolution sees it: the superclasses and func signatures are over the one
    /// parameter.
    pub fn res_def(self) -> res::TraitDef {
        res::TraitDef {
            num_params: Self::num_params(),
            supers: IdVec::from_vec(
                self.supers()
                    .iter()
                    .map(|&super_| res::TraitApp {
                        trait_: TraitId::Builtin(super_),
                        args: vec![res::Type::param(PARAM)],
                    })
                    .collect(),
            ),
            funcs: IdVec::from_vec(
                self.funcs()
                    .iter()
                    .map(|func| res::TraitFuncSig {
                        num_own_params: Count::from_value(0),
                        own_constrs: IdVec::new(),
                        body: func.shape().res_type(),
                    })
                    .collect(),
            ),
        }
    }

    /// The trait as every pass after signature elaboration sees it.  Its types mention no
    /// constrained constructor, so they carry no evidence.
    pub fn elab_def(self) -> &'static elab::TraitDef {
        static DEFS: OnceLock<Vec<elab::TraitDef>> = OnceLock::new();
        let defs = DEFS.get_or_init(|| {
            BuiltinTrait::ALL
                .iter()
                .map(|trait_| elab::TraitDef {
                    param_kinds: IdVec::from_vec(vec![Kind::TYPE]),
                    supers: IdVec::from_vec(
                        trait_
                            .supers()
                            .iter()
                            .map(|&super_| elab::TraitApp {
                                trait_: TraitId::Builtin(super_),
                                args: vec![elab::Type::param(PARAM)],
                            })
                            .collect(),
                    ),
                    funcs: IdVec::from_vec(
                        trait_
                            .funcs()
                            .iter()
                            .map(|func| elab::TraitFuncSig {
                                own_param_kinds: IdVec::new(),
                                own_constrs: IdVec::new(),
                                body: func.shape().elab_type(),
                            })
                            .collect(),
                    ),
                })
                .collect()
        });
        &defs[BuiltinTrait::ALL
            .iter()
            .position(|&trait_| trait_ == self)
            .expect("every builtin trait is listed")]
    }
}

/// The parameter of a builtin trait.
const PARAM: TypeParamId = TypeParamId(0);

/// A func of a builtin trait, which is what an operator stands for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BuiltinTraitFunc {
    Eq,
    Lt,
    Lte,
    Gt,
    Gte,
    Add,
    Sub,
    Mul,
    Div,
    Neg,
    Not,
}

/// The signature of a builtin trait func, over the trait's parameter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FuncShape {
    /// `(a, a) -> a`
    Binary,
    /// `(a, a) -> Bool`
    Comparison,
    /// `a -> a`
    Unary,
}

impl FuncShape {
    pub fn res_type(self) -> res::Type {
        let param = res::Type::param(PARAM);
        let bool_ = res::Type::ctor(TypeId::Bool);
        let (arg, ret) = match self {
            FuncShape::Binary => (res::Type::Tuple(vec![param.clone(), param.clone()]), param),
            FuncShape::Comparison => (res::Type::Tuple(vec![param.clone(), param]), bool_),
            FuncShape::Unary => (param.clone(), param),
        };
        res::Type::Func(Purity::Pure, Box::new(arg), Box::new(ret))
    }

    pub fn elab_type(self) -> elab::Type<Derivation<elab::TraitGiven>> {
        let param = elab::Type::param(PARAM);
        let bool_ = elab::Type::ctor(TypeId::Bool);
        let (arg, ret) = match self {
            FuncShape::Binary => (elab::Type::Tuple(vec![param.clone(), param.clone()]), param),
            FuncShape::Comparison => (elab::Type::Tuple(vec![param.clone(), param]), bool_),
            FuncShape::Unary => (param.clone(), param),
        };
        elab::Type::Func(Purity::Pure, Box::new(arg), Box::new(ret))
    }
}

impl BuiltinTraitFunc {
    pub const ALL: [BuiltinTraitFunc; 11] = [
        BuiltinTraitFunc::Eq,
        BuiltinTraitFunc::Lt,
        BuiltinTraitFunc::Lte,
        BuiltinTraitFunc::Gt,
        BuiltinTraitFunc::Gte,
        BuiltinTraitFunc::Add,
        BuiltinTraitFunc::Sub,
        BuiltinTraitFunc::Mul,
        BuiltinTraitFunc::Div,
        BuiltinTraitFunc::Neg,
        BuiltinTraitFunc::Not,
    ];

    pub fn trait_(self) -> BuiltinTrait {
        match self {
            BuiltinTraitFunc::Eq => BuiltinTrait::PartialEq,
            BuiltinTraitFunc::Lt
            | BuiltinTraitFunc::Lte
            | BuiltinTraitFunc::Gt
            | BuiltinTraitFunc::Gte => BuiltinTrait::PartialOrd,
            BuiltinTraitFunc::Add => BuiltinTrait::Add,
            BuiltinTraitFunc::Sub => BuiltinTrait::Sub,
            BuiltinTraitFunc::Mul => BuiltinTrait::Mul,
            BuiltinTraitFunc::Div => BuiltinTrait::Div,
            BuiltinTraitFunc::Neg => BuiltinTrait::Neg,
            BuiltinTraitFunc::Not => BuiltinTrait::Not,
        }
    }

    /// The func's position among its trait's funcs.
    pub fn id(self) -> TraitFuncId {
        TraitFuncId(
            self.trait_()
                .funcs()
                .iter()
                .position(|&func| func == self)
                .expect("every builtin trait func is listed by its trait"),
        )
    }

    pub fn of(trait_: BuiltinTrait, id: TraitFuncId) -> BuiltinTraitFunc {
        trait_.funcs()[id.0]
    }

    pub fn name(self) -> &'static str {
        match self {
            BuiltinTraitFunc::Eq => "eq",
            BuiltinTraitFunc::Lt => "lt",
            BuiltinTraitFunc::Lte => "lte",
            BuiltinTraitFunc::Gt => "gt",
            BuiltinTraitFunc::Gte => "gte",
            BuiltinTraitFunc::Add => "add",
            BuiltinTraitFunc::Sub => "sub",
            BuiltinTraitFunc::Mul => "mul",
            BuiltinTraitFunc::Div => "div",
            BuiltinTraitFunc::Neg => "neg",
            BuiltinTraitFunc::Not => "not",
        }
    }

    pub fn shape(self) -> FuncShape {
        match self {
            BuiltinTraitFunc::Eq
            | BuiltinTraitFunc::Lt
            | BuiltinTraitFunc::Lte
            | BuiltinTraitFunc::Gt
            | BuiltinTraitFunc::Gte => FuncShape::Comparison,
            BuiltinTraitFunc::Add
            | BuiltinTraitFunc::Sub
            | BuiltinTraitFunc::Mul
            | BuiltinTraitFunc::Div => FuncShape::Binary,
            BuiltinTraitFunc::Neg | BuiltinTraitFunc::Not => FuncShape::Unary,
        }
    }
}

/// A builtin type that has impls of builtin traits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BuiltinImplType {
    Bool,
    Num(NumType),
}

impl BuiltinImplType {
    pub const ALL: [BuiltinImplType; 4] = [
        BuiltinImplType::Bool,
        BuiltinImplType::Num(NumType::Byte),
        BuiltinImplType::Num(NumType::Int),
        BuiltinImplType::Num(NumType::Float),
    ];

    pub fn type_id(self) -> TypeId {
        match self {
            BuiltinImplType::Bool => TypeId::Bool,
            BuiltinImplType::Num(NumType::Byte) => TypeId::Byte,
            BuiltinImplType::Num(NumType::Int) => TypeId::Int,
            BuiltinImplType::Num(NumType::Float) => TypeId::Float,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            BuiltinImplType::Bool => "Bool",
            BuiltinImplType::Num(NumType::Byte) => "Byte",
            BuiltinImplType::Num(NumType::Int) => "Int",
            BuiltinImplType::Num(NumType::Float) => "Float",
        }
    }
}

/// The impl of a builtin trait for a builtin type.  Only the combinations that exist can be
/// constructed: `Bool` has equality and `Not` only, `Float` has no total equality or order, and
/// `Int` is the only number with `Not`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct BuiltinImpl {
    trait_: BuiltinTrait,
    type_: BuiltinImplType,
}

impl BuiltinImpl {
    pub fn new(trait_: BuiltinTrait, type_: BuiltinImplType) -> Option<BuiltinImpl> {
        let exists = match (trait_, type_) {
            (
                BuiltinTrait::PartialEq | BuiltinTrait::Eq | BuiltinTrait::Not,
                BuiltinImplType::Bool,
            ) => true,
            (_, BuiltinImplType::Bool) => false,
            (BuiltinTrait::Eq | BuiltinTrait::Ord, BuiltinImplType::Num(NumType::Float)) => false,
            (BuiltinTrait::Not, BuiltinImplType::Num(num)) => matches!(num, NumType::Int),
            (_, BuiltinImplType::Num(_)) => true,
        };
        exists.then_some(BuiltinImpl { trait_, type_ })
    }

    pub fn all() -> impl Iterator<Item = BuiltinImpl> {
        BuiltinTrait::ALL.into_iter().flat_map(|trait_| {
            BuiltinImplType::ALL
                .into_iter()
                .filter_map(move |type_| BuiltinImpl::new(trait_, type_))
        })
    }

    pub fn trait_(self) -> BuiltinTrait {
        self.trait_
    }

    pub fn type_(self) -> BuiltinImplType {
        self.type_
    }

    pub fn name(self) -> String {
        format!("{}{}", self.trait_.name(), self.type_.name())
    }

    /// The impl's evidence for each superclass of its trait, which exists by construction.
    pub fn supers(self) -> IdVec<SuperId, BuiltinImpl> {
        IdVec::from_vec(
            self.trait_
                .supers()
                .iter()
                .map(|&super_| {
                    BuiltinImpl::new(super_, self.type_)
                        .expect("a builtin impl's type has impls of the trait's superclasses")
                })
                .collect(),
        )
    }

    /// The intrinsic implementing one of the impl's funcs.
    pub fn func_intrinsic(self, func: TraitFuncId) -> Intrinsic {
        use BuiltinTraitFunc::*;
        use Intrinsic as I;
        let func = BuiltinTraitFunc::of(self.trait_, func);
        match (func, self.type_) {
            (Eq, BuiltinImplType::Bool) => I::EqBool,
            (Not, BuiltinImplType::Bool) => I::Not,
            (_, BuiltinImplType::Bool) => unreachable!("Bool has equality and not only"),
            (func, BuiltinImplType::Num(num)) => match (func, num) {
                (Eq, NumType::Byte) => I::EqByte,
                (Lt, NumType::Byte) => I::LtByte,
                (Lte, NumType::Byte) => I::LteByte,
                (Gt, NumType::Byte) => I::GtByte,
                (Gte, NumType::Byte) => I::GteByte,
                (Add, NumType::Byte) => I::AddByte,
                (Sub, NumType::Byte) => I::SubByte,
                (Mul, NumType::Byte) => I::MulByte,
                (Div, NumType::Byte) => I::DivByte,
                (Neg, NumType::Byte) => I::NegByte,
                (Eq, NumType::Int) => I::EqInt,
                (Lt, NumType::Int) => I::LtInt,
                (Lte, NumType::Int) => I::LteInt,
                (Gt, NumType::Int) => I::GtInt,
                (Gte, NumType::Int) => I::GteInt,
                (Add, NumType::Int) => I::AddInt,
                (Sub, NumType::Int) => I::SubInt,
                (Mul, NumType::Int) => I::MulInt,
                (Div, NumType::Int) => I::DivInt,
                (Neg, NumType::Int) => I::NegInt,
                (Eq, NumType::Float) => I::EqFloat,
                (Lt, NumType::Float) => I::LtFloat,
                (Lte, NumType::Float) => I::LteFloat,
                (Gt, NumType::Float) => I::GtFloat,
                (Gte, NumType::Float) => I::GteFloat,
                (Add, NumType::Float) => I::AddFloat,
                (Sub, NumType::Float) => I::SubFloat,
                (Mul, NumType::Float) => I::MulFloat,
                (Div, NumType::Float) => I::DivFloat,
                (Neg, NumType::Float) => I::NegFloat,
                (Not, NumType::Int) => I::IntBitNot,
                (Not, NumType::Byte | NumType::Float) => {
                    unreachable!("Int is the only number with not")
                }
            },
        }
    }
}

/// The definition of a trait, builtin or declared.
pub fn elab_trait_def(
    traits: &IdVec<res::CustomTraitId, elab::TraitDef>,
    trait_: TraitId,
) -> &elab::TraitDef {
    match trait_ {
        TraitId::Builtin(builtin) => builtin.elab_def(),
        TraitId::Custom(custom) => &traits[custom],
    }
}

/// The superclass evidence a builtin impl carries: the impls of the same type for its trait's
/// superclasses.
pub fn builtin_impl_supers(impl_: BuiltinImpl) -> IdVec<SuperId, elab::Derivation> {
    impl_
        .supers()
        .map(|_, super_| Derivation::Impl(res::ImplId::Builtin(super_), IdVec::new(), IdVec::new()))
}

/// The name of a trait, builtin or declared.
pub fn trait_name(
    symbols: &IdVec<res::CustomTraitId, res::TraitSymbols>,
    trait_: TraitId,
) -> String {
    match trait_ {
        TraitId::Builtin(builtin) => builtin.name().to_owned(),
        TraitId::Custom(custom) => symbols[custom].trait_name.0.clone(),
    }
}

/// The name of a trait func, builtin or declared.
pub fn trait_func_name(
    symbols: &IdVec<res::CustomTraitId, res::TraitSymbols>,
    trait_: TraitId,
    func: TraitFuncId,
) -> String {
    match trait_ {
        TraitId::Builtin(builtin) => BuiltinTraitFunc::of(builtin, func).name().to_owned(),
        TraitId::Custom(custom) => symbols[custom].func_symbols[func].func_name.0.clone(),
    }
}
