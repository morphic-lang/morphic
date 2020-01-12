use pretty::{BoxDoc, Doc};
use std::collections::BTreeSet;
use std::fmt;

use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast as res;
use crate::util::id_type::Id;
use crate::util::id_vec::IdVec;

impl fmt::Debug for lifted::Program {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut w = Vec::new();
        self.to_doc().render(80, &mut w).unwrap();
        write!(f, "{}", String::from_utf8(w).unwrap())
    }
}

impl lifted::Program {
    fn to_doc<'a>(&'a self) -> Doc<'a, BoxDoc<()>> {
        let top_level_lams: BTreeSet<lifted::LamId> = self
            .vals
            .iter()
            .filter_map(|(_val_id, val)| match val.body {
                lifted::Expr::Lam(lam_id, _) => Some(lam_id),
                _ => None,
            })
            .collect();
        let custom_types = Doc::intersperse(
            self.custom_types
                .iter()
                .map(|(i, x)| x.to_doc(i, &self.custom_type_data)),
            Doc::newline().append(Doc::newline()),
        );

        let lams = Doc::intersperse(
            self.lams
                .iter()
                .filter(|(i, _)| !top_level_lams.contains(i))
                .map(|(i, lam)| {
                    lam.to_doc(i, &self.custom_type_data, &self.val_data, &self.lam_data[i])
                }),
            Doc::newline().append(Doc::newline()),
        );
        let vals = Doc::intersperse(
            self.vals
                .iter()
                .map(|(i, val)| val.to_doc(i, &self.custom_type_data, &self.val_data, &self.lams)),
            Doc::newline().append(Doc::newline()),
        );
        custom_types
            .append(Doc::newline())
            .append(Doc::newline())
            .append(lams)
            .append(Doc::newline())
            .append(Doc::newline())
            .append(vals)
    }
}

impl res::VariantData {
    fn to_doc<'a>(&'a self) -> Doc<'a, BoxDoc<()>> {
        Doc::text(&self.variant_name.0)
    }
}

impl lifted::LamData {
    fn to_doc<'a>(
        &'a self,
        val_data: &'a IdVec<mono::CustomGlobalId, mono::ValData>,
    ) -> Doc<'a, BoxDoc<()>> {
        Doc::text("// Generated from ")
            .append(Doc::text(&val_data[self.lifted_from].val_name.0))
            .append(Doc::newline())
    }
}

impl mono::ValData {
    fn to_doc<'a>(
        &'a self,
        _: &'a IdVec<mono::CustomTypeId, mono::TypeData>,
    ) -> Doc<'a, BoxDoc<()>> {
        Doc::text(&self.val_name.0)
    }
}

impl lifted::LocalId {
    fn to_doc(&self) -> Doc<BoxDoc<()>> {
        Doc::text("%").append(Doc::as_string(self.0)).append("")
    }
}

impl lifted::CaptureId {
    fn to_doc(&self) -> Doc<BoxDoc<()>> {
        Doc::text("#").append(Doc::as_string(self.0))
    }
}

impl Op {
    fn to_doc(&self) -> Doc<BoxDoc<()>> {
        match self {
            Op::AddByte => Doc::text("+&"),
            Op::SubByte => Doc::text("-&"),
            Op::MulByte => Doc::text("*&"),
            Op::DivByte => Doc::text("/&"),
            Op::NegByte => Doc::text("-&"),

            Op::EqByte => Doc::text("=&"),
            Op::LtByte => Doc::text("<&"),
            Op::LteByte => Doc::text("<=&"),

            Op::AddInt => Doc::text("+"),
            Op::SubInt => Doc::text("-"),
            Op::MulInt => Doc::text("*"),
            Op::DivInt => Doc::text("/"),
            Op::NegInt => Doc::text("-"),

            Op::EqInt => Doc::text("="),
            Op::LtInt => Doc::text("<"),
            Op::LteInt => Doc::text("<="),

            Op::AddFloat => Doc::text("+."),
            Op::SubFloat => Doc::text("-."),
            Op::MulFloat => Doc::text("*."),
            Op::DivFloat => Doc::text("/."),
            Op::NegFloat => Doc::text("-."),

            Op::EqFloat => Doc::text("=."),
            Op::LtFloat => Doc::text("<."),
            Op::LteFloat => Doc::text("<=."),
        }
    }
}

impl res::ArrayOp {
    fn to_doc(&self) -> Doc<BoxDoc<()>> {
        match self {
            res::ArrayOp::Item => Doc::text("item"),
            res::ArrayOp::Len => Doc::text("len"),
            res::ArrayOp::Push => Doc::text("push"),
            res::ArrayOp::Pop => Doc::text("pop"),
        }
    }
}

impl res::IOOp {
    fn to_doc(&self) -> Doc<BoxDoc<()>> {
        match self {
            res::IOOp::Input => Doc::text("input"),
            res::IOOp::Output => Doc::text("output"),
        }
    }
}

impl lifted::LamDef {
    fn to_doc<'a>(
        &'a self,
        id: lifted::LamId,
        type_data: &'a IdVec<mono::CustomTypeId, mono::TypeData>,
        val_data: &'a IdVec<mono::CustomGlobalId, mono::ValData>,
        lam_data: &'a lifted::LamData,
    ) -> Doc<'a, BoxDoc<()>> {
        let (arg_doc, arg_local_count) = self.arg.to_doc(type_data, NumBindings(0));
        lam_data
            .to_doc(val_data)
            .append(match self.purity {
                Purity::Pure => Doc::nil(),
                Purity::Impure => Doc::text("proc "),
            })
            .append(Doc::text("λ"))
            .append(Doc::as_string(id.to_index()))
            .append(Doc::text(": {"))
            .append(Doc::intersperse(
                self.captures.iter().map(|(i, x)| {
                    Doc::text("#")
                        .append(Doc::as_string(i.to_index()))
                        .append(Doc::text(": ").append(x.to_doc_toplevel(type_data)))
                }),
                Doc::text(", "),
            ))
            .append(Doc::text("} "))
            .append(self.arg_type.to_doc(type_data, TypePrecedence::FuncLeft))
            .append(Doc::text(" → "))
            .append(self.ret_type.to_doc(type_data, TypePrecedence::TopLevel))
            .append(Doc::newline())
            .append(Doc::text("λ"))
            .append(Doc::as_string(id.to_index()))
            .append(Doc::text(" "))
            .append(arg_doc)
            .append(" =")
            .append(
                Doc::newline()
                    .append(self.body.to_doc(type_data, val_data, arg_local_count))
                    .nest(2),
            )
    }
}

impl mono::TypeDef {
    fn to_doc<'a>(
        &'a self,
        type_index: mono::CustomTypeId,
        type_data: &'a IdVec<mono::CustomTypeId, mono::TypeData>,
    ) -> Doc<'a, BoxDoc<()>> {
        Doc::text(&type_data[type_index].type_name.0)
            .append(Doc::text(" "))
            .append(Doc::intersperse(
                type_data[type_index]
                    .mono_with
                    .iter()
                    .map(|x| x.to_doc_toplevel(type_data)),
                Doc::text(" "),
            ))
            .append(Doc::text(" {"))
            .append(Doc::newline())
            .append(Doc::intersperse(
                self.variants.iter().map(|(variant_id, variant)| {
                    Doc::text("  ").append(
                        Doc::text(
                            &type_data[type_index].variant_data[variant_id]
                                .variant_name
                                .0,
                        )
                        .append(match variant {
                            None => Doc::nil(),
                            Some(type_) => match type_ {
                                mono::Type::Tuple(_) => type_.to_doc_toplevel(type_data),
                                _ => Doc::text("(")
                                    .append(type_.to_doc_toplevel(type_data))
                                    .append(Doc::text(")")),
                            },
                        })
                        .append(Doc::text(",")),
                    )
                }),
                Doc::newline(),
            ))
            .append(Doc::newline())
            .append(Doc::text("}"))
    }
}

impl lifted::ValDef {
    fn to_doc<'a>(
        &'a self,
        index: mono::CustomGlobalId,
        type_data: &'a IdVec<mono::CustomTypeId, mono::TypeData>,
        val_data: &'a IdVec<mono::CustomGlobalId, mono::ValData>,
        lam_data: &'a IdVec<lifted::LamId, lifted::LamDef>,
    ) -> Doc<'a, BoxDoc<()>> {
        Doc::text(&val_data[index].val_name.0)
            .append(Doc::text(" : "))
            .append(self.type_.to_doc_toplevel(type_data))
            .append(Doc::newline())
            .append(match self.body {
                lifted::Expr::Lam(lam_id, _) => {
                    let (arg_doc, arg_bindings) =
                        lam_data[lam_id].arg.to_doc(type_data, NumBindings(0));
                    Doc::text(&val_data[index].val_name.0)
                        .append(Doc::text(" "))
                        .append(arg_doc)
                        .append(Doc::text(" ="))
                        .append(
                            Doc::newline()
                                .append(lam_data[lam_id].body.to_doc(
                                    type_data,
                                    val_data,
                                    arg_bindings,
                                ))
                                .nest(2),
                        )
                }
                _ => Doc::text(&val_data[index].val_name.0)
                    .append(Doc::text(" ="))
                    .append(
                        Doc::newline()
                            .append(self.body.to_doc(type_data, val_data, NumBindings(0)))
                            .nest(2),
                    ),
            })
    }
}

#[derive(Clone, Debug, Copy)]
struct NumBindings(usize);

impl lifted::Expr {
    fn to_doc<'a>(
        &'a self,
        type_data: &'a IdVec<mono::CustomTypeId, mono::TypeData>,
        val_data: &'a IdVec<mono::CustomGlobalId, mono::ValData>,
        local_count: NumBindings,
    ) -> Doc<'a, BoxDoc<()>> {
        match self {
            lifted::Expr::ArithOp(op) => op.to_doc(),
            lifted::Expr::ArrayOp(arrayop, _) => arrayop.to_doc(),
            lifted::Expr::IOOp(ioop) => ioop.to_doc(),
            lifted::Expr::Ctor(type_id, variant_id) => {
                type_data[*type_id].variant_data[variant_id].to_doc()
            }
            lifted::Expr::Global(global_id) => val_data[*global_id].to_doc(type_data),
            lifted::Expr::Local(localid) => localid.to_doc(),
            lifted::Expr::Capture(captureid) => captureid.to_doc(),
            lifted::Expr::Tuple(tuple) => Doc::text("(").append(
                Doc::intersperse(
                    tuple
                        .into_iter()
                        .map(|x| x.to_doc(type_data, val_data, local_count)),
                    Doc::text(", "),
                )
                .append(Doc::text(")")),
            ),
            lifted::Expr::Lam(lifted::LamId(lamid), exprs) => Doc::text("λ")
                .append(Doc::as_string(lamid))
                .append(Doc::text(" {"))
                .append(Doc::intersperse(
                    exprs
                        .into_iter()
                        .map(|(_, x)| x.to_doc(type_data, val_data, local_count)),
                    Doc::text(", "),
                ))
                .append(Doc::text("}")),

            lifted::Expr::App(purity, func, val) => match purity {
                Purity::Pure => Doc::nil(),
                Purity::Impure => Doc::text("do "),
            }
            .append({
                if let lifted::Expr::Tuple(_) = **val {
                    return func
                        .to_doc(type_data, val_data, local_count)
                        .append(val.to_doc(type_data, val_data, local_count));
                }
                func.to_doc(type_data, val_data, local_count)
                    .append(Doc::text("("))
                    .append(val.to_doc(type_data, val_data, local_count))
                    .append(Doc::text(")"))
            }),
            lifted::Expr::Match(expr, patterns, _) => {
                let mut pat_docs = Vec::new();
                for (pat, pat_expr) in patterns {
                    let (pat_doc, pat_bindings) = pat.to_doc(type_data, local_count);
                    pat_docs.push(pat_doc.append(Doc::text(" ⇨ ")).append(pat_expr.to_doc(
                        type_data,
                        val_data,
                        NumBindings(local_count.0 + pat_bindings.0),
                    )));
                }

                Doc::text("match ")
                    .append(expr.to_doc(type_data, val_data, local_count))
                    .append(Doc::text(" {"))
                    .append(
                        Doc::newline()
                            .append(Doc::intersperse(pat_docs, Doc::newline()))
                            .nest(2),
                    )
                    .append(Doc::newline())
                    .append(Doc::text("}"))
            }
            lifted::Expr::Let(pat, value, expr) => {
                let (pat_doc, pat_bindings) = pat.to_doc(type_data, local_count);

                Doc::text("let (")
                    .append(pat_doc)
                    .append(Doc::text(") = "))
                    .append(value.to_doc(type_data, val_data, local_count))
                    .append(Doc::text(" in"))
                    .append(
                        Doc::newline()
                            .append(expr.to_doc(
                                type_data,
                                val_data,
                                NumBindings(local_count.0 + pat_bindings.0),
                            ))
                            .nest(2),
                    )
            }
            lifted::Expr::ArrayLit(_, elems) => Doc::text("[")
                .append(Doc::intersperse(
                    elems
                        .into_iter()
                        .map(|elem| elem.to_doc(type_data, val_data, local_count)),
                    Doc::text(", "),
                ))
                .append(Doc::text("]")),
            lifted::Expr::BoolLit(b) => {
                if *b {
                    Doc::text("True")
                } else {
                    Doc::text("False")
                }
            }
            lifted::Expr::ByteLit(b) => Doc::as_string(b),
            lifted::Expr::IntLit(n) => Doc::as_string(n),
            lifted::Expr::FloatLit(f) => Doc::as_string(f),
        }
    }
}

impl mono::Pattern {
    fn to_doc<'a>(
        &'a self,
        type_data: &'a IdVec<mono::CustomTypeId, mono::TypeData>,
        local_count: NumBindings,
    ) -> (Doc<'a, BoxDoc<()>>, NumBindings) {
        match self {
            mono::Pattern::Any(_) => (Doc::text("_"), NumBindings(0)),
            mono::Pattern::Var(type_) => (
                Doc::text("%")
                    .append(Doc::as_string(local_count.0))
                    .append(Doc::text(": "))
                    .append(type_.to_doc_toplevel(type_data)),
                NumBindings(1),
            ),
            mono::Pattern::Tuple(patterns) => {
                if patterns.is_empty() {
                    (Doc::text("()"), NumBindings(0))
                } else {
                    let mut doc_list = Vec::new();
                    let mut tuple_local_count = NumBindings(0);
                    for pat in patterns {
                        let (pat_doc, pat_bindings) =
                            pat.to_doc(type_data, NumBindings(local_count.0 + tuple_local_count.0));
                        tuple_local_count.0 += pat_bindings.0;
                        doc_list.push(pat_doc);
                    }
                    (
                        Doc::text("(").append(
                            Doc::intersperse(doc_list, Doc::text(", ")).append(Doc::text(")")),
                        ),
                        tuple_local_count,
                    )
                }
            }
            mono::Pattern::Ctor(type_id, variant_id, pat) => {
                let ctor_doc = type_data[*type_id].variant_data[variant_id].to_doc();
                match pat {
                    None => (ctor_doc, NumBindings(0)),
                    Some(p) => {
                        let (p_doc, p_bindings) = p.to_doc(type_data, local_count);
                        (
                            match &**p {
                                mono::Pattern::Tuple(_) => p_doc,
                                _ => ctor_doc
                                    .append(Doc::text("("))
                                    .append(p_doc)
                                    .append(Doc::text(")")),
                            },
                            NumBindings(p_bindings.0),
                        )
                    }
                }
            }
            mono::Pattern::BoolConst(b) => {
                if *b {
                    (Doc::text("True"), NumBindings(0))
                } else {
                    (Doc::text("False"), NumBindings(0))
                }
            }
            mono::Pattern::ByteConst(s) => (Doc::as_string(s), NumBindings(0)),
            mono::Pattern::IntConst(n) => (Doc::as_string(n), NumBindings(0)),
            mono::Pattern::FloatConst(f) => (Doc::as_string(f), NumBindings(0)),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Copy)]
enum TypePrecedence {
    TopLevel, // Nothing parenthesized
    FuncLeft, // Only functions parenthesized
    TypeApp,  // Type apps and functions parenthesized
}

impl mono::Type {
    fn to_doc_toplevel<'a>(
        &'a self,
        type_data: &'a IdVec<mono::CustomTypeId, mono::TypeData>,
    ) -> Doc<'a, BoxDoc<()>> {
        self.to_doc(type_data, TypePrecedence::TopLevel)
    }
    fn to_doc<'a>(
        &'a self,
        type_data: &'a IdVec<mono::CustomTypeId, mono::TypeData>,
        precedence: TypePrecedence,
    ) -> Doc<'a, BoxDoc<()>> {
        let doc = match self {
            mono::Type::Bool => Doc::text("Bool"),
            mono::Type::Byte => Doc::text("Byte"),
            mono::Type::Int => Doc::text("Int"),
            mono::Type::Float => Doc::text("Float"),
            mono::Type::Array(type_) => {
                Doc::text("Array").append(type_.to_doc(type_data, TypePrecedence::TypeApp))
            }
            mono::Type::Tuple(types) => Doc::text("(").append(
                Doc::intersperse(
                    types
                        .into_iter()
                        .map(|x| x.to_doc(type_data, TypePrecedence::TopLevel)),
                    Doc::text(", "),
                )
                .append(Doc::text(")")),
            ),
            mono::Type::Func(purity, domain, codomain) => match purity {
                Purity::Pure => Doc::nil(),
                Purity::Impure => Doc::text("proc "),
            }
            .append(domain.to_doc(type_data, TypePrecedence::FuncLeft))
            .append(" → ")
            .append(codomain.to_doc(type_data, TypePrecedence::TopLevel)),
            mono::Type::Custom(type_id) => Doc::text(&type_data[*type_id].type_name.0)
                .append(Doc::text(" "))
                .append(Doc::intersperse(
                    type_data[*type_id]
                        .mono_with
                        .iter()
                        .map(|x| x.to_doc(type_data, TypePrecedence::TypeApp)),
                    Doc::text(" "),
                )),
        };

        let should_parenthesize = match self {
            mono::Type::Bool => false,
            mono::Type::Byte => false,
            mono::Type::Int => false,
            mono::Type::Float => false,
            mono::Type::Array(_) => precedence >= TypePrecedence::TypeApp,
            mono::Type::Tuple(_) => false,
            mono::Type::Func(_, _, _) => precedence >= TypePrecedence::FuncLeft,
            mono::Type::Custom(mono::CustomTypeId(_)) => precedence >= TypePrecedence::TypeApp,
        };
        if should_parenthesize {
            Doc::text("(")
        } else {
            Doc::nil()
        }
        .append(doc)
        .append(if should_parenthesize {
            Doc::text(")")
        } else {
            Doc::nil()
        })
    }
}
