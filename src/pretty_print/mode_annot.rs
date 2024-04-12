use id_collections::IdVec;

use crate::data::first_order_ast::{CustomFuncId, CustomTypeId, NumType};
use crate::data::mode_annot_ast2::{
    self as annot, ArrayOp, FuncDef, IoOp, LocalLt, Lt, LtParam, Mode, ModeLowerBound, ModeParam,
    Overlay, Program, Type, TypeDef,
};
use crate::intrinsic_config::intrinsic_to_name;
use crate::pretty_print::utils::{CustomTypeRenderer, FuncRenderer};
use std::io;
use std::io::Write;

const TAB_SIZE: usize = 2;

type Occur = annot::Occur<ModeLowerBound, Lt>;
type Expr = annot::Expr<ModeLowerBound, Lt>;
type Condition = annot::Condition<ModeLowerBound, Lt>;

#[derive(Clone, Debug, Copy)]
struct Context<'a> {
    type_renderer: &'a CustomTypeRenderer<CustomTypeId>,
    func_renderer: &'a FuncRenderer<CustomFuncId>,
    indentation: usize,
    num_locals: usize,
}

impl<'a> Context<'a> {
    fn add_indent(&self) -> Self {
        Self {
            indentation: self.indentation + TAB_SIZE,
            ..*self
        }
    }

    fn remove_indent(&self) -> Self {
        Self {
            indentation: self.indentation.saturating_sub(TAB_SIZE),
            ..*self
        }
    }

    fn writeln(&self, w: &mut dyn Write) -> io::Result<()> {
        writeln!(w)?;
        write!(w, "{}", " ".repeat(self.indentation))
    }
}

// #[derive(Clone, Debug)]
// struct LtMarkers(BTreeSet<LtParam>);
//
// #[derive(Clone, Debug)]
// enum ArrayOp<M, L> {
//     Get(LtMarkers, LtMarkers),
//     Extract(LtMarkers, LtMarkers),
//     Len(LtMarkers),
//     Push(LtMarkers, LtMarkers),
//     Pop(LtMarkers),
//     Replace(LtMarkers, LtMarkers),
//     Reserve(LtMarkers, LtMarkers),
// }
//
// #[derive(Clone, Debug)]
// enum IoOp<M, L> {
//     Input,
//     Output(LtMarkers),
// }
//
// #[derive(Clone, Debug)]
// enum Expr<M, L> {
//     Local(LtMarkers),
//     Call(Purity, first_ord::CustomFuncId, LtMarkers),
//     Branch(LtMarkers, Vec<(Condition<M, L>, Expr<M, L>)>, Type<M, L>),
//     LetMany(Vec<(Type<M, L>, Expr<M, L>)>, LtMarkers),
//
//     Tuple(Vec<LtMarkers>),
//     TupleField(LtMarkers, usize),
//     WrapVariant(first_ord::VariantId, LtMarkers),
//     UnwrapVariant(first_ord::VariantId, LtMarkers),
//     WrapBoxed(
//         LtMarkers,
//         Type<M, L>, // Inner type
//     ),
//     UnwrapBoxed(
//         LtMarkers,
//         Type<M, L>, // Inner type
//     ),
//     WrapCustom(CustomTypeId, LtMarkers),
//     UnwrapCustom(CustomTypeId, LtMarkers),
//
//     Intrinsic(Intrinsic, LtMarkers),
//     ArrayOp(ArrayOp<M, L>),
//     IoOp(IoOp<M, L>),
//     Panic(Type<M, L>, LtMarkers),
//
//     ArrayLit(Type<M, L>, Vec<LtMarkers>),
//     BoolLit(bool),
//     ByteLit(u8),
//     IntLit(i64),
//     FloatLit(f64),
// }

fn write_tuple_like<T>(
    w: &mut dyn Write,
    ldelim: &str,
    rdelim: &str,
    elems: &[T],
    write_elem: impl Fn(&mut dyn Write, &T) -> io::Result<()>,
) -> io::Result<()> {
    if elems.len() == 0 {
        write!(w, "{ldelim}{rdelim}")
    } else if elems.len() == 1 {
        write!(w, "{ldelim}")?;
        write_elem(w, &elems[0])?;
        write!(w, ",{rdelim}")
    } else {
        write!(w, "{ldelim}")?;
        for elem in &elems[..elems.len() - 1] {
            write_elem(w, elem)?;
            write!(w, ", ")?;
        }
        write_elem(w, &elems[elems.len() - 1])?;
        write!(w, "{rdelim}")
    }
}

fn write_condition(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    condition: &Condition,
) -> io::Result<()> {
    match condition {
        Condition::Any => write!(w, "_",),
        Condition::Tuple(conditions) => write_tuple_like(w, "(", ")", conditions, |w, cond| {
            write_condition(w, type_renderer, cond)
        }),
        Condition::Variant(variant_id, subcondition) => {
            write!(w, "variant {} (", variant_id.0)?;
            write_condition(w, type_renderer, subcondition)?;
            write!(w, ")")?;
            Ok(())
        }
        Condition::Boxed(subcondition, _content_type) => {
            write!(w, "boxed (")?;
            write_condition(w, type_renderer, subcondition)?;
            write!(w, ")")?;
            Ok(())
        }
        Condition::Custom(type_id, subcondition) => {
            write!(w, "custom {} (", type_renderer.render(type_id))?;
            write_condition(w, type_renderer, subcondition)?;
            write!(w, ")")?;
            Ok(())
        }
        Condition::BoolConst(val) => write!(w, "{}", if *val { "True" } else { "False" }),
        Condition::ByteConst(val) => write!(w, "{:?}", *val as char),
        Condition::IntConst(val) => write!(w, "{}", val),
        Condition::FloatConst(val) => write!(w, "{}", val),
    }
}

fn write_lifetime_param(w: &mut dyn Write, lt: &LtParam) -> io::Result<()> {
    write!(w, "'{}", lt.0)
}

fn write_local_lifetime(w: &mut dyn Write, lt: &LocalLt) -> io::Result<()> {
    match lt {
        LocalLt::Final => write!(w, "★"),
        LocalLt::Seq(child, i) => {
            write!(w, "↓{i} ")?;
            write_local_lifetime(w, child)?;
            Ok(())
        }
        LocalLt::Par(branches) => {
            write!(w, "(")?;
            assert!(!branches.is_empty());
            for (i, branch) in branches.iter().enumerate() {
                if let Some(branch) = branch {
                    write_local_lifetime(w, branch)?;
                } else {
                    write!(w, "-")?;
                }
                if i < branches.len() - 1 {
                    write!(w, " ‖ ")?;
                }
            }
            write!(w, ")")?;
            Ok(())
        }
    }
}

fn write_lifetime(w: &mut dyn Write, lt: &Lt) -> io::Result<()> {
    match lt {
        Lt::Empty => write!(w, "∅"),
        Lt::Local(lt) => write_local_lifetime(w, lt),
        Lt::Join(params) => {
            assert!(!params.is_empty());
            for (i, param) in params.iter().enumerate() {
                write_lifetime_param(w, param)?;
                if i < params.len() - 1 {
                    write!(w, " ⨆ ")?;
                }
            }
            Ok(())
        }
    }
}

fn write_mode_param(w: &mut dyn Write, m: &ModeParam) -> io::Result<()> {
    write!(w, "${}", m.0)
}

fn write_mode(w: &mut dyn Write, m: &ModeLowerBound) -> io::Result<()> {
    if m.const_ == Mode::Owned {
        write!(w, "●")?;
    } else if !m.vars.is_empty() {
        for (i, param) in m.vars.iter().enumerate() {
            write_mode_param(w, param)?;
            if i < m.vars.len() - 1 {
                write!(w, " ⨆ ")?;
            }
        }
    } else {
        write!(w, "&")?;
    }
    Ok(())
}

fn write_mode_and_lifetime<M, L>(
    w: &mut dyn Write,
    write_mode: &impl Fn(&mut dyn Write, &M) -> io::Result<()>,
    write_lifetime: &impl Fn(&mut dyn Write, &L) -> io::Result<()>,
    m: &M,
    lt: &L,
) -> io::Result<()> {
    write_mode(w, m)?;
    write!(w, "<")?;
    write_lifetime(w, lt)?;
    write!(w, ">")?;
    Ok(())
}

fn write_overlay<M>(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    write_mode: &impl Fn(&mut dyn Write, &M) -> io::Result<()>,
    overlay: &Overlay<M>,
) -> io::Result<()> {
    match overlay {
        Overlay::Bool => write!(w, "Bool"),
        Overlay::Num(NumType::Byte) => write!(w, "Byte"),
        Overlay::Num(NumType::Int) => write!(w, "Int"),
        Overlay::Num(NumType::Float) => write!(w, "Float"),
        Overlay::Tuple(overlays) => write_tuple_like(w, "(", ")", overlays, |w, overlay| {
            write_overlay(w, type_renderer, write_mode, overlay)
        }),
        Overlay::Variants(overlays) => {
            write_tuple_like(w, "{{", "}}", overlays.as_slice(), |w, overlay| {
                write_overlay(w, type_renderer, write_mode, overlay)
            })
        }
        Overlay::SelfCustom(type_id) => write!(w, "{}<self>", type_renderer.render(*type_id)),
        Overlay::Custom(type_id, subst) => {
            write!(w, "{}", type_renderer.render(type_id))?;
            let mut remaining = subst.0.len();
            if remaining > 0 {
                write!(w, "<")?;
                for (param, m) in subst.0.iter() {
                    write_mode_param(w, param)?;
                    write!(w, " = ")?;
                    write_mode(w, m)?;
                    remaining -= 1;
                    if remaining >= 1 {
                        write!(w, ", ")?;
                    }
                }
                write!(w, ">")?;
            }
            Ok(())
        }
        Overlay::Array(m) => {
            write_mode(w, m)?;
            write!(w, " Array")
        }
        Overlay::HoleArray(m) => {
            write_mode(w, m)?;
            write!(w, " HoleArray")
        }
        Overlay::Boxed(m) => {
            write_mode(w, m)?;
            write!(w, " Box")
        }
    }
}

fn write_type<M, L>(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    write_mode: &impl Fn(&mut dyn Write, &M) -> io::Result<()>,
    write_lifetime: &impl Fn(&mut dyn Write, &L) -> io::Result<()>,
    type_: &Type<M, L>,
) -> io::Result<()> {
    match type_ {
        Type::Bool => write!(w, "Bool"),
        Type::Num(NumType::Byte) => write!(w, "Byte"),
        Type::Num(NumType::Int) => write!(w, "Int"),
        Type::Num(NumType::Float) => write!(w, "Float"),
        Type::Tuple(types) => write_tuple_like(w, "(", ")", types, |w, type_| {
            write_type(w, type_renderer, write_mode, write_lifetime, type_)
        }),
        Type::Variants(types) => write_tuple_like(w, "{{", "}}", types.as_slice(), |w, type_| {
            write_type(w, type_renderer, write_mode, write_lifetime, type_)
        }),
        Type::SelfCustom(type_id) => write!(w, "{}<self>", type_renderer.render(*type_id)),
        Type::Custom(type_id, subst) => {
            write!(w, "{}", type_renderer.render(type_id))?;
            let mut remaining = subst.ms.len() + subst.lts.len();
            if remaining > 0 {
                write!(w, "<")?;
                for (_, lt) in subst.lts.iter() {
                    write_lifetime(w, lt)?;
                    remaining -= 1;
                    if remaining >= 1 {
                        write!(w, ", ")?;
                    }
                }
                // TODO: print `os`
                for (p, m) in subst.ms.iter() {
                    write_mode(w, m)?;
                    if let Some(om) = subst.os.0.get(&p) {
                        write!(w, "{{")?;
                        write_mode(w, om)?;
                        write!(w, "}}")?;
                    }
                    remaining -= 1;
                    if remaining >= 1 {
                        write!(w, ", ")?;
                    }
                }
                write!(w, ">")?;
            }
            Ok(())
        }
        Type::Array(m, lt, item_type, overlay) => {
            write_mode_and_lifetime(w, write_mode, write_lifetime, m, lt)?;
            write!(w, " Array (")?;
            write_type(w, type_renderer, write_mode, write_lifetime, item_type)?;
            write!(w, ") as (")?;
            write_overlay(w, type_renderer, write_mode, overlay)?;
            write!(w, ")")
        }
        Type::HoleArray(m, lt, item_type, overlay) => {
            write_mode_and_lifetime(w, write_mode, write_lifetime, m, lt)?;
            write!(w, " HoleArray (")?;
            write_type(w, type_renderer, write_mode, write_lifetime, item_type)?;
            write!(w, ") as (")?;
            write_overlay(w, type_renderer, write_mode, overlay)?;
            write!(w, ")")
        }
        Type::Boxed(m, lt, item_type, overlay) => {
            write_mode_and_lifetime(w, write_mode, write_lifetime, m, lt)?;
            write!(w, " Box (")?;
            write_type(w, type_renderer, write_mode, write_lifetime, item_type)?;
            write!(w, ") as (")?;
            write_overlay(w, type_renderer, write_mode, overlay)?;
            write!(w, ")")
        }
    }
}

fn write_type_concrete(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    type_: &Type<ModeLowerBound, Lt>,
) -> io::Result<()> {
    write_type(w, type_renderer, &write_mode, &write_lifetime, type_)
}

fn write_occur(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    occur: &Occur,
) -> io::Result<()> {
    write!(w, "%{} as ", occur.local.0)?;
    write_type_concrete(w, type_renderer, &occur.ty)
}

fn write_single(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    name: &str,
    occur: &Occur,
) -> io::Result<()> {
    write!(w, "{name}(")?;
    write_occur(w, type_renderer, occur)?;
    write!(w, ")")
}

fn write_double(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    name: &str,
    occur1: &Occur,
    occur2: &Occur,
) -> io::Result<()> {
    write!(w, "{name}(")?;
    write_occur(w, type_renderer, occur1)?;
    write!(w, ", ")?;
    write_occur(w, type_renderer, occur2)?;
    write!(w, ")")
}

fn match_string_bytes(bindings: &[(Type<ModeLowerBound, Lt>, Expr)]) -> Option<String> {
    let mut result_bytes = Vec::new();
    for binding in bindings {
        if let (_, Expr::ByteLit(byte)) = binding {
            result_bytes.push(*byte);
        } else {
            break;
        }
    }
    if result_bytes.len() < 2 {
        return None;
    }
    String::from_utf8(result_bytes).ok()
}

fn write_expr(w: &mut dyn Write, expr: &Expr, context: Context) -> io::Result<()> {
    match expr {
        Expr::Local(occur) => write_occur(w, context.type_renderer, occur),
        Expr::Call(_purity, func_id, occur) => {
            write!(w, "call {} (", context.func_renderer.render(func_id))?;
            write_occur(w, context.type_renderer, occur)?;
            write!(w, ")")
        }
        Expr::Branch(occur, conditions, _return_type) => {
            write!(w, "branch ")?;
            write_occur(w, context.type_renderer, occur)?;
            write!(w, " {{")?;
            let new_context = context.add_indent();
            for (condition, sub_expr) in conditions {
                let newer_context = new_context.add_indent();
                new_context.writeln(w)?;
                write_condition(w, context.type_renderer, condition)?;
                write!(w, " ->")?;
                newer_context.writeln(w)?;
                write_expr(w, sub_expr, newer_context)?;
            }
            context.writeln(w)?;
            write!(w, "}}")?;
            Ok(())
        }
        Expr::LetMany(bindings, final_local) => {
            write!(w, "let")?;
            let new_context = context.add_indent();
            let mut index = 0;
            while index < bindings.len() {
                if let Some(string) = match_string_bytes(&bindings[index..]) {
                    new_context.writeln(w)?;
                    write!(
                        w,
                        "%{}...%{}: Byte = {:?}",
                        context.num_locals + index,
                        context.num_locals + index + string.len() - 1,
                        string,
                    )?;
                    index += string.len();
                } else {
                    let (binding_type, binding_expr) = &bindings[index];
                    new_context.writeln(w)?;
                    write!(w, "%{}: ", context.num_locals + index)?;
                    write_type_concrete(w, context.type_renderer, binding_type)?;
                    write!(w, " = ")?;
                    write_expr(
                        w,
                        binding_expr,
                        Context {
                            num_locals: context.num_locals + index,
                            ..new_context
                        },
                    )?;
                    index += 1;
                }
            }
            context.writeln(w)?;
            write!(w, "in ")?;
            write_occur(w, context.type_renderer, final_local)?;
            Ok(())
        }
        Expr::Tuple(elems) => write_tuple_like(w, "(", ")", elems, |w, occur| {
            write_occur(w, context.type_renderer, occur)
        }),
        Expr::TupleField(occur, index) => {
            write!(w, "tuple field {} ", index)?;
            write_occur(w, context.type_renderer, occur)
        }
        Expr::WrapVariant(_variants, variant_id, occur) => {
            write!(w, "wrap variant {} ", variant_id.0)?;
            write_occur(w, context.type_renderer, occur)
        }
        Expr::UnwrapVariant(variant_id, occur) => {
            write!(w, "unwrap variant {} ", variant_id.0)?;
            write_occur(w, context.type_renderer, occur)
        }
        Expr::WrapBoxed(content, _content_type) => {
            write!(w, "wrap boxed ")?;
            write_occur(w, context.type_renderer, content)
        }
        Expr::UnwrapBoxed(content, _content_type) => {
            write!(w, "unwrap boxed ")?;
            write_occur(w, context.type_renderer, content)
        }
        Expr::WrapCustom(type_id, occur) => {
            write!(w, "wrap custom {} ", context.type_renderer.render(*type_id))?;
            write_occur(w, context.type_renderer, occur)
        }
        Expr::UnwrapCustom(type_id, occur) => {
            write!(
                w,
                "unwrap custom {} ",
                context.type_renderer.render(*type_id)
            )?;
            write_occur(w, context.type_renderer, occur)
        }
        Expr::Intrinsic(intr, local_id) => {
            write!(w, "{} ", intrinsic_to_name(*intr).debug_name())?;
            write_occur(w, context.type_renderer, local_id)
        }
        Expr::ArrayOp(array_op) => match array_op {
            ArrayOp::Get(_item_type, occur1, occur2, output_type) => {
                write_double(w, context.type_renderer, "get", occur1, occur2)?;
                write!(w, " as ")?;
                write_type_concrete(w, context.type_renderer, output_type)
            }
            ArrayOp::Extract(_item_type, occur1, occur2) => {
                write_double(w, context.type_renderer, "extract", occur1, occur2)
            }
            ArrayOp::Len(_item_type, occur) => write_single(w, context.type_renderer, "len", occur),
            ArrayOp::Push(_item_type, occur1, occur2) => {
                write_double(w, context.type_renderer, "push", occur1, occur2)
            }
            ArrayOp::Pop(_item_type, occur) => write_single(w, context.type_renderer, "pop", occur),
            ArrayOp::Replace(_item_type, occur1, occur2) => {
                write_double(w, context.type_renderer, "replace", occur1, occur2)
            }
            ArrayOp::Reserve(_item_type, occur1, occur2) => {
                write_double(w, context.type_renderer, "reserve", occur1, occur2)
            }
        },
        Expr::IoOp(io_op) => match io_op {
            IoOp::Input => write!(w, "input"),
            IoOp::Output(occur) => write_single(w, context.type_renderer, "output", occur),
        },
        Expr::Panic(_ret_type, occur) => write_single(w, context.type_renderer, "panic", occur),
        Expr::ArrayLit(_type, elem_occurs) => {
            let elem_ids = elem_occurs
                .iter()
                .map(|occur| occur.local)
                .collect::<Vec<_>>();

            let elems_are_contiguous = elem_ids.len() > 1
                && (0..elem_ids.len() - 1).all(|i| elem_ids[i].0 + 1 == elem_ids[i + 1].0);

            if elem_ids.len() == 0 {
                write!(w, "[]")?
            } else if elems_are_contiguous {
                write!(
                    w,
                    "[%{}...%{}]",
                    elem_ids.first().unwrap().0,
                    elem_ids.last().unwrap().0
                )?;
            } else {
                write!(w, "[")?;
                for elem_id in &elem_ids[..elem_ids.len() - 1] {
                    write!(w, "%{}, ", elem_id.0)?;
                }
                write!(w, "%{}]", elem_ids[elem_ids.len() - 1].0)?;
            }
            Ok(())
        }
        Expr::BoolLit(val) => write!(w, "{}", if *val { "True" } else { "False" }),
        Expr::ByteLit(val) => write!(w, "{:?}", (*val as char)),
        Expr::IntLit(val) => write!(w, "{}", val),
        Expr::FloatLit(val) => write!(w, "{}", val),
    }
}

fn write_constrs(w: &mut dyn Write, constrs: &IdVec<ModeParam, ModeLowerBound>) -> io::Result<()> {
    assert!(!constrs.is_empty());
    for (p, bound) in constrs {
        for lb in &bound.vars {
            write_mode_param(w, lb)?;
            write!(w, " ≤ ")?;
            write_mode_param(w, &p)?;
            write!(w, ", ")?;
        }
        if bound.const_ == Mode::Owned {
            write!(w, "● ≤ ")?;
            write_mode_param(w, &p)?;
            write!(w, ", ")?;
        }
    }
    Ok(())
}

fn write_func(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    func_renderer: &FuncRenderer<CustomFuncId>,
    func: &FuncDef,
    func_id: CustomFuncId,
) -> io::Result<()> {
    let context = Context {
        type_renderer,
        func_renderer,
        indentation: 0,
        num_locals: 1,
    };

    write!(w, "func {} (%0: ", func_renderer.render(func_id))?;
    write_type(
        w,
        type_renderer,
        &write_mode_param,
        &write_lifetime,
        &func.sig.arg_type,
    )?;
    write!(w, "): ")?;
    write_type(
        w,
        type_renderer,
        &write_mode_param,
        &write_lifetime_param,
        &func.sig.ret_type,
    )?;

    if func.constrs.is_empty() {
        writeln!(w, " =")?;
    } else {
        let context = context.add_indent();
        context.writeln(w)?;
        write!(w, "where")?;

        write_constrs(w, &func.constrs)?;
        context.remove_indent();
        context.writeln(w)?;
        write!(w, "=")?;
    }

    context.add_indent();
    context.writeln(w)?;
    write_expr(w, &func.body, context)?;
    writeln!(w)?;
    writeln!(w)?;
    Ok(())
}

fn write_typedef(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    typedef: &TypeDef,
    type_id: CustomTypeId,
) -> io::Result<()> {
    write!(w, "custom type {} = ", type_renderer.render(type_id))?;
    write_type(
        w,
        type_renderer,
        &write_mode_param,
        &write_lifetime_param,
        &typedef.content,
    )?;
    write!(w, " as ")?;
    write_overlay(w, type_renderer, &write_mode_param, &typedef.overlay)?;
    Ok(())
}

pub fn write_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);

    for (i, typedef) in &program.custom_types.types {
        write_typedef(w, &type_renderer, typedef, i)?;
    }
    writeln!(w)?;
    for (i, func) in &program.funcs {
        write_func(w, &type_renderer, &func_renderer, func, i)?;
    }
    Ok(())
}
