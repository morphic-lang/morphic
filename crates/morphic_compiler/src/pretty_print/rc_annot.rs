use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast::SlotId;
use crate::data::obligation_annot_ast::{BindType, CustomFuncId, CustomTypeId};
use crate::data::rc_annot_ast::{ArrayOp, Expr, FuncDef, IoOp, Occur, Program, RcOp, Selector};
use crate::intrinsic_config::intrinsic_to_name;
use crate::pretty_print::mode_annot::{self as annot_pp};
use crate::pretty_print::obligation_annot::{self as ob_annot_pp};
use crate::pretty_print::utils::{
    write_delimited, write_metadata, CustomTypeRenderer, FuncRenderer,
};
use std::io::{self, Write};
use std::{fmt, str};

const TAB_SIZE: usize = 2;

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

    fn writeln(&self, w: &mut dyn Write) -> io::Result<()> {
        writeln!(w)?;
        write!(w, "{}", " ".repeat(self.indentation))
    }
}

fn write_occur(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    occur: &Occur,
) -> io::Result<()> {
    write!(w, "%{} as ", occur.id.0)?;
    ob_annot_pp::write_type(w, Some(type_renderer), &occur.ty)
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

fn match_string_bytes(bindings: &[(BindType, Expr, Metadata)]) -> Option<String> {
    let mut result_bytes = Vec::new();
    for binding in bindings {
        if let (_, Expr::ByteLit(byte), _) = binding {
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

fn write_selector(
    type_renderer: Option<&CustomTypeRenderer<CustomTypeId>>,
    w: &mut dyn Write,
    selector: &Selector,
) -> io::Result<()> {
    let res = (0..selector.shape.num_slots)
        .map(|slot| {
            if selector.true_.contains(&SlotId(slot)) {
                "*"
            } else {
                "_"
            }
        })
        .collect::<Vec<_>>();
    write!(w, "{} ", selector.true_.len())?;
    annot_pp::write_type_raw(
        w,
        type_renderer,
        &|w, res| write!(w, "{}", res),
        &selector.shape,
        &res,
    )
}

fn write_expr(w: &mut dyn Write, expr: &Expr, context: Context) -> io::Result<()> {
    match expr {
        Expr::Local(occur) => write_occur(w, context.type_renderer, occur),
        Expr::Call(_purity, func_id, occur) => {
            write!(w, "call {} (", context.func_renderer.render(func_id))?;
            write_occur(w, context.type_renderer, occur)?;
            write!(w, ")")
        }
        Expr::LetMany(bindings, final_local) => {
            write!(w, "let")?;
            let new_context = context.add_indent();
            let mut index = 0;
            let mut real_index = 0;
            while index < bindings.len() {
                if let Some(string) = match_string_bytes(&bindings[index..]) {
                    new_context.writeln(w)?;
                    let last_index = index + string.len() - 1;
                    write!(
                        w,
                        "{}...{}: %{}...%{}: Byte = {:?}",
                        index,
                        last_index,
                        context.num_locals + index,
                        context.num_locals + last_index,
                        string,
                    )?;
                    index += string.len();
                    real_index += string.len();
                } else {
                    let (binding_type, binding_expr, metadata) = &bindings[index];
                    write_metadata(w, new_context.indentation, metadata)?;
                    new_context.writeln(w)?;
                    write!(w, "{}: %{}: ", real_index, context.num_locals + index)?;
                    ob_annot_pp::write_bind_type(w, Some(context.type_renderer), binding_type)?;
                    new_context.writeln(w)?;
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
                    match binding_expr {
                        Expr::RcOp(_, _, _) => {}
                        _ => {
                            real_index += 1;
                        }
                    }
                }
            }
            context.writeln(w)?;
            write!(w, "in ")?;
            write_occur(w, context.type_renderer, final_local)?;
            Ok(())
        }
        Expr::If(occur, then_branch, else_branch) => {
            write!(w, "if ")?;
            write_occur(w, context.type_renderer, occur)?;
            write!(w, " {{")?;

            let new_context = context.add_indent();
            new_context.writeln(w)?;
            write_expr(w, then_branch, new_context)?;
            context.writeln(w)?;

            write!(w, "}} else {{")?;
            new_context.writeln(w)?;
            write_expr(w, else_branch, new_context)?;
            context.writeln(w)?;

            write!(w, "}}")?;
            Ok(())
        }
        Expr::CheckVariant(variant_id, occur) => {
            write!(w, "check variant {} ", variant_id.0)?;
            write_occur(w, context.type_renderer, occur)
        }
        Expr::Unreachable(_type) => write!(w, "unreachable"),
        Expr::Tuple(elems) => write_delimited(w, elems, "(", ")", ", ", |w, occur| {
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
        Expr::WrapBoxed(content, _) => {
            write!(w, "wrap boxed ")?;
            write_occur(w, context.type_renderer, content)
        }
        Expr::UnwrapBoxed(content, _) => {
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
        Expr::RcOp(RcOp::Retain, selector, local) => {
            write!(w, "retain ")?;
            write!(w, "%{} (", local.0)?;
            write_selector(Some(context.type_renderer), w, selector)?;
            write!(w, ")")
        }
        Expr::RcOp(RcOp::Release, selector, local) => {
            write!(w, "release ")?;
            write!(w, "%{} (", local.0)?;
            write_selector(Some(context.type_renderer), w, selector)?;
            write!(w, ")")
        }
        Expr::Intrinsic(intr, local_id) => {
            write!(w, "{} ", intrinsic_to_name(*intr).debug_name())?;
            write_occur(w, context.type_renderer, local_id)
        }
        Expr::ArrayOp(array_op) => match array_op {
            ArrayOp::Get(occur1, occur2) => {
                write_double(w, context.type_renderer, "get", occur1, occur2)
            }
            ArrayOp::Extract(occur1, occur2) => {
                write_double(w, context.type_renderer, "extract", occur1, occur2)
            }
            ArrayOp::Len(occur) => write_single(w, context.type_renderer, "len", occur),
            ArrayOp::Push(occur1, occur2) => {
                write_double(w, context.type_renderer, "push", occur1, occur2)
            }
            ArrayOp::Pop(occur) => write_single(w, context.type_renderer, "pop", occur),
            ArrayOp::Replace(occur1, occur2) => {
                write_double(w, context.type_renderer, "replace", occur1, occur2)
            }
            ArrayOp::Reserve(occur1, occur2) => {
                write_double(w, context.type_renderer, "reserve", occur1, occur2)
            }
        },
        Expr::IoOp(io_op) => match io_op {
            IoOp::Input => write!(w, "input"),
            IoOp::Output(occur) => write_single(w, context.type_renderer, "output", occur),
        },
        Expr::Panic(_ret_type, occur) => write_single(w, context.type_renderer, "panic", occur),
        Expr::ArrayLit(_type, elem_occurs) => {
            let elem_ids = elem_occurs.iter().map(|occur| occur.id).collect::<Vec<_>>();

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

pub fn write_func(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    func_renderer: &FuncRenderer<CustomFuncId>,
    func: &FuncDef,
    func_id: CustomFuncId,
) -> io::Result<()> {
    write!(w, "func {} (%0: ", func_renderer.render(func_id))?;
    ob_annot_pp::write_bind_type(w, Some(type_renderer), &func.arg_ty)?;
    write!(w, "): ")?;
    ob_annot_pp::write_ret_type(w, Some(type_renderer), &func.ret_ty)?;
    write!(w, " =\n")?;

    let context = Context {
        type_renderer,
        func_renderer,
        indentation: 0,
        num_locals: 1,
    };

    write_expr(w, &func.body, context)?;
    writeln!(w)?;
    Ok(())
}

pub fn write_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);

    for (i, typedef) in &program.custom_types.types {
        annot_pp::write_typedef(w, Some(&type_renderer), typedef, i)?;
        writeln!(w)?;
    }
    writeln!(w)?;
    for (i, func) in &program.funcs {
        write_func(w, &type_renderer, &func_renderer, func, i)?;
        writeln!(w)?;
    }
    Ok(())
}

pub struct DisplaySelector<'a> {
    type_renderer: Option<&'a CustomTypeRenderer<CustomTypeId>>,
    selector: &'a Selector,
}

impl fmt::Display for DisplaySelector<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut w = Vec::new();
        write_selector(self.type_renderer, &mut w, self.selector).unwrap();
        f.write_str(str::from_utf8(&w).unwrap())
    }
}

impl Selector {
    pub fn display<'a>(&'a self) -> DisplaySelector<'a> {
        DisplaySelector {
            type_renderer: None,
            selector: self,
        }
    }

    pub fn display_with<'a>(
        &'a self,
        type_renderer: &'a CustomTypeRenderer<CustomTypeId>,
    ) -> DisplaySelector<'a> {
        DisplaySelector {
            type_renderer: Some(type_renderer),
            selector: self,
        }
    }
}
