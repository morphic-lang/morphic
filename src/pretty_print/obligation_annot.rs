use crate::data::first_order_ast::CustomTypeId;
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast2::{
    self as annot, HeapModes, Lt, Mode, Position, ResModes, Shape, ShapeInner, SlotId,
};
use crate::data::num_type::NumType;
use crate::data::obligation_annot_ast::{
    ArrayOp, CustomFuncId, CustomTypeDef, Expr, FuncDef, IoOp, Occur, Program, StackLt, Type,
};
use crate::intrinsic_config::intrinsic_to_name;
use crate::pretty_print::borrow_common::*;
use crate::pretty_print::mode_annot::{write_custom, write_resource_modes};
use crate::pretty_print::utils::{
    write_delimited, write_metadata, CustomTypeRenderer, FuncRenderer,
};
use std::collections::BTreeMap;
use std::io::{self, Write};

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

fn write_type_impl(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<CustomTypeId>>,
    ob: Option<&BTreeMap<SlotId, Lt>>,
    shape: &Shape,
    res: &[ResModes<Mode>],
    slot: usize,
) -> io::Result<()> {
    let write_opt_ob = |w: &mut dyn Write, slot| -> io::Result<()> {
        if let Some(lt) = ob.and_then(|ob| ob.get(&SlotId(slot))) {
            write!(w, "<")?;
            write_lifetime(w, lt)?;
            write!(w, ">")?;
        }
        Ok(())
    };
    match &*shape.inner {
        ShapeInner::Bool => write!(w, "Bool"),
        ShapeInner::Num(NumType::Byte) => write!(w, "Byte"),
        ShapeInner::Num(NumType::Int) => write!(w, "Int"),
        ShapeInner::Num(NumType::Float) => write!(w, "Float"),
        ShapeInner::Tuple(shapes) => {
            let items = annot::enumerate_shapes(shapes, res);
            write_delimited(w, items, "(", ")", ", ", |w, (shape, (start, _), res)| {
                write_type_impl(w, type_renderer, ob, shape, res, slot + start)
            })
        }
        ShapeInner::Variants(shapes) => {
            let items = annot::enumerate_shapes(shapes.as_slice(), res);
            write_delimited(w, items, "{", "}", ", ", |w, (shape, (start, _), res)| {
                write_type_impl(w, type_renderer, ob, shape, res, slot + start)
            })
        }
        ShapeInner::Custom(type_id) => {
            write_custom(w, type_renderer, *type_id)?;
            write_delimited(w, res.iter().enumerate(), "<", ">", ", ", |w, (i, res)| {
                write_resource_modes(w, &write_mode, res)?;
                write_opt_ob(w, slot + i)
            })
        }
        ShapeInner::SelfCustom(type_id) => write!(w, "Self#{}", type_id.0),
        ShapeInner::Array(shape) => {
            write_resource_modes(w, &write_mode, &res[0])?;
            write_opt_ob(w, slot)?;
            write!(w, " Array (")?;
            write_type_impl(w, type_renderer, ob, shape, &res[1..], slot + 1)?;
            write!(w, ")")
        }
        ShapeInner::HoleArray(shape) => {
            write_resource_modes(w, &write_mode, &res[0])?;
            write_opt_ob(w, slot)?;
            write!(w, " HoleArray (")?;
            write_type_impl(w, type_renderer, ob, shape, &res[1..], slot + 1)?;
            write!(w, ")")
        }
        ShapeInner::Boxed(shape) => {
            write_resource_modes(w, &write_mode, &res[0])?;
            write_opt_ob(w, slot)?;
            write!(w, " Boxed (")?;
            write_type_impl(w, type_renderer, ob, shape, &res[1..], slot + 1)?;
            write!(w, ")")
        }
    }
}

pub fn write_type(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<CustomTypeId>>,
    ob: Option<&StackLt>,
    type_: &Type,
) -> io::Result<()> {
    assert!(ob.map_or(true, |ob| ob.shape == type_.shape));
    write_type_impl(
        w,
        type_renderer,
        ob.map(|ob| &ob.data),
        &type_.shape,
        type_.res.as_slice(),
        0,
    )
}

fn write_shape_impl(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<CustomTypeId>>,
    pos: Position,
    shape: &Shape,
) -> io::Result<()> {
    let write_res = |w: &mut dyn Write| {
        let dummy = match pos {
            Position::Stack => ResModes::Stack(()),
            Position::Heap => ResModes::Heap(HeapModes {
                access: (),
                storage: (),
            }),
        };
        write_resource_modes(w, &|w, _| write!(w, "_"), &dummy)
    };
    match &*shape.inner {
        ShapeInner::Bool => write!(w, "Bool"),
        ShapeInner::Num(NumType::Byte) => write!(w, "Byte"),
        ShapeInner::Num(NumType::Int) => write!(w, "Int"),
        ShapeInner::Num(NumType::Float) => write!(w, "Float"),
        ShapeInner::Tuple(shapes) => write_delimited(w, shapes, "(", ")", ", ", |w, shape| {
            write_shape_impl(w, type_renderer, pos, shape)
        }),
        ShapeInner::Variants(shapes) => {
            write_delimited(w, shapes.values(), "{", "}", ", ", |w, shape| {
                write_shape_impl(w, type_renderer, pos, shape)
            })
        }
        ShapeInner::Custom(type_id) => {
            write_custom(w, type_renderer, *type_id)?;
            write!(w, "<...>")
        }
        ShapeInner::SelfCustom(type_id) => write!(w, "Self#{}", type_id.0),
        ShapeInner::Array(shape) => {
            write_res(w)?;
            write!(w, " Array (")?;
            write_shape_impl(w, type_renderer, Position::Heap, shape)?;
            write!(w, ")")
        }
        ShapeInner::HoleArray(shape) => {
            write_res(w)?;
            write!(w, " HoleArray (")?;
            write_shape_impl(w, type_renderer, Position::Heap, shape)?;
            write!(w, ")")
        }
        ShapeInner::Boxed(shape) => {
            write_res(w)?;
            write!(w, " Boxed (")?;
            write_shape_impl(w, type_renderer, Position::Heap, shape)?;
            write!(w, ")")
        }
    }
}

pub fn write_shape(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<CustomTypeId>>,
    shape: &Shape,
) -> io::Result<()> {
    write_shape_impl(w, type_renderer, Position::Stack, shape)
}

fn write_occur(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    occur: &Occur,
) -> io::Result<()> {
    write!(w, "%{} as ", occur.id.0)?;
    write_type(w, Some(type_renderer), None, &occur.ty)
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

fn match_string_bytes(bindings: &[(Type, StackLt, Expr, Metadata)]) -> Option<String> {
    let mut result_bytes = Vec::new();
    for binding in bindings {
        if let (_, _, Expr::ByteLit(byte), _) = binding {
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
        Expr::LetMany(bindings, final_local) => {
            write!(w, "let")?;
            let new_context = context.add_indent();
            let mut index = 0;
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
                } else {
                    let (binding_type, obligation, binding_expr, metadata) = &bindings[index];
                    write_metadata(w, new_context.indentation, metadata)?;
                    new_context.writeln(w)?;
                    write!(w, "{}: %{}: ", index, context.num_locals + index)?;
                    write_type(
                        w,
                        Some(context.type_renderer),
                        Some(obligation),
                        binding_type,
                    )?;
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
            ArrayOp::Get(occur1, occur2, output_type) => {
                write_double(w, context.type_renderer, "get", occur1, occur2)?;
                write!(w, " as ")?;
                write_type(w, Some(context.type_renderer), None, output_type)
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
    write_type(w, Some(type_renderer), None, &func.arg_ty)?;
    write!(w, "): ")?;
    write_type(w, Some(type_renderer), None, &func.ret_ty)?;
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

pub fn write_typedef(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<CustomTypeId>>,
    typedef: &CustomTypeDef,
    type_id: CustomTypeId,
) -> io::Result<()> {
    write!(w, "custom type ")?;
    write_custom(w, type_renderer, type_id)?;
    write!(w, " = ")?;
    write_shape(w, type_renderer, &typedef.content)?;
    Ok(())
}

pub fn write_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);

    for (i, typedef) in &program.custom_types.types {
        write_typedef(w, Some(&type_renderer), typedef, i)?;
        writeln!(w)?;
    }
    writeln!(w)?;
    for (i, func) in &program.funcs {
        write_func(w, &type_renderer, &func_renderer, func, i)?;
        writeln!(w)?;
    }
    Ok(())
}
