use crate::data::first_order_ast::CustomTypeId;
use crate::data::guarded_ast::{CustomTypeDef, Program};
use crate::pretty_print::flat::{write_func, write_type};
use crate::pretty_print::utils::{CustomTypeRenderer, FuncRenderer};
use std::io::{self, Write};

pub fn write_typedef(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    typedef: &CustomTypeDef,
    type_id: CustomTypeId,
) -> io::Result<()> {
    write!(w, "custom type {} = ", type_renderer.render(type_id))?;
    write_type(w, type_renderer, &typedef.content)?;
    writeln!(w)?;
    Ok(())
}

pub fn write_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);

    for (i, typedef) in &program.custom_types.types {
        write_typedef(w, &type_renderer, typedef, i)?;
        writeln!(w)?;
    }
    for (i, func) in &program.funcs {
        write_func(w, &type_renderer, &func_renderer, func, i)?;
        writeln!(w)?;
    }
    Ok(())
}
