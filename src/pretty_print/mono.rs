use crate::data::mono_ast::*;
use crate::data::profile::ProfilePointId;
use crate::data::resolved_ast::{ArrayOp, IoOp, VariantId};
// use crate::data::resolved_ast::{
//     ArrayOp, CustomGlobalId, CustomTypeId, GlobalId, IoOp, Type, TypeDef, TypeId, TypeParamId,
//     VariantId,
// };
use crate::util::graph::{self, Graph};

use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::io::Write;

const TAB_SIZE: usize = 2;

enum MlVariant {
    OCAML,
    SML,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Precedence {
    Top,
    Fun,
    App,
    Var,
}

struct Context<'a, 'b> {
    variant: MlVariant,
    writer: &'b mut dyn Write,
    indentation: usize,
    num_locals: usize,
    prog: &'a Program,
}

impl<'a, 'b> Context<'a, 'b> {
    fn add_indent(&mut self) {
        self.indentation += TAB_SIZE;
    }

    fn remove_indent(&mut self) {
        self.indentation -= TAB_SIZE;
    }

    fn add_locals(&mut self, n: usize) {
        self.num_locals += n;
    }

    fn remove_locals(&mut self, n: usize) {
        self.num_locals -= n;
    }

    fn write(&mut self, e: impl std::fmt::Display + Copy) -> io::Result<()> {
        write![self.writer, "{}", e]
    }

    fn writeln(&mut self) -> io::Result<()> {
        writeln![self.writer]?;
        write![self.writer, "{}", " ".repeat(self.indentation)]
    }

    fn write_type(&mut self, type_: &Type, precedence: Precedence) -> io::Result<()> {
        let my_precedence = match type_ {
            Type::Bool => Precedence::Var,
            Type::Byte => Precedence::Var,
            Type::Int => Precedence::Var,
            Type::Float => Precedence::Var,
            Type::Array(_) => Precedence::App,
            Type::Custom(_) => Precedence::App,
            Type::Tuple(_) => Precedence::Fun,
            Type::Func(_, _, _) => Precedence::Fun,
        };
        if precedence > my_precedence {
            self.write("(")?;
        }

        match type_ {
            Type::Bool => self.write("bool")?,
            Type::Byte => self.write("char")?,
            Type::Int => match self.variant {
                MlVariant::OCAML => self.write("int64")?,
                MlVariant::SML => self.write("LargeInt.int")?,
            },
            Type::Float => match self.variant {
                MlVariant::OCAML => self.write("float")?,
                MlVariant::SML => self.write("real")?,
            },
            Type::Array(item_type) => {
                self.write_type(item_type, Precedence::Var)?;
                self.write(" ")?;

                self.write("PersistentArray.array")?
            }
            Type::Custom(type_id) => {
                self.write(
                    &self.prog.custom_type_symbols[type_id]
                        .type_name
                        .0
                        .to_lowercase(),
                )?;
                self.write("_")?;
                self.write(type_id.0)?;
            }
            Type::Tuple(types) => {
                if types.len() == 0 {
                    self.write("unit")?;
                } else {
                    for (i, type_) in types.iter().enumerate() {
                        self.write_type(type_, Precedence::App)?;
                        if i != types.len() - 1 {
                            self.write(" * ")?;
                        }
                    }
                }
            }
            Type::Func(_purity, arg_type, ret_type) => {
                self.write_type(arg_type, Precedence::App)?;
                self.write(" -> ")?;
                self.write_type(ret_type, Precedence::Top)?;
            }
        }

        if precedence > my_precedence {
            self.write(")")?;
        }

        Ok(())
    }

    fn write_variant(&mut self, type_id: CustomTypeId, variant_id: VariantId) -> io::Result<()> {
        self.write(
            &self.prog.custom_type_symbols[type_id].variant_symbols[variant_id]
                .variant_name
                .0,
        )?;

        self.write("_")?;
        self.write(type_id.0)?;
        Ok(())
    }

    fn write_pattern(&mut self, p: &Pattern) -> io::Result<usize> {
        self.write_pattern_rec(p, true)
    }

    fn write_pattern_rec(&mut self, p: &Pattern, write_type: bool) -> io::Result<usize> {
        match p {
            Pattern::Any(_) => {
                self.write("_")?;
                Ok(0)
            }

            Pattern::Var(var_type) => {
                self.write("l")?;
                self.write(self.num_locals)?;
                match self.variant {
                    MlVariant::OCAML => {
                        if write_type {
                            self.write(" : ")?;
                            self.write_type(var_type, Precedence::Top)?;
                        }
                    }
                    MlVariant::SML => {
                        self.write(" : ")?;
                        self.write_type(var_type, Precedence::Top)?;
                    }
                }
                Ok(1)
            }
            Pattern::Tuple(pats) => {
                if pats.len() == 1 {
                    panic!("length 1 tuple");
                }

                if let MlVariant::OCAML = self.variant {
                    if write_type {
                        self.write("(")?;
                    }
                }

                self.write("(")?;
                let mut total_locals = 0;
                for (i, pat) in pats.iter().enumerate() {
                    let num_locals = self.write_pattern_rec(pat, false)?;
                    total_locals += num_locals;
                    self.add_locals(num_locals);
                    if i != pats.len() - 1 {
                        self.write(", ")?;
                    }
                }
                self.remove_locals(total_locals);
                self.write(")")?;

                if let MlVariant::OCAML = self.variant {
                    if write_type {
                        self.write(" : ")?;
                        fn pat_to_type(p: &Pattern) -> Type {
                            match p {
                                Pattern::Any(t) => t.clone(),
                                Pattern::Var(t) => t.clone(),
                                Pattern::Tuple(pats) => {
                                    Type::Tuple(pats.iter().map(|x| pat_to_type(x)).collect())
                                }
                                Pattern::Ctor(type_id, _, _) => Type::Custom(type_id.clone()),
                                Pattern::ByteConst(_) => Type::Byte,
                                Pattern::IntConst(_) => Type::Int,
                                Pattern::FloatConst(_) => Type::Float,
                                Pattern::BoolConst(_) => Type::Bool,
                            }
                        }

                        if pats.len() == 0 {
                            self.write("unit")?;
                        } else {
                            for (i, pat) in pats.iter().enumerate() {
                                self.write_type(&pat_to_type(pat), Precedence::App)?;
                                if i != pats.len() - 1 {
                                    self.write(" * ")?;
                                }
                            }
                        }

                        self.write(")")?;
                    }
                }
                Ok(total_locals)
            }
            Pattern::Ctor(type_id, variant_id, maybe_pattern) => {
                self.write_variant(*type_id, *variant_id)?;
                let new_locals = match maybe_pattern {
                    Some(p) => {
                        self.write(" (")?;
                        let n = self.write_pattern_rec(p, write_type)?;
                        self.write(")")?;
                        n
                    }
                    None => 0,
                };
                Ok(new_locals)
            }
            Pattern::ByteConst(byte) => {
                self.write_byte_const(byte)?;
                Ok(0)
            }
            Pattern::IntConst(int) => {
                self.write_int_const(*int)?;
                Ok(0)
            }
            Pattern::FloatConst(_) => todo!(),
            Pattern::BoolConst(b) => match b {
                true => {
                    self.write("true")?;
                    Ok(0)
                }
                false => {
                    self.write("false")?;
                    Ok(0)
                }
            },
        }
    }

    fn write_expr(&mut self, expr: &Expr, precedence: Precedence) -> io::Result<()> {
        let my_precedence = match expr {
            Expr::Global(custom_global_id) => {
                if let Expr::Lam(_, _, _, _, _, _) = self.prog.vals[custom_global_id].body {
                    Precedence::Var
                } else {
                    Precedence::App
                }
            }
            Expr::Local(_) => Precedence::Var,
            Expr::Tuple(_) => Precedence::Var,
            Expr::Lam(_, _, _, _, _, _) => Precedence::Top,
            Expr::App(_, _, _) => Precedence::App,
            Expr::Match(_, _, _) => Precedence::Top,
            Expr::LetMany(_, _) => Precedence::Top,
            Expr::ArrayLit(_, _) => Precedence::App,
            Expr::ByteLit(_) => Precedence::Var,
            Expr::IntLit(_) => Precedence::Var,
            Expr::FloatLit(_) => Precedence::Var,
            Expr::Intrinsic(_) => Precedence::Var,
            Expr::ArrayOp(_, _) => Precedence::Var,
            Expr::IoOp(_) => Precedence::Var,
            Expr::Panic(_) => Precedence::Var,
            Expr::Ctor(_, _) => Precedence::Var,
            Expr::BoolLit(_) => Precedence::Var,
        };

        if precedence > my_precedence {
            self.write("(")?;
        }

        match expr {
            Expr::Global(global_id) => {
                if let Expr::Lam(_, _, _, _, _, _) = self.prog.vals[global_id].body {
                    self.write_identifier(*global_id)?;
                } else {
                    self.write_identifier(*global_id)?;
                    self.write(" ()")?;
                }
            }
            Expr::Local(local_id) => {
                self.write("l")?;
                self.write(local_id.0)?;
            }
            Expr::Tuple(exprs) => {
                self.write("(")?;
                for (i, expr) in exprs.iter().enumerate() {
                    self.write_expr(expr, Precedence::Fun)?;
                    if i != exprs.len() - 1 {
                        self.write(", ")?;
                    }
                }
                self.write(")")?;
            }
            Expr::Lam(_purity, _arg_type, _ret_type, pattern, body, _prof) => {
                match self.variant {
                    MlVariant::OCAML => {
                        self.write("fun (")?;
                    }
                    MlVariant::SML => {
                        self.write("fn (")?;
                    }
                }
                let num_locals = self.write_pattern(pattern)?;
                self.add_indent();
                self.add_locals(num_locals);
                self.write(") ")?;
                match self.variant {
                    MlVariant::OCAML => {
                        self.write("-> ")?;
                    }
                    MlVariant::SML => {
                        self.write("=> ")?;
                    }
                }
                self.write_expr(body, Precedence::Top)?;
                self.remove_indent();
                self.remove_locals(num_locals);
            }
            Expr::App(_purity, func, arg) => {
                self.write_expr(func, Precedence::Var)?;
                self.write(" ")?;
                self.write_expr(arg, Precedence::Var)?;
            }
            Expr::Match(expr, patterns, _type) => {
                match self.variant {
                    MlVariant::OCAML => {
                        self.write("match ")?;
                        self.write_expr(expr, Precedence::App)?;
                        self.write(" with")?;
                    }
                    MlVariant::SML => {
                        self.write("case ")?;
                        self.write_expr(expr, Precedence::App)?;
                        self.write(" of")?;
                    }
                }
                for (i, (pattern, expr)) in patterns.iter().enumerate() {
                    self.writeln()?;
                    if i == 0 {
                        self.write("  ")?;
                    } else {
                        self.write("| ")?;
                    }

                    let num_locals = self.write_pattern(pattern)?;

                    self.add_indent();
                    self.add_locals(num_locals);
                    match self.variant {
                        MlVariant::OCAML => {
                            self.write(" -> ")?;
                        }
                        MlVariant::SML => {
                            self.write(" => ")?;
                        }
                    }
                    self.write_expr(expr, Precedence::App)?;
                    self.remove_indent();
                    self.remove_locals(num_locals);
                }
            }
            Expr::LetMany(bindings, expr) => {
                let mut total_locals = 0;
                self.write("let")?;
                self.add_indent();

                for (i, binding) in bindings.iter().enumerate() {
                    self.writeln()?;
                    match self.variant {
                        MlVariant::OCAML => {
                            if i != 0 {
                                self.write("in let ")?;
                            }
                        }
                        MlVariant::SML => {
                            self.write("val ")?;
                        }
                    }
                    let num_locals = self.write_pattern(&binding.0)?;
                    total_locals = total_locals + num_locals;
                    self.write(" = ")?;
                    self.write_expr(&binding.1, Precedence::Fun)?;
                    self.add_locals(num_locals);
                }
                self.remove_indent();
                self.writeln()?;
                self.write("in")?;
                self.add_indent();

                self.writeln()?;
                self.write_expr(expr, Precedence::Fun)?;

                self.remove_indent();
                self.remove_locals(total_locals);

                self.writeln()?;
                if let MlVariant::SML = self.variant {
                    self.write("end")?;
                }
            }
            Expr::ArrayLit(_type, elems) => {
                self.write("PersistentArray.fromList ")?;
                match self.variant {
                    MlVariant::OCAML => {
                        self.write("[|")?;
                    }
                    MlVariant::SML => {
                        self.write("[")?;
                    }
                }
                for (i, elem) in elems.iter().enumerate() {
                    self.write_expr(elem, Precedence::Top)?;
                    if i != elems.len() - 1 {
                        match self.variant {
                            MlVariant::OCAML => {
                                self.write("; ")?;
                            }
                            MlVariant::SML => {
                                self.write(", ")?;
                            }
                        }
                    }
                }
                match self.variant {
                    MlVariant::OCAML => {
                        self.write("|]")?;
                    }
                    MlVariant::SML => {
                        self.write("]")?;
                    }
                }
            }
            Expr::ByteLit(byte) => {
                self.write_byte_const(byte)?;
            }
            Expr::IntLit(int) => {
                self.write_int_const(*int)?;
            }
            Expr::FloatLit(float) => {
                self.write_float_const(*float)?;
            }
            Expr::Intrinsic(intrinsic) => {
                self.write("intrinsic_")?;
                self.write(&format!("{:?}", intrinsic))?;
            }
            Expr::ArrayOp(array_op, _array_type) => match array_op {
                ArrayOp::Get => self.write("intrinsic_get")?,
                ArrayOp::Extract => self.write("intrinsic_extract")?,
                ArrayOp::Len => self.write("intrinsic_len")?,
                ArrayOp::Push => self.write("intrinsic_push")?,
                ArrayOp::Pop => self.write("intrinsic_pop")?,
                ArrayOp::Reserve => self.write("intrinsic_reserve")?,
            },
            Expr::IoOp(io_op) => match io_op {
                IoOp::Input => self.write("input")?,
                IoOp::Output => self.write("output")?,
            },
            Expr::Panic(_type) => self.write("panic")?,
            Expr::Ctor(custom_type_id, variant_id) => {
                self.write_variant(*custom_type_id, *variant_id)?;
            }
            Expr::BoolLit(b) => match b {
                true => self.write("true")?,
                false => self.write("false")?,
            },
        };

        if precedence > my_precedence {
            self.write(")")?;
        }
        Ok(())
    }

    fn write_byte_const(&mut self, byte: &u8) -> Result<(), io::Error> {
        match self.variant {
            MlVariant::OCAML => {
                self.write("'")?;
                if *byte == '\'' as u8 {
                    self.write("\\\'")?;
                } else if *byte == '\\' as u8 {
                    self.write("\\\\")?;
                } else if !byte.is_ascii_control() {
                    self.write(*byte as char)?;
                } else {
                    self.write(&format!("\\{:03}", byte))?;
                }
                self.write("\'")?;
            }
            MlVariant::SML => {
                self.write("#\"")?;
                if *byte == '\"' as u8 {
                    self.write("\\\"")?;
                } else if *byte == '\\' as u8 {
                    self.write("\\\\")?;
                } else if !byte.is_ascii_control() {
                    self.write(*byte as char)?;
                } else {
                    self.write(&format!("\\{:03}", byte))?;
                }
                self.write("\"")?;
            }
        }
        Ok(())
    }

    fn write_int_const(&mut self, int: i64) -> Result<(), io::Error> {
        self.write(int)?;
        if let MlVariant::OCAML = self.variant {
            self.write("L")?;
        }
        Ok(())
    }

    fn write_float_const(&mut self, float: f64) -> Result<(), io::Error> {
        self.write(float)?;
        if float.fract() == 0.0 {
            self.write(".0")?;
        }
        Ok(())
    }

    fn write_custom_type(
        &mut self,
        type_id: CustomTypeId,
        def: &TypeDef,
        is_first: bool,
    ) -> io::Result<()> {
        if is_first {
            match self.variant {
                MlVariant::OCAML => self.write("type ")?,
                MlVariant::SML => {
                    self.write("datatype ")?;
                }
            }
        } else {
            self.write("and ")?;
        }

        self.write(
            &self.prog.custom_type_symbols[type_id]
                .type_name
                .0
                .to_lowercase(),
        )?;
        self.write("_")?;
        self.write(type_id.0)?;

        self.write(" = ")?;
        self.writeln()?;
        for (i, (variant_id, variant)) in def.variants.iter().enumerate() {
            if i == 0 {
                self.write("  ")?;
            } else {
                self.write("| ")?;
            }

            match variant {
                Some(type_arg) => {
                    self.write_variant(type_id, variant_id)?;
                    self.write(" of ")?;
                    self.write_type(type_arg, Precedence::App)?;
                }
                None => self.write_variant(type_id, variant_id)?,
            }
            self.writeln()?;
        }

        Ok(())
    }

    fn write_identifier(&mut self, custom_global_id: CustomGlobalId) -> io::Result<()> {
        match &self.prog.val_symbols[custom_global_id] {
            ValSymbols::Wrapper(w) => {
                self.write("wrapper_")?;
                self.write(&w.val_name.0)?;
            }
            ValSymbols::Normal(w) => {
                self.write(&w.val_name.0)?;
            }
        }
        self.write("_")?;
        self.write(custom_global_id.0)?;
        Ok(())
    }

    fn write_program(&mut self, prog: &Program) -> io::Result<()> {
        self.write("(* Lines 1-600ish are prelude, included in every generated program. *)\n")?;
        self.write("(* The generated program begins around line 600. *)")?;
        self.writeln()?;
        match self.variant {
            MlVariant::OCAML => {
                self.write(PRELUDE_PERSISTENT_OCAML)?;
                self.writeln()?;
                self.write(PRELUDE_OCAML)?;
            }
            MlVariant::SML => {
                self.write(PRELUDE_PERSISTENT_SML)?;
                self.writeln()?;
                self.write(PRELUDE_SML)?;
            }
        }
        self.writeln()?;

        let type_sccs = graph::strongly_connected(&Graph {
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
        });

        for scc in type_sccs {
            for (i, id) in scc.iter().enumerate() {
                let type_def = &prog.custom_types[id];
                if i == 0 {
                    self.write_custom_type(*id, type_def, true)?;
                } else {
                    self.write_custom_type(*id, type_def, false)?;
                }
                self.writeln()?;
            }
        }

        let val_sccs = graph::strongly_connected(&Graph {
            edges_out: prog.vals.map(|_, val_def| {
                let mut deps = BTreeSet::new();
                add_func_deps(&mut deps, &val_def.body);
                deps.into_iter().collect()
            }),
        });

        let mut profile_points: BTreeMap<ProfilePointId, CustomGlobalId> = BTreeMap::new();

        for scc in val_sccs {
            for (i, id) in scc.iter().enumerate() {
                let val = &prog.vals[id];
                if let Expr::Lam(_purity, _arg_type, ret_type, pattern, body, prof) = &val.body {
                    if let Some(prof_id) = prof {
                        profile_points.insert(*prof_id, *id);
                        match self.variant {
                            MlVariant::OCAML => {
                                self.write("let total_calls_")?;
                                self.write(id.0)?;
                                self.write(" = ref 0")?;
                                self.writeln()?;
                                self.write("let total_clock_nanos_")?;
                                self.write(id.0)?;
                                self.write(" = ref 0")?;
                                self.writeln()?;
                            }
                            MlVariant::SML => {
                                self.write("val total_calls_")?;
                                self.write(id.0)?;
                                self.write(" = ref 0")?;
                                self.writeln()?;
                                self.write("val total_clock_nanos_")?;
                                self.write(id.0)?;
                                self.write(" = ref 0")?;
                                self.writeln()?;
                            }
                        }
                    }

                    if i == 0 {
                        match self.variant {
                            MlVariant::OCAML => {
                                self.write("let rec ")?;
                            }
                            MlVariant::SML => {
                                self.write("fun ")?;
                            }
                        }
                    } else {
                        self.write("and ")?;
                    }
                    self.write_identifier(*id)?;
                    self.write(" (")?;
                    let num_locals = self.write_pattern(&pattern)?;
                    self.write("): ")?;
                    self.write_type(&ret_type, Precedence::Top)?;
                    if let Some(_) = prof {
                        match self.variant {
                            MlVariant::OCAML => {
                                self.write(" = let start = Unix.gettimeofday () in let res =")?;
                            }
                            MlVariant::SML => {
                                self.write(" = let val start = Time.now () val res =")?;
                            }
                        }
                    } else {
                        self.write(" =")?;
                    }
                    self.add_indent();
                    self.add_locals(num_locals);

                    self.writeln()?;
                    self.write_expr(&body, Precedence::Top)?;

                    self.remove_indent();
                    self.remove_locals(num_locals);

                    if let Some(_) = prof {
                        match self.variant {
                            MlVariant::OCAML => {
                                self.write("in let stop = Unix.gettimeofday () in let _ = incr total_calls_")?;
                                self.write(id.0)?;
                                self.write(" in let _ = total_clock_nanos_")?;
                                self.write(id.0)?;
                                self.write(" := int_of_float ((stop -. start) *. 1000000000.0) + !total_clock_nanos_")?;
                                self.write(id.0)?;
                                self.write(" in res")?;
                            }
                            MlVariant::SML => {
                                self.write(" val stop = Time.now () val _ = total_calls_")?;
                                self.write(id.0)?;
                                self.write(" := !total_calls_")?;
                                self.write(id.0)?;
                                self.write("+ 1 val _ = total_clock_nanos_")?;
                                self.write(id.0)?;
                                self.write(
                                    " := Time.toNanoseconds (Time.- (stop, start)) + !total_clock_nanos_",
                                )?;
                                self.write(id.0)?;
                                self.write(" in res end")?;
                            }
                        }
                    }
                } else {
                    if i == 0 {
                        match self.variant {
                            MlVariant::OCAML => {
                                self.write("let rec ")?;
                            }
                            MlVariant::SML => {
                                self.write("fun ")?;
                            }
                        }
                    } else {
                        self.write("and ")?;
                    }
                    self.write_identifier(*id)?;
                    self.write(" (): ")?;
                    self.write_type(&val.type_, Precedence::Top)?;
                    self.write(" =")?;
                    self.add_indent();
                    self.writeln()?;

                    self.write_expr(&val.body, Precedence::Top)?;
                    self.remove_indent();
                }
                self.writeln()?;
            }
            self.writeln()?;
            self.writeln()?;
        }
        self.writeln()?;
        match self.variant {
            MlVariant::OCAML => {
                self.write("let _ = main_")?;
            }
            MlVariant::SML => {
                self.write("val _ = main_")?;
            }
        }
        self.write(prog.main.0)?;
        self.write(" ();")?;
        self.writeln()?;

        if !profile_points.is_empty() {
            match self.variant {
                MlVariant::OCAML => {
                    self.write("let profile_path = Sys.getenv_opt(\"MORPHIC_PROFILE_PATH\");")?;
                    self.writeln()?;
                    self.write("in match profile_path with")?;
                    self.writeln()?;
                    self.write("  Some (profile_path) ->")?;
                    self.writeln()?;
                    self.write("    let profile_file = open_out profile_path;")?;
                    self.writeln()?;
                    self.write("    in Out_channel.output_string profile_file \"[\";")?;
                    self.writeln()?;
                    for profile_point in profile_points {
                        self.write("Printf.fprintf profile_file ")?;
                        let func_id = profile_point.1 .0;
                        let json_object = format!(
                            r#""{{\"func_id\": {func_id}, \"total_calls\": %d, \"total_clock_nanos\": %d}}""#
                        );
                        self.write(&json_object)?;
                        self.write(&format!(
                            " !total_calls_{func_id} !total_clock_nanos_{func_id};"
                        ))?;
                        self.writeln()?;
                    }
                    self.write("    Out_channel.output_string profile_file \"]\";")?;
                    self.writeln()?;
                    self.write(
                        "  | None -> Printf.eprintf \"Warning: no MORPHIC_PROFILE_PATH provided\"",
                    )?;
                    self.writeln()?;
                }
                MlVariant::SML => {
                    self.write("val profile_path = OS.Process.getEnv(\"MORPHIC_PROFILE_PATH\");")?;
                    self.writeln()?;
                    self.write("val _ = case profile_path of")?;
                    self.writeln()?;
                    self.write("  SOME (profile_path) =>")?;
                    self.writeln()?;
                    self.write("    let val profile_file = TextIO.openOut profile_path;")?;
                    self.writeln()?;
                    self.write("    in TextIO.output (profile_file, \"[\");")?;
                    self.writeln()?;
                    for profile_point in profile_points {
                        let func_id = profile_point.1 .0;
                        self.write(r#"    TextIO.output (profile_file, "{\"func_id\": "#)?;
                        self.write(func_id)?;
                        self.write(r#", \"total_calls\": ");"#)?;
                        self.writeln()?;
                        self.write(&format!(
                            "    TextIO.output (profile_file, (Int.toString (!total_calls_{func_id})));"
                        ))?;
                        self.writeln()?;
                        self.write(
                            r#"    TextIO.output (profile_file, ", \"total_clock_nanos\": ");"#,
                        )?;
                        self.writeln()?;
                        self.write(&format!(
                            "    TextIO.output (profile_file, (LargeInt.toString (!total_clock_nanos_{func_id})));"
                        ))?;
                        self.writeln()?;
                        self.write("    TextIO.output (profile_file, \"}\");")?;
                        self.writeln()?;
                    }
                    self.write("    TextIO.output (profile_file, \"]\")")?;
                    self.writeln()?;
                    self.write("    end")?;
                    self.writeln()?;
                    self.write(
                        "  | NONE => TextIO.output (TextIO.stdErr, \"Warning: no MORPHIC_PROFILE_PATH provided\")",
                    )?;
                    self.writeln()?;
                }
            }
        }
        Ok(())
    }
}

const PRELUDE_SML: &str = include_str!("prelude.sml");
const PRELUDE_OCAML: &str = include_str!("prelude.ml");

// TODO: Add a flag to control whether we use immutable/mutable arrays in the generated SML code.
// We hard-code mutable for now because it's sufficient for the benchmarks we're interested in.
const PRELUDE_PERSISTENT_SML: &str = include_str!("mut.sml");
const PRELUDE_PERSISTENT_OCAML: &str = include_str!("mut.ml");

fn add_func_deps(deps: &mut BTreeSet<CustomGlobalId>, expr: &Expr) {
    match expr {
        Expr::Global(global_id) => {
            deps.insert(*global_id);
        }
        Expr::Local(_) => {}
        Expr::Tuple(elems) => {
            for elem in elems {
                add_func_deps(deps, elem);
            }
        }
        Expr::Lam(_, _, _, _, body, _) => add_func_deps(deps, body),
        Expr::App(_, func, arg) => {
            add_func_deps(deps, func);
            add_func_deps(deps, arg)
        }
        Expr::Match(expr, arms, _) => {
            add_func_deps(deps, expr);
            for (_, arm) in arms {
                add_func_deps(deps, arm);
            }
        }
        Expr::LetMany(lets, body) => {
            for (_, let_) in lets {
                add_func_deps(deps, let_);
            }
            add_func_deps(deps, body);
        }
        Expr::ArrayLit(_, elems) => {
            for elem in elems {
                add_func_deps(deps, elem);
            }
        }
        Expr::ByteLit(_) => {}
        Expr::IntLit(_) => {}
        Expr::FloatLit(_) => {}
        Expr::Intrinsic(_) => {}
        Expr::ArrayOp(_, _) => {}
        Expr::IoOp(_) => {}
        Expr::Panic(_) => {}
        Expr::Ctor(_, _) => {}
        Expr::BoolLit(_) => {}
    }
}

fn add_type_deps(deps: &mut BTreeSet<CustomTypeId>, type_: &Type) {
    match type_ {
        Type::Tuple(elems) => {
            for elem in elems {
                add_type_deps(deps, elem);
            }
        }
        Type::Func(_, arg_type, ret_type) => {
            add_type_deps(deps, arg_type);
            add_type_deps(deps, ret_type);
        }
        Type::Bool => {}
        Type::Byte => {}
        Type::Int => {}
        Type::Float => {}
        Type::Array(item_type) => {
            add_type_deps(deps, item_type);
        }
        Type::Custom(custom_type_id) => {
            deps.insert(*custom_type_id);
        }
    }
}

pub fn write_sml_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let mut context = Context {
        variant: MlVariant::SML,
        writer: w,
        indentation: 0,
        num_locals: 0,
        prog: program,
    };
    context.write_program(program)?;
    Ok(())
}

pub fn write_ocaml_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let mut context = Context {
        variant: MlVariant::OCAML,
        writer: w,
        indentation: 0,
        num_locals: 0,
        prog: program,
    };
    context.write_program(program)?;
    Ok(())
}
