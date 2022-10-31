use crate::data::first_order_ast::*;
use crate::data::mono_ast::ValSymbols;
use crate::data::num_type::NumType;
use crate::data::resolved_ast;
use crate::util::graph::{self, Graph};

use std::collections::BTreeSet;
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
        fn get_precedence(t: &Type) -> Precedence {
            match t {
                Type::Bool => Precedence::Var,
                Type::Num(_) => Precedence::Var,
                Type::Array(_) => Precedence::App,
                Type::HoleArray(_) => Precedence::Fun,
                Type::Tuple(types) => {
                    if types.len() == 0 {
                        Precedence::Var
                    } else if types.len() == 1 {
                        get_precedence(&types[0])
                    } else {
                        Precedence::Top
                    }
                }
                Type::Custom(_) => Precedence::Var,
            }
        }
        let my_precedence = get_precedence(type_);
        if precedence > my_precedence {
            self.write("(")?;
        }

        match type_ {
            Type::Bool => {
                self.write("bool")?;
            }
            Type::Num(num_type) => match num_type {
                NumType::Byte => {
                    self.write("char")?;
                }
                NumType::Int => match self.variant {
                    MlVariant::OCAML => {
                        self.write("int64")?;
                    }
                    MlVariant::SML => {
                        self.write("LargeInt.int")?;
                    }
                },
                NumType::Float => match self.variant {
                    MlVariant::OCAML => self.write("float")?,
                    MlVariant::SML => self.write("real")?,
                },
            },
            Type::Array(elem_type) => {
                self.write_type(elem_type, Precedence::Var)?;
                self.write(" PersistentArray.array")?;
            }
            Type::HoleArray(elem_type) => {
                self.write_type(elem_type, Precedence::App)?;
                self.write(" -> ")?;
                self.write_type(elem_type, Precedence::Var)?;
                self.write(" PersistentArray.array")?;
            }
            Type::Tuple(types) => {
                if types.len() == 0 {
                    self.write("unit")?;
                } else if types.len() == 1 {
                    self.write_type(&types[0], precedence)?;
                } else {
                    for (i, type_) in types.iter().enumerate() {
                        self.write_type(type_, Precedence::App)?;
                        if i != types.len() - 1 {
                            self.write(" * ")?;
                        }
                    }
                }
            }
            Type::Custom(custom_type_id) => {
                self.write_custom_type_id(*custom_type_id)?;
            }
        }

        if precedence > my_precedence {
            self.write(")")?;
        }

        Ok(())
    }

    fn write_custom_type_id(&mut self, type_id: CustomTypeId) -> io::Result<()> {
        match &self.prog.custom_type_symbols[type_id] {
            CustomTypeSymbols::CustomType(type_name) => {
                self.write(&type_name.type_name.0.to_lowercase())?;
                self.write("_")?;
                self.write(type_id.0)?;
            }
            CustomTypeSymbols::ClosureType => {
                self.write("closure_")?;
                self.write(type_id.0)?;
            }
        }
        Ok(())
    }

    fn write_variant(&mut self, type_id: CustomTypeId, variant_id: VariantId) -> io::Result<()> {
        match &self.prog.custom_type_symbols[type_id] {
            CustomTypeSymbols::CustomType(type_symbols) => {
                self.write(
                    &(type_symbols.variant_symbols[resolved_ast::VariantId(variant_id.0)]
                        .variant_name
                        .0),
                )?;
                self.write(type_id.0)?;
                self.write("_")?;
                self.write(variant_id.0)?;
            }
            CustomTypeSymbols::ClosureType => {
                self.write("Variant")?;
                self.write(type_id.0)?;
                self.write("_")?;
                self.write(variant_id.0)?;
            }
        }
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
                    self.write_pattern_rec(&pats[0], write_type)
                } else {
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
                                    Pattern::Ctor(type_id, _, _) => Type::Custom(*type_id),
                                    Pattern::BoolConst(_) => Type::Bool,
                                    Pattern::ByteConst(_) => Type::Num(NumType::Byte),
                                    Pattern::IntConst(_) => Type::Num(NumType::Int),
                                    Pattern::FloatConst(_) => Type::Num(NumType::Float),
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
            Pattern::BoolConst(b) => {
                if *b {
                    self.write("true")?;
                } else {
                    self.write("false")?;
                }
                Ok(0)
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
        }
    }

    fn write_expr(&mut self, expr: &Expr, precedence: Precedence) -> io::Result<()> {
        let my_precedence = match expr {
            Expr::Intrinsic(_, _) => Precedence::App,
            Expr::ArrayOp(_) => Precedence::App,
            Expr::IoOp(_) => Precedence::App,
            Expr::Panic(_, _) => Precedence::App,
            Expr::Ctor(_, _, _) => Precedence::App,
            Expr::Local(_) => Precedence::Var,
            Expr::Tuple(_) => Precedence::Var,
            Expr::Call(_, _, _) => Precedence::App,
            Expr::Match(_, _, _) => Precedence::Fun,
            Expr::LetMany(_, _) => Precedence::App,
            Expr::ArrayLit(_, _) => Precedence::App,
            Expr::BoolLit(_) => Precedence::Var,
            Expr::ByteLit(_) => Precedence::Var,
            Expr::IntLit(_) => Precedence::Var,
            Expr::FloatLit(_) => Precedence::Var,
        };

        if precedence > my_precedence {
            self.write("(")?;
        }

        match expr {
            Expr::Intrinsic(intrinsic, expr) => {
                self.write(&format!("intrinsic_{:?} ", intrinsic))?;
                self.write_expr(expr, Precedence::Var)?;
            }
            Expr::ArrayOp(array_op) => match array_op {
                ArrayOp::Get(_type, a, b) => {
                    self.write("intrinsic_get ")?;
                    self.write_expr(&Expr::Tuple(vec![*a.clone(), *b.clone()]), Precedence::Top)?;
                }
                ArrayOp::Extract(_type, a, b) => {
                    self.write("intrinsic_extract ")?;
                    self.write_expr(&Expr::Tuple(vec![*a.clone(), *b.clone()]), Precedence::Top)?;
                }
                ArrayOp::Len(_type, a) => {
                    self.write("intrinsic_len ")?;
                    self.write_expr(a, Precedence::Var)?;
                }
                ArrayOp::Push(_type, a, b) => {
                    self.write("intrinsic_push ")?;
                    self.write_expr(&Expr::Tuple(vec![*a.clone(), *b.clone()]), Precedence::Top)?;
                }
                ArrayOp::Pop(_type, a) => {
                    self.write("intrinsic_pop ")?;
                    self.write_expr(a, Precedence::Var)?;
                }
                ArrayOp::Replace(_type, a, b) => {
                    self.write("intrinsic_replace ")?;
                    self.write_expr(&Expr::Tuple(vec![*a.clone(), *b.clone()]), Precedence::Top)?;
                }
                ArrayOp::Reserve(_type, a, b) => {
                    self.write("intrinsic_reserve ")?;
                    self.write_expr(&Expr::Tuple(vec![*a.clone(), *b.clone()]), Precedence::Top)?;
                }
            },
            Expr::IoOp(io_op) => match io_op {
                IoOp::Input => self.write("input ()")?,
                IoOp::Output(a) => {
                    self.write("output ")?;
                    self.write_expr(a, Precedence::Var)?;
                }
            },
            Expr::Panic(_type, a) => {
                self.write("panic ")?;
                self.write_expr(a, Precedence::Var)?;
            }
            Expr::Ctor(type_id, variant_id, maybe_expr) => {
                self.write_variant(*type_id, *variant_id)?;
                match maybe_expr {
                    Some(expr) => {
                        self.write(" ")?;
                        self.write_expr(expr, Precedence::Var)?;
                    }
                    None => {}
                }
            }
            Expr::Local(local_id) => {
                self.write("l")?;
                self.write(local_id.0)?;
            }
            Expr::Tuple(exprs) => {
                if exprs.len() == 1 {
                    self.write_expr(&exprs[0], Precedence::Top)?;
                } else {
                    self.write("(")?;
                    for (i, expr) in exprs.iter().enumerate() {
                        self.write_expr(expr, Precedence::Top)?;
                        if i != exprs.len() - 1 {
                            self.write(", ")?;
                        }
                    }
                    self.write(")")?;
                }
            }
            Expr::Call(_purity, func_id, arg) => {
                self.write_custom_func_id(*func_id)?;
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
                    self.write_expr(&binding.1, Precedence::Top)?;
                    self.add_locals(num_locals);
                }
                self.remove_indent();
                self.writeln()?;
                self.write("in")?;
                self.add_indent();

                self.writeln()?;
                self.write_expr(expr, Precedence::Top)?;

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
            Expr::BoolLit(b) => {
                if *b {
                    self.write("true")?;
                } else {
                    self.write("false")?;
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
        self.write_custom_type_id(type_id)?;
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

    fn write_custom_func_id(&mut self, func_id: CustomFuncId) -> io::Result<()> {
        match &self.prog.func_symbols[func_id] {
            FuncSymbols::Global(val_symbols) => match val_symbols {
                ValSymbols::Wrapper(val_name) => {
                    self.write("wrapped_")?;
                    self.write(&val_name.val_name.0)?;
                    self.write("_")?;
                    self.write(func_id.0)?;
                }
                ValSymbols::Normal(val_name) => {
                    self.write(&val_name.val_name.0)?;
                    self.write("_")?;
                    self.write(func_id.0)?;
                }
            },
            FuncSymbols::Lam(lam_symbols) => {
                self.write("lam_")?;
                match &lam_symbols.lifted_from {
                    ValSymbols::Wrapper(val_name) => {
                        self.write("wrapped_")?;
                        self.write(&val_name.val_name.0)?;
                        self.write("_")?;
                        self.write(func_id.0)?;
                    }
                    ValSymbols::Normal(val_name) => {
                        self.write(&val_name.val_name.0)?;
                        self.write("_")?;
                        self.write(func_id.0)?;
                    }
                }
            }
            FuncSymbols::MainWrapper => {
                self.write("main_wrapper_")?;
                self.write(func_id.0)?;
            }
            FuncSymbols::Dispatch => {
                self.write("dispatch_")?;
                self.write(func_id.0)?;
            }
        }
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

        let func_sccs = graph::strongly_connected(&Graph {
            edges_out: prog.funcs.map(|_, func_def| {
                let mut deps = BTreeSet::new();
                add_func_deps(&mut deps, &func_def.body);
                deps.into_iter().collect()
            }),
        });

        for scc in func_sccs {
            for (i, id) in scc.iter().enumerate() {
                let func = &prog.funcs[id];
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

                self.write_custom_func_id(*id)?;
                self.write(" (")?;
                let num_locals = self.write_pattern(&func.arg)?;
                self.write("): ")?;
                self.write_type(&func.ret_type, Precedence::Top)?;
                self.write(" =")?;
                self.add_indent();
                self.add_locals(num_locals);

                self.writeln()?;
                self.write_expr(&func.body, Precedence::Top)?;

                self.remove_indent();
                self.remove_locals(num_locals);
                self.writeln()?;
                self.writeln()?;
            }
        }

        self.writeln()?;
        match self.variant {
            MlVariant::OCAML => {
                self.write("let _ = main_wrapper_")?;
            }
            MlVariant::SML => {
                self.write("val _ = main_wrapper_")?;
            }
        }
        self.write(prog.main.0)?;
        self.write(" ();")?;
        self.writeln()?;

        Ok(())
    }
}

const PRELUDE_SML : &str = "
fun intrinsic_AddByte(x : char, y : char): char = chr (Word8.toInt (Word8.fromInt (ord x) + Word8.fromInt (ord y)))
fun intrinsic_SubByte(x : char, y : char): char = chr (Word8.toInt (Word8.fromInt (ord x) - Word8.fromInt (ord y)))
fun intrinsic_MulByte(x : char, y : char): char = chr (Word8.toInt (Word8.fromInt (ord x) * Word8.fromInt (ord y)))
fun intrinsic_DivByte(x : char, y : char): char = chr (Word8.toInt (Word8.fromInt (ord x) div Word8.fromInt (ord y)))
fun intrinsic_NegByte(x : char): char = chr (Word8.toInt (~ (Word8.fromInt (ord x))))
fun intrinsic_EqByte(x : char, y : char): bool = x = y
fun intrinsic_LtByte(x : char, y : char): bool = x < y
fun intrinsic_LteByte(x : char, y : char): bool = x <= y
fun intrinsic_GtByte(x : char, y : char): bool = x > y
fun intrinsic_GteByte(x : char, y : char): bool = x >= y
fun intrinsic_AddInt(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.fromLargeInt x + Word64.fromLargeInt y)
fun intrinsic_SubInt(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.fromLargeInt x - Word64.fromLargeInt y)
fun intrinsic_MulInt(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.fromLargeInt x * Word64.fromLargeInt y)
fun intrinsic_DivInt(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.fromLargeInt x div Word64.fromLargeInt y)
fun intrinsic_NegInt(x : LargeInt.int): LargeInt.int = Word64.toLargeIntX (~ (Word64.fromLargeInt x))
fun intrinsic_EqInt(x : LargeInt.int, y : LargeInt.int): bool = x = y
fun intrinsic_LtInt(x : LargeInt.int, y : LargeInt.int): bool = x < y
fun intrinsic_LteInt(x : LargeInt.int, y : LargeInt.int): bool = x <= y
fun intrinsic_GtInt(x : LargeInt.int, y : LargeInt.int): bool = x > y
fun intrinsic_GteInt(x : LargeInt.int, y : LargeInt.int): bool = x >= y
fun intrinsic_AddFloat(x : real, y : real): real = x + y
fun intrinsic_SubFloat(x : real, y : real): real = x - y
fun intrinsic_MulFloat(x : real, y : real): real = x * y
fun intrinsic_DivFloat(x : real, y : real): real = x / y
fun intrinsic_NegFloat(x : real): real = ~ x
fun intrinsic_EqFloat(x : real, y : real): bool = Real.== (x, y)
fun intrinsic_LtFloat(x : real, y : real): bool = x < y
fun intrinsic_LteFloat(x : real, y : real): bool = x <= y
fun intrinsic_GtFloat(x : real, y : real): bool = x > y
fun intrinsic_GteFloat(x : real, y : real): bool = x >= y
fun intrinsic_Not(x : bool): bool = not x
fun intrinsic_ByteToInt(x : char): LargeInt.int = Int.toLarge (ord x)
fun intrinsic_ByteToIntSigned(x : char): LargeInt.int = Word8.toLargeIntX (Word8.fromInt (ord x))
fun intrinsic_IntToByte(x : LargeInt.int): char = chr (Word8.toInt (Word8.fromLargeInt x))
fun intrinsic_IntShiftLeft(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.<< (Word64.fromLargeInt x, Word.fromLargeInt (y mod 64)))
fun intrinsic_IntShiftRight(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.>> (Word64.fromLargeInt x, Word.fromLargeInt (y mod 64)))
fun intrinsic_IntBitAnd(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.andb (Word64.fromLargeInt x, Word64.fromLargeInt y))
fun intrinsic_IntBitOr(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.orb (Word64.fromLargeInt x, Word64.fromLargeInt y))
fun intrinsic_IntBitXor(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.xorb (Word64.fromLargeInt x, Word64.fromLargeInt y))

fun intrinsic_get(l : 'a PersistentArray.array, i : LargeInt.int): 'a = PersistentArray.sub (l, (Int.fromLarge i))
fun intrinsic_extract(l : 'a PersistentArray.array, i : LargeInt.int): 'a * ('a -> 'a PersistentArray.array) = (PersistentArray.sub (l, (Int.fromLarge i)), fn new => PersistentArray.update (l, Int.fromLarge i, new))
fun intrinsic_len(l : 'a PersistentArray.array): LargeInt.int = Int.toLarge (PersistentArray.length l)
fun intrinsic_push(l : 'a PersistentArray.array, x : 'a): 'a PersistentArray.array = PersistentArray.append (l, x)
fun intrinsic_pop(l : 'a PersistentArray.array): 'a PersistentArray.array * 'a = PersistentArray.popEnd(l)
fun intrinsic_reserve(l : 'a PersistentArray.array, i : LargeInt.int): 'a PersistentArray.array = l
fun intrinsic_replace(f : 'a -> 'a PersistentArray.array, x : 'a): 'a PersistentArray.array = f x

fun input(()) : char PersistentArray.array = #1 (intrinsic_pop (PersistentArray.fromList (explode (Option.getOpt ((TextIO.inputLine TextIO.stdIn), \"\\n\")))))
fun output(l : char PersistentArray.array) = print (implode (PersistentArray.toList l))
fun panic(l : char PersistentArray.array) = raise Fail (implode (PersistentArray.toList l))
";

const PRELUDE_OCAML : &str = "
let intrinsic_AddByte ((x, y) : char * char): char = Char.chr (((Char.code x + Char.code y) mod 256 + 256) mod 256)
let intrinsic_SubByte ((x, y) : char * char): char = Char.chr (((Char.code x - Char.code y) mod 256 + 256) mod 256)
let intrinsic_MulByte ((x, y) : char * char): char = Char.chr (((Char.code x * Char.code y) mod 256 + 256) mod 256)
let intrinsic_DivByte ((x, y) : char * char): char = Char.chr (((Char.code x / Char.code y) mod 256 + 256) mod 256)
let intrinsic_NegByte (x: char) = Char.chr (((-Char.code x) mod 256 + 256) mod 256)
let intrinsic_EqByte ((x, y) : char * char): bool = x = y
let intrinsic_LtByte ((x, y) : char * char): bool = x < y
let intrinsic_LteByte ((x, y) : char * char): bool = x <= y
let intrinsic_GtByte ((x, y) : char * char): bool = x > y
let intrinsic_GteByte ((x, y) : char * char): bool = x >= y
let intrinsic_AddInt ((x, y) : int64 * int64): int64 = Int64.add x y
let intrinsic_SubInt ((x, y) : int64 * int64): int64 = Int64.sub x y
let intrinsic_MulInt ((x, y) : int64 * int64): int64 = Int64.mul x y
let intrinsic_DivInt ((x, y) : int64 * int64): int64 = Int64.div x y
let intrinsic_NegInt (x : int64) : int64 = Int64.neg x
let intrinsic_EqInt ((x, y) : int64 * int64): bool = x = y
let intrinsic_LtInt ((x, y) : int64 * int64): bool = x < y
let intrinsic_LteInt ((x, y) : int64 * int64): bool = x <= y
let intrinsic_GtInt ((x, y) : int64 * int64): bool = x > y
let intrinsic_GteInt ((x, y) : int64 * int64): bool = x >= y
let intrinsic_AddFloat ((x, y) : float * float): float = x +. y
let intrinsic_SubFloat ((x, y) : float * float): float = x -. y
let intrinsic_MulFloat ((x, y) : float * float): float = x *. y
let intrinsic_DivFloat ((x, y) : float * float): float = x /. y
let intrinsic_NegFloat (x : float) : float = -.x
let intrinsic_EqFloat ((x, y) : float * float): bool = x = y
let intrinsic_LtFloat ((x, y) : float * float): bool = x < y
let intrinsic_LteFloat ((x, y) : float * float): bool = x <= y
let intrinsic_GtFloat ((x, y) : float * float): bool = x > y
let intrinsic_GteFloat ((x, y) : float * float): bool = x >= y
let intrinsic_Not (x : bool) : bool = not x
let intrinsic_ByteToInt (x : char) : int64 = Int64.of_int (Char.code x)
let intrinsic_ByteToIntSigned (x : char) : int64 = Int64.sub (Int64.logxor (Int64.of_int (Char.code x)) 0x80L) 0x80L
let intrinsic_IntToByte (x : int64) : char = Char.chr (Int64.to_int (Int64.rem (Int64.add (Int64.rem x 256L) 256L) 256L))
let intrinsic_IntShiftLeft ((x, y) : int64 * int64): int64 = Int64.shift_left x (Int64.to_int y)
let intrinsic_IntShiftRight ((x, y) : int64 * int64): int64 = Int64.shift_right_logical x (Int64.to_int y)
let intrinsic_IntBitAnd ((x, y) : int64 * int64): int64 = Int64.logand x y
let intrinsic_IntBitOr ((x, y) : int64 * int64): int64 = Int64.logor x y
let intrinsic_IntBitXor ((x, y) : int64 * int64): int64 = Int64.logxor x y

let intrinsic_get ((l, i) : 'a PersistentArray.array * int64): 'a = PersistentArray.sub (l, (Int64.to_int i))
let intrinsic_extract ((l, i) : 'a PersistentArray.array * int64): 'a * ('a -> 'a PersistentArray.array) = (PersistentArray.sub (l, (Int64.to_int i)), fun new_ -> PersistentArray.update (l, Int64.to_int i, new_))
let intrinsic_len (l : 'a PersistentArray.array): int64 = Int64.of_int (PersistentArray.length l)
let intrinsic_push ((l, x) : 'a PersistentArray.array * 'a): 'a PersistentArray.array = PersistentArray.append (l, x)
let intrinsic_pop (l : 'a PersistentArray.array): 'a PersistentArray.array * 'a = PersistentArray.popEnd(l)
let intrinsic_reserve ((l, i) : 'a PersistentArray.array * int64): 'a PersistentArray.array = l
let intrinsic_replace((f, x) : ('a -> 'a PersistentArray.array) * 'a): 'a PersistentArray.array = f x

let input (()) : char PersistentArray.array = let in_ = read_line () in PersistentArray.fromList (Array.init (String.length in_) (String.get in_))
let output (l : char PersistentArray.array) = print_string (String.init (PersistentArray.length l) (fun i -> PersistentArray.sub (l, i)))
let panic (l : char PersistentArray.array) = raise (Failure (String.init (PersistentArray.length l) (fun i -> PersistentArray.sub (l, i))))
";

const PRELUDE_PERSISTENT_SML: &str = include_str!("persistent.sml");
const PRELUDE_PERSISTENT_OCAML: &str = include_str!("persistent.ml");

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

fn add_func_deps(deps: &mut BTreeSet<CustomFuncId>, expr: &Expr) {
    match expr {
        Expr::Intrinsic(_, arg) => {
            add_func_deps(deps, arg);
        }
        Expr::ArrayOp(array_op) => match array_op {
            ArrayOp::Get(_, a, b) => {
                add_func_deps(deps, a);
                add_func_deps(deps, b);
            }
            ArrayOp::Extract(_, a, b) => {
                add_func_deps(deps, a);
                add_func_deps(deps, b);
            }
            ArrayOp::Len(_, a) => {
                add_func_deps(deps, a);
            }
            ArrayOp::Push(_, a, b) => {
                add_func_deps(deps, a);
                add_func_deps(deps, b);
            }
            ArrayOp::Pop(_, a) => {
                add_func_deps(deps, a);
            }
            ArrayOp::Replace(_, a, b) => {
                add_func_deps(deps, a);
                add_func_deps(deps, b);
            }
            ArrayOp::Reserve(_, a, b) => {
                add_func_deps(deps, a);
                add_func_deps(deps, b);
            }
        },
        Expr::IoOp(op) => match op {
            IoOp::Input => {}
            IoOp::Output(a) => add_func_deps(deps, a),
        },
        Expr::Panic(_, a) => add_func_deps(deps, a),
        Expr::Ctor(_, _, a) => match a {
            Some(b) => add_func_deps(deps, b),
            None => {}
        },
        Expr::Local(_) => {}
        Expr::Tuple(elems) => {
            for elem in elems {
                add_func_deps(deps, elem);
            }
        }
        Expr::Call(_, func, arg) => {
            deps.insert(*func);
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
        Expr::BoolLit(_) => {}
        Expr::ByteLit(_) => {}
        Expr::IntLit(_) => {}
        Expr::FloatLit(_) => {}
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
