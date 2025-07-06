use id_collections::IdVec;
use morphic_common::config::LlvmConfig;
use morphic_common::data::low_ast::*;
use morphic_common::data::metadata::Metadata;
use morphic_common::data::mode_annot_ast::Mode;
use morphic_common::data::num_type::NumType;
use morphic_common::data::rc_specialized_ast::{CustomTypes, ModeScheme};
use morphic_common::pseudoprocess::Stdio;

struct ProgramBuilder {
    bindings: Vec<(Type, Expr, Metadata)>,
}

impl ProgramBuilder {
    fn new() -> Self {
        Self { bindings: vec![] }
    }

    fn add_binding(&mut self, type_: Type, expr: Expr) -> LocalId {
        self.bindings.push((type_, expr, Metadata::default()));
        // 0 is reserved for function arguments, so we start at 1
        LocalId(self.bindings.len())
    }

    fn finish(mut self) -> Program {
        let result = self.add_binding(Type::Tuple(vec![]), Expr::Tuple(vec![]));
        let body = Expr::LetMany(self.bindings, result);

        let func = FuncDef {
            tail_funcs: IdVec::new(),
            tail_func_symbols: IdVec::new(),
            arg_type: Type::Tuple(vec![]),
            ret_type: Type::Tuple(vec![]),
            body,
            profile_point: None,
        };

        let mut funcs = IdVec::new();
        let _ = funcs.push(func);

        Program {
            mod_symbols: IdVec::new(),
            custom_types: CustomTypes {
                types: IdVec::new(),
            },
            custom_type_symbols: IdVec::new(),
            funcs,
            func_symbols: IdVec::new(),
            schemes: IdVec::new(),
            profile_points: IdVec::new(),
            main: CustomFuncId(0),
        }
    }

    fn build_output(&mut self, s: LocalId) {
        self.add_binding(
            Type::Tuple(vec![]),
            Expr::IoOp(IoOp::Output(
                ModeScheme::Array(Mode::Borrowed, Box::new(ModeScheme::Num(NumType::Byte))),
                s,
            )),
        );
    }

    fn build_string_lit(&mut self, s: &str) -> LocalId {
        let mut arr = self.add_binding(
            Type::Array(Box::new(Type::Num(NumType::Byte))),
            Expr::ArrayOp(
                ModeScheme::Array(Mode::Owned, Box::new(ModeScheme::Num(NumType::Byte))),
                ArrayOp::New,
            ),
        );

        for c in s.as_bytes() {
            let c_bound = self.add_binding(Type::Num(NumType::Byte), Expr::ByteLit(*c));
            arr = self.add_binding(
                Type::Array(Box::new(Type::Num(NumType::Byte))),
                Expr::ArrayOp(
                    ModeScheme::Array(Mode::Owned, Box::new(ModeScheme::Num(NumType::Byte))),
                    ArrayOp::Push(arr, c_bound),
                ),
            );
        }

        arr
    }
}

#[test]
fn test_print_hello() {
    let mut builder = ProgramBuilder::new();
    let s = builder.build_string_lit("Hello, world!");
    builder.build_output(s);

    let prog = builder.finish();
    let _child = super::run(Stdio::Piped, prog, &LlvmConfig::default(), None).unwrap();
}
