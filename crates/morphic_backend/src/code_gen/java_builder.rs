use std::io::Write;

const INDENT_WIDTH: u32 = 2;

pub struct Ident(pub String);

pub enum Visibility {
    Public,
    Protected,
    PackagePrivate,
    Private,
}

pub struct Enum {
    pub visibility: Visibility,
    pub name: Ident,
    pub members: Vec<Ident>,
}

pub struct Class {
    pub visibility: Visibility,
    pub is_static: bool,
    pub is_value: bool,
    pub name: Ident,
    pub fields: Vec<Field>,
}

pub struct Record {
    pub visibility: Visibility,
    pub is_static: bool,
    pub is_value: bool,
    pub name: Ident,
    pub data: Vec<Arg>,
}

pub enum Field {
    Data(Ident, Type),
    Method(Method),
    Class(Class),
    Record(Record),
}

pub struct Arg {
    pub name: Ident,
    pub ty: Type,
}

pub struct Method {
    pub is_static: bool,
    pub visibility: Visibility,
    pub name: Ident,
    pub args: Vec<Arg>,
    pub ret_ty: Option<Type>,
    pub body: Block,
}

pub enum Pat {
    IntLit(i64),
    FloatLit(f64),
    CharLit(char),
    StringLit(String),
    BoolLit(bool),
    EnumVariant(Ident, Ident),
}

pub enum Type {
    Reference(ReferenceType),
    Value(ValueType),
}

pub enum ReferenceType {
    ClassOrInterface(Ident),
    Array(Box<Type>),
}

pub enum ValueType {
    Boolean,
    Byte,
    Short,
    Int,
    Long,
    Char,
    Float,
    Double,
}

pub struct ExprCase {
    pub pat: Pat,
    pub expr: Box<Expr>,
}

pub struct Block(pub Vec<Stmt>);

pub struct DeclVar {
    pub name: Ident,
    pub ty: Type,
    pub value: Expr,
}

pub enum BinOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Neq,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Shl,
    Shr,
    BitNot,
    BitAnd,
    BitOr,
    BitXor,
}

pub enum Expr {
    Assign(Box<Expr>, Box<Expr>),
    Null,
    This,
    Super,
    Var(Ident),
    New(Type, Vec<Expr>),
    Cast(Type, Box<Expr>),
    InstanceOf(Box<Expr>, Type),
    ArrayAccess(Box<Expr>, Box<Expr>),
    Field(Box<Expr>, Ident),
    MethodCall(Box<Expr>, Ident, Vec<Expr>),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    Switch(Box<Expr>, Vec<ExprCase>, Option<Box<Expr>>),
    IntLit(i64),
    FloatLit(f64),
    CharLit(char),
    StringLit(String),
    BoolLit(bool),
}

pub struct StmtCase {
    pub pat: Pat,
    pub block: Block,
}

pub enum Stmt {
    DeclVar(DeclVar),
    If(Expr, Block, Option<Block>),
    While(Expr, Block),
    For(DeclVar, Expr, Expr, Block),
    Expr(Expr),
    Assert(Expr),
    Switch(Expr, Vec<StmtCase>, Option<Block>),
    Break,
    Continue,
    Return(Option<Expr>),
}

pub trait WriteTo {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error>;
}

pub struct WriteContext {
    indent_level: u32,
}

impl WriteContext {
    pub fn new() -> Self {
        Self { indent_level: 0 }
    }

    fn newline(&self) -> String {
        let mut newline = String::new();
        newline.push('\n');
        for _ in 0..self.indent_level * INDENT_WIDTH {
            newline.push(' ');
        }
        newline
    }

    fn write_line(&mut self, w: &mut impl Write) -> Result<(), std::io::Error> {
        w.write_all(b"\n")?;
        for _ in 0..self.indent_level * INDENT_WIDTH {
            w.write_all(b" ")?;
        }
        Ok(())
    }

    fn write_block<W: Write>(
        &mut self,
        w: &mut W,
        f: impl FnOnce(&mut Self, &mut W) -> Result<(), std::io::Error>,
    ) -> Result<(), std::io::Error> {
        w.write_all(b"{")?;

        let original = self.indent_level;
        self.indent_level += 1;
        self.write_line(w)?;

        f(self, w)?;

        self.indent_level = original;
        self.write_line(w)?;

        w.write_all(b"}")?;
        Ok(())
    }

    fn write_separated<'a, 'b, W, T, I>(
        &mut self,
        sep: &'a str,
        items: I,
        w: &mut W,
    ) -> Result<(), std::io::Error>
    where
        W: Write,
        T: WriteTo + 'b,
        I: Iterator<Item = &'b T>,
    {
        for (i, item) in items.enumerate() {
            if i > 0 {
                w.write_all(sep.as_bytes())?;
            }
            item.write_to(self, w)?;
        }
        Ok(())
    }
}

pub const KEYWORDS: &[&str] = &[
    // reserved keywords
    "abstract",
    "continue",
    "for",
    "new",
    "switch",
    "assert",
    "default",
    "if",
    "package",
    "synchronized",
    "boolean",
    "do",
    "goto",
    "private",
    "this",
    "break",
    "double",
    "implements",
    "protected",
    "throw",
    "byte",
    "else",
    "import",
    "public",
    "throws",
    "case",
    "enum",
    "instanceof",
    "return",
    "transient",
    "catch",
    "extends",
    "int",
    "short",
    "try",
    "char",
    "final",
    "interface",
    "static",
    "void",
    "class",
    "finally",
    "long",
    "strictfp",
    "volatile",
    "const",
    "float",
    "native",
    "super",
    "while",
    "_",
    // contextual keywords
    "exports",
    "opens",
    "requires",
    "uses",
    "yield",
    "module",
    "permits",
    "sealed",
    "var",
    "non-sealed",
    "provides",
    "to",
    "when",
    "open",
    "record",
    "transitive",
    "with",
];

impl WriteTo for Ident {
    fn write_to(&self, _ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        w.write_all(self.0.as_bytes())
    }
}

impl Visibility {
    fn write_to_with_space(
        &self,
        _ctx: &mut WriteContext,
        w: &mut impl Write,
    ) -> Result<(), std::io::Error> {
        match self {
            Visibility::Public => w.write_all(b"public "),
            Visibility::Protected => w.write_all(b"protected "),
            Visibility::PackagePrivate => Ok(()),
            Visibility::Private => w.write_all(b"private "),
        }
    }
}

impl WriteTo for Enum {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        self.visibility.write_to_with_space(ctx, w)?;
        w.write_all(b"enum ")?;
        self.name.write_to(ctx, w)?;
        w.write_all(b" ")?;

        ctx.write_block(w, |ctx, w| {
            let mut sep = ",".to_string();
            sep.push_str(&ctx.newline());

            ctx.write_separated(&sep, self.members.iter(), w)?;
            Ok(())
        })
    }
}

impl WriteTo for Class {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        self.visibility.write_to_with_space(ctx, w)?;
        if self.is_static {
            w.write_all(b"static ")?;
        }
        if self.is_value {
            w.write_all(b"value ")?;
        }
        w.write_all(b"class ")?;
        self.name.write_to(ctx, w)?;
        w.write_all(b" ")?;

        ctx.write_block(w, |ctx, w| {
            ctx.write_separated(&ctx.newline(), self.fields.iter(), w)?;
            Ok(())
        })
    }
}

impl WriteTo for Field {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        match self {
            Field::Data(name, ty) => {
                ty.write_to(ctx, w)?;
                w.write_all(b" ")?;
                name.write_to(ctx, w)?;
                w.write_all(b";")?;
                Ok(())
            }
            Field::Method(method) => method.write_to(ctx, w),
            Field::Class(class) => class.write_to(ctx, w),
            Field::Record(record) => record.write_to(ctx, w),
        }
    }
}

impl WriteTo for Record {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        self.visibility.write_to_with_space(ctx, w)?;
        if self.is_static {
            w.write_all(b"static ")?;
        }
        if self.is_value {
            w.write_all(b"value ")?;
        }
        w.write_all(b"record ")?;
        self.name.write_to(ctx, w)?;
        w.write_all(b"(")?;
        ctx.write_separated(", ", self.data.iter(), w)?;
        w.write_all(b") {}")?;
        Ok(())
    }
}

impl WriteTo for Arg {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        self.ty.write_to(ctx, w)?;
        w.write_all(b" ")?;
        self.name.write_to(ctx, w)
    }
}

impl WriteTo for Method {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        self.visibility.write_to_with_space(ctx, w)?;
        if self.is_static {
            w.write_all(b"static ")?;
        }

        if let Some(ret_ty) = &self.ret_ty {
            ret_ty.write_to(ctx, w)?;
            w.write_all(b" ")?;
        } else {
            w.write_all(b"void ")?;
        }

        self.name.write_to(ctx, w)?;

        w.write_all(b"(")?;
        ctx.write_separated(", ", self.args.iter(), w)?;
        w.write_all(b") ")?;

        self.body.write_to(ctx, w)?;
        Ok(())
    }
}

impl WriteTo for Pat {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        match self {
            Pat::IntLit(n) => write!(w, "{}", n),
            Pat::FloatLit(n) => write!(w, "{}", n),
            Pat::CharLit(c) => write!(w, "'{}'", c),
            Pat::StringLit(s) => write!(w, "\"{}\"", s),
            Pat::BoolLit(b) => write!(w, "{}", b),
            Pat::EnumVariant(ty, name) => {
                ty.write_to(ctx, w)?;
                w.write_all(b".")?;
                name.write_to(ctx, w)?;
                Ok(())
            }
        }
    }
}

impl WriteTo for Type {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        match self {
            Type::Reference(ty) => ty.write_to(ctx, w),
            Type::Value(ty) => ty.write_to(ctx, w),
        }
    }
}

impl WriteTo for ReferenceType {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        match self {
            ReferenceType::ClassOrInterface(name) => name.write_to(ctx, w),
            ReferenceType::Array(ty) => {
                ty.write_to(ctx, w)?;
                w.write_all(b"[]")?;
                Ok(())
            }
        }
    }
}

impl WriteTo for ValueType {
    fn write_to(&self, _ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        match self {
            ValueType::Boolean => w.write_all(b"boolean"),
            ValueType::Byte => w.write_all(b"byte"),
            ValueType::Short => w.write_all(b"short"),
            ValueType::Int => w.write_all(b"int"),
            ValueType::Long => w.write_all(b"long"),
            ValueType::Char => w.write_all(b"char"),
            ValueType::Float => w.write_all(b"float"),
            ValueType::Double => w.write_all(b"double"),
        }
    }
}

impl WriteTo for BinOp {
    fn write_to(&self, _ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        match self {
            BinOp::Lt => w.write_all(b"<"),
            BinOp::Le => w.write_all(b"<="),
            BinOp::Gt => w.write_all(b">"),
            BinOp::Ge => w.write_all(b">="),
            BinOp::Eq => w.write_all(b"=="),
            BinOp::Neq => w.write_all(b"!="),
            BinOp::Add => w.write_all(b"+"),
            BinOp::Sub => w.write_all(b"-"),
            BinOp::Mul => w.write_all(b"*"),
            BinOp::Div => w.write_all(b"/"),
            BinOp::Mod => w.write_all(b"%"),
            BinOp::Shl => w.write_all(b"<<"),
            BinOp::Shr => w.write_all(b">>"),
            BinOp::BitNot => w.write_all(b"~"),
            BinOp::BitAnd => w.write_all(b"&"),
            BinOp::BitOr => w.write_all(b"|"),
            BinOp::BitXor => w.write_all(b"^"),
        }
    }
}

impl WriteTo for ExprCase {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        w.write_all(b"case ")?;
        self.pat.write_to(ctx, w)?;
        w.write_all(b" -> (")?;
        self.expr.write_to(ctx, w)?;
        w.write_all(b")")?;
        Ok(())
    }
}

impl WriteTo for Expr {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        match self {
            Expr::Assign(lhs, rhs) => {
                lhs.write_to(ctx, w)?;
                w.write_all(b" = ")?;
                rhs.write_to(ctx, w)?;
                Ok(())
            }
            Expr::Null => w.write_all(b"null"),
            Expr::This => w.write_all(b"this"),
            Expr::Super => w.write_all(b"super"),
            Expr::Var(name) => name.write_to(ctx, w),
            Expr::New(ty, args) => {
                w.write_all(b"new ")?;
                ty.write_to(ctx, w)?;
                w.write_all(b"(")?;
                ctx.write_separated(", ", args.iter(), w)?;
                w.write_all(b")")?;
                Ok(())
            }
            Expr::Cast(ty, expr) => {
                w.write_all(b"(")?;
                ty.write_to(ctx, w)?;
                w.write_all(b") (")?;
                expr.write_to(ctx, w)?;
                w.write_all(b")")?;
                Ok(())
            }
            Expr::InstanceOf(expr, ty) => {
                w.write_all(b"(")?;
                expr.write_to(ctx, w)?;
                w.write_all(b") instanceof (")?;
                ty.write_to(ctx, w)?;
                w.write_all(b")")?;
                Ok(())
            }
            Expr::ArrayAccess(array, index) => {
                w.write_all(b"(")?;
                array.write_to(ctx, w)?;
                w.write_all(b") [")?;
                index.write_to(ctx, w)?;
                w.write_all(b"]")?;
                Ok(())
            }
            Expr::Field(obj, field) => {
                w.write_all(b"(")?;
                obj.write_to(ctx, w)?;
                w.write_all(b").")?;
                field.write_to(ctx, w)?;
                Ok(())
            }
            Expr::MethodCall(obj, method, args) => {
                w.write_all(b"(")?;
                obj.write_to(ctx, w)?;
                w.write_all(b").")?;
                method.write_to(ctx, w)?;
                w.write_all(b"(")?;
                ctx.write_separated(", ", args.iter(), w)?;
                w.write_all(b")")?;
                Ok(())
            }
            Expr::BinOp(op, lhs, rhs) => {
                w.write_all(b"(")?;
                lhs.write_to(ctx, w)?;
                w.write_all(b") ")?;
                op.write_to(ctx, w)?;
                w.write_all(b" (")?;
                rhs.write_to(ctx, w)?;
                w.write_all(b")")?;
                Ok(())
            }
            Expr::Switch(discrim, cases, default) => {
                w.write_all(b"switch (")?;
                discrim.write_to(ctx, w)?;
                w.write_all(b") ")?;

                ctx.write_block(w, |ctx, w| {
                    ctx.write_separated(&ctx.newline(), cases.iter(), w)?;

                    if let Some(default) = default {
                        if cases.len() > 0 {
                            ctx.write_line(w)?;
                        }
                        w.write_all(b"default: ")?;
                        default.write_to(ctx, w)?;
                    }

                    Ok(())
                })
            }
            Expr::IntLit(n) => write!(w, "{}", n),
            Expr::FloatLit(n) => write!(w, "{}", n),
            Expr::CharLit(c) => write!(w, "'{}'", c),
            Expr::StringLit(s) => write!(w, "\"{}\"", s),
            Expr::BoolLit(b) => write!(w, "{}", b),
        }
    }
}

impl WriteTo for Block {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        ctx.write_block(w, |ctx, w| {
            ctx.write_separated(&ctx.newline(), self.0.iter(), w)
        })
    }
}

impl WriteTo for DeclVar {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        self.ty.write_to(ctx, w)?;
        w.write_all(b" ")?;
        self.name.write_to(ctx, w)?;
        w.write_all(b" = ")?;
        self.value.write_to(ctx, w)?;
        Ok(())
    }
}

impl WriteTo for StmtCase {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        w.write_all(b"case ")?;
        self.pat.write_to(ctx, w)?;
        w.write_all(b": ")?;
        self.block.write_to(ctx, w)
    }
}

impl WriteTo for Stmt {
    fn write_to(&self, ctx: &mut WriteContext, w: &mut impl Write) -> Result<(), std::io::Error> {
        match self {
            Stmt::DeclVar(let_) => {
                let_.write_to(ctx, w)?;
                w.write_all(b";")?;
                Ok(())
            }
            Stmt::If(cond, then, else_) => {
                w.write_all(b"if (")?;
                cond.write_to(ctx, w)?;
                w.write_all(b") ")?;
                then.write_to(ctx, w)?;
                if let Some(else_block) = else_ {
                    w.write_all(b" else ")?;
                    else_block.write_to(ctx, w)?;
                }
                Ok(())
            }
            Stmt::While(cond, body) => {
                w.write_all(b"while (")?;
                cond.write_to(ctx, w)?;
                w.write_all(b") ")?;
                body.write_to(ctx, w)?;
                Ok(())
            }
            Stmt::For(init, cond, update, body) => {
                w.write_all(b"for (")?;
                init.write_to(ctx, w)?;
                w.write_all(b"; ")?;
                cond.write_to(ctx, w)?;
                w.write_all(b"; ")?;
                update.write_to(ctx, w)?;
                w.write_all(b") ")?;
                body.write_to(ctx, w)?;
                Ok(())
            }
            Stmt::Expr(expr) => {
                expr.write_to(ctx, w)?;
                w.write_all(b";")?;
                Ok(())
            }
            Stmt::Assert(cond) => {
                w.write_all(b"assert ")?;
                cond.write_to(ctx, w)?;
                w.write_all(b";")?;
                Ok(())
            }
            Stmt::Switch(discrim, cases, default) => {
                w.write_all(b"switch (")?;
                discrim.write_to(ctx, w)?;
                w.write_all(b") ")?;

                ctx.write_block(w, |ctx, w| {
                    ctx.write_separated(&ctx.newline(), cases.iter(), w)?;

                    if let Some(default_block) = default {
                        if cases.len() > 0 {
                            ctx.write_line(w)?;
                        }
                        w.write_all(b"default: ")?;
                        default_block.write_to(ctx, w)?;
                    }

                    Ok(())
                })
            }
            Stmt::Break => {
                w.write_all(b"break;")?;
                Ok(())
            }
            Stmt::Continue => {
                w.write_all(b"continue;")?;
                Ok(())
            }
            Stmt::Return(expr) => {
                w.write_all(b"return")?;
                if let Some(e) = expr {
                    w.write_all(b" ")?;
                    e.write_to(ctx, w)?;
                }
                w.write_all(b";")?;
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn to_string<T: WriteTo>(x: &T) -> String {
        let mut out = Vec::new();
        let mut ctx = WriteContext::new();
        x.write_to(&mut ctx, &mut out).unwrap();
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn test_expr_stmt() {
        let stmt = Stmt::Expr(Expr::IntLit(42));
        assert_eq!(to_string(&stmt), "42;");
    }

    #[test]
    fn test_assert() {
        let stmt = Stmt::Assert(Expr::BoolLit(true));
        assert_eq!(to_string(&stmt), "assert true;");
    }

    #[test]
    fn test_return() {
        let stmt = Stmt::Return(Some(Expr::IntLit(1)));
        assert_eq!(to_string(&stmt), "return 1;");

        let stmt = Stmt::Return(None);
        assert_eq!(to_string(&stmt), "return;");
    }

    #[test]
    fn test_main_class() {
        let class = Class {
            visibility: Visibility::Public,
            is_static: false,
            is_value: false,
            name: Ident("Main".to_string()),
            fields: vec![Field::Method(Method {
                is_static: true,
                visibility: Visibility::Public,
                name: Ident("main".to_string()),
                args: vec![Arg {
                    name: Ident("args".to_string()),
                    ty: Type::Reference(ReferenceType::Array(Box::new(Type::Reference(
                        ReferenceType::ClassOrInterface(Ident("String".to_string())),
                    )))),
                }],
                ret_ty: None,
                body: Block(vec![Stmt::Expr(Expr::MethodCall(
                    Box::new(Expr::Field(
                        Box::new(Expr::Var(Ident("System".to_string()))),
                        Ident("out".to_string()),
                    )),
                    Ident("println".to_string()),
                    vec![Expr::StringLit("Hello, World!".to_string())],
                ))]),
            })],
        };

        let expected = r#"public class Main {
  public static void main(String[] args) {
    ((System).out).println("Hello, World!");
  }
}"#;

        let mut out = Vec::new();
        let mut ctx = WriteContext::new();
        class.write_to(&mut ctx, &mut out).unwrap();
        assert_eq!(String::from_utf8(out).unwrap(), expected);
    }

    #[test]
    fn test_switch_enum() {
        let enum_ = Enum {
            visibility: Visibility::Public,
            name: Ident("Color".to_string()),
            members: vec![
                Ident("Red".to_string()),
                Ident("Green".to_string()),
                Ident("Blue".to_string()),
            ],
        };

        let expected = r#"public enum Color {
  Red,
  Green,
  Blue
}"#;
        assert_eq!(to_string(&enum_), expected);

        let stmt = Stmt::Switch(
            Expr::Var(Ident("color".to_string())),
            vec![
                StmtCase {
                    pat: Pat::EnumVariant(Ident("Color".to_string()), Ident("Red".to_string())),
                    block: Block(vec![Stmt::Expr(Expr::IntLit(1))]),
                },
                StmtCase {
                    pat: Pat::EnumVariant(Ident("Color".to_string()), Ident("Green".to_string())),
                    block: Block(vec![Stmt::Expr(Expr::IntLit(2))]),
                },
                StmtCase {
                    pat: Pat::EnumVariant(Ident("Color".to_string()), Ident("Blue".to_string())),
                    block: Block(vec![Stmt::Expr(Expr::IntLit(3))]),
                },
            ],
            None,
        );

        let expected = r#"switch (color) {
  case Color.Red: {
    1;
  }
  case Color.Green: {
    2;
  }
  case Color.Blue: {
    3;
  }
}"#;

        assert_eq!(to_string(&stmt), expected);
    }
}
