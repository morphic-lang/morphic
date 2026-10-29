use crate::data::num_type::{NumLit, NumType};
use std::fmt;
use thiserror::Error;

#[derive(Clone, Copy, Debug, Error)]
#[error("Unrecognized token at position {0}")]
pub struct Error(pub usize);

#[derive(Clone, Debug)]
pub enum Token {
    UpperName(String),
    LowerName(String),
    NumLit(NumLit),
    StringLit(String),

    Type,
    Trait,
    Impl,
    Of,
    Where,
    Match,
    If,
    Else,
    Let,
    In,
    Proc,
    Do,
    Then,
    Module,
    Import,
    File,
    From,
    Expose,
    With,
    As,
    Pub,

    LParen,
    RParen,
    LSquare,
    RSquare,
    LCurly,
    RCurly,

    Comma,
    Colon,
    Equal,
    Arrow,
    BackSlash,
    Underscore,
    Dot,
    PipeLeft,
    PipeRight,
    Add,
    Sub,
    Mul,
    Div,
    Lt,
    Lte,
    Gt,
    Gte,

    Exclamation,
    DoubleAmp,
    DoubleBar,
    Amp,
    Bar,
    Caret,
    ShiftLeft,
    ShiftRight,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::UpperName(name) => write!(f, "{}", name),
            Token::LowerName(name) => write!(f, "{}", name),
            Token::NumLit(val) => write!(f, "{}", val),
            Token::StringLit(text) => write!(f, "{:?}", text),
            Token::Type => write!(f, "type"),
            Token::Trait => write!(f, "trait"),
            Token::Impl => write!(f, "impl"),
            Token::Of => write!(f, "of"),
            Token::Where => write!(f, "where"),
            Token::Match => write!(f, "match"),
            Token::If => write!(f, "if"),
            Token::Else => write!(f, "else"),
            Token::Let => write!(f, "let"),
            Token::In => write!(f, "in"),
            Token::Proc => write!(f, "proc"),
            Token::Do => write!(f, "do"),
            Token::Then => write!(f, "then"),
            Token::Module => write!(f, "module"),
            Token::Import => write!(f, "import"),
            Token::File => write!(f, "file"),
            Token::From => write!(f, "from"),
            Token::Expose => write!(f, "expose"),
            Token::With => write!(f, "with"),
            Token::As => write!(f, "as"),
            Token::Pub => write!(f, "pub"),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LSquare => write!(f, "["),
            Token::RSquare => write!(f, "]"),
            Token::LCurly => write!(f, "{{"),
            Token::RCurly => write!(f, "}}"),
            Token::Comma => write!(f, ","),
            Token::Colon => write!(f, ":"),
            Token::Equal => write!(f, "="),
            Token::Arrow => write!(f, "->"),
            Token::BackSlash => write!(f, "\\"),
            Token::Underscore => write!(f, "_"),
            Token::Dot => write!(f, "."),
            Token::Add => write!(f, "+"),
            Token::Sub => write!(f, "-"),
            Token::Mul => write!(f, "*"),
            Token::Div => write!(f, "/"),
            Token::Lt => write!(f, "<"),
            Token::Lte => write!(f, "<="),
            Token::Gt => write!(f, ">"),
            Token::Gte => write!(f, ">="),
            Token::Exclamation => write!(f, "!"),
            Token::DoubleAmp => write!(f, "&&"),
            Token::DoubleBar => write!(f, "||"),
            Token::Amp => write!(f, "&"),
            Token::Bar => write!(f, "|"),
            Token::Caret => write!(f, "^"),
            Token::ShiftLeft => write!(f, "<<"),
            Token::ShiftRight => write!(f, ">>"),
            Token::PipeLeft => write!(f, "<|"),
            Token::PipeRight => write!(f, "|>"),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Lexer<'a> {
    src: &'a str,
    pos: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Lexer { src, pos: 0 }
    }
}

// TODO: Optimize this
fn next_pos(mut pos: usize, src: &str) -> usize {
    pos += 1;

    if pos > src.len() {
        panic!("Lexer index out of range");
    }

    while !src.is_char_boundary(pos) {
        pos += 1;
    }

    pos
}

// TODO: Optimize this
fn char_at(src: &str, pos: usize) -> Option<char> {
    src[pos..].chars().nth(0)
}

fn consume_exact(pos: usize, src: &str, target: &str) -> Option<usize> {
    if src[pos..].starts_with(target) {
        Some(pos + target.len())
    } else {
        None
    }
}

fn consume_comment(mut pos: usize, src: &str) -> Option<usize> {
    pos = consume_exact(pos, src, "//")?;

    while let Some(c) = char_at(src, pos) {
        pos = next_pos(pos, src);
        if c == '\n' {
            break;
        }
    }

    Some(pos)
}

fn consume_whitespace(mut pos: usize, src: &str) -> Option<usize> {
    if !char_at(src, pos)?.is_whitespace() {
        return None;
    }

    while let Some(c) = char_at(src, pos) {
        if c.is_whitespace() {
            pos = next_pos(pos, src);
        } else {
            break;
        }
    }

    Some(pos)
}

fn skip_invisibles(mut pos: usize, src: &str) -> usize {
    loop {
        match (consume_comment(pos, src), consume_whitespace(pos, src)) {
            (None, None) => return pos,
            (Some(after_comment), _) => pos = after_comment,
            (_, Some(after_whitespace)) => pos = after_whitespace,
        }
    }
}

fn consume_name(mut pos: usize, src: &str) -> Option<usize> {
    if !char_at(src, pos)?.is_alphabetic() {
        return None;
    }

    while let Some(c) = char_at(src, pos) {
        if c.is_alphanumeric() || c == '_' {
            pos = next_pos(pos, src);
        } else {
            break;
        }
    }

    Some(pos)
}

fn consume_digits(mut pos: usize, src: &str) -> Option<usize> {
    if !char_at(src, pos)?.is_ascii_digit() {
        return None;
    }

    while let Some(c) = char_at(src, pos) {
        if c.is_ascii_digit() {
            pos = next_pos(pos, src);
        } else {
            break;
        }
    }

    Some(pos)
}

/// A number literal is digits, optionally a `.` and more digits, and optionally a suffix naming
/// its type, such as `u8`, `i32`, or `f32`.  Without a suffix, a literal with a fraction is an
/// `F64` and one without is an `I64`.  Given the end of the leading digits, returns the end of
/// the literal and its value, which is `None` if the text is not a literal of its type: a
/// fraction with an integer type, or a value out of the type's range.
fn lex_num_lit(start: usize, digits_end: usize, src: &str) -> (usize, Option<NumLit>) {
    let (num_end, has_frac) = match consume_exact(digits_end, src, ".") {
        Some(frac_start) => (consume_digits(frac_start, src).unwrap_or(frac_start), true),
        None => (digits_end, false),
    };
    let num = &src[start..num_end];

    const SUFFIXES: [(&str, NumType); 10] = [
        ("i8", NumType::I8),
        ("i16", NumType::I16),
        ("i32", NumType::I32),
        ("i64", NumType::I64),
        ("u8", NumType::U8),
        ("u16", NumType::U16),
        ("u32", NumType::U32),
        ("u64", NumType::U64),
        ("f32", NumType::F32),
        ("f64", NumType::F64),
    ];
    let (lit_end, type_) = match consume_one_of(num_end, src, &SUFFIXES) {
        Some((suffix_end, &type_)) => (suffix_end, type_),
        None if has_frac => (num_end, NumType::F64),
        None => (num_end, NumType::I64),
    };

    // An integer literal is parsed in its own type, so every value of the type can be written.
    let int = |parse: fn(&str) -> Option<NumLit>| if has_frac { None } else { parse(num) };
    let lit = match type_ {
        NumType::I8 => int(|num| num.parse().ok().map(NumLit::I8)),
        NumType::I16 => int(|num| num.parse().ok().map(NumLit::I16)),
        NumType::I32 => int(|num| num.parse().ok().map(NumLit::I32)),
        NumType::I64 => int(|num| num.parse().ok().map(NumLit::I64)),
        NumType::U8 => int(|num| num.parse().ok().map(NumLit::U8)),
        NumType::U16 => int(|num| num.parse().ok().map(NumLit::U16)),
        NumType::U32 => int(|num| num.parse().ok().map(NumLit::U32)),
        NumType::U64 => int(|num| num.parse().ok().map(NumLit::U64)),
        NumType::F32 => num.parse().ok().map(NumLit::F32),
        NumType::F64 => num.parse().ok().map(NumLit::F64),
    };
    (lit_end, lit)
}

fn consume_string_lit(mut pos: usize, src: &str) -> Option<(usize, String)> {
    if char_at(src, pos)? != '"' {
        return None;
    }

    pos = next_pos(pos, src);

    let mut result = String::new();

    while let Some(c) = char_at(src, pos) {
        pos = next_pos(pos, src);

        if c == '"' {
            return Some((pos, result));
        } else if c == '\\' {
            let escape_seq = char_at(src, pos)?;
            pos = next_pos(pos, src);

            let escaped = match escape_seq {
                't' => '\t',
                'r' => '\r',
                'n' => '\n',
                '\'' => '\'',
                '"' => '"',
                '\\' => '\\',
                _ => return None,
            };

            result.push(escaped);
        } else {
            result.push(c);
        }
    }

    None
}

fn consume_one_of<'a, T>(pos: usize, src: &str, cases: &'a [(&str, T)]) -> Option<(usize, &'a T)> {
    cases
        .iter()
        .filter_map(|(target, result)| consume_exact(pos, src, target).map(|end| (end, result)))
        .max_by_key(|&(end, _)| end)
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<(usize, Token, usize), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        self.pos = skip_invisibles(self.pos, self.src);

        if self.pos == self.src.len() {
            return None;
        }

        if let Some(name_end) = consume_name(self.pos, self.src) {
            let name_start = self.pos;
            self.pos = name_end;

            return match &self.src[name_start..name_end] {
                "type" => Some(Ok((name_start, Token::Type, name_end))),
                "trait" => Some(Ok((name_start, Token::Trait, name_end))),
                "impl" => Some(Ok((name_start, Token::Impl, name_end))),
                "of" => Some(Ok((name_start, Token::Of, name_end))),
                "where" => Some(Ok((name_start, Token::Where, name_end))),
                "match" => Some(Ok((name_start, Token::Match, name_end))),
                "if" => Some(Ok((name_start, Token::If, name_end))),
                "else" => Some(Ok((name_start, Token::Else, name_end))),
                "let" => Some(Ok((name_start, Token::Let, name_end))),
                "in" => Some(Ok((name_start, Token::In, name_end))),
                "proc" => Some(Ok((name_start, Token::Proc, name_end))),
                "do" => Some(Ok((name_start, Token::Do, name_end))),
                "then" => Some(Ok((name_start, Token::Then, name_end))),
                "module" => Some(Ok((name_start, Token::Module, name_end))),
                "import" => Some(Ok((name_start, Token::Import, name_end))),
                "file" => Some(Ok((name_start, Token::File, name_end))),
                "from" => Some(Ok((name_start, Token::From, name_end))),
                "expose" => Some(Ok((name_start, Token::Expose, name_end))),
                "with" => Some(Ok((name_start, Token::With, name_end))),
                "as" => Some(Ok((name_start, Token::As, name_end))),
                "pub" => Some(Ok((name_start, Token::Pub, name_end))),
                name => {
                    if char_at(name, 0).unwrap().is_uppercase() {
                        Some(Ok((
                            name_start,
                            Token::UpperName(name.to_owned()),
                            name_end,
                        )))
                    } else {
                        Some(Ok((
                            name_start,
                            Token::LowerName(name.to_owned()),
                            name_end,
                        )))
                    }
                }
            };
        }

        if let Some(digits_end) = consume_digits(self.pos, self.src) {
            let lit_start = self.pos;
            let (lit_end, lit) = lex_num_lit(lit_start, digits_end, self.src);
            self.pos = lit_end;

            return Some(match lit {
                Some(lit) => Ok((lit_start, Token::NumLit(lit), lit_end)),
                None => Err(Error(lit_start)),
            });
        }

        if let Some((string_end, string)) = consume_string_lit(self.pos, self.src) {
            let string_start = self.pos;
            self.pos = string_end;

            return Some(Ok((string_start, Token::StringLit(string), string_end)));
        }

        if let Some((sym_end, sym)) = consume_one_of(
            self.pos,
            self.src,
            &[
                // Delimiters
                ("(", Token::LParen),
                (")", Token::RParen),
                ("[", Token::LSquare),
                ("]", Token::RSquare),
                ("{", Token::LCurly),
                ("}", Token::RCurly),
                // Basic symbols
                (",", Token::Comma),
                (":", Token::Colon),
                ("=", Token::Equal),
                ("->", Token::Arrow),
                ("\\", Token::BackSlash),
                ("_", Token::Underscore),
                (".", Token::Dot),
                ("<|", Token::PipeLeft),
                ("|>", Token::PipeRight),
                // Arithmetic and comparison
                ("+", Token::Add),
                ("-", Token::Sub),
                ("*", Token::Mul),
                ("/", Token::Div),
                ("<", Token::Lt),
                ("<=", Token::Lte),
                (">", Token::Gt),
                (">=", Token::Gte),
                // Bool operators
                ("!", Token::Exclamation),
                ("&&", Token::DoubleAmp),
                ("||", Token::DoubleBar),
                // Bitwise operators
                ("&", Token::Amp),
                ("|", Token::Bar),
                ("^", Token::Caret),
                ("<<", Token::ShiftLeft),
                (">>", Token::ShiftRight),
            ],
        ) {
            let sym_start = self.pos;
            self.pos = sym_end;

            return Some(Ok((sym_start, sym.clone(), sym_end)));
        }

        return Some(Err(Error(self.pos)));
    }
}
