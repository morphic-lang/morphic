use std::fmt;
use thiserror::Error;

#[derive(Clone, Copy, Debug, Error)]
#[error("Unrecognized token at position {0}")]
pub struct Error(pub usize);

#[derive(Clone, Debug)]
pub enum Token {
    UpperName(String),
    LowerName(String),
    FloatLit(f64),
    ByteLit(u8),
    IntLit(i64),
    StringLit(String),

    Type,
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

    AddAmp,
    SubAmp,
    MulAmp,
    DivAmp,
    EqualAmp,
    LtAmp,
    LteAmp,
    GtAmp,
    GteAmp,
    Add,
    Sub,
    Mul,
    Div,
    Lt,
    Lte,
    Gt,
    Gte,
    AddDot,
    SubDot,
    MulDot,
    DivDot,
    EqualDot,
    LtDot,
    LteDot,
    GtDot,
    GteDot,

    Exclamation,
    DoubleAmp,
    DoubleBar,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::UpperName(name) => write!(f, "{}", name),
            Token::LowerName(name) => write!(f, "{}", name),
            Token::FloatLit(val) => write!(f, "{}", val),
            Token::ByteLit(val) => write!(f, "{}", val),
            Token::IntLit(val) => write!(f, "{}", val),
            Token::StringLit(text) => write!(f, "{:?}", text),
            Token::Type => write!(f, "type"),
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
            Token::EqualAmp => write!(f, "=&"),
            Token::AddAmp => write!(f, "+&"),
            Token::SubAmp => write!(f, "-&"),
            Token::MulAmp => write!(f, "*&"),
            Token::DivAmp => write!(f, "/&"),
            Token::LtAmp => write!(f, "<&"),
            Token::LteAmp => write!(f, "<=&"),
            Token::GtAmp => write!(f, ">&"),
            Token::GteAmp => write!(f, ">=&"),
            Token::Add => write!(f, "+"),
            Token::Sub => write!(f, "-"),
            Token::Mul => write!(f, "*"),
            Token::Div => write!(f, "/"),
            Token::Lt => write!(f, "<"),
            Token::Lte => write!(f, "<="),
            Token::Gt => write!(f, ">"),
            Token::Gte => write!(f, ">="),
            Token::AddDot => write!(f, "+."),
            Token::SubDot => write!(f, "-."),
            Token::MulDot => write!(f, "*."),
            Token::DivDot => write!(f, "/."),
            Token::EqualDot => write!(f, "=."),
            Token::LtDot => write!(f, "<."),
            Token::LteDot => write!(f, "<=."),
            Token::GtDot => write!(f, ">."),
            Token::GteDot => write!(f, ">=."),
            Token::Exclamation => write!(f, "!"),
            Token::DoubleAmp => write!(f, "&&"),
            Token::DoubleBar => write!(f, "||"),
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

fn consume_byte(mut pos: usize, src: &str) -> Option<usize> {
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

    pos = consume_exact(pos, src, "b")?;

    Some(pos)
}

fn consume_int(mut pos: usize, src: &str) -> Option<usize> {
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

fn consume_float(pos: usize, src: &str) -> Option<usize> {
    let whole_end = consume_int(pos, src)?;

    let frac_start = consume_exact(whole_end, src, ".")?;

    if let Some(frac_end) = consume_int(frac_start, src) {
        Some(frac_end)
    } else {
        Some(frac_start)
    }
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

        if let Some(float_end) = consume_float(self.pos, self.src) {
            let float_start = self.pos;
            self.pos = float_end;

            return Some(Ok((
                float_start,
                Token::FloatLit(self.src[float_start..float_end].parse().unwrap()),
                float_end,
            )));
        }

        if let Some(byte_end) = consume_byte(self.pos, self.src) {
            let byte_start = self.pos;
            self.pos = byte_end;

            debug_assert!(byte_start < byte_end);

            return Some(Ok((
                byte_start,
                // `- 1` strips trailing 'b'
                Token::ByteLit(self.src[byte_start..byte_end - 1].parse().unwrap()),
                byte_end,
            )));
        }

        if let Some(int_end) = consume_int(self.pos, self.src) {
            let int_start = self.pos;
            self.pos = int_end;

            return Some(Ok((
                int_start,
                Token::IntLit(self.src[int_start..int_end].parse().unwrap()),
                int_end,
            )));
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
                // Byte arithmetic
                ("+&", Token::AddAmp),
                ("-&", Token::SubAmp),
                ("*&", Token::MulAmp),
                ("/&", Token::DivAmp),
                ("=&", Token::EqualAmp),
                ("<&", Token::LtAmp),
                ("<=&", Token::LteAmp),
                (">&", Token::GtAmp),
                (">=&", Token::GteAmp),
                // Int arithmetic
                ("+", Token::Add),
                ("-", Token::Sub),
                ("*", Token::Mul),
                ("/", Token::Div),
                ("<", Token::Lt),
                ("<=", Token::Lte),
                (">", Token::Gt),
                (">=", Token::Gte),
                // Float arithmetic
                ("+.", Token::AddDot),
                ("-.", Token::SubDot),
                ("*.", Token::MulDot),
                ("/.", Token::DivDot),
                ("=.", Token::EqualDot),
                ("<.", Token::LtDot),
                ("<=.", Token::LteDot),
                (">.", Token::GtDot),
                (">=.", Token::GteDot),
                // Bool operators
                ("!", Token::Exclamation),
                ("&&", Token::DoubleAmp),
                ("||", Token::DoubleBar),
            ],
        ) {
            let sym_start = self.pos;
            self.pos = sym_end;

            return Some(Ok((sym_start, sym.clone(), sym_end)));
        }

        return Some(Err(Error(self.pos)));
    }
}
