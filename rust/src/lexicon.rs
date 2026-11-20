//! The token table of ``SYNTAX.md`` §2, as data, plus the two lexers.

use std::fmt;

use crate::errors::{repr, Result, SkijackError};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Kind {
    Macro,
    CMacro,
    TypeDecl,
    NsOpen,
    Scry,
    Case,
    Turnstile,
    Assign,
    MapsTo,
    Arrow,
    Colon,
    Equals,
    Alt,
    QOpen,
    QClose,
    Lambda,
    Dot,
    Semi,
    Comma,
    Slash,
    LParen,
    RParen,
    LBrack,
    RBrack,
    LBrace,
    RBrace,
    Ident,
    Number,
    Axis,
    Fuel,
    Newline,
    Eof,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Kind::Macro => "MACRO",
            Kind::CMacro => "CMACRO",
            Kind::TypeDecl => "TYPEDECL",
            Kind::NsOpen => "NSOPEN",
            Kind::Scry => "SCRY",
            Kind::Case => "CASE",
            Kind::Turnstile => "TURNSTILE",
            Kind::Assign => "ASSIGN",
            Kind::MapsTo => "MAPSTO",
            Kind::Arrow => "ARROW",
            Kind::Colon => "COLON",
            Kind::Equals => "EQUALS",
            Kind::Alt => "ALT",
            Kind::QOpen => "QOPEN",
            Kind::QClose => "QCLOSE",
            Kind::Lambda => "LAMBDA",
            Kind::Dot => "DOT",
            Kind::Semi => "SEMI",
            Kind::Comma => "COMMA",
            Kind::Slash => "SLASH",
            Kind::LParen => "LPAREN",
            Kind::RParen => "RPAREN",
            Kind::LBrack => "LBRACK",
            Kind::RBrack => "RBRACK",
            Kind::LBrace => "LBRACE",
            Kind::RBrace => "RBRACE",
            Kind::Ident => "IDENT",
            Kind::Number => "NUMBER",
            Kind::Axis => "AXIS",
            Kind::Fuel => "FUEL",
            Kind::Newline => "NEWLINE",
            Kind::Eof => "EOF",
        };
        f.write_str(s)
    }
}

pub struct Row {
    pub meaning: &'static str,
    pub kind: Kind,
    pub ascii: &'static str,
    pub unicode: &'static str,
    pub structural: bool,
}

const fn row(meaning: &'static str, kind: Kind, ascii: &'static str, unicode: &'static str) -> Row {
    Row { meaning, kind, ascii, unicode, structural: true }
}

const fn glyph(meaning: &'static str, ascii: &'static str, unicode: &'static str) -> Row {
    Row { meaning, kind: Kind::Ident, ascii, unicode, structural: false }
}

pub static TOKEN_TABLE: &[Row] = &[
    row("macro definition", Kind::Macro, ":=*", "≔*"),
    row("capturing macro", Kind::CMacro, ":=!", "≔!"),
    row("type declaration", Kind::TypeDecl, "===", "≡"),
    row("namespace literal open", Kind::NsOpen, "ns{", "ns{"),
    row("scry", Kind::Scry, "?^", "∵"),
    row("case", Kind::Case, "|>", "▹"),
    row("interpreter selection", Kind::Turnstile, "|-", "⊢"),
    row("definition", Kind::Assign, ":=", "≔"),
    row("fact", Kind::MapsTo, "=>", "↦"),
    row("signature arrow", Kind::Arrow, "->", "→"),
    row("signature colon", Kind::Colon, ":", ":"),
    row("equation", Kind::Equals, "=", "="),
    row("type alternative", Kind::Alt, "|", "|"),
    row("quotation open", Kind::QOpen, "<", "<"),
    row("quotation close", Kind::QClose, ">", ">"),
    row("lambda", Kind::Lambda, "\\", "λ"),
    row("name qualifier", Kind::Dot, ".", "."),
    row("branch separator", Kind::Semi, ";", ";"),
    row("fact separator", Kind::Comma, ",", ","),
    row("path separator", Kind::Slash, "/", "/"),
    row("group open", Kind::LParen, "(", "("),
    row("group close", Kind::RParen, ")", ")"),
    row("cell open", Kind::LBrack, "[", "["),
    row("cell close", Kind::RBrack, "]", "]"),
    row("block open", Kind::LBrace, "{", "{"),
    row("block close", Kind::RBrace, "}", "}"),
    glyph("composition (B)", "B", "∘"),
    glyph("swap (C)", "C", "⇄"),
    glyph("duplicate (W)", "W", "⋈"),
    glyph("fixpoint (Y)", "Y", "Υ"),
    glyph("equality on data", "EQ", "≟"),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lexicon {
    Ascii,
    Unicode,
}

impl Lexicon {
    pub fn parse(s: &str) -> Option<Lexicon> {
        match s {
            "ascii" => Some(Lexicon::Ascii),
            "unicode" => Some(Lexicon::Unicode),
            _ => None,
        }
    }
    pub fn comment(self) -> &'static str {
        match self {
            Lexicon::Ascii => "--",
            Lexicon::Unicode => "⍝",
        }
    }
    pub fn axis_mark(self) -> &'static str {
        match self {
            Lexicon::Ascii => "@",
            Lexicon::Unicode => "⊑",
        }
    }
}

impl fmt::Display for Lexicon {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Lexicon::Ascii => "ascii",
            Lexicon::Unicode => "unicode",
        })
    }
}

/// The spelling of a structural token kind in a lexicon.
pub fn spelling(kind: Kind, lx: Lexicon) -> &'static str {
    for r in TOKEN_TABLE {
        if r.structural && r.kind == kind {
            return match lx {
                Lexicon::Ascii => r.ascii,
                Lexicon::Unicode => r.unicode,
            };
        }
    }
    panic!("no spelling for {}", kind)
}

/// Unicode glyph of a Tier 1 name, if it has one.
pub fn glyph_of(name: &str) -> Option<&'static str> {
    TOKEN_TABLE.iter().find(|r| !r.structural && r.ascii == name).map(|r| r.unicode)
}

fn glyph_to_name(c: char) -> Option<&'static str> {
    let mut buf = [0u8; 4];
    let s: &str = c.encode_utf8(&mut buf);
    TOKEN_TABLE.iter().find(|r| !r.structural && r.unicode == s).map(|r| r.ascii)
}

/// (spelling, kind) in the order the lexer tries them: longest first.
fn ordered(lx: Lexicon) -> Vec<(&'static str, Kind)> {
    let mut out: Vec<(&'static str, Kind)> = TOKEN_TABLE
        .iter()
        .filter(|r| r.structural)
        .map(|r| (match lx {
            Lexicon::Ascii => r.ascii,
            Lexicon::Unicode => r.unicode,
        }, r.kind))
        .collect();
    out.sort_by_key(|(sp, _)| std::cmp::Reverse(sp.chars().count()));
    out
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Text(String),
    Num(u64),
    Policy,
    None,
}

impl Value {
    /// Python's ``repr`` of the value, for messages.
    pub fn repr(&self) -> String {
        match self {
            Value::Text(s) => repr(s),
            Value::Num(n) => n.to_string(),
            Value::Policy => "'policy'".to_string(),
            Value::None => "None".to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: Kind,
    pub value: Value,
    pub line: usize,
    pub col: usize,
}

impl Token {
    pub fn text(&self) -> &str {
        match &self.value {
            Value::Text(s) => s,
            _ => panic!("{} token at {}:{} carries no text", self.kind, self.line, self.col),
        }
    }
    pub fn number(&self) -> u64 {
        match &self.value {
            Value::Num(n) => *n,
            _ => panic!("{} token at {}:{} carries no number", self.kind, self.line, self.col),
        }
    }
}

fn is_sub_digit(c: char) -> bool {
    ('\u{2080}'..='\u{2089}').contains(&c)
}

fn desub(c: char) -> char {
    if is_sub_digit(c) {
        char::from_u32('0' as u32 + (c as u32 - 0x2080)).unwrap()
    } else {
        c
    }
}

fn ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn ident_cont(c: char, lx: Lexicon) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\'' || (lx == Lexicon::Unicode && is_sub_digit(c))
}

fn starts_with(text: &[char], i: usize, s: &str) -> bool {
    let mut j = i;
    for c in s.chars() {
        if j >= text.len() || text[j] != c {
            return false;
        }
        j += 1;
    }
    true
}

fn parse_digits(digits: &[char]) -> u64 {
    let s: String = digits.iter().map(|&c| desub(c)).collect();
    s.parse::<u64>().unwrap_or(u64::MAX)
}

/// Tokenize ``text`` in ``lexicon``.
pub fn lex(text: &str, lx: Lexicon) -> Result<Vec<Token>> {
    let ops = ordered(lx);
    let comment = lx.comment();
    let chars: Vec<char> = text.chars().collect();
    let n = chars.len();
    let mut out: Vec<Token> = Vec::new();
    let (mut i, mut line, mut bol) = (0usize, 1usize, 0usize);
    while i < n {
        let c = chars[i];
        let col = i - bol + 1;
        if c == '\n' {
            if out.last().map(|t| t.kind != Kind::Newline).unwrap_or(false) {
                out.push(Token { kind: Kind::Newline, value: Value::Text("\n".into()), line, col });
            }
            i += 1;
            line += 1;
            bol = i;
            continue;
        }
        if c == ' ' || c == '\t' || c == '\r' {
            i += 1;
            continue;
        }
        if starts_with(&chars, i, comment) {
            while i < n && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        // axis: digits followed by the axis mark
        if c.is_ascii_digit() {
            let mut j = i;
            while j < n && chars[j].is_ascii_digit() {
                j += 1;
            }
            if starts_with(&chars, j, lx.axis_mark()) {
                let v = parse_digits(&chars[i..j]);
                out.push(Token { kind: Kind::Axis, value: Value::Num(v), line, col });
                i = j + lx.axis_mark().chars().count();
                continue;
            }
        }
        // fuel
        match lx {
            Lexicon::Ascii => {
                if c == '@' {
                    if starts_with(&chars, i + 1, "[]") {
                        out.push(Token { kind: Kind::Fuel, value: Value::Policy, line, col });
                        i += 3;
                        continue;
                    }
                    let mut j = i + 1;
                    while j < n && chars[j].is_ascii_digit() {
                        j += 1;
                    }
                    if j > i + 1 {
                        let v = parse_digits(&chars[i + 1..j]);
                        out.push(Token { kind: Kind::Fuel, value: Value::Num(v), line, col });
                        i = j;
                        continue;
                    }
                }
            }
            Lexicon::Unicode => {
                if is_sub_digit(c) {
                    let mut j = i;
                    while j < n && is_sub_digit(chars[j]) {
                        j += 1;
                    }
                    let v = parse_digits(&chars[i..j]);
                    out.push(Token { kind: Kind::Fuel, value: Value::Num(v), line, col });
                    i = j;
                    continue;
                }
                if c == '\u{208D}' && i + 1 < n && chars[i + 1] == '\u{208E}' {
                    out.push(Token { kind: Kind::Fuel, value: Value::Policy, line, col });
                    i += 2;
                    continue;
                }
            }
        }
        if lx == Lexicon::Unicode {
            if let Some(name) = glyph_to_name(c) {
                out.push(Token { kind: Kind::Ident, value: Value::Text(name.to_string()), line, col });
                i += 1;
                continue;
            }
        }
        let mut hit = None;
        for (sp, kind) in &ops {
            if starts_with(&chars, i, sp) {
                hit = Some((*sp, *kind));
                break;
            }
        }
        if let Some((sp, kind)) = hit {
            out.push(Token { kind, value: Value::Text(sp.to_string()), line, col });
            i += sp.chars().count();
            continue;
        }
        if ident_start(c) {
            let mut j = i + 1;
            while j < n && ident_cont(chars[j], lx) {
                j += 1;
            }
            let s: String = chars[i..j].iter().map(|&c| desub(c)).collect();
            out.push(Token { kind: Kind::Ident, value: Value::Text(s), line, col });
            i = j;
            continue;
        }
        if c.is_ascii_digit() {
            let mut j = i;
            while j < n && chars[j].is_ascii_digit() {
                j += 1;
            }
            let v = parse_digits(&chars[i..j]);
            out.push(Token { kind: Kind::Number, value: Value::Num(v), line, col });
            i = j;
            continue;
        }
        return Err(SkijackError::Lex(format!(
            "line {}, column {}: unexpected character {}",
            line,
            col,
            repr(&c.to_string())
        )));
    }
    if out.last().map(|t| t.kind != Kind::Newline).unwrap_or(false) {
        out.push(Token { kind: Kind::Newline, value: Value::Text("\n".into()), line, col: i - bol + 1 });
    }
    out.push(Token { kind: Kind::Eof, value: Value::None, line, col: i - bol + 1 });
    Ok(out)
}
