//! One error type for everything the compiler raises for a bad program.

use std::fmt;

/// The check classes of Stage A, and Stage B's.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProblemKind {
    Arity,
    Case,
    Data,
    Interface,
    SymbolTable,
    Scope,
    TypeMismatch,
}

impl ProblemKind {
    pub fn name(self) -> &'static str {
        match self {
            ProblemKind::Arity => "ArityError",
            ProblemKind::Case => "CaseError",
            ProblemKind::Data => "DataError",
            ProblemKind::Interface => "InterfaceError",
            ProblemKind::SymbolTable => "SymbolTableError",
            ProblemKind::Scope => "ScopeError",
            ProblemKind::TypeMismatch => "TypeMismatchError",
        }
    }
}

/// Where a problem is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Site {
    pub kind: String,
    pub name: String,
    pub core: Option<String>,
}

impl Site {
    pub fn new(kind: &str, name: &str) -> Site {
        Site { kind: kind.to_string(), name: name.to_string(), core: None }
    }
    pub fn in_core(kind: &str, name: &str, core: &str) -> Site {
        Site { kind: kind.to_string(), name: name.to_string(), core: Some(core.to_string()) }
    }
    /// A pre-formatted location (the checker's ``declare`` passes text).
    pub fn raw(text: &str) -> Site {
        Site { kind: text.to_string(), name: String::new(), core: None }
    }
}

impl fmt::Display for Site {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(c) = &self.core {
            return write!(f, "core {}, equation {}", c, self.name);
        }
        if self.name.is_empty() {
            write!(f, "{}", self.kind)
        } else {
            write!(f, "{} {}", self.kind, self.name)
        }
    }
}

#[derive(Debug, Clone)]
pub struct Problem {
    pub kind: ProblemKind,
    pub site: Site,
    pub message: String,
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} in {}: {}", self.kind.name(), self.site, self.message)
    }
}

#[derive(Debug, Clone)]
pub enum SkijackError {
    Lex(String),
    Parse(String),
    Check { kind: ProblemKind, message: String, problems: Vec<Problem> },
    Expand(String),
    Generate(String),
    Quote(String),
    Run(String),
    Probe(String),
    Dictionary(String),
}

impl SkijackError {
    pub fn class_name(&self) -> &'static str {
        match self {
            SkijackError::Lex(_) => "LexError",
            SkijackError::Parse(_) => "ParseError",
            SkijackError::Check { kind, .. } => kind.name(),
            SkijackError::Expand(_) => "ExpandError",
            SkijackError::Generate(_) => "GenerateError",
            SkijackError::Quote(_) => "QuoteError",
            SkijackError::Run(_) => "RunError",
            SkijackError::Probe(_) => "ProbeError",
            SkijackError::Dictionary(_) => "DictionaryError",
        }
    }
    pub fn message(&self) -> &str {
        match self {
            SkijackError::Lex(m)
            | SkijackError::Parse(m)
            | SkijackError::Expand(m)
            | SkijackError::Generate(m)
            | SkijackError::Quote(m)
            | SkijackError::Run(m)
            | SkijackError::Probe(m)
            | SkijackError::Dictionary(m) => m,
            SkijackError::Check { message, .. } => message,
        }
    }
    /// Stage A's ``check``: the first problem's class, every problem in the
    /// message.
    pub fn from_problems(stage: &str, problems: Vec<Problem>) -> SkijackError {
        let n = problems.len();
        let lines: Vec<String> = problems.iter().map(|p| format!("  {}", p)).collect();
        let message = format!(
            "{} {} problem{}:\n{}",
            n,
            stage,
            if n > 1 { "s" } else { "" },
            lines.join("\n")
        );
        SkijackError::Check { kind: problems[0].kind, message, problems }
    }
}

impl fmt::Display for SkijackError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message())
    }
}

impl std::error::Error for SkijackError {}

pub type Result<T> = std::result::Result<T, SkijackError>;

/// Python's ``repr`` of a string, which the messages quote names with.
pub fn repr(s: &str) -> String {
    let quote = if s.contains('\'') && !s.contains('"') { '"' } else { '\'' };
    let mut out = String::new();
    out.push(quote);
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if c == quote => {
                out.push('\\');
                out.push(c);
            }
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                out.push_str(&format!("\\x{:02x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push(quote);
    out
}
