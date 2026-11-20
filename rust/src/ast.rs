//! The lexicon-free syntax tree.  Trees compare structurally, so the ASCII
//! and Unicode spellings of one program parse to equal values.

use std::rc::Rc;

pub type E = Rc<Expr>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Fuel {
    N(u64),
    /// fuel elided, to be supplied by the runtime's policy: ``@[]`` / ``₍₎``
    Policy,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Seg {
    pub tag: String,
    pub payload: Option<E>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Path {
    pub segments: Vec<Seg>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Branch {
    pub ctor: String,
    pub binders: Vec<String>,
    pub body: E,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Name(String),
    App(E, E),
    Cell(Vec<E>),
    Quote { expr: E, fuel: Option<Fuel>, interp: Option<E> },
    Scry(Path),
    Pick { axis: u64, expr: E },
    Lambda { param: String, body: E },
    Case { scrutinee: E, branches: Vec<Branch> },
    NsLit(Vec<(Path, E)>),
}

pub fn name(n: &str) -> E {
    Rc::new(Expr::Name(n.to_string()))
}

pub fn app(f: E, a: E) -> E {
    Rc::new(Expr::App(f, a))
}

pub fn lambda(param: &str, body: E) -> E {
    Rc::new(Expr::Lambda { param: param.to_string(), body })
}

/// (head, args) of an application chain.
pub fn spine(e: &E) -> (E, Vec<E>) {
    let mut args = Vec::new();
    let mut cur = e.clone();
    while let Expr::App(f, a) = &*cur {
        args.push(a.clone());
        let next = f.clone();
        cur = next;
    }
    args.reverse();
    (cur, args)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ctor {
    pub name: String,
    pub fields: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeDecl {
    pub name: String,
    pub ctors: Vec<Ctor>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Equation {
    pub name: String,
    pub binders: Vec<String>,
    pub body: E,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Core {
    pub name: String,
    pub equations: Vec<Equation>,
    pub params: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Macro {
    pub name: String,
    pub params: Vec<String>,
    pub body: E,
    pub capturing: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Decl {
    Type(TypeDecl),
    Sig { name: String, types: Vec<String> },
    Equation(Equation),
    Core(Core),
    Macro(Macro),
    Def { name: String, expr: E },
}

impl Decl {
    pub fn name(&self) -> &str {
        match self {
            Decl::Type(t) => &t.name,
            Decl::Sig { name, .. } => name,
            Decl::Equation(e) => &e.name,
            Decl::Core(c) => &c.name,
            Decl::Macro(m) => &m.name,
            Decl::Def { name, .. } => name,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Program {
    pub decls: Vec<Decl>,
}
