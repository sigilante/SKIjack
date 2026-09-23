//! One grammar over token kinds; both lexers feed it.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::{self as A, Expr, E};
use crate::errors::{repr, Result, SkijackError};
use crate::lexicon::{lex, Kind, Lexicon, Token, Value};

/// constructor name -> (type name, declaration index, arity)
pub type CtorTable = HashMap<String, (String, usize, usize)>;

fn perr(msg: String) -> SkijackError {
    SkijackError::Parse(msg)
}

const ATOM_START: &[Kind] = &[
    Kind::Ident,
    Kind::LParen,
    Kind::LBrack,
    Kind::QOpen,
    Kind::Scry,
    Kind::Axis,
    Kind::Lambda,
    Kind::NsOpen,
    Kind::Number,
];

const DECL_OPS: &[Kind] = &[Kind::TypeDecl, Kind::Colon, Kind::Assign, Kind::Macro, Kind::CMacro, Kind::Equals];

/// Pass one: constructor name -> (type name, declaration index, arity).
pub fn collect_ctors(tokens: &[Token]) -> Result<CtorTable> {
    let mut table = CtorTable::new();
    for (i, tok) in tokens.iter().enumerate() {
        if tok.kind != Kind::TypeDecl {
            continue;
        }
        if i == 0 || tokens[i - 1].kind != Kind::Ident {
            return Err(perr(format!("line {}: type declaration needs a name on its left", tok.line)));
        }
        let tname = tokens[i - 1].text().to_string();
        let mut j = i + 1;
        let mut groups: Vec<Vec<String>> = vec![vec![]];
        while !matches!(tokens[j].kind, Kind::Newline | Kind::Eof) {
            let t = &tokens[j];
            match t.kind {
                Kind::Alt => groups.push(vec![]),
                Kind::Ident => groups.last_mut().unwrap().push(t.text().to_string()),
                k => {
                    return Err(perr(format!(
                        "line {}: unexpected {} in the declaration of type {}",
                        t.line,
                        k,
                        repr(&tname)
                    )))
                }
            }
            j += 1;
        }
        for (idx, g) in groups.iter().enumerate() {
            if g.is_empty() {
                return Err(perr(format!("line {}: empty constructor in type {}", tok.line, repr(&tname))));
            }
            let cname = &g[0];
            if table.contains_key(cname) {
                return Err(perr(format!("constructor {} declared twice", repr(cname))));
            }
            table.insert(cname.clone(), (tname.clone(), idx, g.len() - 1));
        }
    }
    Ok(table)
}

/// A guard against pathological nesting, so the parser fails with a located
/// message rather than exhausting the stack.
const MAX_NESTING: usize = 20_000;

struct Parser<'t> {
    toks: &'t [Token],
    i: usize,
    ctors: CtorTable,
    depth: usize,
    nesting: usize,
}

impl<'t> Parser<'t> {
    fn tok(&self, j: usize) -> &'t Token {
        if j < self.toks.len() {
            &self.toks[j]
        } else {
            &self.toks[self.toks.len() - 1]
        }
    }

    fn peek(&self) -> &'t Token {
        let mut j = self.i;
        loop {
            let t = self.tok(j);
            if t.kind == Kind::Newline && self.depth > 0 {
                j += 1;
                continue;
            }
            return t;
        }
    }

    fn next(&mut self) -> &'t Token {
        while self.tok(self.i).kind == Kind::Newline && self.depth > 0 {
            self.i += 1;
        }
        let t = self.tok(self.i);
        self.i += 1;
        t
    }

    fn expect(&mut self, kind: Kind) -> Result<&'t Token> {
        let t = self.next();
        if t.kind != kind {
            return Err(perr(format!(
                "line {}, column {}: expected {}, got {} {}",
                t.line,
                t.col,
                kind,
                t.kind,
                t.value.repr()
            )));
        }
        Ok(t)
    }

    fn skip_newlines(&mut self) {
        while self.tok(self.i).kind == Kind::Newline {
            self.i += 1;
        }
    }

    fn end_of_decl(&self, also: &[Kind]) -> Result<()> {
        let t = self.tok(self.i);
        if matches!(t.kind, Kind::Newline | Kind::Eof) || also.contains(&t.kind) {
            return Ok(());
        }
        Err(perr(format!(
            "line {}, column {}: unexpected {} {} at the end of a declaration",
            t.line,
            t.col,
            t.kind,
            t.value.repr()
        )))
    }

    fn enter(&mut self) -> Result<()> {
        self.nesting += 1;
        if self.nesting > MAX_NESTING {
            return Err(perr("expression nests too deeply for this compiler".to_string()));
        }
        Ok(())
    }

    fn leave(&mut self) {
        self.nesting -= 1;
    }

    // --- program ---------------------------------------------------------

    fn program(&mut self) -> Result<A::Program> {
        let mut decls = Vec::new();
        loop {
            self.skip_newlines();
            if self.tok(self.i).kind == Kind::Eof {
                break;
            }
            decls.push(self.decl()?);
        }
        Ok(A::Program { decls })
    }

    fn decl(&mut self) -> Result<A::Decl> {
        let (names, op) = self.lookahead_head();
        match op {
            Some(Kind::TypeDecl) => self.type_decl(names),
            Some(Kind::Colon) => self.sig(names),
            Some(Kind::Assign) => self.core_or_def(names),
            Some(Kind::Macro) => self.macro_decl(names, false),
            Some(Kind::CMacro) => self.macro_decl(names, true),
            Some(Kind::Equals) => self.equation(names, &[]).map(A::Decl::Equation),
            _ => {
                let t = self.tok(self.i);
                Err(perr(format!(
                    "line {}, column {}: not a declaration (expected one of :=, :=*, :=!, =, ===, :)",
                    t.line, t.col
                )))
            }
        }
    }

    fn lookahead_head(&self) -> (Vec<String>, Option<Kind>) {
        let mut j = self.i;
        let mut names = Vec::new();
        while self.tok(j).kind == Kind::Ident {
            names.push(self.tok(j).text().to_string());
            j += 1;
        }
        let kind = self.tok(j).kind;
        if names.is_empty() || !DECL_OPS.contains(&kind) {
            return (names, None);
        }
        (names, Some(kind))
    }

    fn take_names(&mut self, n: usize) -> Result<()> {
        for _ in 0..n {
            self.expect(Kind::Ident)?;
        }
        Ok(())
    }

    // --- declarations ----------------------------------------------------

    fn type_decl(&mut self, names: Vec<String>) -> Result<A::Decl> {
        if names.len() != 1 {
            return Err(perr(format!("type declaration {}: one name before ===", repr_list(&names))));
        }
        self.take_names(1)?;
        self.expect(Kind::TypeDecl)?;
        let mut ctors = Vec::new();
        loop {
            let cname = self.expect(Kind::Ident)?.text().to_string();
            let mut fields = Vec::new();
            while self.tok(self.i).kind == Kind::Ident {
                fields.push(self.tok(self.i).text().to_string());
                self.i += 1;
            }
            ctors.push(A::Ctor { name: cname, fields });
            if self.tok(self.i).kind == Kind::Alt {
                self.i += 1;
                continue;
            }
            break;
        }
        self.end_of_decl(&[])?;
        Ok(A::Decl::Type(A::TypeDecl { name: names[0].clone(), ctors }))
    }

    fn sig(&mut self, names: Vec<String>) -> Result<A::Decl> {
        if names.len() != 1 {
            return Err(perr(format!("signature {}: one name before ':'", repr_list(&names))));
        }
        self.take_names(1)?;
        self.expect(Kind::Colon)?;
        let mut types = vec![self.expect(Kind::Ident)?.text().to_string()];
        while self.tok(self.i).kind == Kind::Arrow {
            self.i += 1;
            types.push(self.expect(Kind::Ident)?.text().to_string());
        }
        self.end_of_decl(&[])?;
        Ok(A::Decl::Sig { name: names[0].clone(), types })
    }

    fn core_or_def(&mut self, names: Vec<String>) -> Result<A::Decl> {
        let is_core = self.tok(self.i + names.len() + 1).kind == Kind::LBrace
            || (names.len() == 1
                && self.tok(self.i + 1).kind == Kind::Assign
                && self.tok(self.i + 2).kind == Kind::LBrace);
        if is_core {
            self.take_names(names.len())?;
            self.expect(Kind::Assign)?;
            return self.core(&names[0], names[1..].to_vec());
        }
        if names.len() != 1 {
            return Err(perr(format!(
                "{}: ':=' takes binders only for a core ('name p := {{ equations }}'); \
                 write an equation with '=' or a macro with ':=*'",
                repr(&names[0])
            )));
        }
        self.take_names(1)?;
        self.expect(Kind::Assign)?;
        let e = self.expr()?;
        self.end_of_decl(&[])?;
        Ok(A::Decl::Def { name: names[0].clone(), expr: e })
    }

    fn core(&mut self, name: &str, params: Vec<String>) -> Result<A::Decl> {
        self.expect(Kind::LBrace)?;
        let mut equations = Vec::new();
        loop {
            self.skip_newlines();
            if self.tok(self.i).kind == Kind::RBrace {
                self.i += 1;
                break;
            }
            if self.tok(self.i).kind == Kind::Eof {
                return Err(perr(format!("core {}: unterminated block", repr(name))));
            }
            let (anames, op) = self.lookahead_head();
            if op != Some(Kind::Equals) {
                let t = self.tok(self.i);
                return Err(perr(format!(
                    "line {}: a core body holds equations 'name binder* = body'",
                    t.line
                )));
            }
            equations.push(self.equation(anames, &[Kind::RBrace])?);
        }
        self.end_of_decl(&[])?;
        Ok(A::Decl::Core(A::Core { name: name.to_string(), equations, params }))
    }

    fn macro_decl(&mut self, names: Vec<String>, capturing: bool) -> Result<A::Decl> {
        self.take_names(names.len())?;
        self.next();
        let body = self.expr()?;
        self.end_of_decl(&[])?;
        Ok(A::Decl::Macro(A::Macro { name: names[0].clone(), params: names[1..].to_vec(), body, capturing }))
    }

    fn equation(&mut self, names: Vec<String>, also: &[Kind]) -> Result<A::Equation> {
        self.take_names(names.len())?;
        self.expect(Kind::Equals)?;
        let body = self.expr()?;
        self.end_of_decl(also)?;
        Ok(A::Equation { name: names[0].clone(), binders: names[1..].to_vec(), body })
    }

    // --- expressions -----------------------------------------------------

    fn expr(&mut self) -> Result<E> {
        self.enter()?;
        let mut e = self.app()?;
        loop {
            match self.peek().kind {
                Kind::Case => {
                    self.next();
                    let branches = self.branches()?;
                    e = Rc::new(Expr::Case { scrutinee: e, branches });
                }
                Kind::Turnstile => {
                    self.next();
                    let q = self.quote()?;
                    let Expr::Quote { expr, fuel, .. } = &*q else { unreachable!() };
                    e = Rc::new(Expr::Quote { expr: expr.clone(), fuel: fuel.clone(), interp: Some(e) });
                }
                _ => break,
            }
        }
        self.leave();
        Ok(e)
    }

    fn app(&mut self) -> Result<E> {
        let mut e = self.atom()?;
        while ATOM_START.contains(&self.peek().kind) {
            let a = self.atom()?;
            e = A::app(e, a);
        }
        Ok(e)
    }

    fn atom(&mut self) -> Result<E> {
        let t = self.peek();
        match t.kind {
            Kind::Ident => {
                self.next();
                let mut name = t.text().to_string();
                while self.tok(self.i).kind == Kind::Dot && self.tok(self.i + 1).kind == Kind::Ident {
                    self.i += 1;
                    name.push('.');
                    name.push_str(self.expect(Kind::Ident)?.text());
                }
                Ok(Rc::new(Expr::Name(name)))
            }
            Kind::LParen => {
                self.next();
                self.enter()?;
                self.depth += 1;
                let e = self.expr()?;
                self.depth -= 1;
                self.leave();
                self.expect(Kind::RParen)?;
                Ok(e)
            }
            Kind::LBrack => {
                self.next();
                self.depth += 1;
                let mut items = Vec::new();
                while ATOM_START.contains(&self.peek().kind) {
                    items.push(self.atom()?);
                }
                self.depth -= 1;
                self.expect(Kind::RBrack)?;
                if items.len() < 2 {
                    return Err(perr(format!("line {}: a cell needs at least two items", t.line)));
                }
                Ok(Rc::new(Expr::Cell(items)))
            }
            Kind::QOpen => self.quote(),
            Kind::Scry => {
                self.next();
                let p = self.path()?;
                Ok(Rc::new(Expr::Scry(p)))
            }
            Kind::Axis => {
                self.next();
                let inner = self.atom()?;
                Ok(Rc::new(Expr::Pick { axis: t.number(), expr: inner }))
            }
            Kind::Lambda => {
                self.next();
                let param = self.expect(Kind::Ident)?.text().to_string();
                self.expect(Kind::Dot)?;
                let body = self.expr()?;
                Ok(Rc::new(Expr::Lambda { param, body }))
            }
            Kind::NsOpen => self.nslit(),
            Kind::Number => Err(perr(format!(
                "line {}, column {}: a number is only meaningful in an axis pick ('2@p') or as fuel \
                 ('<t>@10'); the calculus has no integer type (SYNTAX.md §8)",
                t.line, t.col
            ))),
            k => Err(perr(format!(
                "line {}, column {}: expected an expression, got {} {}",
                t.line,
                t.col,
                k,
                t.value.repr()
            ))),
        }
    }

    fn quote(&mut self) -> Result<E> {
        self.expect(Kind::QOpen)?;
        self.depth += 1;
        let e = self.expr()?;
        self.depth -= 1;
        self.expect(Kind::QClose)?;
        let mut fuel = None;
        if self.tok(self.i).kind == Kind::Fuel {
            fuel = Some(match &self.tok(self.i).value {
                Value::Num(n) => A::Fuel::N(*n),
                _ => A::Fuel::Policy,
            });
            self.i += 1;
        }
        Ok(Rc::new(Expr::Quote { expr: e, fuel, interp: None }))
    }

    fn path(&mut self) -> Result<A::Path> {
        let mut segs = Vec::new();
        while self.tok(self.i).kind == Kind::Slash {
            self.i += 1;
            let tag = self.expect(Kind::Ident)?.text().to_string();
            let mut payload = None;
            if self.tok(self.i).kind == Kind::LBrack {
                self.i += 1;
                self.depth += 1;
                payload = Some(self.expr()?);
                self.depth -= 1;
                self.expect(Kind::RBrack)?;
            }
            segs.push(A::Seg { tag, payload });
        }
        if segs.is_empty() {
            let t = self.peek();
            return Err(perr(format!("line {}: a path is one or more '/tag' segments", t.line)));
        }
        Ok(A::Path { segments: segs })
    }

    fn nslit(&mut self) -> Result<E> {
        self.expect(Kind::NsOpen)?;
        self.depth += 1;
        let mut facts = Vec::new();
        if self.peek().kind == Kind::RBrace {
            self.next();
            self.depth -= 1;
            return Ok(Rc::new(Expr::NsLit(facts)));
        }
        loop {
            let p = self.path()?;
            self.expect(Kind::MapsTo)?;
            let v = self.expr()?;
            facts.push((p, v));
            if self.peek().kind == Kind::Comma {
                self.next();
                continue;
            }
            break;
        }
        self.depth -= 1;
        self.expect(Kind::RBrace)?;
        Ok(Rc::new(Expr::NsLit(facts)))
    }

    fn branches(&mut self) -> Result<Vec<A::Branch>> {
        self.expect(Kind::LBrace)?;
        self.depth += 1;
        let mut out = Vec::new();
        loop {
            let t = self.expect(Kind::Ident)?;
            let cname = t.text().to_string();
            let Some(&(_, _, arity)) = self.ctors.get(&cname) else {
                return Err(perr(format!(
                    "line {}, column {}: undeclared constructor {} in a case branch; declare it with \
                     'type === {} ...' before use",
                    t.line,
                    t.col,
                    repr(&cname),
                    cname
                )));
            };
            let mut binders = Vec::new();
            for _ in 0..arity {
                binders.push(self.expect(Kind::Ident)?.text().to_string());
            }
            let body = self.expr()?;
            out.push(A::Branch { ctor: cname, binders, body });
            if self.peek().kind == Kind::Semi {
                self.next();
                continue;
            }
            break;
        }
        self.depth -= 1;
        self.expect(Kind::RBrace)?;
        Ok(out)
    }
}

fn repr_list(names: &[String]) -> String {
    let parts: Vec<String> = names.iter().map(|n| repr(n)).collect();
    format!("[{}]", parts.join(", "))
}

pub fn parse(text: &str, lx: Lexicon) -> Result<A::Program> {
    let tokens = lex(text, lx)?;
    let ctors = collect_ctors(&tokens)?;
    let mut p = Parser { toks: &tokens, i: 0, ctors, depth: 0, nesting: 0 };
    p.program()
}

pub fn parse_ascii(text: &str) -> Result<A::Program> {
    parse(text, Lexicon::Ascii)
}

pub fn parse_unicode(text: &str) -> Result<A::Program> {
    parse(text, Lexicon::Unicode)
}

/// Parse a bare expression.
pub fn parse_expr_text(text: &str, lx: Lexicon) -> Result<E> {
    let tokens = lex(text, lx)?;
    let ctors = collect_ctors(&tokens)?;
    let mut p = Parser { toks: &tokens, i: 0, ctors, depth: 0, nesting: 0 };
    p.depth += 1;
    let e = p.expr()?;
    p.depth -= 1;
    let t = p.tok(p.i);
    if !matches!(t.kind, Kind::Newline | Kind::Eof) {
        return Err(perr(format!("trailing {} {}", t.kind, t.value.repr())));
    }
    Ok(e)
}
