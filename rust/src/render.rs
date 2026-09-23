//! Tree -> text, in either lexicon.

use crate::ast::{self as A, Expr, E};
use crate::lexicon::{glyph_of, spelling, Kind, Lexicon};

struct Renderer {
    lx: Lexicon,
}

fn sub_digits(n: u64) -> String {
    n.to_string().chars().map(|c| char::from_u32(0x2080 + (c as u32 - '0' as u32)).unwrap()).collect()
}

impl Renderer {
    fn t(&self, k: Kind) -> &'static str {
        spelling(k, self.lx)
    }

    fn name(&self, n: &str) -> String {
        if self.lx == Lexicon::Unicode {
            if let Some(g) = glyph_of(n) {
                return g.to_string();
            }
        }
        n.to_string()
    }

    fn fuel(&self, f: &Option<A::Fuel>) -> String {
        match (f, self.lx) {
            (None, _) => String::new(),
            (Some(A::Fuel::Policy), Lexicon::Ascii) => "@[]".to_string(),
            (Some(A::Fuel::N(n)), Lexicon::Ascii) => format!("@{}", n),
            (Some(A::Fuel::Policy), Lexicon::Unicode) => "₍₎".to_string(),
            (Some(A::Fuel::N(n)), Lexicon::Unicode) => sub_digits(*n),
        }
    }

    // prec 0: anywhere;  1: as the function of an application;
    // 2: as an argument / a cell item (must be an atom)
    fn expr(&self, e: &E, prec: u8) -> String {
        match &**e {
            Expr::Name(n) => self.name(n),
            Expr::App(f, a) => {
                let s = format!("{} {}", self.expr(f, 1), self.expr(a, 2));
                if prec >= 2 {
                    format!("({})", s)
                } else {
                    s
                }
            }
            Expr::Cell(items) => {
                let parts: Vec<String> = items.iter().map(|x| self.expr(x, 2)).collect();
                format!("[{}]", parts.join(" "))
            }
            Expr::Pick { axis, expr } => {
                let mark = self.lx.axis_mark();
                format!("{}{}{}", axis, mark, self.expr(expr, 2))
            }
            Expr::Scry(p) => format!("{}{}", self.t(Kind::Scry), self.path(p)),
            Expr::Quote { expr, fuel, interp } => {
                let q = format!("{}{}{}{}", self.t(Kind::QOpen), self.expr(expr, 0), self.t(Kind::QClose), self.fuel(fuel));
                match interp {
                    None => q,
                    Some(i) => {
                        let s = format!("{} {} {}", self.expr(i, 1), self.t(Kind::Turnstile), q);
                        if prec >= 1 {
                            format!("({})", s)
                        } else {
                            s
                        }
                    }
                }
            }
            Expr::Lambda { param, body } => {
                let s = format!("{}{}.{}", self.t(Kind::Lambda), param, self.expr(body, 0));
                if prec >= 1 {
                    format!("({})", s)
                } else {
                    s
                }
            }
            Expr::Case { scrutinee, branches } => {
                let bs: Vec<String> = branches
                    .iter()
                    .map(|b| {
                        let mut parts = vec![self.name(&b.ctor)];
                        parts.extend(b.binders.iter().cloned());
                        parts.push(self.expr(&b.body, 0));
                        parts.join(" ")
                    })
                    .collect();
                let s = format!("{} {} {{ {} }}", self.expr(scrutinee, 1), self.t(Kind::Case), bs.join(" ; "));
                if prec >= 1 {
                    format!("({})", s)
                } else {
                    s
                }
            }
            Expr::NsLit(facts) => {
                let fs: Vec<String> = facts
                    .iter()
                    .map(|(p, v)| format!("{} {} {}", self.path(p), self.t(Kind::MapsTo), self.expr(v, 0)))
                    .collect();
                format!("{}{}}}", self.t(Kind::NsOpen), fs.join(", "))
            }
        }
    }

    fn path(&self, p: &A::Path) -> String {
        let mut out = String::new();
        for seg in &p.segments {
            out.push('/');
            out.push_str(&seg.tag);
            if let Some(pl) = &seg.payload {
                out.push('[');
                out.push_str(&self.expr(pl, 0));
                out.push(']');
            }
        }
        out
    }

    fn decl(&self, d: &A::Decl) -> String {
        match d {
            A::Decl::Type(t) => {
                let ctors: Vec<String> = t
                    .ctors
                    .iter()
                    .map(|c| {
                        let mut parts = vec![self.name(&c.name)];
                        parts.extend(c.fields.iter().cloned());
                        parts.join(" ")
                    })
                    .collect();
                format!("{} {} {}", self.name(&t.name), self.t(Kind::TypeDecl), ctors.join(&format!(" {} ", self.t(Kind::Alt))))
            }
            A::Decl::Sig { name, types } => {
                format!("{} {} {}", self.name(name), self.t(Kind::Colon), types.join(&format!(" {} ", self.t(Kind::Arrow))))
            }
            A::Decl::Equation(eq) => self.equation(eq),
            A::Decl::Core(c) => {
                let eqs: Vec<String> = c.equations.iter().map(|x| format!("  {}", self.equation(x))).collect();
                let mut head = vec![self.name(&c.name)];
                head.extend(c.params.iter().cloned());
                format!("{} {} {{\n{}\n}}", head.join(" "), self.t(Kind::Assign), eqs.join("\n"))
            }
            A::Decl::Macro(m) => {
                let op = if m.capturing { self.t(Kind::CMacro) } else { self.t(Kind::Macro) };
                let mut head = vec![self.name(&m.name)];
                head.extend(m.params.iter().cloned());
                format!("{} {} {}", head.join(" "), op, self.expr(&m.body, 0))
            }
            A::Decl::Def { name, expr } => format!("{} {} {}", self.name(name), self.t(Kind::Assign), self.expr(expr, 0)),
        }
    }

    fn equation(&self, eq: &A::Equation) -> String {
        let mut head = vec![self.name(&eq.name)];
        head.extend(eq.binders.iter().cloned());
        format!("{} {} {}", head.join(" "), self.t(Kind::Equals), self.expr(&eq.body, 0))
    }

    fn program(&self, p: &A::Program) -> String {
        let lines: Vec<String> = p.decls.iter().map(|d| self.decl(d)).collect();
        format!("{}\n", lines.join("\n"))
    }
}

pub fn render_program(p: &A::Program, lx: Lexicon) -> String {
    Renderer { lx }.program(p)
}

pub fn render_decl(d: &A::Decl, lx: Lexicon) -> String {
    Renderer { lx }.decl(d)
}

pub fn render_expr(e: &E, lx: Lexicon) -> String {
    Renderer { lx }.expr(e, 0)
}

pub fn render_ascii(e: &E) -> String {
    render_expr(e, Lexicon::Ascii)
}

pub fn render_unicode(e: &E) -> String {
    render_expr(e, Lexicon::Unicode)
}
