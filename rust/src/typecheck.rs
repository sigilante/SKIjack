//! Stage B: the type discipline.  Hindley--Milner over the declared sum
//! types and function types, with the rule that a datum may be applied and
//! a function is never a datum.  Types live in an arena so the
//! equirecursive graphs the reference builds by reference cells are
//! reproduced by index.

use std::collections::{BTreeMap, HashMap, HashSet};

use indexmap::IndexMap;

use crate::abi::is_isa;
use crate::ast::{self as A, Decl, Expr, Program, E};
use crate::errors::{repr, Problem, ProblemKind, Result, Site, SkijackError};
use crate::expand::expand_macros;
use crate::generate::{find_answer_type, find_loop_types, find_object_type, generate, is_interpreter_core};

pub type Ty = usize;

#[derive(Debug, Clone)]
pub enum TNode {
    Var { id: usize, data: bool, r: Option<Ty> },
    Con { name: String, args: Vec<Ty> },
    Arrow { param: Ty, result: Ty, elim: bool, nominal: Option<String>, datum: bool, checked: Option<String> },
}

#[derive(Debug, Clone)]
pub struct Scheme {
    pub vars: Vec<usize>,
    pub data: Vec<usize>,
    pub ty: Ty,
}

struct Fail(String);

type FResult<T> = std::result::Result<T, Fail>;

type Item = (String, Option<String>, Vec<String>, E, Site);

pub struct Types {
    nodes: Vec<TNode>,
    next_id: usize,
    problems: Vec<Problem>,
    types: IndexMap<String, A::TypeDecl>,
    ctor_of: HashMap<String, A::TypeDecl>,
    env: IndexMap<String, Scheme>,
    core_env: HashMap<String, IndexMap<String, Scheme>>,
    mono: IndexMap<String, Ty>,
    fuel: Ty,
}

impl Types {
    fn new() -> Types {
        let mut t = Types {
            nodes: Vec::new(),
            next_id: 0,
            problems: Vec::new(),
            types: IndexMap::new(),
            ctor_of: HashMap::new(),
            env: IndexMap::new(),
            core_env: HashMap::new(),
            mono: IndexMap::new(),
            fuel: 0,
        };
        t.fuel = t.con("fuel", vec![]);
        t
    }

    fn push(&mut self, n: TNode) -> Ty {
        self.nodes.push(n);
        self.nodes.len() - 1
    }

    fn con(&mut self, name: &str, args: Vec<Ty>) -> Ty {
        self.push(TNode::Con { name: name.to_string(), args })
    }

    fn arrow(&mut self, param: Ty, result: Ty) -> Ty {
        self.push(TNode::Arrow { param, result, elim: false, nominal: None, datum: false, checked: None })
    }

    fn arrow_elim(&mut self, param: Ty, result: Ty, nominal: Option<String>) -> Ty {
        self.push(TNode::Arrow { param, result, elim: true, nominal, datum: false, checked: None })
    }

    fn fresh(&mut self, data: bool) -> Ty {
        self.next_id += 1;
        let id = self.next_id;
        self.push(TNode::Var { id, data, r: None })
    }

    fn list(&mut self, a: Ty) -> Ty {
        self.con("list", vec![a])
    }

    fn cell(&mut self, a: Ty, b: Ty) -> Ty {
        self.con("cell", vec![a, b])
    }

    fn arrows(&mut self, params: &[Ty], result: Ty) -> Ty {
        let mut t = result;
        for p in params.iter().rev() {
            t = self.arrow(*p, t);
        }
        t
    }

    fn scott_spine(&mut self, conts: &[Ty], result: Ty, name: &str) -> Ty {
        let mut t = result;
        for c in conts.iter().rev() {
            t = self.arrow_elim(*c, t, Some(name.to_string()));
        }
        t
    }

    fn resolve(&self, mut t: Ty) -> Ty {
        loop {
            match &self.nodes[t] {
                TNode::Var { r: Some(next), .. } => t = *next,
                _ => return t,
            }
        }
    }

    // ---- rendering

    pub fn render_type(&self, t: Ty, names: &mut BTreeMap<usize, String>) -> String {
        let mut seen: HashSet<Ty> = HashSet::new();
        self.render_go(t, false, names, &mut seen)
    }

    fn render_go(&self, t: Ty, left: bool, names: &mut BTreeMap<usize, String>, seen: &mut HashSet<Ty>) -> String {
        let t = self.resolve(t);
        match &self.nodes[t] {
            TNode::Var { id, .. } => {
                if !names.contains_key(id) {
                    let n = names.len();
                    let nm = if n < 26 { ((b'a' + n as u8) as char).to_string() } else { format!("t{}", n) };
                    names.insert(*id, nm);
                }
                names[id].clone()
            }
            TNode::Con { name, args } => {
                if seen.contains(&t) {
                    return "...".to_string();
                }
                seen.insert(t);
                let s = if args.is_empty() {
                    name.clone()
                } else {
                    let mut parts = vec![name.clone()];
                    for a in args {
                        parts.push(self.render_go(*a, true, names, seen));
                    }
                    format!("({})", parts.join(" "))
                };
                seen.remove(&t);
                s
            }
            TNode::Arrow { param, result, nominal, .. } => {
                if seen.contains(&t) {
                    return "...".to_string();
                }
                seen.insert(t);
                let mut s = format!("{} -> {}", self.render_go(*param, true, names, seen), self.render_go(*result, false, names, seen));
                if let Some(nm) = nominal {
                    s = format!("{} as {}", s, nm);
                }
                seen.remove(&t);
                if left {
                    format!("({})", s)
                } else {
                    s
                }
            }
        }
    }

    fn rt(&self, t: Ty) -> String {
        self.render_type(t, &mut BTreeMap::new())
    }

    // ---- variables and schemes

    fn instantiate(&mut self, s: &Scheme) -> Ty {
        if s.vars.is_empty() {
            return s.ty;
        }
        let mut sub: HashMap<usize, Ty> = HashMap::new();
        for v in &s.vars {
            let f = self.fresh(s.data.contains(v));
            sub.insert(*v, f);
        }
        let mut memo: HashMap<Ty, Ty> = HashMap::new();
        self.inst_go(s.ty, &sub, &mut memo)
    }

    fn inst_go(&mut self, t: Ty, sub: &HashMap<usize, Ty>, memo: &mut HashMap<Ty, Ty>) -> Ty {
        let t = self.resolve(t);
        match self.nodes[t].clone() {
            TNode::Var { id, .. } => sub.get(&id).copied().unwrap_or(t),
            TNode::Con { args, .. } if args.is_empty() => t,
            node => {
                if let Some(h) = memo.get(&t) {
                    return *h;
                }
                let hole = self.fresh(false);
                memo.insert(t, hole);
                let new = match node {
                    TNode::Con { name, args } => {
                        let nargs: Vec<Ty> = args.iter().map(|a| self.inst_go(*a, sub, memo)).collect();
                        self.con(&name, nargs)
                    }
                    TNode::Arrow { param, result, elim, nominal, datum, checked } => {
                        let p = self.inst_go(param, sub, memo);
                        let r = self.inst_go(result, sub, memo);
                        self.push(TNode::Arrow { param: p, result: r, elim, nominal, datum, checked })
                    }
                    TNode::Var { .. } => unreachable!(),
                };
                if let TNode::Var { r, .. } = &mut self.nodes[hole] {
                    *r = Some(new);
                }
                new
            }
        }
    }

    fn free(&self, t: Ty, out: &mut BTreeMap<usize, Ty>, seen: &mut HashSet<Ty>) {
        let t = self.resolve(t);
        match &self.nodes[t] {
            TNode::Var { id, .. } => {
                out.insert(*id, t);
            }
            TNode::Con { args, .. } => {
                if !seen.insert(t) {
                    return;
                }
                for a in args {
                    self.free(*a, out, seen);
                }
            }
            TNode::Arrow { param, result, .. } => {
                if !seen.insert(t) {
                    return;
                }
                self.free(*param, out, seen);
                self.free(*result, out, seen);
            }
        }
    }

    fn env_free(&self) -> HashSet<usize> {
        let mut out: HashSet<usize> = HashSet::new();
        for s in self.env.values() {
            let mut fv = BTreeMap::new();
            self.free(s.ty, &mut fv, &mut HashSet::new());
            for k in fv.keys() {
                if !s.vars.contains(k) {
                    out.insert(*k);
                }
            }
        }
        for t in self.mono.values() {
            let mut fv = BTreeMap::new();
            self.free(*t, &mut fv, &mut HashSet::new());
            out.extend(fv.keys());
        }
        out
    }

    fn generalize(&self, t: Ty) -> Scheme {
        let mut fv = BTreeMap::new();
        self.free(t, &mut fv, &mut HashSet::new());
        let env_fv = self.env_free();
        let qs: Vec<usize> = fv.keys().filter(|k| !env_fv.contains(k)).copied().collect();
        let data: Vec<usize> = qs
            .iter()
            .filter(|k| matches!(self.nodes[fv[k]], TNode::Var { data: true, .. }))
            .copied()
            .collect();
        Scheme { vars: qs, data, ty: t }
    }

    fn close(&self, t: Ty) -> Scheme {
        let mut fv = BTreeMap::new();
        self.free(t, &mut fv, &mut HashSet::new());
        Scheme { vars: fv.keys().copied().collect(), data: vec![], ty: t }
    }

    // ---- the Scott scheme of a datum

    fn scott(&mut self, t: Ty) -> FResult<Option<Ty>> {
        let TNode::Con { name, args } = self.nodes[t].clone() else { unreachable!() };
        let r = self.fresh(false);
        if let Some(decl) = self.types.get(&name).cloned() {
            let mut conts = Vec::new();
            for c in &decl.ctors {
                let mut fields = Vec::new();
                for f in &c.fields {
                    fields.push(self.field(f)?);
                }
                conts.push(self.arrows(&fields, r));
            }
            return Ok(Some(self.scott_spine(&conts, r, &name)));
        }
        match name.as_str() {
            "fuel" => {
                let fuel = self.fuel;
                let a2 = self.arrow(fuel, r);
                Ok(Some(self.scott_spine(&[r, a2], r, "fuel")))
            }
            "list" => {
                let a = args[0];
                let la = self.list(a);
                let c2 = self.arrows(&[a, la], r);
                Ok(Some(self.scott_spine(&[r, c2], r, "list")))
            }
            "cell" => {
                let (a, b) = (args[0], args[1]);
                let c1 = self.arrows(&[a, b], r);
                Ok(Some(self.scott_spine(&[c1], r, "cell")))
            }
            _ => Ok(None),
        }
    }

    fn field(&mut self, name: &str) -> FResult<Ty> {
        if self.types.contains_key(name) {
            return Ok(self.con(name, vec![]));
        }
        Err(Fail(format!("{} is not a declared type", repr(name))))
    }

    // ---- unification

    fn bind(&mut self, v: Ty, t: Ty) -> FResult<()> {
        let t = self.resolve(t);
        if t == v {
            return Ok(());
        }
        let v_data = matches!(self.nodes[v], TNode::Var { data: true, .. });
        if v_data {
            match &mut self.nodes[t] {
                TNode::Arrow { elim, datum, .. } => {
                    if !*elim {
                        let r = self.rt(t);
                        return Err(Fail(format!(
                            "an operand of 'EQ' is a function ({}); a value of function type cannot be compared",
                            r
                        )));
                    }
                    *datum = true;
                }
                TNode::Var { data, .. } => *data = true,
                _ => {}
            }
        }
        if let TNode::Var { r, .. } = &mut self.nodes[v] {
            *r = Some(t);
        }
        Ok(())
    }

    fn unify(&mut self, expected: Ty, given: Ty, seen: &mut HashSet<(Ty, Ty)>) -> FResult<()> {
        let e = self.resolve(expected);
        let g = self.resolve(given);
        if e == g {
            return Ok(());
        }
        if matches!(self.nodes[e], TNode::Var { .. }) {
            return self.bind(e, g);
        }
        if matches!(self.nodes[g], TNode::Var { .. }) {
            return self.bind(g, e);
        }
        if !seen.insert((e, g)) {
            return Ok(());
        }
        let ne = self.nodes[e].clone();
        let ng = self.nodes[g].clone();
        match (ne, ng) {
            (
                TNode::Arrow { param: ep, result: er, elim: ee, nominal: en, datum: ed, .. },
                TNode::Arrow { param: gp, result: gr, elim: ge, nominal: gn, datum: gd, .. },
            ) => {
                if ge && !ee {
                    // a datum-shaped unknown used where a function is wanted
                } else if ee && !ge {
                    if en.is_some() || ed {
                        let what = match &en {
                            Some(n) => format!("a value of type {}", n),
                            None => "a datum".to_string(),
                        };
                        return Err(Fail(format!(
                            "a function ({}) where {} is expected; a function is not a datum",
                            self.rt(g),
                            what
                        )));
                    }
                    if let TNode::Arrow { elim, .. } = &mut self.nodes[e] {
                        *elim = false;
                    }
                } else if ee && ge {
                    if let (Some(a), Some(b)) = (&en, &gn) {
                        if a != b {
                            return Err(Fail(format!("expected {}, found {}", a, b)));
                        }
                    }
                    let nm = en.clone().or(gn.clone());
                    let d = ed || gd;
                    for idx in [e, g] {
                        if let TNode::Arrow { nominal, datum, .. } = &mut self.nodes[idx] {
                            *nominal = nm.clone();
                            *datum = d;
                        }
                    }
                }
                self.unify(gp, ep, seen)?;
                self.unify(er, gr, seen)
            }
            (TNode::Arrow { elim: ee, nominal: en, checked: ec, .. }, TNode::Con { name: gname, .. }) => {
                if ec.as_deref() == Some(gname.as_str()) {
                    return Ok(());
                }
                if ee {
                    if let Some(n) = &en {
                        if *n != gname {
                            return Err(Fail(format!("expected {}, found {}", n, gname)));
                        }
                    }
                }
                let Some(sc) = self.scott(g)? else {
                    return Err(Fail(format!("expected {}, found {}", self.rt(e), gname)));
                };
                if let TNode::Arrow { nominal, checked, elim, .. } = &mut self.nodes[e] {
                    if *elim {
                        *nominal = Some(gname.clone());
                    }
                    *checked = Some(gname.clone());
                }
                if let Err(f) = self.unify(e, sc, seen) {
                    if let TNode::Arrow { checked, .. } = &mut self.nodes[e] {
                        *checked = None;
                    }
                    return Err(f);
                }
                Ok(())
            }
            (TNode::Con { name: ename, .. }, TNode::Arrow { elim: ge, nominal: gn, checked: gc, .. }) => {
                if !ge {
                    return Err(Fail(format!(
                        "a function ({}) where a value of type {} is expected; a function is not a datum",
                        self.rt(g),
                        self.rt(e)
                    )));
                }
                if let Some(n) = &gn {
                    if *n != ename {
                        return Err(Fail(format!("expected {}, found {}", self.rt(e), n)));
                    }
                }
                if gc.as_deref() == Some(ename.as_str()) {
                    return Ok(());
                }
                let Some(sc) = self.scott(e)? else {
                    return Err(Fail(format!("expected {}, found a function", self.rt(e))));
                };
                if let TNode::Arrow { nominal, checked, .. } = &mut self.nodes[g] {
                    *nominal = Some(ename.clone());
                    *checked = Some(ename.clone());
                }
                if let Err(f) = self.unify(g, sc, seen) {
                    if let TNode::Arrow { checked, .. } = &mut self.nodes[g] {
                        *checked = None;
                    }
                    return Err(f);
                }
                Ok(())
            }
            (TNode::Con { name: en, args: ea }, TNode::Con { name: gn, args: ga }) => {
                if en != gn || ea.len() != ga.len() {
                    return Err(Fail(format!("expected {}, found {}", self.rt(e), self.rt(g))));
                }
                for (a, b) in ea.iter().zip(ga.iter()) {
                    self.unify(*a, *b, seen)?;
                }
                Ok(())
            }
            _ => unreachable!(),
        }
    }

    // ---- the environment

    fn builtin(&mut self, name: &str) -> Option<Scheme> {
        let t = match name {
            "S" => {
                let (a, b, c) = (self.fresh(false), self.fresh(false), self.fresh(false));
                let abc = self.arrows(&[a, b], c);
                let ab = self.arrow(a, b);
                self.arrows(&[abc, ab, a], c)
            }
            "K" => {
                let (a, b) = (self.fresh(false), self.fresh(false));
                self.arrows(&[a, b], a)
            }
            "I" => {
                let a = self.fresh(false);
                self.arrow(a, a)
            }
            "B" => {
                let (a, b, c) = (self.fresh(false), self.fresh(false), self.fresh(false));
                let bc = self.arrow(b, c);
                let ab = self.arrow(a, b);
                self.arrows(&[bc, ab, a], c)
            }
            "C" => {
                let (a, b, c) = (self.fresh(false), self.fresh(false), self.fresh(false));
                let abc = self.arrows(&[a, b], c);
                self.arrows(&[abc, b, a], c)
            }
            "W" => {
                let (a, b) = (self.fresh(false), self.fresh(false));
                let aab = self.arrows(&[a, a], b);
                self.arrows(&[aab, a], b)
            }
            "Y" => {
                let a = self.fresh(false);
                let aa = self.arrow(a, a);
                self.arrow(aa, a)
            }
            "pair" => {
                let (a, b) = (self.fresh(false), self.fresh(false));
                let c = self.cell(a, b);
                self.arrows(&[a, b], c)
            }
            "hd" => {
                let (a, b) = (self.fresh(false), self.fresh(false));
                let c = self.cell(a, b);
                self.arrow(c, a)
            }
            "tl" => {
                let (a, b) = (self.fresh(false), self.fresh(false));
                let c = self.cell(a, b);
                self.arrow(c, b)
            }
            "nil" => {
                let a = self.fresh(false);
                self.list(a)
            }
            "cons" => {
                let a = self.fresh(false);
                let la = self.list(a);
                self.arrows(&[a, la], la)
            }
            "zero" => return Some(Scheme { vars: vec![], data: vec![], ty: self.fuel }),
            "suc" => {
                let f = self.fuel;
                let t = self.arrow(f, f);
                return Some(Scheme { vars: vec![], data: vec![], ty: t });
            }
            _ => return None,
        };
        Some(self.close(t))
    }

    fn lookup(&mut self, name: &str, bound: &HashMap<String, Ty>, core: Option<&str>) -> FResult<Ty> {
        if let Some(t) = bound.get(name) {
            return Ok(*t);
        }
        if is_isa(name) {
            let s = self.builtin(name).unwrap();
            return Ok(self.instantiate(&s));
        }
        if let Some(c) = core {
            let key = format!("{}.{}", c, name);
            if let Some(t) = self.mono.get(&key) {
                return Ok(*t);
            }
            if let Some(s) = self.core_env.get(c).and_then(|m| m.get(name)).cloned() {
                return Ok(self.instantiate(&s));
            }
        }
        if let Some(t) = self.mono.get(name) {
            return Ok(*t);
        }
        if let Some(s) = self.env.get(name).cloned() {
            return Ok(self.instantiate(&s));
        }
        if let Some(s) = self.builtin(name) {
            return Ok(self.instantiate(&s));
        }
        Err(Fail(format!("unresolved name {}", repr(name))))
    }

    fn infer(&mut self, e: &E, bound: &HashMap<String, Ty>, core: Option<&str>) -> FResult<Ty> {
        match &**e {
            Expr::Name(n) => self.lookup(n, bound, core),
            Expr::Lambda { param, body } => {
                let p = self.fresh(false);
                let mut b = bound.clone();
                b.insert(param.clone(), p);
                let bt = self.infer(body, &b, core)?;
                Ok(self.arrow(p, bt))
            }
            Expr::App(..) => {
                let (head, args) = A::spine(e);
                let mut tf = self.infer(&head, bound, core)?;
                let is_eq = matches!(&*head, Expr::Name(n) if n == "EQ");
                for (i, x) in args.iter().enumerate() {
                    let mut tx = self.infer(x, bound, core)?;
                    if is_eq && i < 2 {
                        let d = self.fresh(true);
                        self.unify(d, tx, &mut HashSet::new())?;
                        tx = d;
                    }
                    let r = self.fresh(false);
                    let ar = self.arrow_elim(tx, r, None);
                    self.unify(ar, tf, &mut HashSet::new())?;
                    tf = r;
                }
                Ok(tf)
            }
            Expr::Cell(items) => {
                let mut ts = Vec::new();
                for it in items {
                    ts.push(self.infer(it, bound, core)?);
                }
                let mut cell_t = ts[ts.len() - 1];
                for it in ts[..ts.len() - 1].iter().rev() {
                    cell_t = self.cell(*it, cell_t);
                }
                Ok(cell_t)
            }
            Expr::Pick { axis, expr } => {
                let mut pick_t = self.infer(expr, bound, core)?;
                if *axis >= 2 {
                    let bits = 64 - axis.leading_zeros();
                    for i in (0..bits - 1).rev() {
                        let bit = (axis >> i) & 1;
                        let (a, b) = (self.fresh(false), self.fresh(false));
                        let c = self.cell(a, b);
                        self.unify(c, pick_t, &mut HashSet::new())?;
                        pick_t = if bit == 0 { a } else { b };
                    }
                }
                Ok(pick_t)
            }
            Expr::Case { scrutinee, branches } => {
                let first = &branches[0].ctor;
                let Some(decl) = self.ctor_of.get(first).cloned() else {
                    return Err(Fail(format!("undeclared constructor {} in a case branch", repr(first))));
                };
                let st = self.infer(scrutinee, bound, core)?;
                let dt = self.con(&decl.name, vec![]);
                self.unify(dt, st, &mut HashSet::new())?;
                let result = self.fresh(false);
                let fields: HashMap<&str, &Vec<String>> = decl.ctors.iter().map(|c| (c.name.as_str(), &c.fields)).collect();
                for b in branches {
                    let Some(fs) = fields.get(b.ctor.as_str()) else {
                        return Err(Fail(format!("branch {} does not fit type {}", repr(&b.ctor), repr(&decl.name))));
                    };
                    if b.binders.len() != fs.len() {
                        return Err(Fail(format!("branch {} does not fit type {}", repr(&b.ctor), repr(&decl.name))));
                    }
                    let mut inner = bound.clone();
                    for (bn, f) in b.binders.iter().zip(fs.iter()) {
                        let ft = self.field(f)?;
                        inner.insert(bn.clone(), ft);
                    }
                    let bt = self.infer(&b.body, &inner, core)?;
                    self.unify(result, bt, &mut HashSet::new())?;
                }
                Ok(result)
            }
            _ => Ok(self.fresh(false)),
        }
    }

    fn add(&mut self, site: Site, message: String) {
        self.problems.push(Problem { kind: ProblemKind::TypeMismatch, site, message });
    }

    // ---- declarations

    fn run(mut self, prog: &Program) -> Result<Vec<Problem>> {
        let mut macros: IndexMap<String, A::Macro> = IndexMap::new();
        for d in &prog.decls {
            match d {
                Decl::Type(t) => {
                    self.types.insert(t.name.clone(), t.clone());
                    for c in &t.ctors {
                        self.ctor_of.insert(c.name.clone(), t.clone());
                    }
                }
                Decl::Macro(m) => {
                    macros.insert(m.name.clone(), m.clone());
                }
                _ => {}
            }
        }
        let decls: Vec<A::TypeDecl> = self.types.values().cloned().collect();
        for d in &decls {
            for c in &d.ctors {
                let r = (|| -> FResult<Ty> {
                    let mut fs = Vec::new();
                    for f in &c.fields {
                        fs.push(self.field(f)?);
                    }
                    let res = self.con(&d.name, vec![]);
                    Ok(self.arrows(&fs, res))
                })();
                match r {
                    Ok(t) => {
                        self.env.insert(c.name.clone(), Scheme { vars: vec![], data: vec![], ty: t });
                    }
                    Err(Fail(m)) => {
                        self.add(Site::new("type", &d.name), format!("constructor {}: {}", repr(&c.name), m));
                        let t = self.con(&d.name, vec![]);
                        self.env.insert(c.name.clone(), Scheme { vars: vec![], data: vec![], ty: t });
                    }
                }
            }
        }

        let mut obj = None;
        let mut lt = None;
        let mut answer = None;
        if let Ok(o) = find_object_type(prog) {
            if let Some(o) = o {
                if let Ok(l) = find_loop_types(prog, &o) {
                    if let Ok(a) = find_answer_type(prog, &o, &l) {
                        answer = a;
                    }
                    lt = Some(l);
                }
                obj = Some(o);
            }
        }

        let object_t: Option<Ty> = obj.as_ref().map(|o| self.con(o.name(), vec![]));
        let mut runs: Vec<(String, E)> = Vec::new();
        for d in &prog.decls {
            if let Decl::Def { name, expr } = d {
                match &**expr {
                    Expr::Quote { fuel, interp, .. } => {
                        if fuel.is_none() && interp.is_none() {
                            if let Some(ot) = object_t {
                                self.env.insert(name.clone(), Scheme { vars: vec![], data: vec![], ty: ot });
                            }
                        } else {
                            runs.push((name.clone(), expr.clone()));
                        }
                    }
                    Expr::NsLit(_) => {
                        if let (Some(ot), Some(a)) = (object_t, &answer) {
                            let at = self.con(&a.decl.name, vec![]);
                            let t = self.arrow(ot, at);
                            self.env.insert(name.clone(), Scheme { vars: vec![], data: vec![], ty: t });
                        }
                    }
                    _ => {}
                }
            }
        }

        let mut items: Vec<Item> = Vec::new();
        for d in &prog.decls {
            match d {
                Decl::Equation(e) => {
                    items.push((e.name.clone(), None, e.binders.clone(), e.body.clone(), Site::new("equation", &e.name)));
                }
                Decl::Def { name, expr } if !matches!(&**expr, Expr::Quote { .. } | Expr::NsLit(_)) => {
                    items.push((name.clone(), None, vec![], expr.clone(), Site::new("definition", name)));
                }
                Decl::Core(c) => {
                    for eq in &c.equations {
                        let mut binders = c.params.clone();
                        binders.extend(eq.binders.iter().cloned());
                        items.push((
                            eq.name.clone(),
                            Some(c.name.clone()),
                            binders,
                            eq.body.clone(),
                            Site::in_core("equation", &eq.name, &c.name),
                        ));
                    }
                }
                _ => {}
            }
        }
        let key_of = |name: &str, core: &Option<String>| match core {
            Some(c) => format!("{}.{}", c, name),
            None => name.to_string(),
        };
        let keys: HashSet<String> = items.iter().map(|(n, c, ..)| key_of(n, c)).collect();
        let mut expanded: HashMap<String, E> = HashMap::new();
        let mut item_of: HashMap<String, Item> = HashMap::new();
        let mut deps: HashMap<String, HashSet<String>> = HashMap::new();
        for it in &items {
            let (name, core, binders, body, _) = it;
            let key = key_of(name, core);
            item_of.insert(key.clone(), it.clone());
            let ex = expand_macros(body, &macros)?; // its errors are its own
            let mut ds = HashSet::new();
            for nm in names_in(&ex) {
                if binders.contains(&nm) {
                    continue;
                }
                if let Some(c) = core {
                    let k = format!("{}.{}", c, nm);
                    if keys.contains(&k) {
                        ds.insert(k);
                        continue;
                    }
                }
                if keys.contains(&nm) {
                    ds.insert(nm);
                }
            }
            expanded.insert(key.clone(), ex);
            deps.insert(key, ds);
        }
        for group in sccs(&keys, &deps) {
            self.infer_group(&group, &item_of, &expanded);
        }

        for d in &prog.decls {
            if let Decl::Core(c) = d {
                if let Some(o) = &obj {
                    if is_interpreter_core(c, o) {
                        if let Some(l) = self.core_env.get(&c.name).and_then(|m| m.get("loop")).cloned() {
                            self.env.insert(c.name.clone(), l);
                        }
                    }
                }
            }
        }

        for d in &prog.decls {
            if let Decl::Sig { name, types } = d {
                if !self.env.contains_key(name) {
                    continue;
                }
                let s = self.env[name].clone();
                let r = (|| -> FResult<()> {
                    let mut params = Vec::new();
                    for t in &types[..types.len() - 1] {
                        params.push(self.field(t)?);
                    }
                    let res = self.field(&types[types.len() - 1])?;
                    let sig = self.arrows(&params, res);
                    let inst = self.instantiate(&s);
                    self.unify(sig, inst, &mut HashSet::new())
                })();
                if let Err(Fail(m)) = r {
                    let inst = self.instantiate(&s);
                    let rendered = self.rt(inst);
                    self.add(
                        Site::new("signature", name),
                        format!("declared {}, inferred {}: {}", types.join(" -> "), rendered, m),
                    );
                }
            }
        }

        for (name, q) in &runs {
            let (Some(ot), Some(l)) = (object_t, &lt) else { continue };
            let result_name = l.result.name.clone();
            if let Err(Fail(m)) = self.run_decl(name, q, &macros, ot, &result_name) {
                self.add(Site::new("definition", name), m);
            }
        }
        Ok(self.problems)
    }

    fn run_decl(&mut self, name: &str, q: &E, macros: &IndexMap<String, A::Macro>, object_t: Ty, result_name: &str) -> FResult<()> {
        let Expr::Quote { interp, .. } = &**q else { unreachable!() };
        let head0: E = interp.clone().unwrap_or_else(|| A::name("whnfF"));
        let (head, args) = A::spine(&head0);
        let Expr::Name(hn) = &*head else { return Ok(()) };
        let Some(s) = self.env.get(hn).cloned() else { return Ok(()) };
        let mut t = self.instantiate(&s);
        for x in &args {
            let ex = expand_macros(x, macros).map_err(|e| Fail(e.message().to_string()))?;
            let tx = self.infer(&ex, &HashMap::new(), None)?;
            let r = self.fresh(false);
            let ar = self.arrow_elim(tx, r, None);
            self.unify(ar, t, &mut HashSet::new())?;
            t = r;
        }
        let r = self.fresh(false);
        let fuel = self.fuel;
        let want = self.arrows(&[fuel, object_t], r);
        self.unify(want, t, &mut HashSet::new())?;
        let rt = self.con(result_name, vec![]);
        self.unify(rt, r, &mut HashSet::new())?;
        let rt2 = self.con(result_name, vec![]);
        self.env.insert(name.to_string(), Scheme { vars: vec![], data: vec![], ty: rt2 });
        Ok(())
    }

    fn infer_group(&mut self, group: &[String], item_of: &HashMap<String, Item>, expanded: &HashMap<String, E>) {
        for key in group {
            let f = self.fresh(false);
            self.mono.insert(key.clone(), f);
        }
        let mut results: HashMap<String, Ty> = HashMap::new();
        for key in group {
            let (_, core, binders, _, site) = &item_of[key];
            let r = (|| -> FResult<Ty> {
                let mut bound: HashMap<String, Ty> = HashMap::new();
                for b in binders {
                    let f = self.fresh(false);
                    bound.insert(b.clone(), f);
                }
                let params: Vec<Ty> = binders.iter().map(|b| bound[b]).collect();
                let body_t = self.infer(&expanded[key], &bound, core.as_deref())?;
                let t = self.arrows(&params, body_t);
                let m = self.mono[key];
                self.unify(m, t, &mut HashSet::new())?;
                Ok(t)
            })();
            match r {
                Ok(t) => {
                    results.insert(key.clone(), t);
                }
                Err(Fail(m)) => {
                    self.add(site.clone(), m);
                    let f = self.fresh(false);
                    results.insert(key.clone(), f);
                }
            }
        }
        for key in group {
            self.mono.shift_remove(key);
        }
        for key in group {
            let (name, core, ..) = &item_of[key];
            let s = self.generalize(results[key]);
            match core {
                None => {
                    self.env.insert(name.clone(), s);
                }
                Some(c) => {
                    self.core_env.entry(c.clone()).or_default().insert(name.clone(), s);
                }
            }
        }
    }
}

fn names_in(e: &E) -> HashSet<String> {
    fn go(e: &E, out: &mut HashSet<String>) {
        match &**e {
            Expr::Name(n) => {
                out.insert(n.clone());
            }
            Expr::App(f, a) => {
                go(f, out);
                go(a, out);
            }
            Expr::Lambda { body, .. } => go(body, out),
            Expr::Cell(items) => items.iter().for_each(|x| go(x, out)),
            Expr::Pick { expr, .. } => go(expr, out),
            Expr::Case { scrutinee, branches } => {
                go(scrutinee, out);
                for b in branches {
                    go(&b.body, out);
                }
            }
            _ => {}
        }
    }
    let mut out = HashSet::new();
    go(e, &mut out);
    out
}

/// Tarjan's algorithm; groups in dependency order, callees first.
fn sccs(keys: &HashSet<String>, deps: &HashMap<String, HashSet<String>>) -> Vec<Vec<String>> {
    struct St<'a> {
        deps: &'a HashMap<String, HashSet<String>>,
        index: HashMap<String, usize>,
        low: HashMap<String, usize>,
        stack: Vec<String>,
        on: HashSet<String>,
        out: Vec<Vec<String>>,
        counter: usize,
    }
    fn visit(st: &mut St, v: &str) {
        st.index.insert(v.to_string(), st.counter);
        st.low.insert(v.to_string(), st.counter);
        st.counter += 1;
        st.stack.push(v.to_string());
        st.on.insert(v.to_string());
        let mut ws: Vec<String> = st.deps.get(v).map(|s| s.iter().cloned().collect()).unwrap_or_default();
        ws.sort();
        for w in ws {
            if !st.index.contains_key(&w) {
                visit(st, &w);
                let lw = st.low[&w];
                let lv = st.low[v];
                st.low.insert(v.to_string(), lv.min(lw));
            } else if st.on.contains(&w) {
                let iw = st.index[&w];
                let lv = st.low[v];
                st.low.insert(v.to_string(), lv.min(iw));
            }
        }
        if st.low[v] == st.index[v] {
            let mut group = Vec::new();
            loop {
                let w = st.stack.pop().unwrap();
                st.on.remove(&w);
                let done = w == v;
                group.push(w);
                if done {
                    break;
                }
            }
            st.out.push(group);
        }
    }
    let mut st = St { deps, index: HashMap::new(), low: HashMap::new(), stack: Vec::new(), on: HashSet::new(), out: Vec::new(), counter: 0 };
    let mut ks: Vec<&String> = keys.iter().collect();
    ks.sort();
    for v in ks {
        if !st.index.contains_key(v) {
            visit(&mut st, v);
        }
    }
    st.out
}

/// Every Stage B problem in ``program``.  Generates the interface forms
/// first unless ``generated`` says the program already carries them.
pub fn typecheck_program(program: &Program, _prelude: &[&str], generated: bool) -> Result<Vec<Problem>> {
    let owned;
    let prog = if generated {
        program
    } else {
        owned = generate(program)?;
        &owned
    };
    Types::new().run(prog)
}

/// Run Stage B and fail if anything is wrong.
pub fn typecheck(program: &Program, prelude: &[&str], generated: bool) -> Result<()> {
    let problems = typecheck_program(program, prelude, generated)?;
    if problems.is_empty() {
        return Ok(());
    }
    Err(SkijackError::from_problems("Stage B", problems))
}
