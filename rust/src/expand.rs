//! The code generator: syntax tree -> closed ``{S,K,I}`` terms.
//!
//! The passes, in order: macro expansion; case forms, cells and picks;
//! per-equation fixpoints with lambda lifting; bracket abstraction; then
//! quotation and level-1 packaging.

use std::collections::{HashMap, HashSet};

use indexmap::{IndexMap, IndexSet};

use crate::abi::is_tier1;
use crate::ast::{self as A, Decl, Expr, Fuel, Program, E};
use crate::check::check as stage_a;
use crate::env::{bracket_abstract, is_bird, ski_expand, Environment};
use crate::errors::{repr, Result, SkijackError};
use crate::generate::{
    find_answer_type, find_loop_types, find_object_type, find_path_type, generate, AnswerType, ObjectType,
    PathType,
};
use crate::quote::{level1_names, Encoder};
use crate::term::{app as kapp, atom, size, Node, Term};
use crate::typecheck::typecheck;

/// the free atom that stands in for elided fuel, ``<t>@[]``
pub const FUEL_PLACEHOLDER: &str = "\u{0}fuel";

/// names the expander installs before the program is seen
pub const PRELUDE_NAMES: [&str; 7] = ["pair", "hd", "tl", "nil", "cons", "zero", "suc"];

pub const ISA_NAMES: [&str; 3] = ["S", "K", "I"];

fn xerr(msg: String) -> SkijackError {
    SkijackError::Expand(msg)
}

fn a(name: &str) -> Term {
    atom(name)
}

fn k_(parts: &[Term]) -> Term {
    let mut r = parts[0].clone();
    for t in &parts[1..] {
        r = kapp(r, t.clone());
    }
    r
}

// ---------------------------------------------------------------- utilities

/// Names occurring free in an expression.
pub fn free_names(e: &E) -> HashSet<String> {
    let mut out = HashSet::new();
    free_into(e, &mut out);
    out
}

fn free_into(e: &E, out: &mut HashSet<String>) {
    match &**e {
        Expr::Name(n) => {
            out.insert(n.clone());
        }
        Expr::App(f, x) => {
            free_into(f, out);
            free_into(x, out);
        }
        Expr::Cell(items) => items.iter().for_each(|x| free_into(x, out)),
        Expr::Pick { expr, .. } => free_into(expr, out),
        Expr::Lambda { param, body } => {
            let mut inner = HashSet::new();
            free_into(body, &mut inner);
            inner.remove(param);
            out.extend(inner);
        }
        Expr::Case { scrutinee, branches } => {
            free_into(scrutinee, out);
            for b in branches {
                out.insert(b.ctor.clone());
                let mut inner = HashSet::new();
                free_into(&b.body, &mut inner);
                for bn in &b.binders {
                    inner.remove(bn);
                }
                out.extend(inner);
            }
        }
        Expr::Quote { expr, interp, .. } => {
            free_into(expr, out);
            if let Some(i) = interp {
                free_into(i, out);
            }
        }
        Expr::Scry(p) => path_names(p, out),
        Expr::NsLit(facts) => {
            for (p, v) in facts {
                path_names(p, out);
                free_into(v, out);
            }
        }
    }
}

fn path_names(p: &A::Path, out: &mut HashSet<String>) {
    for seg in &p.segments {
        if let Some(pl) = &seg.payload {
            free_into(pl, out);
        }
    }
}

fn fresh(base: &str, taken: &HashSet<String>) -> String {
    if !taken.contains(base) {
        return base.to_string();
    }
    let mut i = 0;
    loop {
        let cand = format!("{}{}", base, i);
        if !taken.contains(&cand) {
            return cand;
        }
        i += 1;
    }
}

/// Capture-avoiding substitution of names by expressions.
pub fn substitute(e: &E, sub: &IndexMap<String, E>) -> Result<E> {
    if sub.is_empty() {
        return Ok(e.clone());
    }
    match &**e {
        Expr::Name(n) => Ok(sub.get(n).cloned().unwrap_or_else(|| e.clone())),
        Expr::App(f, x) => Ok(A::app(substitute(f, sub)?, substitute(x, sub)?)),
        Expr::Cell(items) => {
            let mut out = Vec::new();
            for x in items {
                out.push(substitute(x, sub)?);
            }
            Ok(std::rc::Rc::new(Expr::Cell(out)))
        }
        Expr::Pick { axis, expr } => Ok(std::rc::Rc::new(Expr::Pick { axis: *axis, expr: substitute(expr, sub)? })),
        Expr::Lambda { param, body } => {
            let (param, body) = rename_binder(param, body, sub)?;
            let inner: IndexMap<String, E> = sub.iter().filter(|(k, _)| **k != param).map(|(k, v)| (k.clone(), v.clone())).collect();
            Ok(A::lambda(&param, substitute(&body, &inner)?))
        }
        Expr::Case { scrutinee, branches } => {
            let mut out = Vec::new();
            for b in branches {
                let mut nb = b.binders.clone();
                let mut body = b.body.clone();
                for i in 0..b.binders.len() {
                    let (nbi, nbody) = rename_binder(&b.binders[i], &body, sub)?;
                    nb[i] = nbi;
                    body = nbody;
                }
                let inner: IndexMap<String, E> = sub.iter().filter(|(k, _)| !nb.contains(k)).map(|(k, v)| (k.clone(), v.clone())).collect();
                out.push(A::Branch { ctor: b.ctor.clone(), binders: nb, body: substitute(&body, &inner)? });
            }
            Ok(std::rc::Rc::new(Expr::Case { scrutinee: substitute(scrutinee, sub)?, branches: out }))
        }
        Expr::Quote { expr, fuel, interp } => Ok(std::rc::Rc::new(Expr::Quote {
            expr: substitute(expr, sub)?,
            fuel: fuel.clone(),
            interp: match interp {
                None => None,
                Some(i) => Some(substitute(i, sub)?),
            },
        })),
        Expr::Scry(_) | Expr::NsLit(_) => Err(xerr(
            "quotation, scry and namespace literals are not handled by this step of the expander".to_string(),
        )),
    }
}

fn rename_binder(binder: &str, body: &E, sub: &IndexMap<String, E>) -> Result<(String, E)> {
    let body_free = free_names(body);
    let mut danger: HashSet<String> = HashSet::new();
    for (k, t) in sub {
        if k == binder {
            continue;
        }
        if body_free.contains(k) {
            danger.extend(free_names(t));
        }
    }
    if !danger.contains(binder) {
        return Ok((binder.to_string(), body.clone()));
    }
    let mut taken = danger;
    taken.extend(body_free);
    taken.extend(sub.keys().cloned());
    let fresh_name = fresh(&format!("{}_", binder), &taken);
    let mut one = IndexMap::new();
    one.insert(binder.to_string(), A::name(&fresh_name));
    Ok((fresh_name, substitute(body, &one)?))
}

// ------------------------------------------------------------- pass 1: macros

const MACRO_FUEL: usize = 100;
const MAX_DEPTH: usize = 256;
const MACRO_WORK: usize = 200_000;

struct MacroCtx<'m> {
    macros: &'m IndexMap<String, A::Macro>,
    work: usize,
}

impl<'m> MacroCtx<'m> {
    fn get(&self, name: &str, shadow: &[String]) -> Option<&'m A::Macro> {
        if shadow.iter().any(|s| s == name) {
            return None;
        }
        self.macros.get(name)
    }
}

/// Expand macros to a fixpoint.
pub fn expand_macros(e: &E, macros: &IndexMap<String, A::Macro>) -> Result<E> {
    let mut ctx = MacroCtx { macros, work: MACRO_WORK };
    expand_macros_go(e, &mut ctx, &[], 0, 0)
}

fn expand_macros_go(e: &E, ctx: &mut MacroCtx, shadow: &[String], depth: usize, unfold: usize) -> Result<E> {
    if depth > MAX_DEPTH {
        return Err(xerr(format!("expression nests more than {} levels deep", MAX_DEPTH)));
    }
    if unfold > MACRO_FUEL {
        return Err(xerr(format!(
            "macro expansion did not reach a fixpoint after {} nested unfoldings",
            MACRO_FUEL
        )));
    }
    if ctx.work == 0 {
        return Err(xerr(format!(
            "macro expansion exceeded {} substitutions; a macro that uses another twice costs exponentially in \
             its nesting depth",
            format_thousands(MACRO_WORK)
        )));
    }
    match &**e {
        Expr::Name(n) => {
            if let Some(m) = ctx.get(n, shadow) {
                if !m.params.is_empty() {
                    return Err(xerr(format!(
                        "macro {} takes {} parameter(s); partial application of a macro is an error",
                        repr(&m.name),
                        m.params.len()
                    )));
                }
                ctx.work -= 1;
                let body = m.body.clone();
                return expand_macros_go(&body, ctx, shadow, depth, unfold + 1);
            }
            Ok(e.clone())
        }
        Expr::App(f, x) => {
            let (head, args) = A::spine(e);
            if let Expr::Name(hn) = &*head {
                if let Some(m) = ctx.get(hn, shadow) {
                    if m.capturing {
                        return Err(xerr(format!(
                            "macro {} is declared capturing (':=!'); the capturing form is not implemented",
                            repr(&m.name)
                        )));
                    }
                    let n = m.params.len();
                    if args.len() < n {
                        return Err(xerr(format!(
                            "macro {} takes {} parameter(s) but got {}; partial application of a macro is an error",
                            repr(&m.name),
                            n,
                            args.len()
                        )));
                    }
                    let mut xs = Vec::new();
                    for x in &args {
                        xs.push(expand_macros_go(x, ctx, shadow, depth + 1, unfold)?);
                    }
                    let mut sub = IndexMap::new();
                    for (p, x) in m.params.iter().zip(xs.iter()) {
                        sub.insert(p.clone(), x.clone());
                    }
                    let body = substitute(&m.body, &sub)?;
                    ctx.work -= 1;
                    let mut out = expand_macros_go(&body, ctx, shadow, depth, unfold + 1)?;
                    for extra in &xs[n..] {
                        out = A::app(out, extra.clone());
                    }
                    return Ok(out);
                }
            }
            Ok(A::app(
                expand_macros_go(f, ctx, shadow, depth + 1, unfold)?,
                expand_macros_go(x, ctx, shadow, depth + 1, unfold)?,
            ))
        }
        Expr::Cell(items) => {
            let mut out = Vec::new();
            for x in items {
                out.push(expand_macros_go(x, ctx, shadow, depth + 1, unfold)?);
            }
            Ok(std::rc::Rc::new(Expr::Cell(out)))
        }
        Expr::Pick { axis, expr } => Ok(std::rc::Rc::new(Expr::Pick {
            axis: *axis,
            expr: expand_macros_go(expr, ctx, shadow, depth + 1, unfold)?,
        })),
        Expr::Lambda { param, body } => {
            let mut inner = shadow.to_vec();
            inner.push(param.clone());
            Ok(A::lambda(param, expand_macros_go(body, ctx, &inner, depth + 1, unfold)?))
        }
        Expr::Case { scrutinee, branches } => {
            let mut out = Vec::new();
            for b in branches {
                let mut inner = shadow.to_vec();
                inner.extend(b.binders.iter().cloned());
                out.push(A::Branch {
                    ctor: b.ctor.clone(),
                    binders: b.binders.clone(),
                    body: expand_macros_go(&b.body, ctx, &inner, depth + 1, unfold)?,
                });
            }
            Ok(std::rc::Rc::new(Expr::Case {
                scrutinee: expand_macros_go(scrutinee, ctx, shadow, depth + 1, unfold)?,
                branches: out,
            }))
        }
        Expr::Quote { .. } | Expr::Scry(_) | Expr::NsLit(_) => Err(xerr(
            "quotation, scry and namespace literals are out of scope for this step of the expander".to_string(),
        )),
    }
}

fn format_thousands(n: usize) -> String {
    let s = n.to_string();
    let mut out = String::new();
    for (i, c) in s.chars().enumerate() {
        if i > 0 && (s.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    out
}

// ------------------------------------------ pass 2 and 3: cases, cells, picks

/// The head/tail chain for Nock axis ``n``, outermost last.
pub fn axis_chain(n: u64) -> Result<Vec<&'static str>> {
    if n < 1 {
        return Err(xerr(format!("axis {} does not exist; axes start at 1", n)));
    }
    let bits = 64 - n.leading_zeros();
    let mut out = Vec::new();
    for i in (0..bits - 1).rev() {
        out.push(if (n >> i) & 1 == 0 { "hd" } else { "tl" });
    }
    Ok(out)
}

type CtorTable = HashMap<String, (String, usize, usize)>;

/// Passes 2 and 3: case forms, cells and picks become applications.
pub fn desugar(e: &E, ctors: &CtorTable, types: &IndexMap<String, A::TypeDecl>) -> Result<E> {
    match &**e {
        Expr::Name(_) => Ok(e.clone()),
        Expr::App(f, x) => Ok(A::app(desugar(f, ctors, types)?, desugar(x, ctors, types)?)),
        Expr::Lambda { param, body } => Ok(A::lambda(param, desugar(body, ctors, types)?)),
        Expr::Cell(items) => {
            let mut ds = Vec::new();
            for x in items {
                ds.push(desugar(x, ctors, types)?);
            }
            let mut out = ds[ds.len() - 1].clone();
            for x in ds[..ds.len() - 1].iter().rev() {
                out = A::app(A::app(A::name("pair"), x.clone()), out);
            }
            Ok(out)
        }
        Expr::Pick { axis, expr } => {
            let mut out = desugar(expr, ctors, types)?;
            for step in axis_chain(*axis)? {
                out = A::app(A::name(step), out);
            }
            Ok(out)
        }
        Expr::Case { .. } => lower_case(e, ctors, types),
        Expr::Quote { .. } => Err(xerr("cannot compile Quote in this step".to_string())),
        Expr::Scry(_) => Err(xerr("cannot compile Scry in this step".to_string())),
        Expr::NsLit(_) => Err(xerr("cannot compile NsLit in this step".to_string())),
    }
}

fn lower_case(e: &E, ctors: &CtorTable, types: &IndexMap<String, A::TypeDecl>) -> Result<E> {
    let Expr::Case { scrutinee, branches } = &**e else { unreachable!() };
    if branches.is_empty() {
        return Err(xerr("a case form needs at least one branch".to_string()));
    }
    let first = &branches[0].ctor;
    let Some((tname, _, _)) = ctors.get(first) else {
        return Err(xerr(format!("undeclared constructor {} in a case branch", repr(first))));
    };
    let decl = &types[tname];
    let mut seen: HashMap<String, (Vec<String>, E)> = HashMap::new();
    for b in branches {
        match ctors.get(&b.ctor) {
            Some((t, _, _)) if t == tname => {}
            _ => return Err(xerr(format!("case branch {} is not a constructor of {}", repr(&b.ctor), repr(tname)))),
        }
        if seen.contains_key(&b.ctor) {
            return Err(xerr(format!("case branch {} appears twice", repr(&b.ctor))));
        }
        seen.insert(b.ctor.clone(), (b.binders.clone(), b.body.clone()));
    }
    let missing: Vec<&str> = decl.ctors.iter().filter(|c| !seen.contains_key(&c.name)).map(|c| c.name.as_str()).collect();
    if !missing.is_empty() {
        return Err(xerr(format!(
            "case over {} is missing branch(es) for {}; case must be complete (DESIDERATA.md item 11, Stage A)",
            repr(tname),
            missing.join(", ")
        )));
    }
    let mut out = desugar(scrutinee, ctors, types)?;
    for c in &decl.ctors {
        let (binders, body) = &seen[&c.name];
        let mut k = desugar(body, ctors, types)?;
        for b in binders.iter().rev() {
            k = A::lambda(b, k);
        }
        out = A::app(out, k);
    }
    Ok(out)
}

// --------------------------------------------------- passes 4 and 5: codegen

/// A ``name := I |- <t>@n`` declaration, packaged.
#[derive(Clone)]
pub struct Level1Program {
    pub name: String,
    pub interp: String,
    pub interp_term: Term,
    pub datum: Term,
    pub fuel: Fuel,
    pub object_type: ObjectType,
    pub result_type: A::TypeDecl,
    pub zero: Term,
    pub suc: Term,
    pub params: Vec<Term>,
}

impl Level1Program {
    pub fn numeral(&self, k: usize) -> Term {
        let mut t = self.zero.clone();
        for _ in 0..k {
            t = kapp(self.suc.clone(), t);
        }
        t
    }

    fn apply_fuel(&self, fuel: Term) -> Term {
        let mut t = self.interp_term.clone();
        for p in &self.params {
            t = kapp(t, p.clone());
        }
        kapp(kapp(t, fuel), self.datum.clone())
    }

    /// The closed executable at fuel ``k``.
    pub fn with_fuel(&self, k: usize) -> Term {
        self.apply_fuel(self.numeral(k))
    }

    pub fn placeholder(&self) -> Term {
        self.apply_fuel(a(FUEL_PLACEHOLDER))
    }

    pub fn term(&self) -> Result<Term> {
        match self.fuel {
            Fuel::N(k) => Ok(self.with_fuel(k as usize)),
            Fuel::Policy => Err(xerr(format!(
                "{} has elided fuel ('@[]'); it has no closed term until the runtime policy picks a budget -- use \
                 with_fuel(k), or run.run_policy()",
                repr(&self.name)
            ))),
        }
    }
}

/// The result of [`expand_program`].
pub struct Expansion {
    pub terms: IndexMap<String, Term>,
    pub sizes: IndexMap<String, usize>,
    pub helpers: IndexMap<String, Term>,
    pub backend: HashMap<String, String>,
    pub env: Environment,
    pub types: IndexMap<String, A::TypeDecl>,
    pub ctors: CtorTable,
    pub level1: IndexMap<String, Level1Program>,
    pub object_type: Option<ObjectType>,
    pub answer_type: Option<AnswerType>,
    pub path_type: Option<PathType>,
    pub namespaces: IndexMap<String, Vec<(Term, Term)>>,
}

impl Expansion {
    pub fn term(&self, name: &str) -> Option<&Term> {
        self.terms.get(name)
    }
    pub fn size(&self, name: &str) -> Option<usize> {
        self.sizes.get(name).copied()
    }
}

type Resolver<'r> = &'r dyn Fn(&str) -> Option<Term>;

struct Codegen {
    helper_names: Vec<String>,
    counter: usize,
}

impl Codegen {
    fn gen(&mut self, env: &mut Environment, resolve: Resolver, e: &E, scope: &[String], owner: &str) -> Result<Term> {
        match &**e {
            Expr::Name(n) => {
                if scope.iter().any(|s| s == n) {
                    return Ok(a(n));
                }
                match resolve(n) {
                    Some(t) => Ok(t),
                    None => Err(xerr(format!(
                        "unresolved name {} in {}; free variables do not exist at runtime (SYNTAX.md §8)",
                        repr(n),
                        repr(owner)
                    ))),
                }
            }
            Expr::App(f, x) => {
                let tf = self.gen(env, resolve, f, scope, owner)?;
                let tx = self.gen(env, resolve, x, scope, owner)?;
                Ok(kapp(tf, tx))
            }
            Expr::Lambda { .. } => self.lift(env, resolve, e, scope, owner),
            other => Err(xerr(format!("cannot compile {} in {}", expr_kind(other), repr(owner)))),
        }
    }

    /// Lambda-lift a lambda chain into its own supercombinator.
    fn lift(&mut self, env: &mut Environment, resolve: Resolver, lam: &E, scope: &[String], owner: &str) -> Result<Term> {
        let mut params: Vec<String> = Vec::new();
        let mut body: E = lam.clone();
        while let Expr::Lambda { param, body: b } = &*body {
            params.push(param.clone());
            let next = b.clone();
            body = next;
        }
        let mut fv = free_names(&body);
        for p in &params {
            fv.remove(p);
        }
        let captured: Vec<String> = scope.iter().filter(|s| fv.contains(*s)).cloned().collect();
        let name = self.fresh_name(&format!("{}_b", owner), env);
        let mut inner_scope = captured.clone();
        inner_scope.extend(params);
        let term = self.gen(env, resolve, &body, &inner_scope, owner)?;
        env.define_rule(&name, &inner_scope, term)?;
        self.helper_names.push(name.clone());
        let mut out = a(&name);
        for c in &captured {
            out = kapp(out, a(c));
        }
        Ok(out)
    }

    fn fresh_name(&mut self, base: &str, env: &Environment) -> String {
        self.counter += 1;
        let mut name = format!("{}{}", base, self.counter);
        while env.lookup(&name).is_some() {
            self.counter += 1;
            name = format!("{}{}", base, self.counter);
        }
        name
    }
}

fn expr_kind(e: &Expr) -> &'static str {
    match e {
        Expr::Name(_) => "Name",
        Expr::App(..) => "App",
        Expr::Cell(_) => "Cell",
        Expr::Quote { .. } => "Quote",
        Expr::Scry(_) => "Scry",
        Expr::Pick { .. } => "Pick",
        Expr::Lambda { .. } => "Lambda",
        Expr::Case { .. } => "Case",
        Expr::NsLit(_) => "NsLit",
    }
}

/// A backend name for a source name: the host refuses to shadow a built-in
/// bird, so an equation called ``C`` is defined as ``Cc``.
fn mangle(name: &str, used: &HashSet<String>) -> String {
    let mut cand = name.to_string();
    let suffix: String = name.chars().next().map(|c| c.to_lowercase().collect()).unwrap_or_default();
    while is_bird(&cand) || used.contains(&cand) {
        cand.push_str(&suffix);
    }
    cand
}

// -------------------------------------------------------------- the driver

type Key = (Option<String>, String);

struct Names {
    backend: HashMap<String, String>,
    core_equations: HashMap<String, HashSet<String>>,
    equation_backend: HashMap<(String, String), String>,
}

impl Names {
    /// Name resolution inside ``core`` (``None`` at top level).
    fn resolve(&self, core: Option<&str>, nm: &str) -> Option<Term> {
        if ISA_NAMES.contains(&nm) {
            return Some(a(nm));
        }
        if let Some(c) = core {
            if self.core_equations[c].contains(nm) {
                return Some(a(&self.equation_backend[&(c.to_string(), nm.to_string())]));
            }
        }
        if let Some(b) = self.backend.get(nm) {
            return Some(a(b));
        }
        if is_tier1(nm) {
            return Some(a(nm));
        }
        None
    }
}

/// Compile a program to closed ``{S,K,I}`` terms, one per name.
pub fn expand_program(program: &Program, check: bool, generate_forms: bool) -> Result<Expansion> {
    let mut env = Environment::new();
    if check {
        stage_a(program, &PRELUDE_NAMES)?;
    }
    let generated;
    let program: &Program = if generate_forms {
        generated = generate(program)?;
        &generated
    } else {
        program
    };
    if check {
        typecheck(program, &PRELUDE_NAMES, generate_forms)?;
    }

    // --- collect declarations
    let mut types: IndexMap<String, A::TypeDecl> = IndexMap::new();
    let mut ctors: CtorTable = HashMap::new();
    let mut macros: IndexMap<String, A::Macro> = IndexMap::new();
    let mut equations: Vec<(String, A::Equation, Option<String>)> = Vec::new();
    let mut cores: IndexMap<String, A::Core> = IndexMap::new();
    let mut defs: Vec<(String, E)> = Vec::new();
    let mut qdefs: Vec<(String, E)> = Vec::new();
    for d in &program.decls {
        match d {
            Decl::Type(t) => {
                if types.contains_key(&t.name) {
                    return Err(xerr(format!("type {} declared twice", repr(&t.name))));
                }
                types.insert(t.name.clone(), t.clone());
                for (idx, c) in t.ctors.iter().enumerate() {
                    if ctors.contains_key(&c.name) {
                        return Err(xerr(format!("constructor {} declared twice", repr(&c.name))));
                    }
                    ctors.insert(c.name.clone(), (t.name.clone(), idx, c.fields.len()));
                }
            }
            Decl::Macro(m) => {
                macros.insert(m.name.clone(), m.clone());
            }
            Decl::Sig { .. } => {}
            Decl::Equation(e) => equations.push((e.name.clone(), e.clone(), None)),
            Decl::Core(c) => {
                if cores.contains_key(&c.name) {
                    return Err(xerr(format!("core {} declared twice", repr(&c.name))));
                }
                cores.insert(c.name.clone(), c.clone());
                let mut seen_eq: HashSet<String> = HashSet::new();
                for eq in &c.equations {
                    if !seen_eq.insert(eq.name.clone()) {
                        return Err(xerr(format!(
                            "core {} defines equation {} twice",
                            repr(&c.name),
                            repr(&eq.name)
                        )));
                    }
                    let mut binders = c.params.clone();
                    binders.extend(eq.binders.iter().cloned());
                    equations.push((
                        eq.name.clone(),
                        A::Equation { name: eq.name.clone(), binders, body: eq.body.clone() },
                        Some(c.name.clone()),
                    ));
                }
            }
            Decl::Def { name, expr } => {
                if matches!(&**expr, Expr::Quote { .. } | Expr::NsLit(_)) {
                    qdefs.push((name.clone(), expr.clone()));
                } else {
                    defs.push((name.clone(), expr.clone()));
                }
            }
        }
    }

    // --- the prelude: the Scott pair and its projections
    let mut backend: HashMap<String, String> = HashMap::new();
    let mut used: HashSet<String> = HashSet::new();
    for nm in PRELUDE_NAMES {
        backend.insert(nm.to_string(), nm.to_string());
        used.insert(nm.to_string());
    }
    let s = |x: &str| x.to_string();
    let (x, y, c, p) = ("\u{0}x", "\u{0}y", "\u{0}c", "\u{0}p");
    let (h, t, n, z, sc) = ("\u{0}h", "\u{0}t", "\u{0}n", "\u{0}z", "\u{0}sc");
    env.define_rule("pair", &[s(x), s(y), s(c)], k_(&[a(c), a(x), a(y)]))?;
    env.define_rule("hd", &[s(p)], k_(&[a(p), a("K")]))?;
    env.define_rule("tl", &[s(p)], k_(&[a(p), k_(&[a("K"), a("I")])]))?;
    env.define_rule("nil", &[s(n), s(c)], a(n))?;
    env.define_rule("cons", &[s(h), s(t), s(n), s(c)], k_(&[a(c), a(h), a(t)]))?;
    env.define_rule("zero", &[s(z), s(sc)], a(z))?;
    env.define_rule("suc", &[s(n), s(z), s(sc)], k_(&[a(sc), a(n)]))?;

    // --- backend names
    let mut source_names: Vec<String> = Vec::new();
    for td in types.values() {
        for c in &td.ctors {
            source_names.push(c.name.clone());
        }
    }
    for (name, _, core) in &equations {
        if core.is_none() {
            source_names.push(name.clone());
        }
    }
    for (name, _) in defs.iter().chain(qdefs.iter()) {
        source_names.push(name.clone());
    }
    let mut seen_source: HashSet<String> = HashSet::new();
    for nm in &source_names {
        if !seen_source.insert(nm.clone()) {
            return Err(xerr(format!("{} is defined twice", repr(nm))));
        }
        if PRELUDE_NAMES.contains(&nm.as_str()) {
            continue;
        }
        let m = mangle(nm, &used);
        used.insert(m.clone());
        backend.insert(nm.clone(), m);
    }

    let mut equation_backend: HashMap<(String, String), String> = HashMap::new();
    let mut core_equations: HashMap<String, HashSet<String>> = cores.keys().map(|c| (c.clone(), HashSet::new())).collect();
    for (name, _, core) in &equations {
        let Some(c) = core else { continue };
        core_equations.get_mut(c).unwrap().insert(name.clone());
        let m = mangle(&format!("{}_{}", c, name), &used);
        used.insert(m.clone());
        equation_backend.insert((c.clone(), name.clone()), m);
    }
    for cname in cores.keys() {
        let key = (cname.clone(), "loop".to_string());
        if equation_backend.contains_key(&key) && !backend.contains_key(cname) {
            backend.insert(cname.clone(), equation_backend[&key].clone());
        }
    }
    let names = Names { backend, core_equations, equation_backend };

    // --- the constructors, from the type declarations
    for td in types.values() {
        let nctors = td.ctors.len();
        let conts: Vec<String> = (0..nctors).map(|i| format!("c{}", i)).collect();
        for (idx, c) in td.ctors.iter().enumerate() {
            let fields: Vec<String> = (0..c.fields.len()).map(|i| format!("f{}", i)).collect();
            let mut body = a(&conts[idx]);
            for f in &fields {
                body = kapp(body, a(f));
            }
            let mut formals = fields.clone();
            formals.extend(conts.iter().cloned());
            env.define_rule(&names.backend[&c.name], &formals, body)?;
        }
    }

    let mut cg = Codegen { helper_names: Vec::new(), counter: 0 };

    // --- passes 1..3 on every equation body
    let mut lowered: IndexMap<Key, A::Equation> = IndexMap::new();
    for (name, eq, core) in &equations {
        let body = expand_macros(&eq.body, &macros)?;
        let body = desugar(&body, &ctors, &types)?;
        lowered.insert(
            (core.clone(), name.clone()),
            A::Equation { name: name.clone(), binders: eq.binders.clone(), body },
        );
    }

    let key_of = |core: &Option<String>, nm: &str| -> Option<Key> {
        if let Some(c) = core {
            if names.core_equations[c].contains(nm) && lowered.contains_key(&(core.clone(), nm.to_string())) {
                return Some((core.clone(), nm.to_string()));
            }
        }
        if lowered.contains_key(&(None, nm.to_string())) {
            return Some((None, nm.to_string()));
        }
        None
    };
    let dep_keys = |key: &Key| -> HashSet<Key> {
        let eq = &lowered[key];
        let mut free = free_names(&eq.body);
        for b in &eq.binders {
            free.remove(b);
        }
        let mut out = HashSet::new();
        for nm in &free {
            if ISA_NAMES.contains(&nm.as_str()) {
                continue;
            }
            if let Some(k) = key_of(&key.0, nm) {
                out.insert(k);
            }
        }
        out
    };

    // --- pass 4: recursion.  Per-equation fixpoint; mutual recursion is refused.
    for key in lowered.keys() {
        for okey in dep_keys(key) {
            if &okey == key {
                continue;
            }
            if dep_keys(&okey).contains(key) {
                return Err(xerr(format!(
                    "equations {} and {} are mutually recursive; this expander ties one fixpoint per equation and \
                     cannot compile mutual recursion yet",
                    repr(&key.1),
                    repr(&okey.1)
                )));
            }
        }
    }

    for (key, eq) in lowered.iter() {
        let (core, name) = key;
        let bname = match core {
            None => names.backend[name].clone(),
            Some(c) => names.equation_backend[&(c.clone(), name.clone())].clone(),
        };
        let core_ref = core.as_deref();
        let resolve = |nm: &str| names.resolve(core_ref, nm);
        let recursive = dep_keys(key).contains(key);
        if recursive {
            let mut taken: HashSet<String> = eq.binders.iter().cloned().collect();
            taken.extend(free_names(&eq.body));
            let selfp = fresh("f", &taken);
            let mut sub = IndexMap::new();
            sub.insert(name.clone(), A::name(&selfp));
            let body = substitute(&eq.body, &sub)?;
            let mut scope = vec![selfp];
            scope.extend(eq.binders.iter().cloned());
            let gen_name = mangle(&format!("{}Gen", bname), &used);
            used.insert(gen_name.clone());
            let term = cg.gen(&mut env, &resolve, &body, &scope, &bname)?;
            env.define_rule(&gen_name, &scope, term)?;
            env.define_alias(&bname, k_(&[a("Y"), a(&gen_name)]))?;
        } else {
            let scope: Vec<String> = eq.binders.clone();
            let term = cg.gen(&mut env, &resolve, &eq.body, &scope, &bname)?;
            env.define_rule(&bname, &scope, term)?;
        }
    }

    // --- plain definitions (``name := expr``)
    let top_resolve = |nm: &str| names.resolve(None, nm);
    for (name, expr) in &defs {
        let body = expand_macros(expr, &macros)?;
        let body = desugar(&body, &ctors, &types)?;
        let bname = names.backend[name].clone();
        let term = cg.gen(&mut env, &top_resolve, &body, &[], &bname)?;
        env.define_alias(&bname, term)?;
    }

    // --- pass 5: bracket abstraction
    let mut out = Expansion {
        terms: IndexMap::new(),
        sizes: IndexMap::new(),
        helpers: IndexMap::new(),
        backend: names.backend.clone(),
        env: Environment::new(), // replaced at the end
        types: types.clone(),
        ctors: ctors.clone(),
        level1: IndexMap::new(),
        object_type: None,
        answer_type: None,
        path_type: None,
        namespaces: IndexMap::new(),
    };
    let quoted_names: HashSet<String> = qdefs.iter().map(|(n, _)| n.clone()).collect();
    let mut level0: IndexSet<String> = IndexSet::new();
    for n in source_names.iter().cloned().chain(PRELUDE_NAMES.iter().map(|s| s.to_string())) {
        level0.insert(n);
    }
    let level0: Vec<String> = level0.into_iter().filter(|n| !quoted_names.contains(n)).collect();
    let mut bare_count: HashMap<String, usize> = HashMap::new();
    for (core, name) in lowered.keys() {
        if core.is_some() {
            *bare_count.entry(name.clone()).or_insert(0) += 1;
        }
    }

    let expand_all = |env: &mut Environment, out: &mut Expansion, cg: &Codegen| -> Result<()> {
        for nm in &level0 {
            let t = ski_expand(&a(&names.backend[nm]), env)?;
            out.sizes.insert(nm.clone(), size(&t));
            out.terms.insert(nm.clone(), t);
        }
        for (core, name) in lowered.keys() {
            let Some(c) = core else { continue };
            let t = ski_expand(&a(&names.equation_backend[&(c.clone(), name.clone())]), env)?;
            let dotted = format!("{}.{}", c, name);
            out.sizes.insert(dotted.clone(), size(&t));
            out.terms.insert(dotted, t.clone());
            if bare_count[name] == 1 && !quoted_names.contains(name) {
                out.sizes.insert(name.clone(), size(&t));
                out.terms.insert(name.clone(), t);
            }
        }
        for cname in cores.keys() {
            let dotted = format!("{}.loop", cname);
            if lowered.contains_key(&(Some(cname.clone()), "loop".to_string())) {
                let t = out.terms[&dotted].clone();
                let sz = out.sizes[&dotted];
                out.terms.insert(cname.clone(), t);
                out.sizes.insert(cname.clone(), sz);
            }
        }
        for h in &cg.helper_names {
            let t = ski_expand(&a(h), env)?;
            out.helpers.insert(h.clone(), t);
        }
        Ok(())
    };

    expand_all(&mut env, &mut out, &cg)?;

    // --- pass 6: quotation and level-1 packaging
    if !qdefs.is_empty() {
        let Some(obj) = find_object_type(program)? else {
            return Err(xerr(
                "quotation needs an object type: declare the alphabet the quoted term is written in, e.g. \
                 'term === S | K | I | App term term'"
                    .to_string(),
            ));
        };
        out.object_type = Some(obj.clone());
        let lt = find_loop_types(program, &obj)?;
        out.answer_type = find_answer_type(program, &obj, &lt)?;
        out.path_type = find_path_type(program)?;
        let term_of = |n: &str| out.terms[n].clone();
        let enc = Encoder::new(&obj, &term_of);
        let leafmap = level1_names(&obj);
        let scry_leaf: Option<String> = obj.leaves.iter().find(|c| c.name == "Scry").map(|c| c.name.clone());
        let path_type = out.path_type.clone();

        let mut q = Quoter {
            obj: &obj,
            enc: &enc,
            leafmap: &leafmap,
            scry_leaf: scry_leaf.as_deref(),
            path_type: path_type.as_ref(),
            ctors: &ctors,
            types: &types,
            macros: &macros,
            names: &names,
            cg: &mut cg,
            env: &mut env,
        };

        // 6a: every datum and resolver, in declaration order
        let mut packaged: Vec<(String, E, Term)> = Vec::new();
        for (dname, expr) in &qdefs {
            match &**expr {
                Expr::NsLit(facts) => {
                    compile_nslit(dname, facts, &mut out, &mut q, &names.backend[dname])?;
                    continue;
                }
                Expr::Quote { expr: qe, fuel, interp } => {
                    let datum = q.quote_expr(qe, dname)?;
                    if fuel.is_none() && interp.is_none() {
                        out.sizes.insert(dname.clone(), size(&datum));
                        out.terms.insert(dname.clone(), datum.clone());
                        q.env.define_alias(&names.backend[dname], datum)?;
                        continue;
                    }
                    packaged.push((dname.clone(), expr.clone(), datum));
                }
                _ => return Err(xerr(format!("{}: expected a quotation", repr(dname)))),
            }
        }

        // 6b: a level-0 equation may name one of those datums, so expand again
        expand_all(&mut env, &mut out, &cg)?;

        // 6c: package the level-1 executables
        for (dname, expr, datum) in packaged {
            let Expr::Quote { fuel, interp, .. } = &*expr else { unreachable!() };
            let (iname, iargs) = interp_spine(interp.as_ref(), &cores, &dname)?;
            if !lowered.contains_key(&(Some(iname.clone()), "loop".to_string())) {
                return Err(xerr(format!(
                    "{}: {} is not an interpreter core (it has no fuel loop)",
                    repr(&dname),
                    repr(&iname)
                )));
            }
            let mut params: Vec<Term> = Vec::new();
            for arg in &iargs {
                let body = desugar(&expand_macros(arg, &macros)?, &ctors, &types)?;
                params.push(cg.gen(&mut env, &top_resolve, &body, &[], &dname)?);
            }
            let mut expanded_params = Vec::new();
            for t in &params {
                expanded_params.push(ski_expand(t, &mut env)?);
            }
            let prog = Level1Program {
                name: dname.clone(),
                interp: iname.clone(),
                interp_term: out.terms[&iname].clone(),
                datum,
                fuel: fuel.clone().unwrap_or(Fuel::Policy),
                object_type: obj.clone(),
                result_type: lt.result.clone(),
                zero: out.terms["zero"].clone(),
                suc: out.terms["suc"].clone(),
                params: expanded_params,
            };
            if let Fuel::N(_) = prog.fuel {
                let t = prog.term()?;
                out.sizes.insert(dname.clone(), size(&t));
                out.terms.insert(dname.clone(), t);
            }
            out.level1.insert(dname, prog);
        }
    }
    out.env = env;
    Ok(out)
}

struct Quoter<'q> {
    obj: &'q ObjectType,
    enc: &'q Encoder,
    leafmap: &'q HashMap<String, String>,
    scry_leaf: Option<&'q str>,
    path_type: Option<&'q PathType>,
    ctors: &'q CtorTable,
    types: &'q IndexMap<String, A::TypeDecl>,
    macros: &'q IndexMap<String, A::Macro>,
    names: &'q Names,
    cg: &'q mut Codegen,
    env: &'q mut Environment,
}

impl<'q> Quoter<'q> {
    /// ``/nat/three`` is ``Cons Nat (Cons Three Nil)``.
    fn path_expr(&self, path: &A::Path, owner: &str) -> Result<E> {
        let Some(pt) = self.path_type else {
            return Err(xerr(format!(
                "{}: a path literal needs the path type; declare 'path === Nil | Cons seg path' (SYNTAX.md §6)",
                repr(owner)
            )));
        };
        let mut e = A::name(&pt.nil.name);
        for seg in path.segments.iter().rev() {
            if seg.payload.is_some() {
                return Err(xerr(format!(
                    "{}: a segment payload ('/vane/care[<t>]/desk') is not compiled yet",
                    repr(owner)
                )));
            }
            let cname = crate::check::capitalize(&seg.tag);
            match self.ctors.get(&cname) {
                Some((t, _, _)) if *t == pt.seg => {}
                _ => {
                    return Err(xerr(format!(
                        "{}: path segment {} names no constructor {} of the segment type {}",
                        repr(owner),
                        repr(&seg.tag),
                        repr(&cname),
                        repr(&pt.seg)
                    )))
                }
            }
            e = A::app(A::app(A::name(&pt.cons.name), A::name(&cname)), e);
        }
        Ok(e)
    }

    /// Replace each nested quotation by a placeholder name, compiling it
    /// to its datum first.
    fn strip(&mut self, e: &E, owner: &str, subs: &mut HashMap<String, Term>) -> Result<E> {
        Ok(match &**e {
            Expr::Quote { expr, fuel, interp } => {
                if fuel.is_some() || interp.is_some() {
                    return Err(xerr(format!(
                        "{}: a nested quotation is a datum and may not carry fuel or an interpreter",
                        repr(owner)
                    )));
                }
                let nm = format!("\u{0}quote:{}", subs.len());
                let d = self.quote_expr(expr, owner)?;
                subs.insert(nm.clone(), d);
                A::name(&nm)
            }
            Expr::App(f, x) => A::app(self.strip(f, owner, subs)?, self.strip(x, owner, subs)?),
            Expr::Cell(items) => {
                let mut out = Vec::new();
                for x in items {
                    out.push(self.strip(x, owner, subs)?);
                }
                std::rc::Rc::new(Expr::Cell(out))
            }
            Expr::Pick { axis, expr } => std::rc::Rc::new(Expr::Pick { axis: *axis, expr: self.strip(expr, owner, subs)? }),
            Expr::Lambda { param, body } => A::lambda(param, self.strip(body, owner, subs)?),
            Expr::Case { scrutinee, branches } => {
                let mut out = Vec::new();
                for b in branches {
                    out.push(A::Branch { ctor: b.ctor.clone(), binders: b.binders.clone(), body: self.strip(&b.body, owner, subs)? });
                }
                std::rc::Rc::new(Expr::Case { scrutinee: self.strip(scrutinee, owner, subs)?, branches: out })
            }
            Expr::Scry(path) => {
                let Some(leaf) = self.scry_leaf else {
                    return Err(xerr(format!(
                        "{}: the object type {} has no 'Scry' leaf, so '?^' has nothing to build",
                        repr(owner),
                        repr(self.obj.name())
                    )));
                };
                let pe = self.path_expr(path, owner)?;
                A::app(A::name(leaf), self.strip(&pe, owner, subs)?)
            }
            Expr::NsLit(_) => {
                return Err(xerr(format!(
                    "{}: a namespace literal is a resolver, not a quotable term",
                    repr(owner)
                )))
            }
            Expr::Name(_) => e.clone(),
        })
    }

    /// Compile a quoted expression to its datum.
    fn quote_expr(&mut self, expr: &E, owner: &str) -> Result<Term> {
        let mut subs: HashMap<String, Term> = HashMap::new();
        let body = self.strip(expr, owner, &mut subs)?;
        let body = expand_macros(&body, self.macros)?;
        let body = desugar(&body, self.ctors, self.types)?;
        let names = self.names;
        let leafmap = self.leafmap;
        let qresolve = |nm: &str| -> Option<Term> {
            if subs.contains_key(nm) {
                return Some(a(nm));
            }
            if let Some(l) = leafmap.get(nm) {
                return Some(a(l));
            }
            names.resolve(None, nm)
        };
        let term = self.cg.gen(self.env, &qresolve, &body, &[], owner)?;
        let mut term = ski_expand(&term, self.env)?;
        if !subs.is_empty() {
            term = splice(&term, &subs);
        }
        self.enc.quote(&term)
    }
}

/// ``ns{/nat/two => <I>, /nat/three => <K>}`` is a resolver.
fn compile_nslit(dname: &str, facts: &[(A::Path, E)], out: &mut Expansion, q: &mut Quoter, bname: &str) -> Result<()> {
    let Some(at) = out.answer_type.clone() else {
        return Err(xerr(format!(
            "{}: a namespace literal needs an oracle answer type; declare one, e.g. 'oanswer === OJust t | ONothing | ONotYet'",
            repr(dname)
        )));
    };
    if !out.terms.contains_key("EQ5") {
        return Err(xerr(format!(
            "{}: a namespace literal compares paths with 'EQ5', which this program does not define",
            repr(dname)
        )));
    }
    let mut pairs: Vec<(Term, Term)> = Vec::new();
    for (path, value) in facts {
        let Expr::Quote { expr, fuel: None, interp: None } = &**value else {
            return Err(xerr(format!(
                "{}: a fact's value must be a quotation, e.g. '/nat/two => <I>'; it is stored as data",
                repr(dname)
            )));
        };
        let pe = q.path_expr(path, dname)?;
        let key = q.quote_expr(&pe, dname)?;
        let val = q.quote_expr(expr, dname)?;
        pairs.push((key, val));
    }
    out.namespaces.insert(dname.to_string(), pairs.clone());
    let term = resolver_term(&out.terms["EQ5"], &out.terms[&at.hit.name], &out.terms[&at.notyet.name], &pairs);
    out.sizes.insert(dname.to_string(), size(&term));
    out.terms.insert(dname.to_string(), term.clone());
    q.env.define_alias(bname, term)?;
    Ok(())
}

const RESOLVER_BINDER: &str = "\u{0}p";

/// The closed resolver for a list of (key datum, answer datum) pairs.
pub fn resolver_term(eq: &Term, hit: &Term, notyet: &Term, facts: &[(Term, Term)]) -> Term {
    let mut body = notyet.clone();
    for (key, ans) in facts.iter().rev() {
        body = k_(&[eq.clone(), a(RESOLVER_BINDER), key.clone(), kapp(hit.clone(), ans.clone()), body]);
    }
    bracket_abstract(RESOLVER_BINDER, &body)
}

/// Which interpreter core runs a level-1 declaration, and with what arguments.
fn interp_spine(interp: Option<&E>, cores: &IndexMap<String, A::Core>, owner: &str) -> Result<(String, Vec<E>)> {
    let Some(interp) = interp else {
        if cores.contains_key("whnfF") {
            return Ok(("whnfF".to_string(), vec![]));
        }
        return Err(xerr(format!(
            "{}: no interpreter given and no core named 'whnfF' to default to; write 'I |- <t>@n'",
            repr(owner)
        )));
    };
    let (head, args) = A::spine(interp);
    let Expr::Name(hn) = &*head else {
        return Err(xerr(format!(
            "{}: the interpreter left of '|-' must be a core, optionally applied to its parameters",
            repr(owner)
        )));
    };
    let Some(core) = cores.get(hn) else {
        return Err(xerr(format!("{}: {} is not a core in this program", repr(owner), repr(hn))));
    };
    let want = core.params.len();
    if args.len() != want {
        return Err(xerr(format!(
            "{}: core {} takes {} parameter(s) but got {}; an interpreter is applied to all of them before its fuel",
            repr(owner),
            repr(hn),
            want,
            args.len()
        )));
    }
    Ok((hn.clone(), args))
}

/// Replace placeholder atoms by their terms, iteratively.
fn splice(term: &Term, subs: &HashMap<String, Term>) -> Term {
    let mut out: Vec<Term> = Vec::new();
    let mut work: Vec<(&Term, bool)> = vec![(term, false)];
    while let Some((x, done)) = work.pop() {
        match &**x {
            Node::Atom(n) => out.push(subs.get(&**n).cloned().unwrap_or_else(|| x.clone())),
            Node::App(f, arg) => {
                if !done {
                    work.push((x, true));
                    work.push((arg, false));
                    work.push((f, false));
                } else {
                    let r = out.pop().unwrap();
                    let l = out.pop().unwrap();
                    out.push(kapp(l, r));
                }
            }
        }
    }
    out.pop().unwrap()
}
