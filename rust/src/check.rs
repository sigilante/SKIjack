//! Stage A: the checker.  A pass that can reject and never rewrites.

use std::collections::{HashMap, HashSet};

use indexmap::IndexMap;

use crate::abi::{is_isa, is_tier1};
use crate::ast::{self as A, Decl, Expr, Program, E};
use crate::errors::{repr, Problem, ProblemKind, Result, Site, SkijackError};
use crate::generate::{find_object_type, find_path_type, is_interpreter_core, names_generation_adds, ObjectType, PathType};

struct Env {
    types: IndexMap<String, A::TypeDecl>,
    ctors: HashMap<String, (String, usize, usize)>,
    macros: HashMap<String, A::Macro>,
    equations: HashMap<String, A::Equation>,
    core_equations: HashMap<String, HashMap<String, A::Equation>>,
    cores: HashMap<String, A::Core>,
    defs: HashSet<String>,
    generated: HashSet<String>,
    core_generated: HashMap<String, HashSet<String>>,
    obj: Option<ObjectType>,
    path: Option<PathType>,
    prelude: Vec<String>,
}

impl Env {
    fn known(&self, name: &str, core: Option<&str>) -> bool {
        if is_isa(name) || is_tier1(name) || self.prelude.iter().any(|p| p == name) {
            return true;
        }
        if let Some(c) = core {
            if self.core_equations.get(c).map(|m| m.contains_key(name)).unwrap_or(false) {
                return true;
            }
            if self.core_generated.get(c).map(|s| s.contains(name)).unwrap_or(false) {
                return true;
            }
            if self.cores[c].params.iter().any(|p| p == name) {
                return true;
            }
        }
        self.ctors.contains_key(name)
            || self.equations.contains_key(name)
            || self.defs.contains(name)
            || self.cores.contains_key(name)
            || self.generated.contains(name)
            || self.macros.contains_key(name)
    }
}

struct Checker<'p> {
    program: &'p Program,
    problems: Vec<Problem>,
    env: Env,
}

impl<'p> Checker<'p> {
    fn new(program: &'p Program, prelude: &[&str]) -> Checker<'p> {
        let mut c = Checker {
            program,
            problems: Vec::new(),
            env: Env {
                types: IndexMap::new(),
                ctors: HashMap::new(),
                macros: HashMap::new(),
                equations: HashMap::new(),
                core_equations: HashMap::new(),
                cores: HashMap::new(),
                defs: HashSet::new(),
                generated: HashSet::new(),
                core_generated: HashMap::new(),
                obj: None,
                path: None,
                prelude: prelude.iter().map(|s| s.to_string()).collect(),
            },
        };
        c.collect();
        c
    }

    fn add(&mut self, kind: ProblemKind, site: Site, message: String) {
        self.problems.push(Problem { kind, site, message });
    }

    fn collect(&mut self) {
        let mut seen: HashMap<String, &'static str> = HashMap::new();
        let mut problems: Vec<Problem> = Vec::new();
        fn declare(
            seen: &mut HashMap<String, &'static str>,
            problems: &mut Vec<Problem>,
            name: &str,
            what: &'static str,
            site: Site,
        ) {
            if let Some(prev) = seen.get(name) {
                problems.push(Problem {
                    kind: ProblemKind::Scope,
                    site,
                    message: format!("{} is declared twice (already a {})", repr(name), prev),
                });
            }
            seen.insert(name.to_string(), what);
        }
        for d in &self.program.decls {
            match d {
                Decl::Type(t) => {
                    declare(&mut seen, &mut problems, &t.name, "type", Site::raw(&format!("type {}", t.name)));
                    if self.env.types.contains_key(&t.name) {
                        continue;
                    }
                    self.env.types.insert(t.name.clone(), t.clone());
                    for (i, c) in t.ctors.iter().enumerate() {
                        declare(&mut seen, &mut problems, &c.name, "constructor", Site::raw(&format!("type {}", t.name)));
                        self.env.ctors.entry(c.name.clone()).or_insert((t.name.clone(), i, c.fields.len()));
                    }
                }
                Decl::Macro(m) => {
                    declare(&mut seen, &mut problems, &m.name, "macro", Site::raw(&format!("macro {}", m.name)));
                    self.env.macros.insert(m.name.clone(), m.clone());
                }
                Decl::Equation(e) => {
                    declare(&mut seen, &mut problems, &e.name, "equation", Site::new("equation", &e.name));
                    self.env.equations.insert(e.name.clone(), e.clone());
                }
                Decl::Core(c) => {
                    declare(&mut seen, &mut problems, &c.name, "core", Site::new("core", &c.name));
                    self.env.cores.insert(c.name.clone(), c.clone());
                    let mut inner: HashMap<String, A::Equation> = HashMap::new();
                    for eq in &c.equations {
                        if inner.contains_key(&eq.name) {
                            problems.push(Problem {
                                kind: ProblemKind::Scope,
                                site: Site::new("core", &c.name),
                                message: format!("equation {} is defined twice", repr(&eq.name)),
                            });
                        }
                        inner.insert(eq.name.clone(), eq.clone());
                    }
                    self.env.core_equations.insert(c.name.clone(), inner);
                }
                Decl::Def { name, .. } => {
                    declare(&mut seen, &mut problems, name, "definition", Site::raw(&format!("definition {}", name)));
                    self.env.defs.insert(name.clone());
                }
                Decl::Sig { .. } => {}
            }
        }
        self.problems.extend(problems);
        let r = (|| -> Result<()> {
            self.env.obj = find_object_type(self.program)?;
            self.env.path = find_path_type(self.program)?;
            let (top, per_core) = names_generation_adds(self.program)?;
            self.env.generated = top;
            self.env.core_generated = per_core;
            Ok(())
        })();
        if let Err(e) = r {
            self.add(ProblemKind::Interface, Site::raw("the program"), e.message().to_string());
        }
    }

    fn run(mut self) -> Vec<Problem> {
        for d in &self.program.decls {
            match d {
                Decl::Equation(e) => {
                    let bound: HashSet<String> = e.binders.iter().cloned().collect();
                    self.expr(&e.body, &Site::new("equation", &e.name), None, &bound, false);
                }
                Decl::Macro(m) => {
                    let bound: HashSet<String> = m.params.iter().cloned().collect();
                    self.expr(&m.body, &Site::new("macro", &m.name), None, &bound, true);
                }
                Decl::Core(c) => self.core(c),
                Decl::Def { name, expr } => self.definition(name, expr),
                _ => {}
            }
        }
        self.problems
    }

    fn core(&mut self, d: &A::Core) {
        let bound: HashSet<String> = d.params.iter().cloned().collect();
        for eq in &d.equations {
            let mut b = bound.clone();
            b.extend(eq.binders.iter().cloned());
            self.expr(&eq.body, &Site::in_core("equation", &eq.name, &d.name), Some(&d.name), &b, false);
        }
        if let Some(obj) = self.env.obj.clone() {
            if is_interpreter_core(d, &obj) {
                self.interface(d, &obj);
            }
        }
    }

    fn definition(&mut self, name: &str, expr: &E) {
        let site = Site::new("definition", name);
        match &**expr {
            Expr::NsLit(facts) => {
                for (path, value) in facts {
                    self.path_literal(path, &site);
                    match &**value {
                        Expr::Quote { expr, fuel: None, interp: None } => self.quoted(expr, &site),
                        _ => self.add(
                            ProblemKind::Data,
                            site.clone(),
                            "a namespace fact's value must be data (a quotation); §5 rule 3: a function cannot be \
                             stored as a fact"
                                .to_string(),
                        ),
                    }
                }
            }
            Expr::Quote { expr: inner, interp, .. } => {
                if let Some(i) = interp {
                    self.interp_application(i, &site);
                }
                self.quoted(inner, &site);
            }
            _ => self.expr(expr, &site, None, &HashSet::new(), false),
        }
    }

    fn expr(&mut self, e: &E, site: &Site, core: Option<&str>, bound: &HashSet<String>, is_macro: bool) {
        match &**e {
            Expr::Name(nm) => self.name(nm, site, core, bound, is_macro),
            Expr::App(..) => {
                let (head, args) = A::spine(e);
                self.eq_position(&head, &args, site, core, bound);
                self.expr(&head, site, core, bound, is_macro);
                for x in &args {
                    self.expr(x, site, core, bound, is_macro);
                }
            }
            Expr::Cell(items) => {
                for x in items {
                    self.expr(x, site, core, bound, is_macro);
                }
            }
            Expr::Pick { expr, .. } => self.expr(expr, site, core, bound, is_macro),
            Expr::Lambda { param, body } => {
                let mut b = bound.clone();
                b.insert(param.clone());
                self.expr(body, site, core, &b, is_macro);
            }
            Expr::Case { .. } => self.case(e, site, core, bound, is_macro),
            Expr::Quote { expr, interp, .. } => {
                if let Some(i) = interp {
                    self.expr(i, site, core, bound, is_macro);
                }
                self.quoted(expr, site);
            }
            Expr::Scry(_) => self.add(
                ProblemKind::Data,
                site.clone(),
                "'?^' is live only inside a quotation (§6: nothing at level 0 may use a scry)".to_string(),
            ),
            Expr::NsLit(_) => self.add(
                ProblemKind::Data,
                site.clone(),
                "a namespace literal is a resolver; it belongs on the right of a definition".to_string(),
            ),
        }
    }

    fn name(&mut self, nm: &str, site: &Site, core: Option<&str>, bound: &HashSet<String>, is_macro: bool) {
        if bound.contains(nm) || is_macro {
            return;
        }
        if !self.env.known(nm, core) {
            self.add(
                ProblemKind::Scope,
                site.clone(),
                format!("unresolved name {}; free variables do not exist at runtime (SYNTAX.md §8)", repr(nm)),
            );
        }
    }

    fn case(&mut self, e: &E, site: &Site, core: Option<&str>, bound: &HashSet<String>, is_macro: bool) {
        let Expr::Case { scrutinee, branches } = &**e else { unreachable!() };
        self.expr(scrutinee, site, core, bound, is_macro);
        if branches.is_empty() {
            self.add(ProblemKind::Case, site.clone(), "a case form needs at least one branch".to_string());
            return;
        }
        let first = &branches[0].ctor;
        let Some((tname, _, _)) = self.env.ctors.get(first).cloned() else {
            self.add(ProblemKind::Case, site.clone(), format!("undeclared constructor {} in a case branch", repr(first)));
            return;
        };
        let decl = self.env.types[&tname].clone();
        let mut seen: HashSet<String> = HashSet::new();
        for b in branches {
            let Some((ct, _, _)) = self.env.ctors.get(&b.ctor).cloned() else {
                self.add(ProblemKind::Case, site.clone(), format!("undeclared constructor {} in a case branch", repr(&b.ctor)));
                continue;
            };
            if ct != tname {
                self.add(
                    ProblemKind::Case,
                    site.clone(),
                    format!("branch {} is a constructor of {}, but the case is over {}", repr(&b.ctor), repr(&ct), repr(&tname)),
                );
                continue;
            }
            if seen.contains(&b.ctor) {
                self.add(ProblemKind::Case, site.clone(), format!("branch {} appears twice", repr(&b.ctor)));
            }
            seen.insert(b.ctor.clone());
            let mut bb = bound.clone();
            bb.extend(b.binders.iter().cloned());
            self.expr(&b.body, site, core, &bb, is_macro);
        }
        let missing: Vec<&str> = decl.ctors.iter().filter(|c| !seen.contains(&c.name)).map(|c| c.name.as_str()).collect();
        if !missing.is_empty() {
            self.add(
                ProblemKind::Case,
                site.clone(),
                format!(
                    "case over {} is missing branch(es) for {}; a case must be complete, and the continuations are \
                     emitted in declaration order (DESIDERATA.md item 11)",
                    repr(&tname),
                    missing.join(", ")
                ),
            );
        }
    }

    fn eq_position(&mut self, head: &E, args: &[E], site: &Site, core: Option<&str>, bound: &HashSet<String>) {
        if !matches!(&**head, Expr::Name(n) if n == "EQ") {
            return;
        }
        for (i, x) in args.iter().take(2).enumerate() {
            if let Some(why) = self.provably_function(x, core, bound) {
                self.add(
                    ProblemKind::Data,
                    site.clone(),
                    format!("argument {} of 'EQ' is {}; §5 rule 3: a value of function type cannot be compared", i + 1, why),
                );
            }
        }
    }

    fn provably_function(&self, e: &E, core: Option<&str>, bound: &HashSet<String>) -> Option<String> {
        match &**e {
            Expr::Quote { .. } | Expr::Scry(_) | Expr::Cell(_) => return None,
            Expr::Lambda { .. } => return Some("a lambda".to_string()),
            Expr::NsLit(_) => return Some("a resolver".to_string()),
            _ => {}
        }
        let (head, args) = A::spine(e);
        let Expr::Name(nm) = &*head else { return None };
        if bound.contains(nm) {
            return None;
        }
        if is_isa(nm) || is_tier1(nm) {
            return Some(format!("the combinator {}", repr(nm)));
        }
        if let Some((_, _, arity)) = self.env.ctors.get(nm) {
            if args.len() < *arity {
                return Some(format!(
                    "the constructor {} applied to {} of its {} field(s), which is a function",
                    repr(nm),
                    args.len(),
                    arity
                ));
            }
            return None;
        }
        if self.env.macros.contains_key(nm) {
            return Some(format!("the macro {}", repr(nm)));
        }
        if let Some(eq) = self.env.equations.get(nm) {
            if !eq.binders.is_empty() {
                return Some(format!("the equation {}", repr(nm)));
            }
        }
        if let Some(c) = core {
            if let Some(eq) = self.env.core_equations.get(c).and_then(|m| m.get(nm)) {
                if !eq.binders.is_empty() {
                    return Some(format!("the equation {}", repr(nm)));
                }
            }
        }
        if self.env.cores.contains_key(nm) {
            return Some(format!("the core {}", repr(nm)));
        }
        None
    }

    fn quoted(&mut self, e: &E, site: &Site) {
        let obj = self.env.obj.clone();
        match &**e {
            Expr::Scry(path) => {
                self.path_literal(path, site);
                if let Some(o) = &obj {
                    if !o.leaves.iter().any(|c| c.name == "Scry") {
                        self.add(
                            ProblemKind::SymbolTable,
                            site.clone(),
                            format!("'?^' needs a 'Scry' leaf in the object type {}", repr(o.name())),
                        );
                    }
                }
            }
            Expr::Quote { expr, fuel, interp } => {
                if fuel.is_some() || interp.is_some() {
                    self.add(
                        ProblemKind::Data,
                        site.clone(),
                        "a nested quotation is a datum and may not carry fuel or an interpreter".to_string(),
                    );
                }
                self.quoted(expr, site);
            }
            Expr::NsLit(_) => self.add(
                ProblemKind::Data,
                site.clone(),
                "a namespace literal is a resolver, not a quotable term".to_string(),
            ),
            Expr::Lambda { body, .. } => self.quoted(body, site),
            Expr::Cell(items) => {
                for x in items {
                    self.quoted(x, site);
                }
            }
            Expr::Pick { expr, .. } => self.quoted(expr, site),
            Expr::Case { scrutinee, branches } => {
                self.quoted(scrutinee, site);
                for b in branches {
                    self.quoted(&b.body, site);
                }
            }
            Expr::Name(_) | Expr::App(..) => {
                let (head, args) = A::spine(e);
                for x in &args {
                    self.quoted(x, site);
                }
                let Expr::Name(nm) = &*head else {
                    self.quoted(&head, site);
                    return;
                };
                let obj_names: HashSet<&str> = match &obj {
                    Some(o) => o.decl.ctors.iter().map(|c| c.name.as_str()).collect(),
                    None => HashSet::new(),
                };
                if obj_names.contains(nm.as_str()) {
                    return;
                }
                if self.env.known(nm, None) {
                    if let Some((_, _, arity)) = self.env.ctors.get(nm) {
                        if args.len() != *arity {
                            self.add(
                                ProblemKind::Arity,
                                site.clone(),
                                format!(
                                    "constructor {} takes {} field(s) but is given {} inside a quotation, where it \
                                     denotes data",
                                    repr(nm),
                                    arity,
                                    args.len()
                                ),
                            );
                        }
                    }
                    return;
                }
                let tail = match &obj {
                    Some(o) => format!(" {}", repr(o.name())),
                    None => String::new(),
                };
                self.add(
                    ProblemKind::SymbolTable,
                    site.clone(),
                    format!(
                        "{} names neither table (§6b): it is not a constructor of the object type{} and not a level-0 name",
                        repr(nm),
                        tail
                    ),
                );
            }
        }
    }

    fn path_literal(&mut self, path: &A::Path, site: &Site) {
        let Some(pt) = self.env.path.clone() else {
            self.add(
                ProblemKind::Scope,
                site.clone(),
                "a path literal needs the path type; declare 'path === Nil | Cons seg path' (SYNTAX.md §6)".to_string(),
            );
            return;
        };
        for seg in &path.segments {
            if seg.payload.is_some() {
                self.add(
                    ProblemKind::Data,
                    site.clone(),
                    "a segment payload ('/vane/care[<t>]/desk') is not compiled yet; only path literals are accepted \
                     until Stage B (SYNTAX.md §6)"
                        .to_string(),
                );
                continue;
            }
            let cname = capitalize(&seg.tag);
            match self.env.ctors.get(&cname) {
                Some((t, _, arity)) if t == &pt.seg => {
                    if *arity != 0 {
                        self.add(
                            ProblemKind::Arity,
                            site.clone(),
                            format!(
                                "path segment constructor {} carries {} field(s); a segment tag is nullary",
                                repr(&cname),
                                arity
                            ),
                        );
                    }
                }
                _ => self.add(
                    ProblemKind::Scope,
                    site.clone(),
                    format!(
                        "path segment {} names no constructor {} of the segment type {}",
                        repr(&seg.tag),
                        repr(&cname),
                        repr(&pt.seg)
                    ),
                ),
            }
        }
    }

    fn interp_application(&mut self, interp: &E, site: &Site) {
        let (head, args) = A::spine(interp);
        let Expr::Name(nm) = &*head else {
            self.add(
                ProblemKind::Interface,
                site.clone(),
                "the interpreter left of '|-' must be a core, optionally applied to its parameters".to_string(),
            );
            return;
        };
        let Some(core) = self.env.cores.get(nm) else {
            self.add(ProblemKind::Interface, site.clone(), format!("{} is not a core in this program", repr(nm)));
            return;
        };
        if args.len() != core.params.len() {
            self.add(
                ProblemKind::Interface,
                site.clone(),
                format!(
                    "core {} takes {} parameter(s) but is applied to {}; an interpreter is applied to all of them \
                     before its fuel",
                    repr(nm),
                    core.params.len(),
                    args.len()
                ),
            );
        }
    }

    fn interface(&mut self, d: &A::Core, obj: &ObjectType) {
        let site = Site::new("core", &d.name);
        let leaves: Vec<String> = obj.leaves.iter().map(|c| c.name.clone()).collect();
        for eq in &d.equations {
            if !eq.name.starts_with("step") || eq.name == "step" {
                continue;
            }
            let rest = &eq.name[4..];
            if rest == obj.app.name {
                self.add(
                    ProblemKind::Interface,
                    site.clone(),
                    format!(
                        "{}: the application constructor {} has no step equation -- it is the spine the walker \
                         descends, not a head that fires (§6c)",
                        repr(&eq.name),
                        repr(&obj.app.name)
                    ),
                );
            }
        }
        let written: HashMap<&str, &A::Equation> = d.equations.iter().map(|e| (e.name.as_str(), e)).collect();
        if let Some(step) = written.get("step") {
            self.step_arm(step, &leaves, &site);
        }
        if let Some(l) = written.get("loop") {
            let n = l.binders.len();
            if n != 2 {
                self.add(
                    ProblemKind::Interface,
                    site.clone(),
                    format!(
                        "a written 'loop' takes the fuel and the term, two binders after the core's parameters; this \
                         one has {}",
                        n
                    ),
                );
            }
        }
        if written.contains_key("loop1") && !written.contains_key("loop") {
            self.add(
                ProblemKind::Interface,
                site.clone(),
                "'loop1' is written but 'loop' is not; write both or neither".to_string(),
            );
        }
        if let Some(l1) = written.get("loop1") {
            if l1.binders.len() != 3 {
                self.add(
                    ProblemKind::Interface,
                    site.clone(),
                    format!(
                        "a written 'loop1' takes the loop, the term and the remaining fuel, three binders after the \
                         core's parameters; this one has {}",
                        l1.binders.len()
                    ),
                );
            }
        }
    }

    fn step_arm(&mut self, eq: &A::Equation, leaves: &[String], site: &Site) {
        if eq.binders.len() != 1 {
            self.add(
                ProblemKind::Interface,
                site.clone(),
                format!(
                    "a written 'step' takes the term, one binder after the core's parameters; this one has {}",
                    eq.binders.len()
                ),
            );
            return;
        }
        let (head, args) = A::spine(&eq.body);
        if !matches!(&*head, Expr::Name(n) if n == "sp") {
            return;
        }
        if args.len() != 2 + leaves.len() {
            self.add(
                ProblemKind::Interface,
                site.clone(),
                format!(
                    "'step' hands the walker {} step equation(s) but the object type has {} leaves ({})",
                    args.len() as isize - 2,
                    leaves.len(),
                    leaves.join(", ")
                ),
            );
            return;
        }
        let got: Vec<Option<String>> = args[2..]
            .iter()
            .map(|x| {
                let (h, _) = A::spine(x);
                match &*h {
                    Expr::Name(n) => Some(n.clone()),
                    _ => None,
                }
            })
            .collect();
        let want: Vec<String> = leaves.iter().map(|c| format!("step{}", c)).collect();
        let named: Vec<String> = got.iter().flatten().cloned().collect();
        let mut sorted_named = named.clone();
        sorted_named.sort();
        let mut sorted_want = want.clone();
        sorted_want.sort();
        if named.len() == got.len()
            && named.iter().all(|g| g.starts_with("step"))
            && sorted_named == sorted_want
            && named != want
        {
            self.add(
                ProblemKind::Interface,
                site.clone(),
                format!(
                    "'step' installs the leaf equations in the order {}, but the object type declares {}; declaration \
                     order is the ABI and a wrong order is silent wrong semantics (DESIDERATA.md item 11)",
                    named.join(", "),
                    leaves.join(", ")
                ),
            );
        }
    }
}

pub fn capitalize(s: &str) -> String {
    let mut cs = s.chars();
    match cs.next() {
        None => String::new(),
        Some(c) => c.to_uppercase().collect::<String>() + cs.as_str(),
    }
}

/// Every Stage A problem in ``program``, in source order.
pub fn check_program(program: &Program, prelude: &[&str]) -> Vec<Problem> {
    Checker::new(program, prelude).run()
}

/// Run Stage A and fail if anything is wrong.
pub fn check(program: &Program, prelude: &[&str]) -> Result<()> {
    let problems = check_program(program, prelude);
    if problems.is_empty() {
        return Ok(());
    }
    Err(SkijackError::from_problems("Stage A", problems))
}
