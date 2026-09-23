//! Running a compiled program, at level 0 and at level 1, and reading the
//! result behaviorally.

use std::collections::{HashMap, HashSet};

use crate::ast::{self as A, E};
use crate::env::Environment;
use crate::errors::{repr, Result, SkijackError};
use crate::expand::{resolver_term, Expansion, Level1Program};
use crate::generate::ObjectType;
use crate::reduce::{fast_reduce, head_args, ReduceResult, Status};
use crate::render::render_ascii;
use crate::term::{apply, atom, pretty, ptr, Node, Term};

fn rerr(msg: String) -> SkijackError {
    SkijackError::Run(msg)
}

/// the runtime's default ceiling for iterative deepening
pub const DEFAULT_CAP: usize = 4096;

pub struct Outcome {
    pub term: Term,
    pub status: Status,
    pub steps: usize,
}

impl Outcome {
    pub fn whnf(&self) -> bool {
        matches!(self.status, Status::Whnf | Status::Normal)
    }
}

fn fresh_env() -> Environment {
    Environment::new()
}

/// Reduce a level-0 term directly.
pub fn run_level0(term: &Term, max_steps: usize, whnf_only: bool) -> Outcome {
    let env = fresh_env();
    let r: ReduceResult = fast_reduce(term, &env, whnf_only, max_steps, None);
    Outcome { term: r.term, status: r.status, steps: r.steps }
}

/// Reduce ``interp fuel <program>``.
pub fn run_level1(prog: &Level1Program, max_steps: usize, fuel: Option<usize>) -> Result<Outcome> {
    let term = match fuel {
        Some(k) => prog.with_fuel(k),
        None => prog.term()?,
    };
    Ok(run_level0(&term, max_steps, true))
}

fn truncate(s: &str, n: usize) -> String {
    s.chars().take(n).collect()
}

/// Read the outer result: which constructor of ``decl`` is it, and what
/// does it carry?
pub fn peel(result: &Term, decl: &A::TypeDecl, max_steps: usize) -> Result<(String, Vec<Term>)> {
    let env = fresh_env();
    let marks: Vec<Term> = (0..decl.ctors.len()).map(|i| atom(&format!("\u{0}r{}", i))).collect();
    let r = fast_reduce(&apply(result.clone(), marks.iter().cloned()), &env, true, max_steps, None);
    if !r.whnf() {
        return Err(rerr(format!(
            "probing the result did not reach weak head normal form ({} after {} contractions)",
            r.status.value(),
            r.steps
        )));
    }
    let (head, args) = head_args(&r.term);
    let idx = head.as_deref().and_then(|h| marks.iter().position(|m| matches!(&**m, Node::Atom(n) if &**n == h)));
    let Some(idx) = idx else {
        return Err(rerr(format!(
            "not a value of {}: probing gave {}",
            repr(&decl.name),
            truncate(&pretty(&r.term), 80)
        )));
    };
    let ctor = &decl.ctors[idx];
    if args.len() != ctor.fields.len() {
        return Err(rerr(format!(
            "{} carries {} field(s) but the probe returned {}",
            ctor.name,
            ctor.fields.len(),
            args.len()
        )));
    }
    Ok((ctor.name.clone(), args))
}

/// Turn a quoted datum back into a surface term, by probing.
pub fn decode(datum: &Term, obj: &ObjectType, max_steps: usize, max_nodes: usize) -> Result<E> {
    let env = fresh_env();
    let ctors = &obj.decl.ctors;
    let marks: Vec<Term> = (0..ctors.len()).map(|i| atom(&format!("\u{0}c{}", i))).collect();
    let names: Vec<String> = (0..ctors.len()).map(|i| format!("\u{0}c{}", i)).collect();
    let app_idx = ctors.iter().position(|c| c.name == obj.app.name).unwrap();
    let mut cache: HashMap<*const Node, (Term, E)> = HashMap::new();

    let one = |node: &Term| -> Result<(usize, Vec<Term>)> {
        let r = fast_reduce(&apply(node.clone(), marks.iter().cloned()), &env, true, max_steps, None);
        if !r.whnf() {
            return Err(rerr(format!(
                "decoding did not reach weak head normal form ({} after {} contractions)",
                r.status.value(),
                r.steps
            )));
        }
        let (head, args) = head_args(&r.term);
        let idx = head.as_deref().and_then(|h| names.iter().position(|n| n == h));
        let Some(idx) = idx else {
            return Err(rerr(format!(
                "not a datum of {}: probing gave {}",
                repr(obj.name()),
                truncate(&pretty(&r.term), 80)
            )));
        };
        Ok((idx, args))
    };

    let mut todo: Vec<(Term, bool)> = vec![(datum.clone(), false)];
    let mut built: Vec<E> = Vec::new();
    let mut visited = 0usize;
    while let Some((node, done)) = todo.pop() {
        if done {
            let r = built.pop().unwrap();
            let l = built.pop().unwrap();
            let e = A::app(l, r);
            cache.insert(ptr(&node), (node.clone(), e.clone()));
            built.push(e);
            continue;
        }
        if let Some((_, e)) = cache.get(&ptr(&node)) {
            built.push(e.clone());
            continue;
        }
        visited += 1;
        if visited > max_nodes {
            return Err(rerr(format!("datum has more than {} nodes", max_nodes)));
        }
        let (idx, args) = one(&node)?;
        if idx == app_idx {
            let (l, r) = (args[0].clone(), args[1].clone());
            todo.push((node, true));
            todo.push((r, false));
            todo.push((l, false));
        } else {
            let e = A::name(&ctors[idx].name);
            cache.insert(ptr(&node), (node.clone(), e.clone()));
            built.push(e);
        }
    }
    Ok(built.pop().unwrap())
}

/// The constructor a loop returns when the fuel runs out: ``R``'s last
/// terminal.
pub fn timeout_constructor(decl: &A::TypeDecl) -> Result<String> {
    let terminals: Vec<&A::Ctor> = decl.ctors.iter().filter(|c| c.fields.is_empty()).collect();
    match terminals.last() {
        Some(c) => Ok(c.name.clone()),
        None => Err(rerr(format!(
            "result type {} has no terminal constructor, so a loop over it has nothing to return when the fuel runs out",
            repr(&decl.name)
        ))),
    }
}

pub struct PolicyResult {
    pub constructor: String,
    pub fields: Vec<Term>,
    pub budget: Option<usize>,
    pub budgets: Vec<usize>,
    pub steps: usize,
    pub timed_out: bool,
}

impl PolicyResult {
    pub fn payload(&self) -> Option<&Term> {
        self.fields.first()
    }
}

/// Iterative deepening over elided fuel: double from ``start`` until a
/// value or ``cap``.
pub fn run_policy(prog: &Level1Program, start: usize, cap: usize, max_steps: usize) -> Result<PolicyResult> {
    let timeout_ctor = timeout_constructor(&prog.result_type)?;
    let mut tried: Vec<usize> = Vec::new();
    let mut budget = start.max(1);
    loop {
        tried.push(budget);
        let out = run_level1(prog, max_steps, Some(budget))?;
        if !out.whnf() {
            return Err(rerr(format!(
                "host reducer gave up at budget {} ({} after {} contractions)",
                budget,
                out.status.value(),
                out.steps
            )));
        }
        let (ctor, fields) = peel(&out.term, &prog.result_type, max_steps)?;
        if ctor != timeout_ctor {
            return Ok(PolicyResult { constructor: ctor, fields, budget: Some(budget), budgets: tried, steps: out.steps, timed_out: false });
        }
        if budget >= cap {
            return Ok(PolicyResult { constructor: ctor, fields, budget: None, budgets: tried, steps: out.steps, timed_out: true });
        }
        budget = (budget * 2).min(cap);
    }
}

/// The result constructor a blocked run returns: the second payload-carrying
/// constructor.
pub fn block_constructor(decl: &A::TypeDecl) -> Option<String> {
    let carriers: Vec<&A::Ctor> = decl.ctors.iter().filter(|c| c.fields.len() == 1).collect();
    if carriers.len() > 1 {
        Some(carriers[1].name.clone())
    } else {
        None
    }
}

/// A closed resolver over ``facts``, built at run time.
pub fn make_resolver(exp: &Expansion, facts: &[(Term, Term)]) -> Result<Term> {
    let Some(at) = &exp.answer_type else {
        return Err(rerr("this program declares no oracle answer type, so it has no resolvers to build".to_string()));
    };
    let Some(eq5) = exp.terms.get("EQ5") else {
        return Err(rerr("this program does not define 'EQ5'".to_string()));
    };
    Ok(resolver_term(eq5, &exp.terms[&at.hit.name], &exp.terms[&at.notyet.name], facts))
}

pub struct NamespaceRun {
    pub trace: Vec<(usize, String)>,
    pub constructor: Option<String>,
    pub payload: Option<Term>,
    pub rounds: usize,
    pub steps: usize,
}

impl NamespaceRun {
    pub fn events(&self) -> Vec<&str> {
        self.trace.iter().map(|(_, e)| e.as_str()).collect()
    }
}

/// The resume loop: re-run from scratch with a resolver built from
/// everything learned so far.
#[allow(clippy::too_many_arguments)]
pub fn run_with_namespace(
    exp: &Expansion,
    prog: &Level1Program,
    resolution: &HashMap<String, Term>,
    fuel: Option<usize>,
    max_rounds: usize,
    max_steps: usize,
    start: usize,
    cap: usize,
) -> Result<NamespaceRun> {
    let Some(block) = block_constructor(&prog.result_type) else {
        return Err(rerr(format!(
            "result type {} has no blocking constructor, so this interpreter cannot block",
            repr(&prog.result_type.name)
        )));
    };
    let timeout = timeout_constructor(&prog.result_type)?;
    let mut namespace: Vec<(Term, Term)> = Vec::new();
    let mut known: HashSet<String> = HashSet::new();
    let mut trace: Vec<(usize, String)> = Vec::new();
    let mut steps = 0;
    for rnd in 1..=max_rounds {
        let mut run = prog.clone();
        let mut params = vec![make_resolver(exp, &namespace)?];
        params.extend(prog.params.iter().skip(1).cloned());
        run.params = params;
        let out = match fuel {
            None => {
                let mut budget = start.max(1);
                let mut out;
                loop {
                    out = run_level1(&run, max_steps, Some(budget))?;
                    if !out.whnf() {
                        break;
                    }
                    let (ctor, _) = peel(&out.term, &prog.result_type, max_steps)?;
                    if ctor != timeout || budget >= cap {
                        break;
                    }
                    budget = (budget * 2).min(cap);
                }
                if out.whnf() {
                    trace.push((rnd, format!("budget {}", budget)));
                }
                out
            }
            Some(f) => run_level1(&run, max_steps, Some(f))?,
        };
        steps = out.steps;
        if !out.whnf() {
            trace.push((rnd, format!("status:{}", out.status.value())));
            return Ok(NamespaceRun { trace, constructor: None, payload: None, rounds: rnd, steps });
        }
        let (ctor, fields) = peel(&out.term, &prog.result_type, max_steps)?;
        if ctor != block {
            trace.push((rnd, ctor.clone()));
            return Ok(NamespaceRun { trace, constructor: Some(ctor), payload: fields.first().cloned(), rounds: rnd, steps });
        }
        let key_datum = fields[0].clone();
        let key = render_ascii(&decode(&key_datum, &prog.object_type, max_steps, 200_000)?);
        trace.push((rnd, format!("BLOCK on {}", key)));
        if known.contains(&key) || !resolution.contains_key(&key) {
            trace.push((rnd, "STUCK".to_string()));
            return Ok(NamespaceRun { trace, constructor: None, payload: None, rounds: rnd, steps });
        }
        namespace.push((key_datum, resolution[&key].clone()));
        known.insert(key);
    }
    trace.push((max_rounds, "EXCEEDED MAX ROUNDS".to_string()));
    Ok(NamespaceRun { trace, constructor: None, payload: None, rounds: max_rounds, steps })
}
