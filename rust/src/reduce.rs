//! Normal-order reduction with a step budget: ``aviary_kernel.reduce`` and
//! ``skijack.probe.fast_reduce`` in one.
//!
//! The reducer holds the current position as a head atom and its argument
//! spine, kept *reversed* so that consuming the first arguments and
//! pushing a contractum's spine are both O(1) per element.  The
//! contraction order, and so the step count, is the reference host's.

use std::collections::HashMap;

use crate::env::Environment;
use crate::term::{apply, atom_name, dag_size, spine, substitute, Node, Term};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Normal,
    Whnf,
    Fuel,
    Size,
}

impl Status {
    pub fn value(self) -> &'static str {
        match self {
            Status::Normal => "normal",
            Status::Whnf => "whnf",
            Status::Fuel => "fuel",
            Status::Size => "size",
        }
    }
}

pub struct ReduceResult {
    pub term: Term,
    pub steps: usize,
    pub status: Status,
}

impl ReduceResult {
    pub fn whnf(&self) -> bool {
        matches!(self.status, Status::Whnf | Status::Normal)
    }
}

pub const SIZE_CHECK_EVERY: usize = 512;

struct Frame {
    head: Term,
    done: Vec<Term>,
    todo: Vec<Term>,
}

/// Push ``t``'s spine: the head replaces ``head`` and the arguments go on
/// the reversed argument stack.
#[inline]
fn decompose_into(t: &Term, head: &mut Term, args_rev: &mut Vec<Term>) {
    let mut cur = t;
    loop {
        match &**cur {
            Node::App(f, a) => {
                args_rev.push(a.clone());
                cur = f;
            }
            Node::Atom(_) => {
                *head = cur.clone();
                return;
            }
        }
    }
}

fn full_term(head: &Term, args_rev: &[Term], stack: &[Frame]) -> Term {
    let mut result = apply(head.clone(), args_rev.iter().rev().cloned());
    for fr in stack.iter().rev() {
        let remaining = &fr.todo[fr.done.len() + 1..];
        let args = fr.done.iter().cloned().chain(std::iter::once(result)).chain(remaining.iter().cloned());
        result = apply(fr.head.clone(), args);
    }
    result
}

/// Try to contract the redex at the current position.  Returns whether it
/// did.
#[inline]
fn try_contract(head: &mut Term, args_rev: &mut Vec<Term>, env: &Environment) -> bool {
    let name = match &**head {
        Node::Atom(n) => n,
        Node::App(..) => unreachable!("head is always an atom"),
    };
    let n = args_rev.len();
    match &**name {
        "S" => {
            if n < 3 {
                return false;
            }
            let a = args_rev.pop().unwrap();
            let b = args_rev.pop().unwrap();
            let c = args_rev.pop().unwrap();
            args_rev.push(crate::term::app(b, c.clone()));
            args_rev.push(c);
            decompose_into(&a, head, args_rev);
            true
        }
        "K" => {
            if n < 2 {
                return false;
            }
            let a = args_rev.pop().unwrap();
            args_rev.pop();
            decompose_into(&a, head, args_rev);
            true
        }
        "I" => {
            if n < 1 {
                return false;
            }
            let a = args_rev.pop().unwrap();
            decompose_into(&a, head, args_rev);
            true
        }
        other => {
            // the generic rule: any other bird or definition the
            // environment knows (never reached for closed {S,K,I} terms)
            let Some(comb) = env.lookup(other) else { return false };
            if n < comb.arity {
                return false;
            }
            let mut mapping: HashMap<&str, Term> = HashMap::new();
            let consumed: Vec<Term> = (0..comb.arity).map(|_| args_rev.pop().unwrap()).collect();
            for (f, t) in comb.formals.iter().zip(consumed.into_iter()) {
                mapping.insert(f.as_str(), t);
            }
            let new_term = substitute(&comb.body, &mapping);
            decompose_into(&new_term, head, args_rev);
            true
        }
    }
}

/// Reduce ``term`` under normal order to weak head normal form, or to full
/// normal form when ``whnf_only`` is false.  ``max_size`` samples a
/// DAG-size guard every ``SIZE_CHECK_EVERY`` contractions; ``None`` turns
/// it off.
pub fn fast_reduce(
    term: &Term,
    env: &Environment,
    whnf_only: bool,
    max_steps: usize,
    max_size: Option<usize>,
) -> ReduceResult {
    let mut steps = 0usize;
    let mut stack: Vec<Frame> = Vec::new();
    let mut head: Term = term.clone();
    let mut args_rev: Vec<Term> = Vec::new();
    decompose_into(term, &mut head, &mut args_rev);

    loop {
        // bring the current position to WHNF
        loop {
            if steps >= max_steps {
                return ReduceResult { term: full_term(&head, &args_rev, &stack), steps, status: Status::Fuel };
            }
            if !try_contract(&mut head, &mut args_rev, env) {
                break;
            }
            steps += 1;
            if let Some(limit) = max_size {
                if steps.is_multiple_of(SIZE_CHECK_EVERY) {
                    let t = full_term(&head, &args_rev, &stack);
                    if dag_size(&t) > limit {
                        return ReduceResult { term: t, steps, status: Status::Size };
                    }
                }
            }
        }

        if whnf_only && stack.is_empty() {
            let t = apply(head.clone(), args_rev.iter().rev().cloned());
            return ReduceResult { term: t, steps, status: Status::Whnf };
        }

        if !args_rev.is_empty() {
            let todo: Vec<Term> = args_rev.iter().rev().cloned().collect();
            let first = todo[0].clone();
            stack.push(Frame { head: head.clone(), done: Vec::new(), todo });
            args_rev.clear();
            decompose_into(&first, &mut head, &mut args_rev);
            continue;
        }

        // the head alone is fully normal here
        let mut result = head.clone();
        loop {
            let Some(fr) = stack.last_mut() else {
                return ReduceResult { term: result, steps, status: Status::Normal };
            };
            fr.done.push(result);
            if fr.done.len() < fr.todo.len() {
                let next = fr.todo[fr.done.len()].clone();
                args_rev.clear();
                decompose_into(&next, &mut head, &mut args_rev);
                break;
            }
            let fr = stack.pop().unwrap();
            result = apply(fr.head, fr.done);
        }
    }
}

/// The head atom and the arguments of a reduced term, in order.
pub fn head_args(t: &Term) -> (Option<String>, Vec<Term>) {
    let (h, args) = spine(t);
    (atom_name(&h).map(|s| s.to_string()), args)
}
