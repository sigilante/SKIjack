//! Term model: binary application trees over atoms, shared by reference.
//!
//! Mirrors ``aviary_kernel.terms``.  Sharing is by ``Rc``; nothing here
//! updates a node in place, so a term is an immutable DAG whose tree
//! reading (``size``, ``pretty``, ``canonical``) is what the compiler
//! reports and whose node identity (``ptr``) is what the decoders memoize.

use std::collections::HashMap;
use std::rc::Rc;

pub type Sym = Rc<str>;

pub enum Node {
    Atom(Sym),
    App(Term, Term),
}

pub type Term = Rc<Node>;

thread_local! {
    static PLACEHOLDER: Term = Rc::new(Node::Atom(Rc::from("")));
}

impl Drop for Node {
    /// Iterative drop: a datum can be tens of thousands of nodes deep, and
    /// the default recursive drop would exhaust the stack on it.
    fn drop(&mut self) {
        let Node::App(f, a) = self else { return };
        let Ok(nil) = PLACEHOLDER.try_with(|p| p.clone()) else { return };
        let mut stack: Vec<Term> = Vec::new();
        for child in [f, a] {
            if Rc::strong_count(child) == 1 && matches!(**child, Node::App(..)) {
                stack.push(std::mem::replace(child, nil.clone()));
            }
        }
        while let Some(t) = stack.pop() {
            if let Ok(mut node) = Rc::try_unwrap(t) {
                if let Node::App(f, a) = &mut node {
                    for child in [f, a] {
                        if Rc::strong_count(child) == 1 && matches!(**child, Node::App(..)) {
                            stack.push(std::mem::replace(child, nil.clone()));
                        }
                    }
                }
            }
        }
    }
}

pub fn atom(name: &str) -> Term {
    Rc::new(Node::Atom(Rc::from(name)))
}

pub fn atom_sym(name: &Sym) -> Term {
    Rc::new(Node::Atom(name.clone()))
}

pub fn app(f: Term, a: Term) -> Term {
    Rc::new(Node::App(f, a))
}

/// Left-fold a head applied to a sequence of arguments.
pub fn apply<I: IntoIterator<Item = Term>>(head: Term, args: I) -> Term {
    let mut r = head;
    for a in args {
        r = app(r, a);
    }
    r
}

pub fn ptr(t: &Term) -> *const Node {
    Rc::as_ptr(t)
}

pub fn is_atom(t: &Term, name: &str) -> bool {
    matches!(&**t, Node::Atom(n) if &**n == name)
}

pub fn atom_name(t: &Term) -> Option<&Sym> {
    match &**t {
        Node::Atom(n) => Some(n),
        Node::App(..) => None,
    }
}

/// (head, args) by walking the ``fn`` chain; args in application order.
pub fn spine(t: &Term) -> (Term, Vec<Term>) {
    let mut args = Vec::new();
    let mut cur = t.clone();
    loop {
        let next = match &*cur {
            Node::App(f, a) => {
                args.push(a.clone());
                f.clone()
            }
            Node::Atom(_) => break,
        };
        cur = next;
    }
    args.reverse();
    (cur, args)
}

/// Count atoms in the *tree* reading of a term.
pub fn size(t: &Term) -> usize {
    let mut n = 0usize;
    let mut stack = vec![t];
    while let Some(x) = stack.pop() {
        match &**x {
            Node::Atom(_) => n += 1,
            Node::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
        }
    }
    n
}

/// Does the atom ``name`` occur anywhere in ``t``?  Memoized by node so a
/// shared DAG is walked once.
pub fn occurs(name: &str, t: &Term, memo: &mut HashMap<*const Node, bool>) -> bool {
    // iterative post-order over the DAG
    enum W<'a> {
        Enter(&'a Term),
        Exit(&'a Term),
    }
    let mut work = vec![W::Enter(t)];
    while let Some(w) = work.pop() {
        match w {
            W::Enter(x) => {
                if memo.contains_key(&ptr(x)) {
                    continue;
                }
                match &**x {
                    Node::Atom(n) => {
                        memo.insert(ptr(x), &**n == name);
                    }
                    Node::App(f, a) => {
                        work.push(W::Exit(x));
                        work.push(W::Enter(f));
                        work.push(W::Enter(a));
                    }
                }
            }
            W::Exit(x) => {
                if let Node::App(f, a) = &**x {
                    let v = memo[&ptr(f)] || memo[&ptr(a)];
                    memo.insert(ptr(x), v);
                }
            }
        }
    }
    memo[&ptr(t)]
}

/// Substitute atoms by name.  Unchanged subtrees keep their identity.
pub fn substitute(t: &Term, mapping: &HashMap<&str, Term>) -> Term {
    if mapping.is_empty() {
        return t.clone();
    }
    let mut result: Vec<Term> = Vec::new();
    let mut work: Vec<(&Term, bool)> = vec![(t, false)];
    while let Some((x, expanded)) = work.pop() {
        match &**x {
            Node::Atom(n) => {
                result.push(mapping.get(&**n).cloned().unwrap_or_else(|| x.clone()));
            }
            Node::App(f, a) => {
                if !expanded {
                    work.push((x, true));
                    work.push((a, false));
                    work.push((f, false));
                } else {
                    let new_a = result.pop().unwrap();
                    let new_f = result.pop().unwrap();
                    if Rc::ptr_eq(&new_f, f) && Rc::ptr_eq(&new_a, a) {
                        result.push(x.clone());
                    } else {
                        result.push(app(new_f, new_a));
                    }
                }
            }
        }
    }
    result.pop().unwrap()
}

/// Left-associative implicit application, parenthesizing only right-nested
/// applications.
pub fn pretty(t: &Term) -> String {
    enum W<'a> {
        Emit(&'a Term, bool),
        Text(&'static str),
    }
    let mut out = String::new();
    let mut work = vec![W::Emit(t, false)];
    while let Some(w) = work.pop() {
        match w {
            W::Text(s) => out.push_str(s),
            W::Emit(x, paren) => match &**x {
                Node::Atom(n) => out.push_str(n),
                Node::App(f, a) => {
                    if paren {
                        out.push('(');
                        work.push(W::Text(")"));
                    }
                    work.push(W::Emit(a, true));
                    work.push(W::Text(" "));
                    work.push(W::Emit(f, false));
                }
            },
        }
    }
    out
}

/// Structural equality, iterative.
pub fn term_eq(a: &Term, b: &Term) -> bool {
    let mut work = vec![(a, b)];
    while let Some((x, y)) = work.pop() {
        if Rc::ptr_eq(x, y) {
            continue;
        }
        match (&**x, &**y) {
            (Node::Atom(p), Node::Atom(q)) => {
                if p != q {
                    return false;
                }
            }
            (Node::App(f1, a1), Node::App(f2, a2)) => {
                work.push((f1, f2));
                work.push((a1, a2));
            }
            _ => return false,
        }
    }
    true
}

/// DAG-aware node count.
pub fn dag_size(t: &Term) -> usize {
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![t];
    let mut n = 0;
    while let Some(x) = stack.pop() {
        if !seen.insert(ptr(x)) {
            continue;
        }
        n += 1;
        if let Node::App(f, a) = &**x {
            stack.push(f);
            stack.push(a);
        }
    }
    n
}
