//! The dictionary: Tier 1's table, and lift.

use std::collections::HashMap;

use indexmap::IndexMap;
use sha2::{Digest, Sha256};

use crate::abi::is_isa;
use crate::ast::{self as A, Expr, E};
use crate::env::ski_expand;
use crate::errors::{repr, Result, SkijackError};
use crate::expand::Expansion;
use crate::term::{app, atom, ptr, size, Node, Term};

/// the table's version; a change to any entry is a change to this
pub const VERSION: &str = "skijack-1";

/// entries smaller than this are tabled but never lifted
pub const MIN_LIFT_SIZE: usize = 3;

/// The fully parenthesized printed form.
pub fn canonical(term: &Term) -> String {
    enum W<'a> {
        T(&'a Term),
        S(&'static str),
    }
    let mut out = String::new();
    let mut work = vec![W::T(term)];
    while let Some(w) = work.pop() {
        match w {
            W::S(s) => out.push_str(s),
            W::T(x) => match &**x {
                Node::Atom(n) => out.push_str(n),
                Node::App(f, a) => {
                    work.push(W::S(")"));
                    work.push(W::T(a));
                    work.push(W::S(" "));
                    work.push(W::T(f));
                    work.push(W::S("("));
                }
            },
        }
    }
    out
}

/// The 16 hex digits of a truncated sha256, as bytes.
fn digest16(input: &[u8]) -> [u8; 16] {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let h = Sha256::digest(input);
    let mut out = [0u8; 16];
    for i in 0..8 {
        out[2 * i] = HEX[(h[i] >> 4) as usize];
        out[2 * i + 1] = HEX[(h[i] & 15) as usize];
    }
    out
}

/// Every node's Merkle digest, bottom up, in one pass.  A leaf hashes its
/// name; an application hashes ``"(" + hash(fn) + " " + hash(arg) + ")"``.
pub fn hash_all(term: &Term) -> HashMap<*const Node, (Term, String)> {
    let mut memo: HashMap<*const Node, (Term, [u8; 16])> = HashMap::new();
    let mut work: Vec<(&Term, bool)> = vec![(term, false)];
    let mut buf = [0u8; 35];
    buf[0] = b'(';
    buf[17] = b' ';
    buf[34] = b')';
    while let Some((x, done)) = work.pop() {
        if memo.contains_key(&ptr(x)) {
            continue;
        }
        match &**x {
            Node::Atom(n) => {
                memo.insert(ptr(x), (x.clone(), digest16(n.as_bytes())));
            }
            Node::App(f, a) => {
                if !done {
                    work.push((x, true));
                    work.push((f, false));
                    work.push((a, false));
                } else {
                    buf[1..17].copy_from_slice(&memo[&ptr(f)].1);
                    buf[18..34].copy_from_slice(&memo[&ptr(a)].1);
                    memo.insert(ptr(x), (x.clone(), digest16(&buf)));
                }
            }
        }
    }
    memo.into_iter().map(|(k, (t, d))| (k, (t, String::from_utf8(d.to_vec()).unwrap()))).collect()
}

/// The published hash of a term.
pub fn structural_hash(term: &Term) -> String {
    let memo = hash_all(term);
    format!("{}:{}", VERSION, memo[&ptr(term)].1)
}

#[derive(Clone)]
pub struct Entry {
    pub name: String,
    pub term: Term,
    pub size: usize,
    pub hash: String,
    pub tier: u8,
    pub note: String,
}

/// A versioned table of named expansions.
pub struct Dictionary {
    pub version: String,
    pub entries: IndexMap<String, Entry>,
}

impl Default for Dictionary {
    fn default() -> Self {
        Self::new()
    }
}

impl Dictionary {
    pub fn new() -> Dictionary {
        Dictionary { version: VERSION.to_string(), entries: IndexMap::new() }
    }

    pub fn add(&mut self, entry: Entry, replace: bool) -> Result<()> {
        if let Some(old) = self.entries.get(&entry.name) {
            if old.hash != entry.hash && !replace {
                return Err(SkijackError::Dictionary(format!(
                    "{} is already in the table as {} ({} atoms) and would become {} ({} atoms); one name is one \
                     expansion, and a change is a version change (DESIDERATA.md §5)",
                    repr(&entry.name),
                    old.hash,
                    old.size,
                    entry.hash,
                    entry.size
                )));
            }
        }
        self.entries.insert(entry.name.clone(), entry);
        Ok(())
    }

    pub fn register(&mut self, name: &str, term: &Term, tier: u8, note: &str, replace: bool) -> Result<Entry> {
        let e = Entry {
            name: name.to_string(),
            term: term.clone(),
            size: size(term),
            hash: structural_hash(term),
            tier,
            note: note.to_string(),
        };
        self.add(e.clone(), replace)?;
        Ok(e)
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn contains(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }

    pub fn get(&self, name: &str) -> Option<&Entry> {
        self.entries.get(name)
    }

    pub fn names(&self) -> Vec<String> {
        let mut v: Vec<String> = self.entries.keys().cloned().collect();
        v.sort();
        v
    }

    /// The published table: (name, atoms, hash), sorted by name.
    pub fn rows(&self) -> Vec<(String, usize, String)> {
        self.names().into_iter().map(|n| (n.clone(), self.entries[&n].size, self.entries[&n].hash.clone())).collect()
    }

    /// hash -> name, for the entries lift may name.
    pub fn lift_index(&self, min_size: usize, exclude: &[String]) -> HashMap<String, String> {
        let mut index: HashMap<String, String> = HashMap::new();
        let mut names: Vec<&String> = self.entries.keys().collect();
        names.sort_by_key(|n| (n.matches('.').count(), n.len(), (*n).clone()));
        for name in names {
            if exclude.contains(name) || is_isa(name) {
                continue;
            }
            let e = &self.entries[name];
            if e.size < min_size {
                continue;
            }
            index.entry(e.hash.clone()).or_insert_with(|| name.clone());
        }
        index
    }
}

/// Register a compiled program's names.
pub fn from_expansion(exp: &mut Expansion) -> Result<Dictionary> {
    let mut d = Dictionary::new();
    if !d.contains("Y") {
        let y = ski_expand(&atom("Y"), &mut exp.env)?;
        d.register("Y", &y, 1, "the fixpoint every recursive equation is tied with", false)?;
    }
    let names: Vec<String> = exp.terms.keys().cloned().collect();
    for name in names {
        let t = exp.terms[&name].clone();
        d.register(&name, &t, 1, "", false)?;
    }
    Ok(d)
}

/// Name every subterm that is an exact structural match of a dictionary
/// entry, largest match first; leave everything else raw.
pub fn lift(term: &Term, dictionary: &Dictionary, min_size: usize, exclude: &[String]) -> E {
    let index = dictionary.lift_index(min_size, exclude);
    let memo = hash_all(term);
    let h = |x: &Term| -> String {
        match memo.get(&ptr(x)) {
            Some((_, d)) => format!("{}:{}", VERSION, d),
            None => structural_hash(x),
        }
    };
    let mut out: Vec<E> = Vec::new();
    let mut work: Vec<(&Term, bool)> = vec![(term, false)];
    while let Some((x, done)) = work.pop() {
        if done {
            let r = out.pop().unwrap();
            let l = out.pop().unwrap();
            out.push(A::app(l, r));
            continue;
        }
        if let Some(name) = index.get(&h(x)) {
            out.push(A::name(name));
            continue;
        }
        match &**x {
            Node::Atom(n) => out.push(A::name(n)),
            Node::App(f, a) => {
                work.push((x, true));
                work.push((a, false));
                work.push((f, false));
            }
        }
    }
    out.pop().unwrap()
}

/// Take a lifted tree back to the closed term.
pub fn lower(named: &E, dictionary: &Dictionary) -> Result<Term> {
    let mut out: Vec<Term> = Vec::new();
    let mut work: Vec<(&E, bool)> = vec![(named, false)];
    while let Some((x, done)) = work.pop() {
        if done {
            let r = out.pop().unwrap();
            let l = out.pop().unwrap();
            out.push(app(l, r));
            continue;
        }
        match &**x {
            Expr::Name(n) => {
                if is_isa(n) {
                    out.push(atom(n));
                } else if let Some(e) = dictionary.get(n) {
                    out.push(e.term.clone());
                } else {
                    return Err(SkijackError::Dictionary(format!(
                        "{} is neither a dictionary entry nor a primitive, so it cannot be lowered",
                        repr(n)
                    )));
                }
            }
            Expr::App(f, a) => {
                work.push((x, true));
                work.push((a, false));
                work.push((f, false));
            }
            _ => return Err(SkijackError::Dictionary("cannot lower a non-application form".to_string())),
        }
    }
    Ok(out.pop().unwrap())
}
