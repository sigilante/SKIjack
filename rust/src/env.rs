//! The bird registry, the definition environment and basis expansion:
//! ``aviary_kernel.birds``, ``environment`` and ``abstraction`` in one.

use std::collections::{HashMap, HashSet};

use indexmap::IndexMap;

use crate::errors::{Result, SkijackError};
use crate::term::{app, atom, occurs, ptr, Node, Term};

const FORMALS: [&str; 7] = ["a", "b", "c", "d", "e", "f", "g"];

pub struct Bird {
    pub name: &'static str,
    pub display: &'static str,
    pub aliases: &'static [&'static str],
    pub arity: usize,
    pub rule: Term,
    pub ski: Option<Term>,
}

/// Parse a bare rule string such as ``a (b c)``.
fn parse_rule(src: &str) -> Term {
    fn go(chars: &[char], i: &mut usize) -> Term {
        let mut out: Option<Term> = None;
        while *i < chars.len() {
            let c = chars[*i];
            let item = if c == ' ' {
                *i += 1;
                continue;
            } else if c == ')' {
                break;
            } else if c == '(' {
                *i += 1;
                let inner = go(chars, i);
                *i += 1; // ')'
                inner
            } else {
                let start = *i;
                while *i < chars.len() && !" ()".contains(chars[*i]) {
                    *i += 1;
                }
                let name: String = chars[start..*i].iter().collect();
                atom(&name)
            };
            out = Some(match out {
                None => item,
                Some(f) => app(f, item),
            });
        }
        out.expect("empty rule")
    }
    let chars: Vec<char> = src.chars().collect();
    let mut i = 0;
    go(&chars, &mut i)
}

const Y_SKI: &str = "S (K (S I I)) (S (S (K S) K) (K (S I I)))";

fn bird(
    name: &'static str,
    display: &'static str,
    aliases: &'static [&'static str],
    arity: usize,
    rule: &str,
    ski: Option<&str>,
) -> Bird {
    Bird { name, display, aliases, arity, rule: parse_rule(rule), ski: ski.map(parse_rule) }
}

pub struct BirdTable {
    pub birds: Vec<Bird>,
    pub by_name: HashMap<&'static str, usize>,
}

fn build_birds() -> BirdTable {
    let birds = vec![
        bird("B", "B", &[], 3, "a (b c)", None),
        bird("B1", "B₁", &[], 4, "a (b c d)", None),
        bird("B2", "B₂", &[], 5, "a (b c d e)", None),
        bird("B3", "B₃", &[], 4, "a (b (c d))", None),
        bird("C", "C", &[], 3, "a c b", None),
        bird("C*", "C*", &[], 4, "a b d c", None),
        bird("C**", "C**", &[], 5, "a b c e d", None),
        bird("D", "D", &[], 4, "a b (c d)", None),
        bird("D1", "D₁", &[], 5, "a b c (d e)", None),
        bird("D2", "D₂", &[], 5, "a (b c) (d e)", None),
        bird("E", "E", &[], 5, "a b (c d e)", None),
        bird("Ê", "Ê", &["E^"], 7, "a (b c d) (e f g)", None),
        bird("F", "F", &[], 3, "c b a", None),
        bird("F*", "F*", &[], 4, "a d c b", None),
        bird("F**", "F**", &[], 5, "a b e d c", None),
        bird("G", "G", &[], 4, "a d (b c)", None),
        bird("H", "H", &[], 3, "a b c b", None),
        bird("I", "I", &[], 1, "a", None),
        bird("I*", "I*", &[], 2, "a b", None),
        bird("I**", "I**", &[], 3, "a b c", None),
        bird("J", "J", &[], 4, "a b (a d c)", None),
        bird("K", "K", &[], 2, "a", None),
        bird("Ki", "Ki", &[], 2, "b", None),
        bird("KM", "KM", &[], 2, "b b", None),
        bird("KM'", "KM'", &[], 2, "a a", None),
        bird("L", "L", &[], 2, "a (b b)", None),
        bird("M", "M", &[], 1, "a a", None),
        bird("M2", "M₂", &[], 2, "a b (a b)", None),
        bird("O", "O", &[], 2, "b (a b)", None),
        bird("Φ", "Φ", &["Phi"], 4, "a (b d) (c d)", None),
        bird("Ψ", "Ψ", &["Psi"], 4, "a (b c) (b d)", None),
        bird("Q", "Q", &[], 3, "b (a c)", None),
        bird("Q1", "Q₁", &[], 3, "a (c b)", None),
        bird("Q2", "Q₂", &[], 3, "b (c a)", None),
        bird("Q3", "Q₃", &[], 3, "c (a b)", None),
        bird("Q4", "Q₄", &[], 3, "c (b a)", None),
        bird("R", "R", &[], 3, "b c a", None),
        bird("R*", "R*", &[], 4, "a c d b", None),
        bird("R**", "R**", &[], 5, "a b d e c", None),
        bird("S", "S", &[], 3, "a c (b c)", None),
        bird("T", "T", &[], 2, "b a", None),
        bird("U", "U", &[], 2, "b (a a b)", None),
        bird("V", "V", &[], 3, "c a b", None),
        bird("V*", "V*", &[], 4, "a d b c", None),
        bird("V**", "V**", &[], 5, "a b e c d", None),
        bird("W", "W", &[], 2, "a b b", None),
        bird("W*", "W*", &[], 3, "a b c c", None),
        bird("W**", "W**", &[], 4, "a b c d d", None),
        bird("W'", "W'", &[], 2, "b a a", None),
        bird("Y", "Y", &[], 1, "a (Y a)", Some(Y_SKI)),
    ];
    let mut by_name = HashMap::new();
    for (i, b) in birds.iter().enumerate() {
        by_name.insert(b.name, i);
        for a in b.aliases {
            by_name.insert(*a, i);
        }
    }
    BirdTable { birds, by_name }
}

thread_local! {
    static BIRDS: BirdTable = build_birds();
}

/// Is ``name`` a built-in bird (or an alias of one)?
pub fn is_bird(name: &str) -> bool {
    BIRDS.with(|t| t.by_name.contains_key(name))
}

fn with_bird<R>(name: &str, f: impl FnOnce(&Bird) -> R) -> Option<R> {
    BIRDS.with(|t| t.by_name.get(name).map(|&i| f(&t.birds[i])))
}

/// Normalized view over a bird or a definition.
#[derive(Clone)]
pub struct Combinator {
    pub name: String,
    pub arity: usize,
    pub formals: Vec<String>,
    pub body: Term,
    pub ski: Option<Term>,
    pub is_builtin: bool,
    pub is_alias: bool,
}

#[derive(Clone)]
pub struct Definition {
    pub name: String,
    pub arity: usize,
    pub formals: Vec<String>,
    pub body: Term,
    pub is_alias: bool,
    pub builtin: bool,
}

/// Session definitions plus the built-in birds behind one lookup.
pub struct Environment {
    pub definitions: IndexMap<String, Definition>,
    alias_keys: HashMap<String, String>,
    pub expansion_cache: HashMap<String, Term>,
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}

impl Environment {
    pub fn new() -> Environment {
        let mut env = Environment {
            definitions: IndexMap::new(),
            alias_keys: HashMap::new(),
            expansion_cache: HashMap::new(),
        };
        // Θ is preloaded as if the user had typed `Θ := U U`
        env.definitions.insert(
            "Θ".to_string(),
            Definition {
                name: "Θ".to_string(),
                arity: 0,
                formals: vec![],
                body: app(atom("U"), atom("U")),
                is_alias: true,
                builtin: true,
            },
        );
        env.alias_keys.insert("Theta".to_string(), "Θ".to_string());
        env
    }

    pub fn lookup(&self, name: &str) -> Option<Combinator> {
        if let Some(c) = with_bird(name, |b| Combinator {
            name: b.name.to_string(),
            arity: b.arity,
            formals: FORMALS[..b.arity].iter().map(|s| s.to_string()).collect(),
            body: b.rule.clone(),
            ski: b.ski.clone(),
            is_builtin: true,
            is_alias: false,
        }) {
            return Some(c);
        }
        let canon = self.alias_keys.get(name).map(|s| s.as_str()).unwrap_or(name);
        self.definitions.get(canon).map(|d| Combinator {
            name: d.name.clone(),
            arity: d.arity,
            formals: d.formals.clone(),
            body: d.body.clone(),
            ski: None,
            is_builtin: d.builtin,
            is_alias: d.is_alias,
        })
    }

    fn check_shadow(&self, name: &str) -> Result<()> {
        if is_bird(name) {
            return Err(SkijackError::Expand(format!("cannot shadow built-in '{}'", name)));
        }
        if let Some(d) = self.definitions.get(name) {
            if d.builtin {
                return Err(SkijackError::Expand(format!("cannot shadow built-in '{}'", name)));
            }
        }
        Ok(())
    }

    pub fn define_alias(&mut self, name: &str, body: Term) -> Result<()> {
        self.check_shadow(name)?;
        self.definitions.insert(
            name.to_string(),
            Definition {
                name: name.to_string(),
                arity: 0,
                formals: vec![],
                body,
                is_alias: true,
                builtin: false,
            },
        );
        self.expansion_cache.clear();
        Ok(())
    }

    pub fn define_rule(&mut self, name: &str, formals: &[String], body: Term) -> Result<()> {
        self.check_shadow(name)?;
        let mut seen = std::collections::HashSet::new();
        for v in formals {
            if !seen.insert(v.as_str()) {
                return Err(SkijackError::Expand(format!(
                    "duplicate variable '{}' in definition of '{}'",
                    v, name
                )));
            }
            if v != name && self.lookup(v).is_some() {
                return Err(SkijackError::Expand(format!("variable '{}' shadows a combinator", v)));
            }
        }
        self.definitions.insert(
            name.to_string(),
            Definition {
                name: name.to_string(),
                arity: formals.len(),
                formals: formals.to_vec(),
                body,
                is_alias: false,
                builtin: false,
            },
        );
        self.expansion_cache.clear();
        Ok(())
    }
}

// ---------------------------------------------------------------- abstraction

thread_local! {
    static S: Term = atom("S");
    static K: Term = atom("K");
    static I: Term = atom("I");
}

pub fn s_atom() -> Term {
    S.with(|t| t.clone())
}
pub fn k_atom() -> Term {
    K.with(|t| t.clone())
}
pub fn i_atom() -> Term {
    I.with(|t| t.clone())
}

/// Curry's bracket abstraction with the eta-optimization:
///
/// ```text
///     [x] x        = I
///     [x] E        = K E              if x not free in E
///     [x] (E x)    = E                if x not free in E   (eta)
///     [x] (E F)    = S ([x]E) ([x]F)  otherwise
/// ```
pub fn bracket_abstract(x: &str, body: &Term) -> Term {
    let mut memo: HashMap<*const Node, bool> = HashMap::new();
    fn go(x: &str, t: &Term, memo: &mut HashMap<*const Node, bool>) -> Term {
        match &**t {
            Node::Atom(n) => {
                if &**n == x {
                    i_atom()
                } else {
                    app(k_atom(), t.clone())
                }
            }
            Node::App(e, f) => {
                if !occurs(x, t, memo) {
                    return app(k_atom(), t.clone());
                }
                if let Node::Atom(fname) = &**f {
                    if &**fname == x && !occurs(x, e, memo) {
                        return e.clone();
                    }
                }
                app(app(s_atom(), go(x, e, memo)), go(x, f, memo))
            }
        }
    }
    go(x, body, &mut memo)
}

/// Expand every non-basis combinator atom into S/K/I.  Memoized per name.
pub fn ski_expand(term: &Term, env: &mut Environment) -> Result<Term> {
    expand_inner(term, env, &mut Vec::new())
}

fn expand_inner(term: &Term, env: &mut Environment, in_progress: &mut Vec<String>) -> Result<Term> {
    match &**term {
        Node::App(f, a) => {
            let nf = expand_inner(f, env, in_progress)?;
            let na = expand_inner(a, env, in_progress)?;
            Ok(app(nf, na))
        }
        Node::Atom(name) => {
            let name: &str = name;
            if name == "S" || name == "K" || name == "I" {
                return Ok(term.clone());
            }
            if let Some(t) = env.expansion_cache.get(name) {
                return Ok(t.clone());
            }
            let Some(comb) = env.lookup(name) else {
                return Ok(term.clone()); // a free variable passes through
            };
            if in_progress.iter().any(|n| n == name) {
                return Err(SkijackError::Expand(format!(
                    "cannot expand recursive combinator '{}' to a finite S/K/I term; \
                     define it via a fixed-point combinator (e.g. {} := Y step) instead",
                    name, name
                )));
            }
            in_progress.push(name.to_string());
            let result = if let Some(ski) = &comb.ski {
                expand_inner(ski, env, in_progress)?
            } else if comb.is_alias {
                expand_inner(&comb.body, env, in_progress)?
            } else {
                let mut r = expand_inner(&comb.body, env, in_progress)?;
                // Abstraction only removes the abstracted variable, so a
                // formal absent from the expanded body is absent from every
                // intermediate result too, and ``[x] E = K E`` is immediate.
                let fv = free_atoms(&r);
                for formal in comb.formals.iter().rev() {
                    r = if fv.contains(formal.as_str()) { bracket_abstract(formal, &r) } else { app(k_atom(), r) };
                }
                r
            };
            in_progress.pop();
            env.expansion_cache.insert(name.to_string(), result.clone());
            Ok(result)
        }
    }
}

/// Every atom name occurring in ``t`` (a DAG walk, each node once).
pub fn free_atoms(t: &Term) -> HashSet<String> {
    let mut out = HashSet::new();
    let mut seen: HashSet<*const Node> = HashSet::new();
    let mut stack = vec![t];
    while let Some(x) = stack.pop() {
        if !seen.insert(ptr(x)) {
            continue;
        }
        match &**x {
            Node::Atom(n) => {
                out.insert(n.to_string());
            }
            Node::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
        }
    }
    out
}
