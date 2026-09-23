//! Quotation: a term encoded as Scott data over a declared object type.

use std::collections::HashMap;

use crate::errors::{repr, Result, SkijackError};
use crate::generate::ObjectType;
use crate::term::{app, Node, Term};

/// Leaves of the object type that have no level-0 meaning are carried
/// through the level-0 code generator as atoms under this prefix.
pub const OBJECT_LEAF_PREFIX: &str = "\u{0}leaf:";

pub struct Encoder {
    pub obj: ObjectType,
    pub app_term: Term,
    pub leaf_terms: HashMap<String, Term>,
}

impl Encoder {
    pub fn new(obj: &ObjectType, term_of: &dyn Fn(&str) -> Term) -> Encoder {
        let app_term = term_of(&obj.app.name);
        let mut leaf_terms = HashMap::new();
        for c in &obj.leaves {
            let t = term_of(&c.name);
            leaf_terms.insert(c.name.clone(), t.clone());
            leaf_terms.insert(format!("{}{}", OBJECT_LEAF_PREFIX, c.name), t);
        }
        Encoder { obj: obj.clone(), app_term, leaf_terms }
    }

    pub fn leaf(&self, name: &str) -> Option<&Term> {
        self.leaf_terms.get(name)
    }

    /// Encode ``term`` structurally.  Iterative: a level-2 datum is far
    /// deeper than any stack.
    pub fn quote(&self, term: &Term) -> Result<Term> {
        let mut out: Vec<Term> = Vec::new();
        let mut work: Vec<(&Term, bool)> = vec![(term, false)];
        while let Some((x, done)) = work.pop() {
            match &**x {
                Node::Atom(n) => {
                    let Some(enc) = self.leaf(n) else {
                        let leaves: Vec<&str> = self.obj.leaves.iter().map(|c| c.name.as_str()).collect();
                        return Err(SkijackError::Quote(format!(
                            "cannot quote the atom {}: the object type {} has no leaf constructor for it (its leaves are {})",
                            repr(n),
                            repr(self.obj.name()),
                            leaves.join(", ")
                        )));
                    };
                    out.push(enc.clone());
                }
                Node::App(f, a) => {
                    if !done {
                        work.push((x, true));
                        work.push((a, false));
                        work.push((f, false));
                    } else {
                        let r = out.pop().unwrap();
                        let l = out.pop().unwrap();
                        out.push(app(app(self.app_term.clone(), l), r));
                    }
                }
            }
        }
        Ok(out.pop().unwrap())
    }
}

/// The level-1 table for ``obj``: leaf constructor name -> the atom the
/// level-0 code generator should emit for it inside ``< >``.
pub fn level1_names(obj: &ObjectType) -> HashMap<String, String> {
    obj.leaves.iter().map(|c| (c.name.clone(), format!("{}{}", OBJECT_LEAF_PREFIX, c.name))).collect()
}
