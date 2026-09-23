//! Type-generated forms: the interpreter interface of
//! ``SURFACE-LANGUAGE-DESIGN.md`` §6c, produced as surface syntax.

use std::collections::{HashMap, HashSet};

use crate::ast::{self as A, Decl, Equation, Program, E};
use crate::errors::{repr, Result, SkijackError};

fn gerr(msg: String) -> SkijackError {
    SkijackError::Generate(msg)
}

fn n(name: &str) -> E {
    A::name(name)
}

fn ap(head: E, parts: &[E]) -> E {
    let mut out = head;
    for p in parts {
        out = A::app(out, p.clone());
    }
    out
}

fn apn(head: &str, parts: &[&str]) -> E {
    let mut out = n(head);
    for p in parts {
        out = A::app(out, n(p));
    }
    out
}

fn arm(name: &str, binders: &[&str], body: E) -> Equation {
    Equation { name: name.to_string(), binders: binders.iter().map(|s| s.to_string()).collect(), body }
}

// ----------------------------------------------------------- shape discovery

/// A declared alphabet for a virtualizing interpreter.
#[derive(Debug, Clone)]
pub struct ObjectType {
    pub decl: A::TypeDecl,
    pub app: A::Ctor,
    pub leaves: Vec<A::Ctor>,
}

impl ObjectType {
    pub fn name(&self) -> &str {
        &self.decl.name
    }
    pub fn leaf_index(&self, cname: &str) -> Option<usize> {
        self.leaves.iter().position(|c| c.name == cname)
    }
}

/// The program's object type, identified by shape.
pub fn find_object_type(program: &Program) -> Result<Option<ObjectType>> {
    let mut found: Vec<ObjectType> = Vec::new();
    for d in &program.decls {
        let Decl::Type(t) = d else { continue };
        let apps: Vec<usize> = t
            .ctors
            .iter()
            .enumerate()
            .filter(|(_, c)| c.fields.len() == 2 && c.fields.iter().all(|f| *f == t.name))
            .map(|(i, _)| i)
            .collect();
        if apps.is_empty() {
            continue;
        }
        if apps.len() > 1 {
            let names: Vec<&str> = apps.iter().map(|&i| t.ctors[i].name.as_str()).collect();
            return Err(gerr(format!(
                "type {} has {} binary self-referential constructors ({}); an object type must have \
                 exactly one, the application constructor",
                repr(&t.name),
                apps.len(),
                names.join(", ")
            )));
        }
        let others: Vec<&A::Ctor> = t.ctors.iter().enumerate().filter(|(i, _)| *i != apps[0]).map(|(_, c)| c).collect();
        let bad: Vec<&str> = others.iter().filter(|c| !c.fields.is_empty()).map(|c| c.name.as_str()).collect();
        if !bad.is_empty() {
            return Err(gerr(format!(
                "object type {}: constructor(s) {} carry fields; apart from the application constructor \
                 every constructor must be a leaf",
                repr(&t.name),
                bad.join(", ")
            )));
        }
        found.push(ObjectType {
            decl: t.clone(),
            app: t.ctors[apps[0]].clone(),
            leaves: others.into_iter().cloned().collect(),
        });
    }
    if found.is_empty() {
        return Ok(None);
    }
    if found.len() > 1 {
        let names: Vec<&str> = found.iter().map(|o| o.name()).collect();
        return Err(gerr(format!(
            "more than one object type declared ({}); an interpreter walks one alphabet",
            names.join(", ")
        )));
    }
    Ok(found.pop())
}

/// The step-outcome type ``O`` and the result type ``R`` of a fuel loop.
#[derive(Debug, Clone)]
pub struct LoopTypes {
    pub outcome: A::TypeDecl,
    pub result: A::TypeDecl,
    pub stepped: A::Ctor,
    pub done: A::Ctor,
    pub o_rest: Vec<A::Ctor>,
    pub value: A::Ctor,
    pub timeout: A::Ctor,
    pub mapping: Vec<(String, String)>,
}

impl LoopTypes {
    pub fn r_of(&self, oname: &str) -> &str {
        self.mapping.iter().find(|(o, _)| o == oname).map(|(_, r)| r.as_str()).expect("mapped")
    }
}

/// (the first ctor carrying exactly one field of type ``tname``, the rest)
fn carrier(d: &A::TypeDecl, tname: &str) -> Option<(A::Ctor, Vec<A::Ctor>)> {
    if d.ctors.len() < 2 {
        return None;
    }
    let idx = d.ctors.iter().position(|c| c.fields.len() == 1 && c.fields[0] == tname)?;
    let rest = d.ctors.iter().enumerate().filter(|(i, _)| *i != idx).map(|(_, c)| c.clone()).collect();
    Some((d.ctors[idx].clone(), rest))
}

pub fn find_loop_types(program: &Program, obj: &ObjectType) -> Result<LoopTypes> {
    let mut cands: Vec<(A::TypeDecl, A::Ctor, Vec<A::Ctor>)> = Vec::new();
    for d in &program.decls {
        let Decl::Type(t) = d else { continue };
        if t.name == obj.name() {
            continue;
        }
        if let Some((c, rest)) = carrier(t, obj.name()) {
            cands.push((t.clone(), c, rest));
        }
    }
    if cands.is_empty() {
        return Err(gerr(format!(
            "object type {} is declared but no step-outcome type is: declare one, e.g. 'maybe === Nothing | Just {}'",
            repr(obj.name()),
            obj.name()
        )));
    }
    let (od, stepped, o_rest, rd, value) = if cands.len() == 1 {
        let (od, stepped, o_rest) = cands[0].clone();
        (od.clone(), stepped.clone(), o_rest, od, stepped)
    } else {
        let (od, stepped, o_rest) = cands[cands.len() - 2].clone();
        let (rd, value, _) = cands[cands.len() - 1].clone();
        (od, stepped, o_rest, rd, value)
    };
    if od.ctors.len() != rd.ctors.len() {
        return Err(gerr(format!(
            "outcome type {} has {} constructors and result type {} has {}; the loop needs one result \
             constructor per outcome constructor (one terminal is spent on the timeout)",
            repr(&od.name),
            od.ctors.len(),
            repr(&rd.name),
            rd.ctors.len()
        )));
    }
    build_loop_types(od, stepped, o_rest, rd, value)
}

fn build_loop_types(
    od: A::TypeDecl,
    stepped: A::Ctor,
    o_rest: Vec<A::Ctor>,
    rd: A::TypeDecl,
    value: A::Ctor,
) -> Result<LoopTypes> {
    let r_nullary: Vec<&A::Ctor> = rd.ctors.iter().filter(|c| c.fields.is_empty()).collect();
    if r_nullary.is_empty() {
        return Err(gerr(format!(
            "result type {} has no nullary constructor, so the loop has nothing to return when the fuel runs out",
            repr(&rd.name)
        )));
    }
    let timeout = r_nullary[r_nullary.len() - 1].clone();
    let spare: Vec<&A::Ctor> = r_nullary
        .iter()
        .filter(|c| c.name != timeout.name && c.name != value.name)
        .cloned()
        .collect();
    let nullary_o: Vec<&A::Ctor> = o_rest.iter().filter(|c| c.fields.is_empty()).collect();
    if nullary_o.is_empty() {
        return Err(gerr(format!(
            "outcome type {} has no nullary constructor, so the loop cannot tell when the term has no redex left",
            repr(&od.name)
        )));
    }
    let done = nullary_o[0].clone();
    let mut mapping = vec![(done.name.clone(), value.name.clone())];
    let mut spare_i = 0;
    for c in &o_rest {
        if c.name == done.name {
            continue;
        }
        if !c.fields.is_empty() {
            let idx = od.ctors.iter().position(|x| x.name == c.name).unwrap();
            if idx >= rd.ctors.len() || rd.ctors[idx].fields.len() != c.fields.len() {
                return Err(gerr(format!(
                    "outcome constructor {} carries {} field(s), so the result type needs a constructor \
                     carrying as many at position {}",
                    repr(&c.name),
                    c.fields.len(),
                    idx + 1
                )));
            }
            mapping.push((c.name.clone(), rd.ctors[idx].name.clone()));
            continue;
        }
        if spare_i >= spare.len() {
            return Err(gerr(format!(
                "outcome constructor {} has no result constructor left to map onto in {}",
                repr(&c.name),
                repr(&rd.name)
            )));
        }
        mapping.push((c.name.clone(), spare[spare_i].name.clone()));
        spare_i += 1;
    }
    let o_rest_out = o_rest.iter().filter(|c| c.name != done.name).cloned().collect();
    Ok(LoopTypes { outcome: od, result: rd, stepped, done, o_rest: o_rest_out, value, timeout, mapping })
}

/// The oracle's answer type: what a resolver returns.
#[derive(Debug, Clone)]
pub struct AnswerType {
    pub decl: A::TypeDecl,
    pub hit: A::Ctor,
    pub notyet: A::Ctor,
}

pub fn find_answer_type(program: &Program, obj: &ObjectType, lt: &LoopTypes) -> Result<Option<AnswerType>> {
    let mut cands: Vec<(A::TypeDecl, A::Ctor)> = Vec::new();
    for d in &program.decls {
        let Decl::Type(t) = d else { continue };
        if t.name == obj.name() || t.name == lt.outcome.name || t.name == lt.result.name {
            continue;
        }
        if let Some((c, _)) = carrier(t, obj.name()) {
            cands.push((t.clone(), c));
        }
    }
    if cands.is_empty() {
        return Ok(None);
    }
    if cands.len() > 1 {
        let names: Vec<&str> = cands.iter().map(|(d, _)| d.name.as_str()).collect();
        return Err(gerr(format!(
            "more than one oracle answer type declared ({}); a namespace literal would not know which to build",
            names.join(", ")
        )));
    }
    let (d, hit) = cands.pop().unwrap();
    let nullary: Vec<&A::Ctor> = d.ctors.iter().filter(|c| c.fields.is_empty()).collect();
    if nullary.is_empty() {
        return Err(gerr(format!(
            "answer type {} has no nullary constructor for 'no answer'",
            repr(&d.name)
        )));
    }
    let notyet = nullary[nullary.len() - 1].clone();
    Ok(Some(AnswerType { decl: d, hit, notyet }))
}

/// ``path === Nil | Cons seg path``, found by name.
#[derive(Debug, Clone)]
pub struct PathType {
    pub decl: A::TypeDecl,
    pub nil: A::Ctor,
    pub cons: A::Ctor,
    pub seg: String,
}

pub fn find_path_type(program: &Program) -> Result<Option<PathType>> {
    for d in &program.decls {
        let Decl::Type(t) = d else { continue };
        if t.name != "path" {
            continue;
        }
        let nils: Vec<&A::Ctor> = t.ctors.iter().filter(|c| c.fields.is_empty()).collect();
        let conses: Vec<&A::Ctor> = t.ctors.iter().filter(|c| c.fields.len() == 2 && c.fields[1] == t.name).collect();
        if t.ctors.len() != 2 || nils.len() != 1 || conses.len() != 1 {
            return Err(gerr(
                "the path type must be 'path === Nil | Cons seg path': a nullary constructor and one carrying a \
                 segment and a tail (SYNTAX.md §6)"
                    .to_string(),
            ));
        }
        return Ok(Some(PathType {
            decl: t.clone(),
            nil: nils[0].clone(),
            cons: conses[0].clone(),
            seg: conses[0].fields[0].clone(),
        }));
    }
    Ok(None)
}

pub fn is_interpreter_core(core: &A::Core, obj: &ObjectType) -> bool {
    let names: HashSet<&str> = core.equations.iter().map(|e| e.name.as_str()).collect();
    if names.contains("step") || names.contains("loop") {
        return true;
    }
    obj.decl.ctors.iter().any(|c| names.contains(format!("step{}", c.name).as_str()))
}

// ----------------------------------------------------------------- generation

pub fn generated_names(obj: &ObjectType) -> Vec<String> {
    let mut out: Vec<String> = ["spApp", "sp", "rb1", "rb"].iter().map(|s| s.to_string()).collect();
    out.extend(obj.leaves.iter().map(|c| format!("res{}", c.name)));
    for leaf in ["I", "K", "S"] {
        if obj.leaves.iter().any(|c| c.name == leaf) {
            out.extend(default_step_names(leaf));
        }
    }
    out
}

fn default_step_names(leaf: &str) -> Vec<String> {
    let arity = match leaf {
        "I" => 1,
        "K" => 2,
        _ => 3,
    };
    let mut out: Vec<String> = (1..=arity).rev().map(|i| format!("step{}{}", leaf, i)).collect();
    out.push(format!("step{}", leaf));
    out
}

fn walker_and_rebuilder(obj: &ObjectType) -> Vec<Equation> {
    let leaves = &obj.leaves;
    let conts: Vec<String> = (0..leaves.len()).map(|i| format!("c{}", i)).collect();
    let mut out = Vec::new();
    for (j, c) in leaves.iter().enumerate() {
        let mut binders: Vec<&str> = vec!["acc"];
        binders.extend(conts.iter().map(|s| s.as_str()));
        out.push(arm(&format!("res{}", c.name), &binders, apn(&conts[j], &["acc"])));
    }
    out.push(arm("spApp", &["f", "acc", "t", "u"], ap(n("f"), &[n("t"), apn("cons", &["u", "acc"])])));
    let mut slots: Vec<E> = Vec::new();
    for c in &obj.decl.ctors {
        if c.name == obj.app.name {
            slots.push(apn("spApp", &["sp", "acc"]));
        } else {
            slots.push(apn(&format!("res{}", c.name), &["acc"]));
        }
    }
    out.push(arm("sp", &["m", "acc"], ap(n("m"), &slots)));
    out.push(arm("rb1", &["f", "h", "x", "xs"], ap(n("f"), &[apn(&obj.app.name, &["h", "x"]), n("xs")])));
    out.push(arm("rb", &["h", "args"], ap(n("args"), &[n("h"), apn("rb1", &["rb", "h"])])));
    out
}

fn default_step_equations(obj: &ObjectType, lt: &LoopTypes) -> Vec<Equation> {
    let stepped = lt.stepped.name.as_str();
    let done = lt.done.name.as_str();
    let app_c = obj.app.name.as_str();
    let have: HashSet<&str> = obj.leaves.iter().map(|c| c.name.as_str()).collect();
    let mut out = Vec::new();
    if have.contains("I") {
        out.push(arm("stepI1", &["x", "rest"], ap(n(stepped), &[apn("rb", &["x", "rest"])])));
        out.push(arm("stepI", &["args"], ap(n("args"), &[n(done), n("stepI1")])));
    }
    if have.contains("K") {
        out.push(arm("stepK2", &["x", "y", "rest"], ap(n(stepped), &[apn("rb", &["x", "rest"])])));
        out.push(arm("stepK1", &["x", "r"], ap(n("r"), &[n(done), apn("stepK2", &["x"])])));
        out.push(arm("stepK", &["args"], ap(n("args"), &[n(done), n("stepK1")])));
    }
    if have.contains("S") {
        let rebuilt = ap(n(app_c), &[apn(app_c, &["x", "z"]), apn(app_c, &["y", "z"])]);
        out.push(arm("stepS3", &["x", "y", "z", "rest"], ap(n(stepped), &[ap(n("rb"), &[rebuilt, n("rest")])])));
        out.push(arm("stepS2", &["x", "y", "r2"], ap(n("r2"), &[n(done), apn("stepS3", &["x", "y"])])));
        out.push(arm("stepS1", &["x", "r"], ap(n("r"), &[n(done), apn("stepS2", &["x"])])));
        out.push(arm("stepS", &["args"], ap(n("args"), &[n(done), n("stepS1")])));
    }
    out
}

fn core_step_equation(obj: &ObjectType, core: &A::Core) -> Equation {
    let mine: HashSet<&str> = core.equations.iter().map(|e| e.name.as_str()).collect();
    let mut slots: Vec<E> = Vec::new();
    for c in &obj.leaves {
        let nm = format!("step{}", c.name);
        if mine.contains(nm.as_str()) {
            let params: Vec<&str> = core.params.iter().map(|s| s.as_str()).collect();
            slots.push(apn(&nm, &params));
        } else {
            slots.push(n(&nm));
        }
    }
    let mut parts = vec![n("m"), n("nil")];
    parts.extend(slots);
    arm("step", &["m"], ap(n("sp"), &parts))
}

fn core_loop_equations(lt: &LoopTypes, core: &A::Core) -> Vec<Equation> {
    let ps: Vec<&str> = core.params.iter().map(|s| s.as_str()).collect();
    let mut conts: Vec<E> = Vec::new();
    for c in &lt.outcome.ctors {
        if c.name == lt.stepped.name {
            let mut parts: Vec<E> = ps.iter().map(|x| n(x)).collect();
            parts.push(n("n2"));
            conts.push(ap(n("f"), &parts));
        } else if c.name == lt.done.name {
            conts.push(apn(&lt.value.name, &["m"]));
        } else {
            conts.push(n(lt.r_of(&c.name)));
        }
    }
    let mut loop1_parts = vec![n("m")];
    loop1_parts.extend(conts);
    vec![
        arm("loop1", &["f", "m", "n2"], ap(apn("step", &ps), &loop1_parts)),
        arm("loop", &["n", "m"], ap(n("n"), &[n(&lt.timeout.name), ap(apn("loop1", &ps), &[n("loop"), n("m")])])),
    ]
}

/// What ``generate`` will supply, without generating it.
pub fn names_generation_adds(program: &Program) -> Result<(HashSet<String>, HashMap<String, HashSet<String>>)> {
    let Some(obj) = find_object_type(program)? else {
        return Ok((HashSet::new(), HashMap::new()));
    };
    let mut taken: HashSet<String> = HashSet::new();
    for d in &program.decls {
        match d {
            Decl::Type(t) => taken.extend(t.ctors.iter().map(|c| c.name.clone())),
            Decl::Equation(_) | Decl::Macro(_) | Decl::Def { .. } | Decl::Core(_) => {
                taken.insert(d.name().to_string());
            }
            Decl::Sig { .. } => {}
        }
    }
    let top: HashSet<String> = generated_names(&obj).into_iter().filter(|n| !taken.contains(n)).collect();
    let mut per_core = HashMap::new();
    for d in &program.decls {
        if let Decl::Core(c) = d {
            if is_interpreter_core(c, &obj) {
                let have: HashSet<&str> = c.equations.iter().map(|e| e.name.as_str()).collect();
                let mut extra = HashSet::new();
                if !have.contains("step") {
                    extra.insert("step".to_string());
                }
                if !have.contains("loop") {
                    extra.insert("loop".to_string());
                    extra.insert("loop1".to_string());
                }
                per_core.insert(c.name.clone(), extra);
            }
        }
    }
    Ok((top, per_core))
}

/// Return ``program`` with the type-generated forms added.
pub fn generate(program: &Program) -> Result<Program> {
    let Some(obj) = find_object_type(program)? else {
        return Ok(program.clone());
    };
    let lt = find_loop_types(program, &obj)?;
    let mut taken: HashSet<String> = HashSet::new();
    for d in &program.decls {
        match d {
            Decl::Type(t) => taken.extend(t.ctors.iter().map(|c| c.name.clone())),
            Decl::Sig { .. } => {}
            _ => {
                taken.insert(d.name().to_string());
            }
        }
    }
    let mut extra = walker_and_rebuilder(&obj);
    extra.extend(default_step_equations(&obj, &lt));
    let extra: Vec<Equation> = extra.into_iter().filter(|x| !taken.contains(&x.name)).collect();
    let mut decls = Vec::new();
    for d in &program.decls {
        match d {
            Decl::Core(c) if is_interpreter_core(c, &obj) => decls.push(Decl::Core(fill_core(c, &obj, &lt)?)),
            _ => decls.push(d.clone()),
        }
    }
    decls.extend(extra.into_iter().map(Decl::Equation));
    Ok(Program { decls })
}

fn fill_core(core: &A::Core, obj: &ObjectType, lt: &LoopTypes) -> Result<A::Core> {
    let have: HashSet<&str> = core.equations.iter().map(|e| e.name.as_str()).collect();
    let mut added = Vec::new();
    if !have.contains("step") {
        added.push(core_step_equation(obj, core));
    }
    if !have.contains("loop") {
        if have.contains("loop1") {
            return Err(gerr(format!(
                "core {} writes 'loop1' but not 'loop'; write both or neither",
                repr(&core.name)
            )));
        }
        added.extend(core_loop_equations(lt, core));
    }
    let mut equations = core.equations.clone();
    equations.extend(added);
    Ok(A::Core { name: core.name.clone(), equations, params: core.params.clone() })
}
