//! The laws the reference test suite states, over the shipped corpus.

use skijack::ast::Program;
use skijack::corpus;
use skijack::dictionary::{from_expansion, lift, lower, structural_hash, MIN_LIFT_SIZE};
use skijack::lexicon::Lexicon;
use skijack::parser::parse;
use skijack::render::render_program;
use skijack::run::{decode, peel, run_level1, run_policy};
use skijack::term::{size, term_eq};

fn lx(s: &str) -> Lexicon {
    Lexicon::parse(s).unwrap()
}

#[test]
fn the_self_interpreter_is_618_atoms() {
    let e = skijack::compile(corpus::read("interp-whnff", "ascii").unwrap(), Lexicon::Ascii).unwrap();
    assert_eq!(e.sizes["whnfF"], 618);
    let u = skijack::compile(corpus::read("interp-whnff", "unicode").unwrap(), Lexicon::Unicode).unwrap();
    assert!(term_eq(&e.terms["whnfF"], &u.terms["whnfF"]));
}

#[test]
fn both_spellings_parse_to_one_tree() {
    for stem in corpus::names() {
        let a = parse(corpus::read(stem, "ascii").unwrap(), Lexicon::Ascii);
        let u = parse(corpus::read(stem, "unicode").unwrap(), Lexicon::Unicode);
        match (a, u) {
            (Ok(a), Ok(u)) => assert_eq!(a, u, "{}", stem),
            (Err(a), Err(u)) => assert_eq!(a.class_name(), u.class_name(), "{}", stem),
            _ => panic!("{}: one spelling parses and the other does not", stem),
        }
    }
}

#[test]
fn render_round_trips_within_and_across_lexicons() {
    for s in corpus::SOURCES {
        let Ok(tree): Result<Program, _> = parse(s.text, lx(s.lexicon)) else { continue };
        for target in ["ascii", "unicode"] {
            let text = render_program(&tree, lx(target));
            let back = parse(&text, lx(target)).unwrap_or_else(|e| panic!("{}.{} -> {}: {}", s.stem, s.lexicon, target, e));
            assert_eq!(back, tree, "{}.{} -> {}", s.stem, s.lexicon, target);
        }
    }
}

#[test]
fn lower_undoes_lift_on_every_corpus_term() {
    for stem in corpus::names() {
        let Ok(mut e) = skijack::compile(corpus::read(stem, "ascii").unwrap(), Lexicon::Ascii) else { continue };
        let terms: Vec<_> = e.terms.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        let d = from_expansion(&mut e).unwrap();
        for (name, t) in terms {
            let named = lift(&t, &d, MIN_LIFT_SIZE, &[]);
            let back = lower(&named, &d).unwrap();
            assert!(term_eq(&back, &t), "{}::{}", stem, name);
            assert_eq!(structural_hash(&back), structural_hash(&t));
            assert_eq!(size(&back), e.sizes[&name]);
        }
    }
}

#[test]
fn hashes_are_merkle_and_versioned() {
    let mut e = skijack::compile(corpus::read("sec1-nat", "ascii").unwrap(), Lexicon::Ascii).unwrap();
    let d = from_expansion(&mut e).unwrap();
    let y = d.get("Y").unwrap();
    assert_eq!(y.size, 14);
    assert!(y.hash.starts_with("skijack-1:"));
    assert_eq!(y.hash.len(), "skijack-1:".len() + 16);
}

#[test]
fn the_tower_runs_and_decodes() {
    let e = skijack::compile(corpus::read("tower", "ascii").unwrap(), Lexicon::Ascii).unwrap();
    let t1 = &e.level1["t1"];
    let o = run_level1(t1, 5_000_000, None).unwrap();
    assert!(o.whnf());
    assert_eq!(o.steps, 91_556);
    let (ctor, fields) = peel(&o.term, &t1.result_type, 5_000_000).unwrap();
    assert_eq!(ctor, "Just");
    let v = decode(&fields[0], &t1.object_type, 5_000_000, 200_000).unwrap();
    assert_eq!(skijack::render::render_ascii(&v), "K");
    let t2 = &e.level1["t2"];
    let o = run_level1(t2, 5_000_000, None).unwrap();
    assert_eq!(o.steps, 504_930);
}

#[test]
fn elided_fuel_deepens_until_a_value() {
    let e = skijack::compile(corpus::read("level1-flipa", "ascii").unwrap(), Lexicon::Ascii).unwrap();
    let r = run_policy(&e.level1["policy"], 8, 4096, 5_000_000).unwrap();
    assert_eq!(r.constructor, "Just");
    assert_eq!(r.budget, Some(64));
    assert_eq!(r.budgets, vec![8, 16, 32, 64]);
}

#[test]
fn stage_a_rejects_with_the_first_problems_class() {
    let err = skijack::compile("f x = x nowhere\n", Lexicon::Ascii).err().expect("expected an error");
    assert_eq!(err.class_name(), "ScopeError");
    assert!(err.to_string().contains("1 Stage A problem"));
    let err = skijack::compile_with("f x = x nowhere\n", Lexicon::Ascii, false, true).err().expect("expected an error");
    assert_eq!(err.class_name(), "ExpandError");
}

#[test]
fn stage_b_refuses_a_function_as_a_datum() {
    let err = skijack::compile("nat === Zero | Suc nat\nf := Suc K\n", Lexicon::Ascii).err().expect("expected an error");
    assert_eq!(err.class_name(), "TypeMismatchError");
    assert!(err.to_string().contains("a function is not a datum"), "{}", err);
}

#[test]
fn macro_work_is_bounded() {
    let mut lines = vec!["nat === Zero | Suc nat".to_string(), "m0 x :=* x".to_string()];
    for i in 1..25 {
        lines.push(format!("m{} x :=* m{} (m{} x)", i, i - 1, i - 1));
    }
    lines.push("f := m24 I".to_string());
    let err = skijack::compile(&(lines.join("\n") + "\n"), Lexicon::Ascii).err().expect("expected an error");
    assert!(err.to_string().contains("substitutions"));
}
