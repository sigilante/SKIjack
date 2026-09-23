use std::time::Instant;
use skijack::{check::check_program, corpus, expand::{expand_program, PRELUDE_NAMES}, generate::generate, lexicon::Lexicon, parser::parse, typecheck::typecheck_program};
fn main() {
    let stem = std::env::args().nth(1).unwrap_or("ascii-digits".into());
    let src = corpus::read(&stem, "ascii").unwrap();
    let t = Instant::now(); let p = parse(src, Lexicon::Ascii).unwrap(); println!("parse      {:7.2} ms", t.elapsed().as_secs_f64()*1e3);
    let t = Instant::now(); let pr = check_program(&p, &PRELUDE_NAMES); println!("stage A    {:7.2} ms ({} problems)", t.elapsed().as_secs_f64()*1e3, pr.len());
    let t = Instant::now(); let g = generate(&p).unwrap(); println!("generate   {:7.2} ms", t.elapsed().as_secs_f64()*1e3);
    let t = Instant::now(); let pr = typecheck_program(&g, &PRELUDE_NAMES, true).unwrap(); println!("stage B    {:7.2} ms ({} problems)", t.elapsed().as_secs_f64()*1e3, pr.len());
    let t = Instant::now(); let e = expand_program(&g, false, false).unwrap(); println!("expand     {:7.2} ms ({} terms)", t.elapsed().as_secs_f64()*1e3, e.terms.len());
}
