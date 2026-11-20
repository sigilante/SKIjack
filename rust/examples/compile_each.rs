use std::time::Instant;
use skijack::{corpus, lexicon::Lexicon};
fn main() {
    let mut rows = Vec::new();
    for s in corpus::SOURCES {
        if s.lexicon != "ascii" { continue; }
        let lx = Lexicon::parse(s.lexicon).unwrap();
        let mut best = f64::MAX;
        let mut n = 0;
        for _ in 0..5 {
            let t0 = Instant::now();
            if let Ok(e) = skijack::compile(s.text, lx) { n = e.terms.len(); }
            best = best.min(t0.elapsed().as_secs_f64() * 1000.0);
        }
        rows.push((best, s.stem, n));
    }
    rows.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    for (ms, stem, n) in rows { println!("{:8.2} ms  {:28} {} terms", ms, stem, n); }
}
