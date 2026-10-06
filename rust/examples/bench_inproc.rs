//! In-process timings of each pipeline stage, to separate the reducer's
//! throughput from process start-up.  Prints one line per measurement:
//! ``label  min_ms  median_ms  extra``.
use std::time::Instant;

use skijack::corpus;
use skijack::dictionary::from_expansion;
use skijack::lexicon::Lexicon;
use skijack::run::{decode, peel, run_level1};

fn timeit<T>(reps: usize, mut f: impl FnMut() -> T) -> (f64, f64, T) {
    let mut times = Vec::new();
    let mut last = None;
    for _ in 0..reps {
        let t0 = Instant::now();
        last = Some(f());
        times.push(t0.elapsed().as_secs_f64() * 1000.0);
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (times[0], times[times.len() / 2], last.unwrap())
}

fn main() {
    let reps: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(5);
    // 1. compile every corpus program (parse, Stage A, generate, Stage B, expand)
    let (mn, md, n) = timeit(reps, || {
        let mut n = 0;
        for s in corpus::SOURCES {
            let lx = Lexicon::parse(s.lexicon).unwrap();
            if let Ok(e) = skijack::compile(s.text, lx) {
                n += e.terms.len();
            }
        }
        n
    });
    println!("compile-corpus\t{:.2}\t{:.2}\t{} terms over {} files", mn, md, n, corpus::SOURCES.len());
    // 2. compile tower alone, and its dictionary
    let src = corpus::read("tower", "ascii").unwrap();
    let (mn, md, _) = timeit(reps, || skijack::compile(src, Lexicon::Ascii).unwrap());
    println!("compile-tower\t{:.2}\t{:.2}\t", mn, md);
    let (mn, md, _) = timeit(reps, || {
        let mut e = skijack::compile(src, Lexicon::Ascii).unwrap();
        from_expansion(&mut e).unwrap().len()
    });
    println!("dictionary-tower\t{:.2}\t{:.2}\t", mn, md);
    // 3. the reducer: t0, t1, t2, and scry-ns answer
    let exp = skijack::compile(src, Lexicon::Ascii).unwrap();
    for name in ["t0", "t1", "t2"] {
        let prog = &exp.level1[name];
        let (mn, md, o) = timeit(reps, || run_level1(prog, 5_000_000, None).unwrap());
        let rate = o.steps as f64 / (mn / 1000.0);
        println!("run-{}\t{:.2}\t{:.2}\t{} contractions, {:.1} M/s at best", name, mn, md, o.steps, rate / 1e6);
        let (mn, md, _) = timeit(reps, || {
            let (_, fields) = peel(&o.term, &prog.result_type, 5_000_000).unwrap();
            decode(&fields[0], &prog.object_type, 5_000_000, 200_000).unwrap()
        });
        println!("decode-{}\t{:.2}\t{:.2}\t", name, mn, md);
    }
    let src = corpus::read("scry-ns", "ascii").unwrap();
    let exp = skijack::compile(src, Lexicon::Ascii).unwrap();
    let prog = &exp.level1["answer"];
    let (mn, md, o) = timeit(reps, || run_level1(prog, 5_000_000, None).unwrap());
    println!("run-answer\t{:.2}\t{:.2}\t{} contractions", mn, md, o.steps);
}
