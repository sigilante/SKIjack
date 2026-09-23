//! The conformance corpus, embedded from ``python/skijack/corpus``.

pub struct Source { pub stem: &'static str, pub lexicon: &'static str, pub text: &'static str }

pub static SOURCES: &[Source] = &[
    Source { stem: "ascii-digits", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/ascii-digits.ascii.ski") },
    Source { stem: "ascii-digits", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/ascii-digits.unicode.ski") },
    Source { stem: "interp-t3", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/interp-t3.ascii.ski") },
    Source { stem: "interp-t3", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/interp-t3.unicode.ski") },
    Source { stem: "interp-whnff", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/interp-whnff.ascii.ski") },
    Source { stem: "interp-whnff", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/interp-whnff.unicode.ski") },
    Source { stem: "interp-whnff-written", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/interp-whnff-written.ascii.ski") },
    Source { stem: "interp-whnff-written-loop", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/interp-whnff-written-loop.ascii.ski") },
    Source { stem: "interp-whnff-written-loop", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/interp-whnff-written-loop.unicode.ski") },
    Source { stem: "interp-whnff-written", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/interp-whnff-written.unicode.ski") },
    Source { stem: "kernel-events", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/kernel-events.ascii.ski") },
    Source { stem: "kernel-events", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/kernel-events.unicode.ski") },
    Source { stem: "level1-flipa", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/level1-flipa.ascii.ski") },
    Source { stem: "level1-flipa", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/level1-flipa.unicode.ski") },
    Source { stem: "misc-forms", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/misc-forms.ascii.ski") },
    Source { stem: "misc-forms", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/misc-forms.unicode.ski") },
    Source { stem: "parse-chars", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/parse-chars.ascii.ski") },
    Source { stem: "parse-chars", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/parse-chars.unicode.ski") },
    Source { stem: "scry-block", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/scry-block.ascii.ski") },
    Source { stem: "scry-block", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/scry-block.unicode.ski") },
    Source { stem: "scry-ns", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/scry-ns.ascii.ski") },
    Source { stem: "scry-ns", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/scry-ns.unicode.ski") },
    Source { stem: "scry-wfn", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/scry-wfn.ascii.ski") },
    Source { stem: "scry-wfn", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/scry-wfn.unicode.ski") },
    Source { stem: "scry-wfq", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/scry-wfq.ascii.ski") },
    Source { stem: "scry-wfq", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/scry-wfq.unicode.ski") },
    Source { stem: "sec1-nat", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/sec1-nat.ascii.ski") },
    Source { stem: "sec1-nat", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/sec1-nat.unicode.ski") },
    Source { stem: "sec2-c", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/sec2-c.ascii.ski") },
    Source { stem: "sec2-c", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/sec2-c.unicode.ski") },
    Source { stem: "sec3-swap", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/sec3-swap.ascii.ski") },
    Source { stem: "sec3-swap", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/sec3-swap.unicode.ski") },
    Source { stem: "sec4-interp", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/sec4-interp.ascii.ski") },
    Source { stem: "sec4-interp", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/sec4-interp.unicode.ski") },
    Source { stem: "sec5-lookup", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/sec5-lookup.ascii.ski") },
    Source { stem: "sec5-lookup", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/sec5-lookup.unicode.ski") },
    Source { stem: "syntax3-resolver", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/syntax3-resolver.ascii.ski") },
    Source { stem: "syntax3-resolver", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/syntax3-resolver.unicode.ski") },
    Source { stem: "tower", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/tower.ascii.ski") },
    Source { stem: "tower", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/tower.unicode.ski") },
    Source { stem: "words-to-numbers", lexicon: "ascii", text: include_str!("../../python/skijack/corpus/words-to-numbers.ascii.ski") },
    Source { stem: "words-to-numbers", lexicon: "unicode", text: include_str!("../../python/skijack/corpus/words-to-numbers.unicode.ski") },
];

/// Every program, once, without its lexicon suffix.
pub fn names() -> Vec<&'static str> {
    let mut v: Vec<&'static str> = SOURCES.iter().map(|s| s.stem).collect();
    v.sort();
    v.dedup();
    v
}

pub fn read(stem: &str, lexicon: &str) -> Option<&'static str> {
    SOURCES.iter().find(|s| s.stem == stem && s.lexicon == lexicon).map(|s| s.text)
}
