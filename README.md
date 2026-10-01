# SKIjack

![](./img/hero.jpg)

[![CI](https://github.com/sigilante/SKIjack/actions/workflows/ci.yml/badge.svg)](https://github.com/sigilante/SKIjack/actions/workflows/ci.yml)

(Pronounced "sky-jack".)

**Status ~2026.9.22:  Two papers covering this work have been submitted to journals.  The
repository is at version 0.2.0 and considered stable and usable.**

* N E Davis (2027, in review) A Self-Interpreter for $SKI$: Authoring Semantics for New Symbols. *Journal of Functional Programming*.  doi:10.5281/zenodo.22867957
* N E Davis (2027a, in review) SKIjack: A Low-Level Native Language for the $SKI$ Calculus.  *The Art, Science, and Engineering of Programming*.

A supercombinator language over the $SKI$ combinatory logic and a graph-reduction runtime with jet-accelerated code to make it
(marginally) viable.

- `SPEC.md`: **the specification** — the language as implemented and tested, one rule per decision, with the decision and the test that pins it. Start here; the notes below are its history.
- `DESIDERATA.md`: what the language must be, stated as twelve properties borrowed from nockasm's discipline, and the four tiers of exposure (primitives, combinators, supercombinators, macros).
- `SYNTAX.md`: the surface direction: equations, cores, glyph-named combinators, two brackets, one grammar with two lexicons (ASCII and Unicode) related by a bijective token table, and the scry namespace discipline.
- `SURFACE-LANGUAGE-DESIGN.md`: the kernel forms, the representation ABI (Scott pairs as cells, Nock axes over data, cores tied with `Y`), the compile rules, compile-time name resolution with no runtime environment, the standard library the runtime supplies at boot, and the quotation line that a theorem fixes.
- `EXAMPLES.md`: numerals (increment, decrement, addition, subtraction), a combinator three ways, a macro over pairs at level 0 and level 1, a user interpreter, a value lookup, words to numbers both as a case and as a namespace, full ASCII as a type with a digit parser, and an event type with a kernel the runtime pokes — in both spellings, with the codegen and the checks that were actually run.
- `RUNTIME-DESIGN.md`: why a Turner-style reducer with jets is required, what it must reproduce, and what it must not do.
- `avon/DESIGN.md`: the build plan for the C runtime — the measurement that fixes its acceptance test (sharing changes the paper's counts and not its values, so Avon carries two strategies), the node and arena representation, jets as loader-installed wrappers rather than runtime hashing, the conformance harness, and eight stages with what each one has to prove. `avon/bench/strategies.py` reproduces the measurement, and `avon/bench/jets.py` lists the structures the compiled corpus repeats most, the candidates for jets.

- `rust/`: a Rust port of `skijack`, conformant with the reference implementation to the byte on
  every corpus program, flag and run of the CLI (`rust/tests/golden.manifest` pins 2,200 reference
  invocations); its README records the measured speed-ups against the Python reference.

- `editors/vscode/`: syntax highlighting for `.ski` in VS Code, both lexicons, driven by the token table; symlink it into `~/.vscode/extensions/` (its README says how).

- `python/`: `skijack`, the reference implementation in Python on `aviary-kernel`: the two lexers over one token table, one parser, renderers for both lexicons, the expander through bracket abstraction, and behavioral probes; `python/README.md` records every decision taken and what its test suite proves. Its corpus under `python/skijack/corpus/` is written in both spellings and is also Avon's conformance suite: the C runtime is correct when it reproduces `skijack`'s terms and decoded values on every file there, and the reference host's contraction counts under its faithful strategy (`avon/DESIGN.md` §1).

Three levels: an **equation** `f x y = body` is what an author writes, a
**supercombinator** is the closed `Y`-tied term it compiles to, and a
**core** is the group it is declared in. The AST node is `A.Equation`,
a core entry's backend name is `core_equation`, and Stage A reports
`in core C, equation f`.

The reference artifact and every count the papers report live in
[`sigilante/artifact-metacircular-ski`](https://github.com/sigilante/artifact-metacircular-ski);
this repository depends on that one, never the reverse. The self-interpreter it compiles to is
described in *A self-interpreter for SKI: Authoring semantics for new symbols*
([doi:10.5281/zenodo.22867957](https://doi.org/10.5281/zenodo.22867957), in review at JFP),
and the language in the companion paper on SKIjack (in review).

## Install and test

    pip install -e "python[test]"
    python -m pytest python/tests

The suite is self-contained: the four oracle scripts from
`artifact-metacircular-ski` are vendored under `python/tests/artifact/` (provenance in the
README there), so all 855 tests run with no setup. To check against a live checkout of the
artifact instead, set `SKIJACK_ARTIFACT_DIR` to it. CI runs the suite on Python 3.10–3.13.

