# skijack

A surface language over the $SKI$ combinator calculus that compiles to
closed `{S,K,I}` terms, with the interpreter of the companion paper as
its conformance target.

The claim this package exists to support: **the abstraction is free, and
term equality proves it.** The self-interpreter of Davis (2027)---618
atoms of pure `{S,K,I}`, built by hand---compiles from three lines of
surface source to the same term, atom for atom. So do five more: the
observability pair at 768 and 771, the blocking interpreters at 950 and
1,066, and structural equality on encoded terms at 240.

Everything is compile-time. Quotation happens in the compiler and
nowhere else, because no closed term quotes every live term; the
language's job is to make that line visible rather than to pretend it
isn't there.

* N E Davis (2027, in review) A Self-Interpreter for $SKI$: Authoring Semantics for New Symbols. *Journal of Functional Programming*.  doi:10.5281/zenodo.22867957
* N E Davis (2027a, in review) SKIjack: A Low-Level Native Language for the $SKI$ Calculus.  *The Art, Science, and Engineering of Programming*.

## Install

```sh
pip install skijack
```

Requires Python 3.10+ and `aviary-kernel`, which supplies bracket
abstraction, the term representation and the reducer. This package
reimplements none of them.

## Use

```sh
skijack FILE                     # a summary
skijack FILE --check             # Stage A, then B; exits 1 and lists every problem
skijack FILE --expand            # every compiled term, with atom counts
skijack FILE --dictionary        # the Tier 1 table: name, atoms, hash
skijack FILE --lift NAME         # NAME, with what the table knows named
skijack FILE --render unicode    # the same program in the other lexicon
skijack FILE --run NAME [--fuel N]   # run a level-1 declaration and decode it
```

The lexicon is taken from the filename (`*.unicode.ski`) unless
`--lexicon` says otherwise. The twenty-two programs of the conformance
corpus ship with the package; eighteen compile, and Stage A refuses the
other four for stated reasons:

```python
>>> import skijack
>>> from skijack import corpus
>>> skijack.compile(corpus.read("interp-whnff")).sizes["whnfF"]
618
```

From Python:

```python
import skijack
exp   = skijack.compile(open("prog.ski").read())   # parse, check, generate, expand
d     = skijack.from_expansion(exp)                # the Tier 1 table
named = skijack.lift(exp.term("whnfF"), d)         # back to named source
out   = skijack.run_level1(exp.level1["answer"], 1_000_000)
```

Everything this package raises for a bad program derives from
`skijack.SkijackError`, including a refusal by aviary, the host that
abstracts and expands, which reaches the caller as an `ExpandError`.

## Definitions

An author writes an **equation** `f x y = body`. The closed `Y`-tied
term to which it compiles is the **supercombinator**, the unit of
naming, sharing, jetting and lifting. The group an equation is declared
in is a **core**. Names resolve in a compile-time table and are gone
before anything runs; there is no environment at run time.

## Tests

```sh
pip install skijack[test]
python3 -m pytest -q
```

Roughly a third of the suite compares compiled terms against the
hand-built artifact of the companion paper. Point `SKIJACK_ARTIFACT_DIR`
at a checkout of it, or set `SKIJACK_ALLOW_SKIP=1` to run the reduced
suite knowingly --- the suite refuses to run silently without its
oracle, because what remains would check the compiler only against
itself.

## More

The language is specified in `SPEC.md` at the repository root; `NOTES.md`
beside this file is the decision log it was derived from.

`NOTES.md` records what the suite proves, every open question the
specification left and how it was answered, and any discrepancies found
in the original specification itself.
