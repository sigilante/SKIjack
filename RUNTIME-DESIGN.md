# Design note: the runtime

> **Status (2026-09-21).** Design note written 2026-09-16. The compiler it targets is now implemented as `python/skijack`; the runtime it plans is not built, and `avon/bench/` reproduces the measurements it rests on. Where this note and the compiler differ, the compiler and its tests are authoritative.

*2026-09-16. Companion to `SURFACE-LANGUAGE-DESIGN.md`. The language
note fixes what programs compile to; this note fixes what runs them and
why a real runtime is needed for the language to be viable. Nothing here
is built. The research artifact (public as `artifact-metacircular-ski`) runs on
`aviary-kernel`'s Python reducer, and that remains the reference
implementation for every count the paper reports.*

## 0. Thesis

The viable runtime is Turner's SKI graph-reduction machine with jets.
Jets are the runtime performing, from outside the calculus, the two
operations the calculus cannot perform for itself: recognizing the
structure of a live term, and (at the encoding boundary) quoting one.
Both are metalevel by theorem, not by engineering convenience, so the
runtime's job description is fixed before a line of it is written.

## 1. What the reference host is

`aviary-kernel` 0.1.0 reduces terms as a DAG with sharing, under normal
order, one contraction per step, with a fuel cap and a sampled size cap.
Sharing is why the artifact runs at all: the tower's intermediate states
are a few hundred DAG nodes while their tree unfoldings reach 10⁵ atoms.
Measured throughput is about 12,000 contractions per second (T2's
504,930 contractions in about 40 s). It has no jets and no notion of a
known combinator; every `S`, `K`, `I` is reduced by its rule.

For the paper that is the right tool. Its counts are the claims, and a
reducer that did anything cleverer would make the counts about the
reducer.

## 2. What viability requires

Three orders of magnitude in throughput, and the removal of the
per-level interpretive overhead.

- **Throughput.** A C or Rust graph reducer with hash-consed nodes and
  an explicit spine stack runs at 10⁷ to 10⁸ contractions per second.
  That makes a third tower level, the self-hosting compiler, and the
  partial-evaluation runs routine instead of overnight. This is the
  well-trodden part: Turner's machine \[1\], supercombinators \[2\], the
  G-machine \[3\], and the Reduceron \[4\] for the hardware end.

- **Jets.** Nock is viable because Vere matches batteries against a
  dashboard of known cores by hash and runs native code. The SKI
  analogue matches expanded subterms against a table of known
  combinators by structural hash: the standard subject's supercombinators first
  (numerals, lists, `EQ`), then the interpreters. Jetting `whnfF` is the
  decisive one: it is exactly why `+mock` costs nothing per level in
  Nock, and it removes the roughly 10³-per-level overhead the paper
  reports, by the same means and with the same honesty about where the
  speed comes from. Turner's built-in combinator set was already this
  idea under another name.

- **Correctness of jets.** A jet is a claim that native code agrees with
  the term it replaces. The artifact's discipline transfers directly:
  a jet is admitted when the fresh-marker probes and the reduction
  certificates (`NEXT-STEPS.md` item 3 in the paper's repository) agree
  with the reduced term on the checked inputs. Differential testing
  against the unjetted reducer is the ongoing check, as it is for Vere.

## 3. Where the runtime sits relative to the theorems

Proposition 3.1 of the paper: no SKI term can quote a live term, because
factorisation of live combinators is not representable (Jay and
Given-Wilson 2011, Thm. 3.2). The proof is about terms; Jay and
Given-Wilson explicitly set aside "the Turing machine with the term on
its tape," which can factorise freely. The runtime is that machine.

So the two metalevel operations the language design (`SURFACE-LANGUAGE-DESIGN.md`
§5) must stage are exactly the two the runtime performs:

| operation | inside the calculus | in the runtime |
|---|---|---|
| quote a live term | impossible (Prop. 3.1) | the compiler, at compile time |
| recognize a live term's structure | impossible (same theorem) | jet matching, at run time |

This is the sentence the follow-up paper should state in its
introduction: the runtime does for the calculus the two things it cannot
do for itself, and both are fixed by a theorem rather than chosen.

## 3a. Two runtimes

- **`skijack`**: Python, on `aviary-kernel`'s reducer. The reference
  implementation and the conformance oracle; slow, exact, and the thing
  the paper's counts come from.
- **Avon** (a nod to Vere): a C runtime. Vere's own language, and the
  right one for a graph reducer, which is a flat arena of immutable
  shared nodes addressed by integer index with an explicit stack and no
  hidden allocation; an ownership model buys nothing for that. The
  architecture is the Ares / NockVM one recast in C:
  - **Arena.** One flat array of nodes, each a small tagged struct: leaf
    `S`/`K`/`I`, `App(left, right)` as two 32-bit indices, and an
    indirection node for the result of a contraction so sharing survives
    reduction. Bump allocation; a hash table from `(left, right)` to
    index so structurally equal applications are one node
    (hash-consing), which is also what makes jet lookup O(1).
  - **Reducer.** Normal-order head reduction with an explicit spine
    stack of indices, one contraction per step, fuel as a counter, a
    size cap on the arena. No recursion in the reducer, so a
    thousand-deep spine costs nothing on the C stack.
  - **Memory reclamation.** Vere's two-sided loom (allocate from both
    ends, copy the live graph on return from a computation) is the
    proven design for a persistent noun store and transfers directly;
    reference counting is the simpler first version and is correct for
    an acyclic arena, which this is.
  - **Jets.** A table from the structural hash of a node to a C function
    pointer, consulted when a hash-consed node is about to be reduced;
    the interpreter jet first. The hash is computed once at
    hash-cons insertion, so matching is a table probe, not a walk.
  - **Snapshots.** The arena is a flat array, so a snapshot is a write of
    the array plus the hash table's rebuild on load; interchange uses
    the bitstring encoding of §3d.
  - **Discipline.** Compiled with sanitizers in tests; differential
    against `skijack` on every corpus term, byte-identical outputs and
    identical contraction counts; no behaviour the Python reference does
    not also have.
  Byte-identical to `skijack` on every conformance target, by the
  nockasm discipline.

Both implement the same boot protocol (§3b), so a compiled kernel moves
between them.

## 3b. Boot protocol and kernel shape

**An executable is a function of the runtime's initial subject, and the
runtime always starts by applying the loaded term to it.** Nothing else
needs to be known to start a program. The initial subject carries the
quoted standard library (`SURFACE-LANGUAGE-DESIGN.md` §6b), so this also
settles who supplies `<subject>`: the runtime, at boot.

A **kernel** is a door in Arvo's shape (`SPEC.md` §4.1): a cell
`[battery state]` whose battery holds three arms at fixed axes, which the
runtime pulls by axis and applies to the whole kernel, as Nock 9 does:
- `poke` (axis 4): kernel → event → `[effects kernel']`;
- `peek` (axis 10): kernel → path → answer, which is the scry namespace
  of `SYNTAX.md` §6, served to level-1 programs that `∵`;
- `load` (axis 11): kernel → old state → kernel', the upgrade path.

An arm reaches its own battery and state by axis, so no arm names its
kernel. The worked form is `python/skijack/corpus/kernel-events.ascii.ski`,
and the loop that pokes it is `tests/test_examples.py`.

The runtime's loop: pull `poke`, apply it to the kernel and the event,
install the kernel it returns, serve `peek` to anything that scries,
emit the effects. A program that is not a kernel is just a term applied once to the initial subject.

## 3c. Fuel policy

The compiler cannot fill in elided fuel: a term's fuel is its running
time, and convergence is only semi-decidable (the paper's §5). Elided
fuel, `<t>@[]`, therefore means *runtime policy*: iterative deepening,
doubling the budget until a value or a configured cap, with the cap
reported as the timeout outcome, never hidden. One static case exists:
a term the compiler can prove affine (no `Y`, no contraction, by the
paper's census) is strongly normalizing with a step count bounded by
its size, and the compiler may fill exact fuel for it. Everything else
is the runtime's.

## 3d. Serialization

A term at rest is Tromp's bitstring encoding, `S̃ = 00`, `K̃ = 01`,
application `1 M̃ Ñ`, extended with a third leaf code for `I` (or with
`I` expanded to `S K K`, at the cost of two atoms per occurrence; the
choice is a version decision). This is the SKI `jam`: bijective,
self-delimiting, and already in the paper's bibliography. Sharing is not
preserved by the bitstring; a runtime that needs it (snapshots of
reduced states, whose tree unfoldings are exponential) uses its own
hash-consed image format and the bitstring for interchange only.

## 4. Architecture, in the order it should be built

1. **Graph reducer.** Nodes are `S`, `K`, `I`, `App`, plus an
   indirection node for sharing after contraction. Normal-order head
   reduction with an explicit spine stack (no recursion), fuel, and a
   size cap. Hash-consing of application nodes so structurally equal
   subterms are one node; this is what makes jet lookup cheap and is
   also what the reference host approximates by identity-sharing. Output
   must reproduce every count in the paper exactly: T0 340, T1 91,556,
   T2 504,930, the T3 table, the scry tables. That is the acceptance
   test, and the reference host is the oracle for it.
2. **Encoded-term I/O.** Read and write the printed form the paper's
   appendix uses and the `figures/*.txt` files, so terms move between
   the reference host and the runtime without a third format.
3. **Jet table.** Keyed by the hash of the expanded term. First entries:
   the Scott constructors and case forms, numerals and arithmetic, lists,
   `EQ`. Each entry ships with its probe-based test against the reducer.
4. **The interpreter jet.** `whnfF`, `wfQ`, `wfN` as native code that
   reads encoded terms and produces encoded outcomes, with the same fuel
   semantics (fuel `k` permits `k` step-attempts, the last of which must
   be the no-redex check). This is the `+mock` jet and the point at which
   virtualization becomes free.
5. **Scry.** The runtime owns the resolver's external side: the fact
   store, and the resume loop when the language's core-based driver is
   not used. Blocking semantics as in the paper: re-run from scratch
   under an append-only namespace, with the fuel non-neutrality
   documented rather than hidden.
6. **A subject loader and the boot protocol** (§3b). The standard subject
   compiled once, hash-consed, quoted once for level 1, and shared across
   programs; `poke`/`peek` served by the loop.

## 5. What the runtime must not do

- Change any count the paper reports. The reference host stays the
  oracle; the runtime agrees with it or is wrong.
- Reduce under jets in ways the unjetted term would not. A jet is an
  optimization of a reduction that exists, never a semantics of its own.
- Perform quotation on behalf of a running term. The compiler quotes;
  the runtime never turns a live value into data for a program to
  inspect, because the language (§5 of the language note) promises that
  cannot happen.

## 6. Literature to read first

Most of this note is a re-implementation of work from 1979 to 1985, and
`avon/DESIGN.md` §14 says so in the form of a table. The reading list:

1. D. A. Turner, "A New Implementation Technique for Applicative
   Languages", *Software: Practice and Experience* 9(1), 1979. The SKI
   graph-reduction machine. With "Another Algorithm for Bracket
   Abstraction", *JSL* 44(2), 1979, for the compiler's back end.
2. R. J. M. Hughes, "Super-combinators: A New Implementation Method for
   Applicative Languages", *ACM Symposium on LISP and Functional
   Programming*, 1982.
3. T. Johnsson, "Efficient Compilation of Lazy Evaluation", *ACM
   SIGPLAN Symposium on Compiler Construction*, 1984. The G-machine.
   S. L. Peyton Jones, *The Implementation of Functional Programming
   Languages*, Prentice Hall, 1987, is the standard account of all of it.
4. **SKIM.** T. J. W. Clarke, P. J. S. Gladstone, C. D. MacLean and
   A. C. Norman, "SKIM — The S, K, I Reduction Machine", *LISP
   Conference*, 1980; then W. R. Stoye, T. J. W. Clarke and A. C.
   Norman, "Some Practical Methods for Rapid Combinator Reduction",
   *LFP*, 1984, and Stoye's thesis, *The Implementation of Functional
   Languages Using Custom Hardware*, Cambridge Computer Laboratory
   TR 81, 1985. This is the direct ancestor: a combinator graph reducer
   with a fixed set of recognized combinators executed natively, which
   is jetting under another name and in microcode. Read it before
   writing §4's stage 1, and read it again before claiming anything in
   this note is new.
5. K. Noshita, *IPL* 20(2), 1985, and M. S. Joy, V. J. Rayward-Smith and
   F. W. Burton, "Efficient Combinator Code", *Computer Languages* 10,
   1985, for the cost of abstraction in combinators per source symbol —
   the tradition the paper's atom counts belong to.
6. M. Naylor and C. Runciman, "The Reduceron Reconfigured", *ICFP 2010*.
   Graph reduction in hardware, modern.
7. The Urbit whitepaper (Yarvin, Monk, Dyudin, Pasco, 2016) and the Vere
   source for the jet dashboard's matching and registration discipline.
8. B. Jay and T. Given-Wilson, "A Combinatory Account of Internal
   Structure", *JSL* 76(3), 2011, §3, for what the runtime is allowed to
   do that the calculus is not — the one thing on this list that is not
   an implementation technique, and the only reason the interpreter jet
   is more than an optimization.

(Entries 1 to 6 are from memory and should be checked against the
sources before they are cited anywhere.)

## 7. Relationship to the other repository

The `artifact-metacircular-ski` repository holds the reference artifact and the numbers; the paper is deposited at doi:10.5281/zenodo.22867957.
This repository holds the language (`SURFACE-LANGUAGE-DESIGN.md`) and
the runtime (this note). The dependency runs one way: the runtime must
reproduce the artifact's counts, and the language compiles to the
artifact's ABI; nothing in the paper depends on either.

## 8. Notes: jet candidates

The point of this section is to flag supercombinator patterns that will
merit jetting, and to do it from a census rather than by eye.
`avon/bench/jets.py` keys every subterm of the compiled corpus by
structural hash (section 5's key: the subterm and nothing else), counts
tree occurrences with multiplicities propagated through sharing, and
ranks by occurrences times atoms. Run on the 17 compilable corpus
programs, 2026-09-22:

```
occurrences atoms progs  name       structure
      2,809    39     7  App        S (K (S (K K))) (S (K (S (K K))) (S (K (S (K K))) (S (K 
      2,809    34     7  -          S (K (S (K K))) (S (K (S (K K))) (S (K (S (K (S (K K))))
     18,186     5    17  -          S (K (S (K K)))
      2,809    29     7  -          S (K (S (K K))) (S (K (S (K (S (K K))))) (S (S (K S) (S 
         73  1052     3  -          S (K (S (K K))) (S (K (S (K K))) (S (K (S (K K))) (S (K 
         73  1013     3  -          S (K (S (K K))) (S (K (S (K K))) (S (K (S (K K))) (S (K 
      4,272    17    17  pair       S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K)
      2,809    24     7  -          S (K (S (K (S (K K))))) (S (S (K S) (S (K K) (S (K S) (S
      4,272    15    17  -          S (S (K S) (S (K K) (S (K S) (S (K (S I)) K))))
      4,272    14    17  -          S (K S) (S (K K) (S (K S) (S (K (S I)) K)))
         73   774     3  -          S (K (S (K K))) (S (K (S (K K))) (S (K (S (K K))) (S (K 
         73   719     3  -          S (K (S (K K))) (S (K (S (K K))) (S (K (S (K K))) (S (K 
         73   680     3  -          S (K (S (K K))) (S (K (S (K K))) (S (K (S (K K))) (S (K 
      4,272    11    17  -          S (K K) (S (K S) (S (K (S I)) K))

10,296 distinct structures; among the top 40, 7 are named supercombinators.
```

Reading it: by frequency the object type's `App` constructor and the
`pair` cell dominate, together with their sub-spines (the unnamed rows
with the same counts are prefixes of those two selector chains, and are
covered the moment the parent is jetted); by size, `step`, `loop1` and
the generated 128-way selectors of `ascii-digits`. The 5-atom
`S (K (S (K K)))` at 18,186 occurrences and the 8-atom
`S (K S) (S (K (S I)) K)` at 4,851 are not supercombinators at all but
the abstraction algorithm's weakening chains -- the BCKW census's
finding seen from the other side -- which is the case for Turner's
extended set (B, C, S', B', C') at the runtime rather than a jet per
chain. Only 7 of the top 40 structures are named; jets should key on the
named ones and let the sub-spines fall out.

**The dynamic census agrees on the chains and reverses the named
ranking.** `avon census` (`avon/DESIGN.md` §6.7) counts the terms a run
calls and weighs each by the contractions a residual jet on it would
absorb. Over this corpus's 45 runs (1,730,432 contractions) and
SKIlark's 41 (928,398), 2026-09-28:

- The weakening chains lead on time as they lead on occurrences:
  `S (K (S (K K)))` = `B (B K)` would absorb 8.1% alone, and `B (B S)`,
  `S B` and `T` 5.2--5.6% each.
- Scott constructors are the named leaders: `Cons` 7.1%, `pair` 6.1%,
  `App` 4.2%, `Suc` 3.0%. One jet parametrized by field count, index and
  constructor count covers them all.
- `step` is large (2,428 atoms, 189 contractions a call) but called 589
  times, 4.2%. By size it led the static table; by time, constructors
  outrank it.

The census supports Turner's extended set at the runtime and a
parametric constructor jet over a jet per named supercombinator.

* Avon:  jet $S(S(S(SS)S(S(SSS)S)))S$ -- **as written this diverges**:
  `S (S S) S (S (S S S) S)` is a saturated `S`, and the term grows 12 →
  37 → 398 → 7,492 atoms in 5, 20 and 60 steps with no normal form, so
  there is nothing for a jet to compute. Kept pending clarification of
  what it was meant to denote.

## 9. Templates: the compiler's supercombinators, beside the terms

**The expander hands the runtime the functions that bracket abstraction
erases, and changes no term doing it.** Every rule with formals -- each
equation, recursion body, group part, lifted lambda, constructor and
prelude rule -- is also written as a template: its formals and its open
body, keyed by the §5 hash of the SKI term it compiles to
(`skijack/templates.py`; `export.py` writes `templates.tsv` and
`template_terms.tsv` beside the dictionary).

- **The SKI stays the program.** The terms, their hashes and every other
  export file are byte for byte what they were; a runtime without
  templates, or one that ignores them, runs the SKI as before.
- **A template proves itself.** Abstracting its body over its formals,
  the last first, gives its key; the runtime checks that before using
  one (`avon/docs/DESIGN.md` §6.9), and so does `templates.check`. An atom
  of a body is a reference exactly when aviary's expansion expands it.
- **It is lean-ski's template.** `(formals, open body)` is what
  `Ski/JetTable.lean`'s `jetTable` licenses as a supercombinator proof jet
  (`avon/docs/DESIGN.md` §18.1), with the same exclusions: no rule without
  formals, no open body, no η-template (`λ xs. G xs`, which instantiating
  would repeat forever).

On the 17 compilable corpus programs, 744 rules give 736 templates, the
other 8 being η-templates, and every one abstracts back to its term; the
SKIjack-0 front end gives 993, each one of spec0's rules.

**Numeral operations are named by their terms.** A program that names the
prelude's `natAdd`, `natSub`, `natMul`, `natIfEq` or `natIfLe` (`SPEC.md`
§4) gets `words.tsv` beside its templates (`templates.write_words`): each
operation's §5 hash, its name (`add`, `sub`, `mul`, `ifeq`, `ifle`) and
its term. Avon's data jets (`avon/docs/DESIGN.md` §6.10) hold numerals as
numbers and run these natively on them, after checking each term against
its hash and running it on small numerals. An operation another needs is
listed with it: `natMul` adds with `natAdd`. A program's own `natAdd` is
its code and is never listed.

## 10. Inlining: fewer calls, the same values

**An optional pass unfolds small functions where they are called.**
`skijack.compile(..., inline=True)`, or `python3 -m skijack --inline`,
runs `skijack/inline.py` between macro expansion and case lowering. A call
to a top-level function that is not recursive, takes at least one
argument, and has a body of at most twelve nodes becomes that body with
the arguments in place; a case on a constructor written out takes its
branch; a case of a case pushes small alternatives into the inner
branches. `and (implies x y) r` becomes a case on `x`, and in its `True`
branch a case on `y`: two dispatches where there were two calls, two
dispatches and a boolean built and taken apart.

- **The values are the same.** Each rewrite is an equation of the lambda
  calculus. Compiled with the pass, the SKIjack-0 front end changes 134 of
  its 492 terms and still compiles its own source, the 67 edge programs
  and random ones exactly as Python does without it
  (`tests/test_inline.py`; `run0 --inline`, with and without Avon's
  templates).
- **No work is copied.** An argument replaces a parameter only if it is a
  bare name, or the parameter is used at most once and not under a
  lambda, a case's branches counting as one use. Constants are never
  unfolded. A rewrite that a local binder would capture is left out, and
  so is anything near a quotation, a scry or a namespace literal, and the
  equations of cores.
- **It is off by default.** The terms change, so a program compiled
  without it is byte for byte what it was, and every export with it.
- **It pays under templates, not as pure SKI.** A larger body is more
  S/K plumbing: the front end as pure SKI takes 369 million contractions
  inlined against 307 million, and with Avon's templates and data jets
  14.4 million against 17.4 million. The Reduceron's compiler inlines
  for the same reason (its Table 3); `avon/docs/BENCHMARK.md` has the
  measurements.
