# Avon: the native runtime, planned

> **Status (2026-09-27).** Design note written 2026-09-16. The compiler it targets is now implemented as `python/skijack`; the runtime it plans is not built, and `avon/bench/` reproduces the measurements it rests on. Where this note and the compiler differ, the compiler and its tests are authoritative. §17 and §18 (added 2026-09-27) fit Avon to the proof system in `lean-ski`: a third strategy whose runs the circuit proves, and the licence a jet needs inside a proof.

*2026-09-16. The build plan for the C runtime named in `RUNTIME-DESIGN.md`
§3a. Its constraints come from three places: the reference host
(`aviary_kernel.reduce`, which is where the paper's counts come from), the
compiler (`python/skijack`, which is what produces the terms), and the
paper's measured targets. §1 reports a measurement that changes one of
`RUNTIME-DESIGN.md`'s stated acceptance criteria, and most of what follows
is downstream of it. Nothing here is built; `avon/` is empty.*

## 0. What Avon is, and what it is not

Avon **consumes terms**. It has no lexer, no parser, no expander, no Stage A
checker, and no dictionary builder. Those are `skijack`, they stay in
Python, and they stay the oracle. The nockasm discipline puts expansion in a
library and execution in a runtime, and the line between them is the
compiled term.

Avon's whole job list:

1. reduce closed `{S,K,I}` terms fast, with fuel and a size cap;
2. read a value out of a reduced term the way the paper does, by probing
   with fresh marker atoms;
3. serialize terms and reduced states;
4. recognize known terms and run native code for them (jets), including the
   interpreter;
5. serve a scry namespace and the blocking resume loop;
6. boot a kernel: apply a term to an initial subject, then `poke`/`peek`;
7. emit the witness a zero-knowledge proof of a run needs (§17).

Items 1 to 3 are a runtime. Items 4 to 6 are what makes it *this* runtime.
Self-hosting does not change the list: when the expander is written in the
surface it is a term, and Avon runs it as one.

**Avon is SKIM-class technology rebuilt in C, and should say so first.**
A machine that reduces combinator graphs with sharing, an explicit spine
stack and a fixed set of recognized combinators executed natively is
Turner 1979 and SKIM 1980, the latter in microcode (§14).
Nothing in stages 1 to 3 below is a new idea and none of it should be
presented as one. What is not inherited is narrow and worth stating
exactly: the **interpreter jet** of §7, which accelerates a term that is
itself a reducer and is licensed by a theorem rather than by a benchmark;
the **two-strategy conformance contract** of §1, which exists because the
artifact being reproduced is a published set of counts; and the **scry
loop** of §8, which has no antecedent in that literature at all. A
systems paper that claimed the reducer as novel would be correctly
dismissed, and this note is written so that one cannot.

The input alphabet is `S`, `K`, `I`, application, and **opaque atoms** —
anything else, inert, never contracted. Opaque atoms exist because the
paper's verification discipline reads values by applying terms to fresh
markers, and Avon must be able to do that too.

## 1. The measurement that fixes the acceptance test

`RUNTIME-DESIGN.md` §4 asks for two things that cannot both hold: a graph
reducer with sharing, and "output must reproduce every count in the paper
exactly: T0 340, T1 91,556, T2 504,930."

They conflict because `aviary_kernel.reduce` is not a graph reducer. It is a
*substitution* reducer: `_try_contract` substitutes the arguments into the
combinator's body and builds fresh application nodes, and nothing is ever
mutated. Subterms are shared in *representation* (the same Python object
appears twice after `S x y z → x z (y z)`), which is what keeps the tower's
memory finite, but no reduction *work* is shared: when the first copy of a
duplicated redex is contracted, the second copy is untouched and gets
contracted again. The paper's counts are therefore term-rewriting counts.

A reducer that overwrites the redex root in place — Turner's machine, the
one §3a asks for — contracts a duplicated redex once. Both strategies,
transcribed onto a common node representation (`avon/bench/strategies.py`)
and run on the paper's three targets:

| target | paper / substitution | copy (no update) | share (update in place) | share + hash-consing |
|---|---|---|---|---|
| T0 `whnfF 3 <I K>` | 340 | **340** | 323 | 293 |
| T1 `whnfF 120 <UQ <I K>>` | 91,556 | **91,556** | 63,326 | 53,244 |
| T2 `whnfF 500 <whnfF 3 <I K>>` | 504,930 | **504,930** | 313,860 | 262,801 |

Three things this establishes.

- **Sharing changes the counts and not the values.** A differential run of
  the sharing reducer against `aviary` on 2,986 random `{S,K,I}` terms
  reduced to full normal form gave 0 mismatches, and the sharing reducer
  never took more steps than `aviary` on any of them. Values are safe;
  counts are not.
- **A copying reducer reproduces the paper exactly.** The copy column is
  not fitted to those numbers: it is the reference's own strategy on a
  different representation —
  keep the current position as a flat `(head, args)` pair with no parent
  pointers, contract by building the body fresh, never mutate — and it
  lands on 340, 91,556, 504,930 with no tuning.
- **Sharing-mode counts are not a function of the term.** They depend on how
  much sharing the input carried: hash-consing the *loaded* term alone moves
  T2 from 313,860 to 308,871. A count that depends on the representation
  cannot be a conformance target.

### 1.1 The contract, restated

Avon ships **two strategies in one binary**, selected per run:

- `--strategy=copy` (the *faithful* strategy): no update in place, no
  hash-consing, jets off. Reproduces the reference host's contraction counts
  exactly. This is what the conformance harness runs, and it is how Avon
  earns the right to be called an implementation of the paper's artifact.
- `--strategy=share` (the default for work): update in place. Same values,
  fewer contractions, and its counts are reported as *its own*, in a
  published table beside the reference counts, never in place of them.

A third strategy, `--strategy=witness`, exists for proofs: the circuit's
machine executed literally, with the `copy` counts and a trace the prover
consumes. §17 gives it; neither strategy above can stand in for it.

What is conformance, precisely:

| claim | conformance target? |
|---|---|
| decoded value of every corpus target | yes, always, in both strategies |
| object-level step counts (the fuel a term consumes) | yes — they are computed by the term, so every correct reducer agrees |
| host contraction counts | yes in `copy`, never in `share` |
| `SIZE` outcomes | no: the reference samples its size guard every 512 steps and measures a different quantity (see §3.3) |
| wall-clock, node counts | reported, never asserted |

This is the same honesty §5 of `RUNTIME-DESIGN.md` already asks for about
jets, applied one level down: the speed comes from somewhere, and the note
says where.

## 2. Representation

**Node.** Eight bytes, two 32-bit words, tag in the top two bits of the
first:

```c
typedef struct { uint32_t l, r; } av_node;     /* tag = l >> 30 */

#define AV_APP  0u   /* l = left index,   r = right index            */
#define AV_IND  1u   /* l = target index, r = unused   (share mode)  */
#define AV_LEAF 2u   /* l = tag only,     r = atom id (0=S, 1=K, 2=I) */
#define AV_JET  3u   /* l = jet id,       r = fallback term index    */
```

Indices, not pointers: the arena can be `realloc`'d without a fixup pass,
a snapshot is a `write(2)`, and a node is half the size it would be at 64
bits. The ceiling is 2³⁰ nodes ≈ 8.6 GB of heap, which is far past anything
these programs need.

Atom ids 0, 1, 2 are `S`, `K`, `I`, and their three leaf nodes are interned
at node indices 0, 1, 2, so both the leaf test and the arity lookup are
integer compares. Atom ids ≥ 3 are opaque atoms, with names in a side table
that the wire format carries (§4.2).

**Arena.** One flat array, bump-allocated. Measured working sets, for
sizing: T2 builds 647,236 nodes in copy mode and 320,899 in share mode —
about 5 MB and 2.5 MB. The compiled interpreter is 618 atoms, hence 1,235
nodes as a tree and 348 as a DAG; the unquoter is 43 atoms, 85 nodes as a
tree, 62 as a DAG. Nothing here is large. A 64 MB default arena with
doubling growth is generous.

**Reclamation.** Bump allocate; collect by stop-and-copy (Cheney) from the
roots — the spine stack, the current root, the subject, the fact store, the
jet dashboard's registered terms. Reasons to prefer it over the reference
counting `RUNTIME-DESIGN.md` §3a proposes first: it costs no per-node count
field (the node stays at 8 bytes), it is O(live) rather than O(garbage),
and it compacts, which matters for a structure this pointer-chasing. The
note is right that the graph is acyclic — `S f g x → f x (g x)` builds its
new children out of nodes strictly below the redex root, so update in place
cannot create a cycle — so refcounting *would* be sound; it is a fallback,
not the plan. (Hash-consing during reduction breaks that acyclicity
argument: see §2.1.)

**Sharing on load.** The loader preserves the DAG when the input format
carries it (§4.2). It changes no `copy`-mode count and lowers `share`-mode
counts, which is the point.

### 2.1 Hash-consing: measured, and off by default

`RUNTIME-DESIGN.md` §3a wants a `(left,right) → index` table so that equal
applications are one node, "which is also what makes jet lookup O(1)". Both
halves of that need revising.

Consing every node built during reduction buys 16% of T2's contractions
(313,860 → 262,801) and 18% of its nodes, at the cost of one hash probe per
allocation — 306,384 probes for T2. In C a probe is comparable in cost to
the contraction it is trying to avoid, so this is close to a wash and has to
be measured on the target, not assumed. Two further costs: the table is a
GC root set that must be rebuilt on every collection, and a cons that
returns a node which happens to be an *ancestor* of the redex makes the
graph cyclic, after which the term can no longer be printed or serialized as
a tree. No corpus run produced such a cycle — the bench script walks the
reachable graph after every run and reports back edges, and there are none
— but nothing rules one out, and a runtime that can silently produce
an unprintable state is worse than one that is 16% slower.

Decision: `--hash-cons` is a flag, default off, benchmarked in stage 1,
and never on in `copy` mode. Jet lookup does not need it (§6).

## 3. The reducer

### 3.1 Two loops, one file

Both are iterative with an explicit stack; neither recurses, so spine depth
costs heap and not C stack. Measured peak spine depth on T0–T2 is 16, which
says the initial stack can be small (64 K entries) and grow by doubling.

`share`: walk down `l` pointers pushing application nodes; at a leaf with
arity `k` and at least `k` frames, overwrite the redex root — `I x` and
`K x y` become `AV_IND` to `x`; `S f g x` becomes an `AV_APP` of two fresh
nodes — pop `k` frames, continue from the root. Indirections are followed
on every load and short-circuited when walked.

`copy`: hold the position as a head plus a flat argument vector, contract by
constructing the combinator body and re-decomposing it (`nargs + rest`,
exactly as `_try_contract` does), and never touch a parent. Descending into
an argument for full normal form pushes a frame that rebuilds on the way
out.

Full normal form is the outer loop in both: reduce the head to WHNF, then
each argument left to right, then rebuild. `whnf_only` stops at the top
position only, which is what the paper's targets use.

### 3.2 Fuel

One counter, checked **before** each contraction, matching the reference.
`FUEL` is a status, not an error. Note the distinction Avon must keep
visible in its output: *host fuel* is a property of the run, *object fuel*
is the numeral inside a level-1 term and is consumed by the term itself, so
only the first is Avon's.

A proved run has two further budgets, rows and memory cells, which count
different things from host fuel and are fixed by the caller in public
(§17.2).

### 3.3 The size cap

The reference computes a DAG node count of the whole term every 512
contractions. Avon gets a cheaper and different quantity for free — arena
occupancy, which includes garbage — so its cap fires at different moments.
Therefore: the size cap is a resource guard, never a conformance target,
and conformance runs set it out of reach (the harness uses 10⁹ today). If a
run needs the cap to mean the same thing as the reference's, it must ask for
live-node accounting after a collection, and pay for it.

### 3.4 Status

`WHNF`, `NORMAL`, `FUEL`, `SIZE`, `INTERRUPTED`. Same five the reference has,
same names, so the harness can compare them as strings.

## 4. Term I/O

### 4.1 Printed form

`aviary_kernel.terms.pretty`: left-associative juxtaposition, parentheses
only around a right-nested application. Avon must produce this byte for
byte for any term small enough to print, and parse it back. This is
`RUNTIME-DESIGN.md` §4 item 2, and it is what lets terms move between the
two runtimes without a third format.

The hazard is that printing is a *tree* walk and reduced states are DAGs
whose unfoldings are exponential — the whole reason the paper's harness
counts DAG nodes. So the printer takes a node budget and refuses past it,
loudly. Printing a reduced tower state is not a thing Avon offers; §4.2 is.

### 4.2 Bitstrings, and a sharing format

Tromp's encoding, as §3d fixes it: `S̃ = 00`, `K̃ = 01`, application
`1 M̃ Ñ`, plus a third leaf code for `I`. Two open ends in that note, which
this plan closes as decisions to take rather than leaving implicit:

- the third code for `I` versus expanding `I` to `S K K` is a **version
  decision**; take it before stage 2 ships, because it is in the wire
  format. Recommendation: the third code, `10` with applications moving to
  `11`, since expanding `I` changes atom counts and the paper's counts are
  about atoms.
- opaque atoms have no encoding at all in Tromp's scheme. Since the
  conformance harness needs to ship probe markers, the term file format is
  a small container: a header with the atom-name table, then the bitstring
  with atom ids in an extended leaf code.

The bitstring does not preserve sharing. For snapshots of reduced states
Avon writes its own image — the arena and the root — which is a `write(2)`
of a flat array, and uses the bitstring only for interchange. A snapshot is
not a proof witness: it carries indirections, jet nodes and the
collector's moves, and the circuit's memory table has none of them
(§17.1).

### 4.3 Atom hygiene, and a trap worth naming

The Python oracle reduces in an `Environment` where **53 bird names are live
combinators** — `B`, `C`, `W`, `Y`, `T`, `M`, `U` and the rest all have
arities and rules. Avon has three. A term containing an atom named `W` is
inert in Avon and contracts in Python. Today nothing collides — the markers
are `X1…Xn`, `Z`, `S_`, and the harness's `\x00`-prefixed names, none of
which is a bird — but nothing prevents it either.

So: the exporter asserts that no atom in an exported term or marker set is a
bird name, and Avon's loader rejects any atom whose name is in the bird
table unless `--allow-bird-atoms` is passed. A conformance divergence should
never be able to come from this.

## 5. Structural hash

`python/skijack/dictionary.py` already fixes it: a Merkle hash, leaf hashes
its name, application hashes `"(" + h(fn) + " " + h(arg) + ")"`, `sha256`
truncated to 16 hex digits, published with the version prefix
`skijack-1:`. Avon computes the same values, in one bottom-up pass, with a
vendored public-domain `sha256.c` (~200 lines, no dependency).

It is computed **at load time only** — once per dictionary entry and once
per candidate node in the loaded program — and never on the reduction hot
path. §6 is why that suffices.

The hash is for **dispatch, not commitment**. Sixty-four bits admit a
collision after about 2³² work, which is harmless when a wrong match only
wastes a jet check and fatal when a verifier trusts it. Nothing a proof
relies on is keyed by it: a proof binds terms by the circuit's own field
fingerprints (`lean-ski`'s `zk/`, with a proved collision bound), and a jet
inside a proof is licensed by recomputing the term it stands for (§18.1),
not by its hash.

## 6. Jets

### 6.1 What the key is

**The subterm, and nothing else.** The key is the Merkle hash of §5 over
that node's tree — leaf names and application structure — published with
the `skijack-1:` prefix. Not the name it was compiled from, not the type
declaration it came out of, not the subject it will be applied to, not its
arity.

The subject cannot be in the key and does not need to be, and the reason is
the same fact that makes bracket abstraction the whole compiler: **after
abstraction there are no variables left.** Every subterm of a compiled
program is a closed `{S,K,I}` term, so its behaviour is a function of
itself alone; there is no environment for it to mean something different
in. A subject reaches a supercombinator as an *argument*: the use site
is the application node `(sc subject)`, and the supercombinator is that
node's left child,
hashed on its own. (The corpus programs have no subject argument at all yet
— the standard subject is unbuilt — so this is a statement about what will
not change when it exists.)

This is where Avon and Vere differ, and it is worth being precise about
why. A Nock formula's meaning depends on the subject it runs against, so
Vere cannot key on code alone: it matches a *core* — a battery plus a claim
about the payload — and registers it under a parent in the dashboard.
Nothing here needs that. Putting the subject in the key would also be
actively wrong: the subject grows every time the program gains an unrelated
equation, and every jet would miss the moment it did. The battery is hashed and
the payload is not, for the same reason, one level down.

### 6.2 What a loader actually finds

Measured, on the compiled interpreter (`avon/bench/coverage.py`):

- **whnfF, 618 atoms, 348 distinct nodes: 40 of them are dictionary rows**,
  35 of those above the size floor below. The supercombinators survive intact and
  nested — `sp` is a subterm of `step`, `step` of `whnfF`, `rb` of `stepS`,
  `rb1` of `rb` — so one bottom-up hashing pass at load time finds the whole
  hierarchy, not just the top. On `wfN` (1,066 atoms, 621 nodes) 118 nodes
  match a row and 54 are above the floor, the scry ones among them.
- **A hash names a term, not a name.** In that one program `whnfF`, `loop`
  and `whnfF.loop` are one hash; so are `Just` and `suc`, and `Nothing`,
  `nil` and `zero`. In `wfN`, `SteppedN`, `RValN` and `resS` are one term.
  So the dashboard is `hash → (arity, native fn)`, several names may point
  at one row, and the names are commentary.
- **And one name is not one hash across programs.** `sp` over a
  four-constructor object type and `sp` over a five-constructor one are
  different terms with different hashes, which is exactly why
  `DESIDERATA.md` §5 wants a table per object type and why the registry
  refuses to give one name two terms. Keying on the term makes that fall
  out instead of having to be enforced.
- **Matching needs a size floor.** `K` is `Nothing`, `nil` and `zero` at
  once, and occurs five times inside `whnfF`; `I` as an *object-type
  constructor* is three atoms and occurs eight times inside `wfN`. Lift
  already has this floor (`MIN_LIFT_SIZE = 3`); jets take the same one, and
  should take a higher one, since a jet below a handful of atoms cannot pay
  for its own dispatch.
- **Quotation changes the key, as it must.** `<whnfF>` is a Scott datum: a
  different tree, a different hash, no match. A jet for a function does not
  fire on the encoding of that function, and the encoding boundary is
  exactly where it should stop.

### 6.3 Dispatch is a tag test, not a hash lookup

The obvious design — hash every node as it is built, probe a dashboard —
is what `RUNTIME-DESIGN.md` §3a describes, and it is not necessary here.
The hashes of §6.1 are computed once, bottom up, over the loaded program —
one pass over the DAG, so 348 hashes for the 618-atom interpreter, not
1,235 — and after that the structure is already marked. That means:

> The loader matches the dictionary's hashes against the loaded program
> once, wraps each match in an `AV_JET` node, and from then on jet dispatch
> is a tag test on the head node. No hashing during reduction at all.

An `AV_JET` node carries a jet id and the index of the term it stands for.
With fewer arguments than the jet's arity it behaves as that term; with
enough, native code runs. This is Turner's built-in combinator set under
another name, which is the same observation §2 of the runtime note already
makes.

A wrapped node keeps its wrapper for as long as nothing rebuilds it, and
neither strategy rebuilds a subterm it is not contracting: a supercombinator sitting
inside a larger term is passed along by reference until it reaches head
position with its arguments, which is when the jet fires. Wrappers are lost
when reduction copies the term apart — `S` distributing over a jetted
subterm produces unwrapped children. That is exactly Vere
losing a battery match, it is not a correctness problem, and it is a further
reason the surface pushes work into supercombinators pulled by projection (`DESIDERATA.md`
§3, Tier 2) rather than large open terms.

### 6.4 The mechanism is old; the licence is not

Matching a term against a table of known combinators and running native
code for it is Turner's extended combinator set and SKIM's microcode
(§14), not a new mechanism, and the parts of §6.1 to §6.3 that are about
*how* to match are engineering choices inside a forty-six-year-old
design. The theorem changes what the mechanism is *for*. Turner's
recognized combinators are an optimization of a reduction the calculus
performs anyway; the interpreter jet performs a structural recognition
that no term can perform for itself (Proposition 3.1), so it is not a
faster path to an operation the language has — it is the only place that
operation exists.

That distinction earns exactly one operational rule, and it is already in
§12: a jet may never quote on behalf of a running term. Everything else
about jets here is Turner's, plus bookkeeping.

### 6.5 Jets change counts

A jet replaces contractions with a C call, so a jetted run's contraction
count is meaningless as a comparison. Jets are therefore **off in `copy`
mode**, and a jetted run reports `(contractions, jet calls)` as two numbers.

### 6.6 Admitting a jet

A jet is a claim, and the claim is checked three ways, all of which the
artifact already does in Python:

1. **Probe tests.** Every entry ships fresh-marker probes, the same ones
   `python/skijack/probe.py` runs.
2. **Differential.** `--jet-check=N` runs the unjetted term alongside every
   *N*-th fire and compares the decoded results; `N=1` in the test build.
3. **Corpus.** The whole conformance suite runs jets on and jets off, and
   the values must agree.

A jet that cannot be validated this way is not registered.

Testing is the admission rule for `share` mode only. Inside a proof the
verifier cannot re-run the term, so a jet there needs a theorem (§18).

## 7. The interpreter jet

`whnfF`, and then `wfQ` and `wfN`. Native code that:

- reads an encoded object term — a Scott datum over `S | K | I | App t u` —
  by probing it with markers, the same way `run.decode` does, memoized by
  node index (the memo is by index, so the id-recycling trap that
  `probe.py` documents does not arise);
- reduces it natively;
- re-encodes the outcome as the declared result type's datum.

It must implement the paper's fuel semantics exactly: fuel `k` permits `k`
step-attempts, the last of which must be the no-redex check, so `s`
contractions need `s+1`. The fuel boundary cases in `EXAMPLES.md` §4 are
the test: the answer must flip at the same numeral, not one either side.

The payoff is the one Nock gets from `+mock`: the paper measures level 1 at
340 contractions per object step and level 2 at ~1,485× on top of that, and
a correct interpreter jet collapses both to roughly the cost of the object
reduction itself. That is stage 5, and it is the stage that makes a third
tower level and the partial-evaluation runs ordinary work.

## 8. Scry

The runtime owns the external side, as §4 item 5 of the runtime note says.
`python/skijack/run.py` already contains the whole protocol and Avon
transcribes it:

- a **fact store**: an append-only list of (key datum, answer datum) pairs;
- `make_resolver`: build the resolver term from `EQ5`, the answer type's
  hit and not-yet constructors, and the facts learned so far;
- the **resume loop**: run, peel the result, and if it is the blocking
  constructor, decode the blocked path, look it up, append, and **re-run
  from scratch**. Re-running is not an optimization failure; it is what
  makes blocking sound under an append-only namespace, and the paper says
  so.

Two properties to keep visible in Avon's output rather than in a comment:
the namespace is append-only (a key already known and still blocking is
`STUCK`, not a retry), and fuel is not neutral across a resume — a later
round starting from scratch consumes fuel again.

The elided-fuel policy `@[]` is §3c: iterative deepening, doubling from 8 to
a cap of 4096, the cap reported as the timeout outcome. Composed with the
resume loop exactly as `run_with_namespace` composes them.

Two rules for proved runs (§17). The policy may size a budget, off the
record, but may not choose the budget a proof uses: doubling until the run
succeeds publishes its length within a factor of two, which is what a
budget-exact trace exists to hide. And the rounds of the resume loop run
off-circuit; only the final run is proved, with the final fact store as
its committed private input, so the fact store must be exportable, in the
order its facts were learned, as that input.

## 9. Boot

`RUNTIME-DESIGN.md` §3b, unchanged: an executable is a function of the
initial subject, and the runtime starts by applying the loaded term to it.
The initial subject carries the quoted standard library, which settles who
supplies `<subject>`.

A kernel is a core whose interface Avon pulls by axis: `poke : event →
[effects, kernel']` and `peek : path → answer`. The loop applies `poke`,
installs the result, serves `peek` to anything that scries, emits the
effects. A term that is not a kernel is applied once and reduced.

Effects and events are terms. Avon does not invent a syntax for them.

## 10. The conformance harness

### 10.1 What Python must export

One new module, `python/skijack/export.py`, and a CLI flag. For each corpus
program it writes a directory:

```
avon/tests/conformance/<name>/
  atoms.txt          the atom-name table (with the bird-name assertion, §4.3)
  <term>.skit        one file per named term: container + bitstring
  manifest.json      the targets and what each must produce
```

A manifest entry is: the term file, the strategy-independent expectations
(decoded constructor and fields, rendered surface form, atom count,
structural hash), and the `copy`-strategy expectations (contraction count,
status). The paper's targets — T0, T1, T2, the T3 table, the scry tables,
the `EXAMPLES.md` §4 fuel boundaries — are entries like any other.

This is the only change to the Python side the plan requires, and it is
additive: no existing behaviour moves.

### 10.2 What the suite asserts

1. every decoded value matches, in both strategies, jets on and off;
2. every `copy`-mode contraction count matches the reference exactly;
3. `lower(lift(t)) == t` over the dictionary, computed in C, matches
   Python's answer;
4. `cue(jam(t)) == t` for every corpus term and for reduced states;
5. `print(parse(s)) == s` for every printed form Python emits;
6. the structural hash of every dictionary entry matches Python's, string
   for string, including the `skijack-1:` prefix.

### 10.3 Fuzzing

The differential in `avon/bench/strategies.py` is the template: generate
random small `{S,K,I}` terms, normalize in Avon (both strategies) and in
`aviary`, compare normal forms and — for `copy` — counts. 2,986 terms found
0 mismatches against a Python transcription; against C it should run
millions, under ASan/UBSan, in CI. Add a second fuzzer over the wire format
(`cue` on random bytes must never crash and must reject cleanly).

## 11. Stages, with acceptance criteria

Each stage ends with something testable. Rough sizes are C lines, excluding
tests.

| # | stage | contents | acceptance | ~lines |
|---|---|---|---|---|
| 0 | skeleton | `Makefile` (C11, clang, `-Wall -Wextra -Werror`, ASan/UBSan debug target), `include/avon.h`, unit-test runner | `make check` runs and passes nothing | 150 |
| 1 | heap and reducer | arena, nodes, GC, both strategies, fuel, size cap, statuses, and a reader for the printed form (terms have to get in somehow) | T0/T1/T2 in `copy` mode give 340 / 91,556 / 504,930; `share` mode gives the same values; the random-term differential against `aviary` is clean over millions of terms under ASan/UBSan; throughput ≥ 10⁷ contractions/s in `share` | 900 |
| 2 | the wire format | printer with a node budget, container + bitstring `jam`/`cue`, atom table, hygiene check, arena snapshots | round-trips 10.2 items 4 and 5 on the whole corpus; the bitstring fuzzer never crashes and always rejects cleanly | 500 |
| 3 | probing and the harness | markers, `peel`, `decode`, Scott-numeral reader, manifest runner; `export.py` on the Python side; the `witness` strategy (§17) | every corpus target's decoded value matches; the paper's T3 and scry tables reproduce; every corpus witness passes `lake exe aircheck` and proves and verifies with `lean-ski`'s `bench/plonky3`, at the `copy` contraction counts | 750 |
| 4 | hash and jets | `sha256`, Merkle hash, dashboard, `AV_JET`, loader matching, `--jet-check`, the Scott and numeral jets | hashes match Python's strings; corpus identical jets on and off | 700 |
| 5 | the interpreter jet | `whnfF`, then `wfQ`, `wfN`; boundary decode/encode; exact fuel semantics | `EXAMPLES.md` §4 boundaries flip at the same numeral; T2's cost falls to roughly T0's; values unchanged | 700 |
| 6 | scry | fact store, resolver construction, resume loop, `@[]` policy | `scry-*` corpus entries reproduce their traces, round for round, including `STUCK` | 500 |
| 7 | boot | subject loader, `poke`/`peek`, effects, snapshots | a kernel survives a `poke`, answers a `peek`, and reloads from a snapshot to the same state | 500 |

Stages 1 to 3 are the runtime proper and are worth doing on their own; a
correct, fast, conformant reducer with a harness is the thing everything
else is measured against. Stages 4 and 5 are where the viability argument
of `RUNTIME-DESIGN.md` §2 is either demonstrated or refuted. Stages 6 and 7
are the parts that make Avon a platform rather than a calculator, and they
should not start before 5 is green.

The order is deliberate about one thing in particular: **the harness comes
before the jets.** A jet is a claim about agreement, and there is nothing
to agree with until stage 3 exists.

## 12. What Avon must not do

Inherited from `RUNTIME-DESIGN.md` §5, still binding:

- change any count the paper reports — the reference host is the oracle;
- reduce under a jet in a way the unjetted term would not;
- quote on behalf of a running term. The compiler quotes. The runtime never
  turns a live value into data for a program to inspect, because the
  language promises that cannot happen, and Proposition 3.1 is why the
  promise is keepable.

Three more this plan adds:

- **never report a `share`-mode count as a contraction count of the paper's
  artifact.** The two numbers go in two columns.
- **never print a reduced state as a tree without a budget.** The unfolding
  is exponential and the runtime knows it.
- **never silently accept an atom that the Python oracle would contract**
  (§4.3).

And three that proofs add (§17, §18):

- **never emit a witness from `share` mode**, or from a run with a jet whose
  tier theorem is not proved;
- **never choose a published budget from the run it bounds**;
- **never let a structural hash stand where a proof needs a commitment.**

## 13. Corrections this plan makes to `RUNTIME-DESIGN.md`

Stated plainly so the note can be amended rather than quietly contradicted:

1. **§4 item 1.** "Output must reproduce every count in the paper exactly"
   is achievable only by a non-updating reducer. As written, alongside "hash
   consing of application nodes", it asks for two incompatible things.
   Replace with the two-strategy contract of §1.1.
2. **§3a, hash-consing.** It is not what makes jet lookup O(1) — loader-time
   wrapping is (§6.3) — it is worth ~16% of contractions at the price of a
   probe per allocation, and it can make the graph cyclic. Flag, default
   off.
3. **§3a, reclamation.** The claim that the arena is acyclic is correct for
   SKI update-in-place, so refcounting is sound; but it costs a field per
   node and does not compact, and enabling hash-consing would invalidate the
   acyclicity it relies on. Stop-and-copy first.
4. **§1, throughput.** "About 12,000 contractions per second" is low for
   this machine: T2's 504,930 contractions run in 8.3 s here, about 61,000/s.
   Worth re-measuring before it is quoted anywhere. For scale, a *Python*
   transcription of the sharing strategy runs the same job in 0.15 s — so
   about 55× of the expected speedup is strategy and representation, before
   any of it is C, and the language buys the order of magnitude after
   that. The funding drafts in `ski-in-ski/funding/` quote the Python
   reference at about 10⁴/s; reconcile the two before either goes out.

## 14. Ancestry

What this runtime is a re-implementation of, so that the claim is never
implied by silence. Titles and years are believed right; **page ranges
and exact titles are from memory and must be checked before any of this
is cited** (the same caveat `RUNTIME-DESIGN.md` §6 carries). Turner's SP&E
paper (9:31–49, 1979) and Jay and Given-Wilson (JSL 76(3):807–826, 2011,
Theorem 3.2) are now checked, in `lean-ski`'s `paper/refs.bib`;
Proposition 3.1 is proved there as `no_quote`.

| what | where it comes from |
|---|---|
| bracket abstraction as the compiler's back end | Turner, *A New Implementation Technique for Applicative Languages*, SP&E 9(1), 1979; and *Another Algorithm for Bracket Abstraction*, JSL 44(2), 1979 |
| the supercombinator as the unit of compilation | Hughes, *Super-Combinators*, LFP 1982 — the word and the lifting are his, the motivation is not: he proposed them as the alternative to compiling into a fixed combinator set, and here the fixed set is the ISA |
| compiling that to a machine | Johnsson, *Efficient Compilation of Lazy Evaluation*, 1984; Peyton Jones, *The Implementation of Functional Programming Languages*, 1987 |
| graph reduction with sharing and update in place | Turner 1979 |
| a machine that reduces combinator graphs directly, with recognized combinators run natively — **jets, in hardware, in 1980** | Clarke, Gladstone, MacLean and Norman, *SKIM — The S, K, I Reduction Machine*, LISP 1980; Stoye, Clarke and Norman, *Some Practical Methods for Rapid Combinator Reduction*, LFP 1984; Stoye, *The Implementation of Functional Languages Using Custom Hardware*, Cambridge Computer Laboratory TR 81, 1985 |
| the cost of abstraction in combinators per symbol | Noshita, IPL 20(2), 1985; Joy, Rayward-Smith and Burton, *Efficient Combinator Code*, Computer Languages 10, 1985 |
| graph reduction in hardware, modern | Naylor and Runciman, *The Reduceron Reconfigured*, ICFP 2010 |
| the jet dashboard's matching and registration discipline | Vere, and the Urbit whitepaper |
| what the runtime may do that the calculus may not | Jay and Given-Wilson, JSL 76(3), 2011, §3 |

The one question that separates this runtime from SKIM is not a
technique but a location: SKIM's answer to *where does the interpreter
live* is microcode, and this project's answer is that the interpreter is
a term. Avon exists to make that answer affordable, not to make it true.

## 15. Decisions still to take

- `I` as a third bitstring leaf code versus expansion to `S K K` (§4.2).
  Recommended: the third code. Needed before stage 2 ships.
- Whether `copy` or `share` is the default strategy for a bare `avon run`.
  Recommended: `share`, with the strategy printed on every report.
- Jet id stability across dictionary versions, and whether a jetted snapshot
  records the dashboard version it was taken under. Recommended: it does,
  and a mismatch refuses to load.
- Whether Avon ever serves `peek` to a *level-0* program. The language says
  scry works only under virtualization (`DESIDERATA.md` item 6); the boot
  loop must not quietly widen that. Settle it before stage 7: a `peek`
  answered for a level-0 program is a private input the public statement
  does not name.
- Atoms in the circuit. Decided and done in `lean-ski` (§17.3): the
  machine has an inert `atom` cell and the AIR a halting kind for it. What
  remains is carrying atoms through the Plonky3 tables and the checker.

## 16. Provenance of the numbers in this note

Every count in §1, §2 and §13 was measured on this machine against
`aviary-kernel` 0.1.0 and `tower_harness.py` from `artifact-metacircular-ski`. The script is
`avon/bench/strategies.py`, and it reproduces the whole of §1 in about a
second: the four strategies on the three targets, their node, probe, spine
depth and result sizes, the cycle check, and the 2,986-term differential.
Run it before trusting any number here, and again from C when stage 1
lands.

§6.2's coverage figures come from `avon/bench/coverage.py`, which compiles
a corpus program, builds its dictionary, and reports which rows occur inside
which — the same pass the C loader will make, so the two should agree once
stage 4 lands.

Two details that bite: T2 is `--kk 500` — the harness's default object fuel
of 120 is below what the inner term needs, and produces a different, smaller
run — and node counts include the leaves built at load, so they are node
counts and not atom counts.

## 17. Proofs: the witness strategy

*Added 2026-09-27.* The proof system is in `lean-ski`. Its circuit
(`Ski/Air.lean`, built in Plonky3 in `bench/plonky3`) proves runs of one
machine, the write-once heap machine of `Ski/Heap.lean`:

- a row is the machine's registers: head pointer, stack pointer and
  allocation counter;
- the heap is one committed memory table of cells `S | K | I | A f x | N |
  C x r`, addressed in allocation order, each written once at the counter,
  with the argument stack in the heap as `C` cells;
- the rule table is `Air.stepG`: an unwind pushes one stack cell, `I` and
  `K` pop their arguments, `S` writes three cells.

Lean decides the constraints on a concrete table (`Air.checkA_iff`, run as
`lake exe aircheck`) and proves that an accepted table ends on the value
the reference reducer reaches (`Air.air_sound`).

Neither strategy of §1.1 produces that trace. `copy` has the circuit's
contraction counts, but holds arguments in a C vector and writes no stack
cells. `share` updates in place, and the circuit proves no update in place.
So Avon adds a third:

- `--strategy=witness`: `Air.stepG` executed literally over an append-only
  arena in the circuit's cell encoding. No collection, no hash-consing, and
  jets only as §18 allows. It emits the rows and the memory table, padded
  to public budgets (§17.2). Its contraction counts equal `copy`'s, and its
  values equal both. The Rust `step` and `traces` in `lean-ski`'s
  `bench/plonky3/src/main.rs` are its reference.

`share` stays the way to find an answer fast. The proof comes from a
witness-mode replay, which must reach the same decoded value.

### 17.1 What a witness is

- The rows and the memory table, in the format `Ski/AirCheck.lean` reads,
  or directly as the prover's traces.
- Nothing from the arena. A §4.2 snapshot carries indirections, jet nodes
  and the collector's moves; the memory table has none of them.
- Weak head normal form only. The circuit proves reduction to WHNF, as
  `run.py` runs it (`whnf_only`), so a `NORMAL` run has no witness.

### 17.2 Budgets are public

A proved run reports three quantities, apart:

- **host fuel**, in contractions (§3.2);
- **rows**, one per transition, contractions and unwinds together: about
  2.44 per contraction on the corpus (`lean-ski`'s `lake exe aircost`);
- **memory cells**: the loaded heap, plus one cell per unwind and three
  per `S`.

The circuit accepts a table of `k` rows exactly when `k` exceeds the run's
transitions (`Air.air_budgets`), and the memory table pads to any larger
size (`Air.Accepts.pad`). So the caller fixes both, as powers of two, before
the run, and publishes them with the statement. §8's rule applies: the
elided-fuel policy may size a budget off the record, but may not choose the
one a proof uses.

### 17.3 What a witness does not yet give

- **An output, except by probing.** The constraints fix the run, not the
  value it ends on. Probe decoding (§1, §7) binds it: `v X₁ … Xₙ` reaching
  `Xᵢ` at the head names the constructor, and the stack holds its fields.
  `lean-ski` has the inert atom cell this needs, with a halting kind for an
  atom at the head. A table started from a term applied to atom markers,
  whose last row has the atom `i` at the head, proves that the term
  reduces to `Xᵢ` applied to arguments (`Air.air_probe`). The Plonky3
  tables carry atoms (tag 6), and an AIR may require its last row to read
  a named accepting atom.
- **Secrecy, except for statements.** The corpus proofs load the whole
  term in the clear under a non-hiding commitment. A statement `V x w`
  keeps `w` private: `lean-ski` proves a Sudoku solution in zero
  knowledge (`Ski/Sudoku.lean`, `bench/plonky3/src/sudoku.rs`), with a
  hiding PCS, the witness as a private table of Scott Booleans, fixed
  heights, the last row checked for the accepting atom, and blinding for
  the per-table lookup sums Plonky3 publishes, which otherwise let a
  verifier check a guessed witness. The verifier checks the statement file
  in Lean first. Other witness shapes need their own witness tables and
  blinding. The zero-knowledge argument is informal.
- **Scry.** Only a resume loop's final run is proved, with the final fact
  store as a committed private input (§8).

## 18. Jets in a proof

§6 licenses a jet by testing: probes, differential runs and the corpus.
Inside a proof the verifier cannot re-run the term, so a jet there is a
precompile, licensed by a theorem. There are three tiers, in the order to
build them.

### 18.1 Supercombinator jets: one theorem for all of them

Every lifted λ-chain compiles to a closed combinator, `absN (caps ++ ps)
body`, applied to its captured variables (`wrapLift`, in skijack's `comp`
and `lean-ski`'s `Ski/Compile.lean`). Applied to all its arguments, it
reduces to the body with the arguments substituted. `lean-ski` proves that
once, for every body: `absN_beta_close` is weak β for all formals at once.
The reduction it replaces costs up to `3^k · vsize body` weak contractions
for `k` formals (`absN_beta_count`). A supercombinator jet replaces all of
it with one instantiation of the body. That is the Reduceron's template
instantiation, and its licence is one theorem, not one per jet.

**In the circuit** a supercombinator jet is a row kind `INST(g)`:

- the head cell is a jet cell `J g`, which the loader places;
- the row reads `arity(g)` stack cells;
- it writes the body's cells at `ctr, ctr + 1, …`, each argument variable
  replaced by the pointer its stack cell holds;
- it sets the head to the body's root and the stack to the rest.

The body's cells are fixed per supercombinator, so they form a preprocessed
**template table**, one row per body cell, which the verifier builds from
the public program. A witness **instantiation table**, one row per written
cell, looks each cell up in the template and writes it to memory. The
`INST` row joins the two by a bus message `(g, ctr, arguments)`. Arities
above the row's width chain across rows.

**Soundness, proved in `lean-ski`** (`Ski/Inst.lean`). The instantiation
step pops the arguments' pointers and writes the body with them
(`Mach.instStep`). When the head reads back as `absN xs body` and the
body's variables are among `xs`, the state after reads back as a weak
reduct of the state before (`Mach.inst_sound`, from `absN_beta_close` and
`WSteps.appT`, lifted through `decode`). A run mixing machine transitions
with such steps, halting on a weak head normal form, proves normal-order
evaluation up to weak reduction of the value (`Mach.jet_run_eval`, by
`eval_of_wsteps`). Weak reduction from a WHNF keeps its head and arity
(`small_lemma_whnf`, and `small_lemma` for a variable-headed spine), so a
jetted run reads back the head and arity an unjetted one does
(`jet_run_shape`). Carrying that to atom probes needs instantiation over
open terms, which comes with the circuit's `INST` rows. The contraction count changes; the value does not.
Budgets count rows, `INST` rows included. The circuit's `INST` rows and
template table are planned in `lean-ski`'s `bench/plonky3/DESIGN.md` §2,
not yet built. That plan replaces the `J g` cell with a public roots table:
the addresses in the loaded heap where the compiled `absN` sits. This
matches `Mach.JStep.inst`'s hypothesis as it stands, with no new cell and
no change to `decode`. It keeps the static identity check below, done in
Lean over the loaded heap.

**Identity is static.** The verifier checks every jet root in the public
program: `termAt` there must read `absN (caps ++ ps) body` for the
template the roots table names, which Lean recomputes from the template.
No hash is trusted. The structural hash of §5 finds candidates at load
time; the recomputation licenses them. `S` copies pointers, not cells, so
a copy of a root is the root and stays jettable. (The superseded `J g`
design needed a wrapper cell that a copy could lose.)

**It cannot quote.** An instantiation moves argument pointers and never
inspects what they point to. So the one rule the theorem does not give
(§12: a jet never quotes for a running term) holds by construction.

### 18.2 Data jets: native values at the boundary

Arithmetic on Scott numerals is unary, so a jet for it pays only over
native values. That needs a word cell `W n`: an inert leaf with a
field-element payload, whose meaning is a term, `⟦W n⟧` being the numeral
`n`. Each jet then gets a table that proves its function on words (`ADD`,
with range checks, and so on), joined to the CPU by a bus.

The licence is per jet: a Lean theorem that the jet's term, applied to
`⟦a⟧ …`, weakly reduces to `⟦f(a …)⟧`. That is `lean-ski`'s word-level
composition theorem for that word (`composition`, with the three-valued
contract proved for the kit's eliminator and owed per table). It is the
paper's jet contract, and the word type is the representation ABI at the
VM boundary.

### 18.3 The interpreter jet

§7's jet collapses a tower level. As a precompile its licence is the
tower's adequacy theorem: the self-interpreter, on an encoded term,
computes the encoding of the term's value. It reads encoded data, which is
allowed. It is the last tier and has the largest payoff.

### 18.4 What changes elsewhere

- §6.5: a jetted witness reports jet calls beside contractions, and has
  fewer rows, not the same count.
- §6.6: testing stays the admission rule for `share` mode. In `witness`
  mode a jet is admitted only when its tier's theorem is proved: 18.1
  once, 18.2 per jet, 18.3 once.
- §11: stage 4 should build the supercombinator jets first. They need no
  per-jet proof, and they already cover the Scott constructors, which
  compile to `absN` like any lifted chain (`ctorO`). Numeral arithmetic is
  recursive, not one template, and waits for 18.2's word cells.

## 19. Lessons from Nockchain's persistent memory arena

*Added 2026-09-27, from `nockchain-official` master at `6ccb9e85`:
`docs/pma/DESIGN.md`, `crates/nockvm/rust/nockvm/src/pma.rs` and the
`docs/pma/` incident notes. What is read in that code is marked as such;
the rest is inference.*

**What it is (read).** The PMA is a file mapped `MAP_SHARED`, which the
runtime reaches by offset from a base, with a 64-byte trailer at the end
holding the allocation offset. Allocation only bumps. After each event
the new state is copied forward into the arena; nodes already there are
terminals the copier never descends into, and old pages are never
rewritten. Reclamation is a periodic Cheney copy into a second slab. They
built a b-tree heap with mark-and-sweep and dropped it, at about 35 s
against about 5 s. There is no hash-consing; the mug is cached in the
metadata word. A snapshot is a copy of the slab, hashed over its used
prefix.

**It confirms §2.** Bump allocation, indices rather than pointers, a
stop-and-copy collector and snapshots of the used prefix are where
Nockchain arrived after trying the alternatives. Four details to adopt:

- keep arena metadata outside index space, as their trailer does;
- hash only the used prefix of an image;
- write the root and a checksum last, in a sidecar, after the data is
  synced, and reject an image whose root lies at or beyond its allocation
  offset;
- verify an image before trusting it. Their design calls raw slabs from
  third parties unsafe to load (read), and Avon's loader should refuse
  one that fails its checksum.

**Durability order, for §8 and §9 (read, then adopted).** Nockchain appends
the event to its log first, then advances the heap, then writes the
trailer, syncs, and writes the sidecar last. Recovery loads the latest
verified image and replays the log from it. Avon's kernel loop should keep
the same order, and the scry fact store should be an append-only log in
that order. That log is also the committed private input §17.3 needs, in
the order its facts were learned.

**Jets, for §6 (inferred).** Nockchain's cold, warm and hot jet state and
its ancestry checks exist because a Nock formula's meaning depends on its
subject. §6.1's closed-term argument removes that need, so Avon should not
import the machinery. Keep the dashboard derived, rebuilt at load time,
and never persisted: Nockchain's persisted cold state held process-local
pointers, and a PMA boot now rebuilds it empty (read, `form.rs`). Avoid
rebuilding the whole table on each registration, and avoid an equality
test that mutates during lookup; both are in their code.

**Witness mode, for §17 (inferred).** Nockchain's write-back is
append-only, but four of its writes would break the circuit's write-once
memory, and the witness strategy must forbid each:

- forwarding pointers written into from-space, so no collection during a
  witnessed run: size the arena first;
- unifying equality, which rewrites slots, and so no indirection rewrites
  (`AV_IND`) and no hash-consing;
- caching a hash in node metadata: keep any hash cache in a side array;
- a trailer rewritten on every allocation: in witness mode the bump
  pointer is the counter, `ctr`, and it is recorded in the rows.

Their prover takes nothing from the runtime heap (read): its memory table
lists noun nodes by content, not by address, so nothing there resembles
the allocation-ordered memory table `lean-ski`'s circuit uses. Avon's
witness mode is the first runtime path that must produce one.

**Pitfalls they hit (read), and what Avon takes from them.**

- A boot loop advanced the persisted allocation offset without a new
  event, and copying runtime caches into the arena grew one file from
  1.6 GiB to over 8 GiB. Only a committed root may advance a persisted
  offset.
- Snapshot cleanup moved the valid snapshots aside, and a collection then
  destroyed the only fallback. Never collect without a verified image to
  fall back on.
- "Alien noun" bugs: raw words were decoded against the wrong arena, and
  the fix was branded handles. Avon's `uint32_t` indices carry the same
  risk the day there are two arenas, such as a snapshot and a live heap.
  Tag indices by arena in any API that sees both.
- Checking tag and location on every dereference cost them 1.13× to 4×.
  This favours Avon's single index space, with no location bits in a
  node.
