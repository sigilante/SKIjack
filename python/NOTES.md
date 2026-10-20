# `skijack` — implementation notes

The record of what this package does, what its test suite proves, which
questions the specification left open and how each was answered, and the
places where the specification itself turned out to be wrong.  The
front page is `README.md`; the specification is the design notes one
directory up; the normative statement of the language, derived from the
decisions below, is `SPEC.md` there.

## What passes

`python3 -m pytest -q` from `python/`:

```
855 passed
```

* `tests/test_lexicon.py` — the token table is checked at import as a
  **strict bijection with no exceptions** (no two rows share a token
  kind; neither column repeats a spelling); both lexers emit the same
  token kinds and values for nine paired snippets; comments run to end
  of line; maximal munch resolves `:=*`/`:=!` before `:=`, `===` and
  `=>` before `=`, `|>`/`|-` before `|`; the fact arrow `=>`/`↦` and the
  signature arrow `->`/`→` are separate kinds in both lexicons; and axis
  picks are told apart from fuel.
* `tests/test_parser.py` — every corpus file parses in its own lexicon;
  the ASCII and Unicode spellings of each corpus file produce *equal
  trees*; application is left-associative; the two documented parsing
  decisions behave as specified, including a clear error on an
  undeclared constructor in a case branch.
* `tests/test_roundtrip.py` — for each of the 22 corpus programs `S` in
  lexicon `L`: `parse_L(render_L(parse_L(S))) == parse_L(S)`;
  `parse_M(render_M(parse_L(S))) == parse_L(S)` for the other lexicon
  `M`; `render_L` is idempotent on text; and a there-and-back trip
  through the other lexicon returns the same tree.
* `tests/test_expand.py` — the exact terms and atom counts of
  `EXAMPLES.md` sections 1–3 (below), plus the behaviour of each pass
  and the errors it raises.
* `tests/test_probe.py` — every "check run" of `EXAMPLES.md` sections
  1–3, read behaviorally, plus two regression tests for the
  Scott-numeral reader's memo table (see "A bug this step found").
* `tests/test_generate.py` — shape discovery (the object type, the
  outcome and result types), what each core is filled with, that a
  user-written `sp` / `step` / `loop` is never replaced, and that
  everything generated is surface syntax that renders and re-parses.
* `tests/test_interpreter.py` — the step-3 milestone: every definition
  of the compiled `whnfF` against the artifact's, T0's 340 contractions
  and its decoded value, and the T3 pair's sizes, table and faithfulness.
* `tests/test_quote.py` — the Scott encoding against the artifact's own
  `encP` and `enc5`, nested quotation against its tower datum, the
  level-1 symbol table, and level-1 packaging.
* `tests/test_level1.py` — the step-4 milestones below, including the
  paper's T2, which is marked `slow` and runs once
  (`pytest -m "not slow"` skips it; the whole suite takes ~14 s with it).
* `tests/test_scry.py` — the step-5a milestones: `wfQ`, `wfN` and `EQ5`
  compiled from surface source against the paper's, the whole scry
  table, the blocking driver, prefix discrimination, and
  `EXAMPLES.md` §5 run.
* `tests/test_check.py` — one rejected program per Stage A check, with
  the error class and message asserted; the whole compilable corpus
  clean; and that checking never changes a term.
* `tests/test_dictionary.py` — the hash, the table, `lower ∘ lift = id`
  on every corpus term, and lift recovering the interpreter's own names.
* `tests/test_cli.py` — the package API and every CLI flag.
* `tests/test_types.py` — Stage B: every compilable corpus program is
  well typed and compiles to the same terms with the check on or off;
  the refusals of `SPEC.md` §9b, each with its message; the blocked
  payload's old spelling refused.
* `tests/test_examples.py` — the three worked examples of `EXAMPLES.md`
  §8–§10: words to numbers two ways, full ASCII as a type with a digit
  parser, and an event type with a kernel the runtime pokes; sizes and
  read-back values pinned.

### The measured values, reproduced

Compiled from both spellings of the corpus; every one is atom-identical
to `EXAMPLES.md`.

| name | atoms | term |
|---|---|---|
| `Zero` | 1 | `K` |
| `Suc` | 8 | `S (K K) (S (K (S I)) K)` |
| `inc` | 8 | `S (K K) (S (K (S I)) K)` — identical to `Suc` (the abstraction algorithm η-reduces `λn. Suc n`) |
| `dec` | 7 | `S (S I (K K)) (K I)` |
| `add` | 42 | `Y`-tied; the first fourteen atoms are `Y` |
| `sub` | 43 | `Y`-tied |
| `C` | 10 | `S (S (K S) (S (K K) S)) (K K)` |
| `flipK1` | 11 | `S (S (K S) (S (K K) S)) (K K) K` |
| `flipK2` | 5 | `S (K (S K)) K` |
| `pair` | 17 | `S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K)` |
| `hd` | 4 | `S I (K K)` |
| `tl` | 5 | `S I (K (K I))` |
| `flipA` | 29 | `S (S (K (S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K))) (S I (K (K I)))) (S I (K K))` |

Probes (fresh marker atoms, never combinator syntax): `inc 2 = 3`,
`dec 3 = 2`, `dec 0 = 0`, `add 2 3 = 5`, `add 0 4 = 4`, `sub 5 2 = 3`,
`sub 2 5 = 0`; `C K X1 X2 → X2`; `flipK1 X1 X2 → X2`;
`flipK2 X1 X2 → X2`; `flipA [X1 X2] K → X2`. Contraction counts also
match `EXAMPLES.md`: `dec 3` reaches WHNF in 15 host contractions and
`flipA [K I] K` reduces to `I` in 40.

### The interpreter, compiled from surface source

`skijack/corpus/interp-whnff.*.ski` is the whole of the paper's base
interpreter:

```
term === S | K | I | App term term
maybe === Nothing | Just term

whnfF := {
  step m = sp m nil stepS stepK stepI
}
```

`generate.py` supplies the rest from the two declarations: the walker
`sp`, the rebuilder `rb`, their helpers, the default `stepS` / `stepK` /
`stepI`, and the core's fuel loop. Every definition it produces is
**byte-identical** to the artifact's, checked one by one in
`test_interpreter.py::test_every_definition_matches_the_artifact`:

| this package | the artifact | atoms |
|---|---|---|
| `whnfF` (the core's loop) | `whnfF` | **618** |
| `whnfF.loop1` | `wf1` | 588 |
| `whnfF.step` | `step` | **569** (`SURFACE-LANGUAGE-DESIGN.md` §9) |
| `sp` / `spApp` / `resS` / `resK` / `resI` | same names | 126 / 48 / 15 / 13 / 11 |
| `rb` / `rb1` | same names | 74 / 44 |
| `stepS`…`stepS3`, `stepK`…`stepK2`, `stepI`, `stepI1` | same names | 237 / 105 / 92 … |
| `S` `K` `I` `App` | `encS` `encK` `encI` `encA` | 7 / 5 / 3 / 32 |
| `Nothing` `Just` `nil` `cons` | `nothing` `just` `nil` `cons` | 1 / 8 / 1 / 22 |

**T0.** `whnfF 3 <I K>` reaches weak head normal form in exactly **340**
host contractions, and decodes behaviorally to `Just <K>`: the outcome
selects the `Just` marker and its payload, applied to four markers,
selects the `K` one.

A second corpus file writes the loop out instead
(`interp-whnff-written-loop.*.ski`) and compiles to the same 618-atom
term, which is what "a written loop overrides the generated one" has to
mean.  A third, `interp-whnff-written.*.ski`, is **the interpreter with
nothing generated**: exactly what `render(generate(parse(…)))` prints,
kept as ordinary user source.  Compiled with generation *off* it gives
the same 618-atom term and the same 340-contraction T0 — which is the
claim that `generate.py` emits surface syntax and adds no semantics of
its own, made checkable.

**T3.** `interp-t3.*.ski` declares the five-constructor alphabet, the
three-way outcome and the three-way result, and two cores differing in
one equation:

```
wf5Abs := { stepErr acc = Errd }
wf5Omg := { stepErr acc = omega }
```

`wf5Abs` compiles to **768** atoms and `wf5Omg` to **771**, both
byte-identical to the artifact's, as are their `step`, `loop1`, `stepErr`
and the shared `sp` / `rb` / `stepS` / `stepK` / `stepI`. With fuel 20
and a host cap of 400,000 contractions the table is the paper's:

| object term | `wf5Abs` | `wf5Omg` |
|---|---|---|
| `Err` | ERR (127 contractions) | host diverges (hits the cap) |
| `Err K` | ERR (222) | host diverges |
| `K I Err` | VAL (574) | VAL (574) |
| `I K` | VAL (438) | VAL (438) |
| `Omega` | TIME (10,130) | TIME (10,130) |

The two agree exactly — answer *and* contraction count — wherever the
`Err` equation never fires, which is the faithfulness claim; they differ
only where it does, and there the absorbing one reports a crash the other
hides as host divergence.

### Quotation and the level-1 run

`<t>` is compile-time quotation and emits a datum; `I |- <t>@n` packages
`interp fuel <program>`, the level-1 executable of
`SURFACE-LANGUAGE-DESIGN.md` §6.  `skijack/corpus/level1-flipa.*.ski` and
`skijack/corpus/tower.*.ski` carry the sources; every number below is
measured on this expander and matches the artifact's.

| declaration | contractions | peels to | decodes to |
|---|---|---|---|
| `wf5Abs \|- <K I Err>@5` | 574 | `RVal` | `I` |
| `wf5Abs \|- <K I Err>@1` | — | `RTime` | — |
| `whnfF \|- <flipA [K I] K>@41` | **29,191** | `Just` | `I` |
| `whnfF \|- <flipA [K I] K>@40` | 29,072 | `Nothing` | — |
| `whnfF \|- <I K>@3` (T0) | **340** | `Just` | `K` |
| `whnfF \|- <UQ <I K>>@120` (T1) | **91,556** | `Just` | `K` |
| `whnfF \|- <whnfF three <I K>>@500` (T2) | **504,930** | `Just` | the level-1 view of `just <K>` |

Data, against the artifact's encoders: `<I K>` is byte-identical to
`encP(I K)`, `<K I Err>` to `enc5P(K I Err)`, and `<UQ <I K>>` to
`encP(A(UP, encP(I K)))` — nested quotation is exactly the artifact's
tower datum.  `<flipA [K I] K>` is **1,809 atoms** for a 49-atom program,
as `EXAMPLES.md` §3 records, and the surface `UQ` compiles to the
artifact's **43-atom** unquoter.

T2's payload is the quotation of the *level-0* answer `just <K>`.  It is
read by unquoting it with the surface `UQ` (178 contractions) and then
probing: the level-0 Maybe selects its `Just` marker in 446, and that
payload selects its `K` marker in 4,807.  Nothing is decoded by reading
syntax, and `pretty` is never called on a tower-scale graph — the tree
unfolding of a shared graph that size is enormous.

**Fuel.** `EXAMPLES.md` §3 fixes the semantics: "fuel `k` permits `k`
step-attempts of which the last must be the no-redex check". Measured:
`K I Err` needs 2 (one contraction plus the check), `flipA [K I] K`
needs 41. Elided fuel `<t>@[]` is the runtime's policy
(`RUNTIME-DESIGN.md` §3c): `run.run_policy` deepens iteratively from 8,
doubling — budgets 8, 16, 32, 64 for the `flipA` program, succeeding at
64 with the same 29,191 contractions the explicit `@41` takes — and
reports the cap as the timeout outcome rather than hiding it.

### Scry: resolvers, typed paths, and blocking

`skijack/corpus/scry-*.ski` carry the sources. A core may take
parameters, which is how a resolver enters:

```
term5 === S | K | I | App term5 term5 | Scry
maybe === Nothing | Just term5
outcome === Stepped term5 | Done | Errd
result === RVal term5 | RErr | RTime

scHit rest v = Stepped (rb v rest)

wfQ e := {
  stepScry1 p rest = e p Errd (scHit rest)
  stepScry args    = args Done (stepScry1 e)
}
```

Three interpreters compile from surface source, each **byte-identical**
to the paper's, definition by definition:

| from surface | the paper's | atoms |
|---|---|---|
| `wfQ` | `wfQ` (`scry_harness.py`) | **950** |
| `wfN` | `wfN` (`scry_namespace.py`) | **1,066** |
| `EQ5` | `EQ5` (`scry_paths.py`) | **240** |

and so do their parts: `stepQE` 822, `stepNE` 896, `spQ` 166, `rbQ` 81,
`scHit` 104, `stepScQ` 138, `stepScN` 179, the three test resolvers
(`oracleAlways` 8, `oracleNever` 2, `oracleIfKk` 15, `oracleIfK` 198),
and every constructor of the five declared types.

**The scry table** (`scry_harness.py`'s whole `main`), each row a
level-1 declaration, read by probe:

| declaration | result | value |
|---|---|---|
| `wfQ oracleAlways \|- <I K>@3` | `RVal` | `K` |
| `wfQ oracleNever \|- <I K>@3` | `RVal` | `K` (never consulted) |
| `wfQ oracleAlways \|- <I (Scry K)>@10` | `RVal` | `K` |
| `wfQ oracleNever \|- <I (Scry K)>@10` | `RErr` | a miss |
| `wfQ oracleNever \|- <Scry K>@10` | `RErr` | |
| `wfQ oracleAlways \|- <Scry K>@10` | `RVal` | `K` |
| `wfQ oracleAlways \|- <Scry>@10` | `RVal` | `Scry` — stuck, not a miss |
| `wfQ oracleNever \|- <K K (Scry K)>@10` | `RVal` | `K` — laziness |
| `wfQ oracleIfK \|- <Scry K>@10` | `RVal` | `I` |
| `wfQ oracleIfK \|- <Scry (S K K)>@10` | `RErr` | head is `S` |
| `wfQ oracleAlways \|- <S I I (S I I)>@5` | `RTime` | |

Miss, stuck and timeout come out as three different constructors, which
is the whole reason the outcome type grew.

**Blocking.** `wfN` answers three ways, so its outcome and result each
grow a fourth constructor carrying the path that blocked —
`PendingN term5` maps to `RBlockN term5`, the constructor at the same
position handed the same payload. `run.run_with_namespace` is
`scry_namespace.py`'s resume loop: an append-only namespace, the program
re-run from scratch each round, the blocked path decoded by probe and
used as the key.

| program | facts | trace | value |
|---|---|---|---|
| `<I K>` | — | `RValN` | `K` |
| `<I (Scry K)>` | `K ↦ I` | `BLOCK on K`, `RValN` | `I` |
| `<Scry S>` | `S ↦ Scry K`, `K ↦ I` | `BLOCK on S`, `BLOCK on K`, `RValN` | `I` |
| `<I (Scry K)>` | — | `BLOCK on K`, `STUCK` | |
| `<S I I (S I I)>` @5 | — | `RTimeN` | |
| `<Scry (S K)>` | `S K ↦ I` | `BLOCK on S K`, `RValN` | `I` |
| `<Scry (S K K)>` | `S K ↦ I`, `S K K ↦ K` | | `K` — not the prefix's `I` |
| `<Scry (S K)>` | `K S ↦ I` | `BLOCK on S K`, `STUCK` | no false hit |

**Typed paths and the namespace literal.** `path === Nil | Cons seg path`
with `seg === Nat | Two | Three`; `/nat/three` denotes
`Cons Nat (Cons Three Nil)`. Inside `< >` the path's constructors are
level-0 names, so they are inlined and quoted, and `?^` wraps the result
in the object type's `Scry` leaf: `<?^/nat/three>` is **2,485 atoms**.
`ns{/nat/two => <I>, /nat/three => <K>}` compiles to
`scry_paths.py`'s `make_path_oracle` shape — a flat `EQ5` chain,
**5,375 atoms** — and `EXAMPLES.md` §5's
`answer := wfN resolve |- <?^/nat/three>@10` peels to `RValN` and
decodes to **`K`** in 28,661 contractions; `/nat/two` decodes to `I` in
14,502.

### Stage A, and the dictionary

**The checker** (`skijack/check.py`) is a pass that rejects and never
rewrites, so `expand_program`'s output is the same whether it runs or
not — `DESIDERATA.md` item 11, asserted on the whole corpus. It collects
*every* problem and reports them together; the exception it raises is the
first problem's class, so a caller can catch one check and still read the
list. The Stage A items and their classes:

| item | check | class |
|---|---|---|
| (a) | constructor arity where an application denotes data | `ArityError` |
| (b) | case completeness, repetition, mixed types, order | `CaseError` |
| (c) | data versus function at §5's positions | `DataError` |
| (d) | the §6c interpreter interface | `InterfaceError` |
| (e) | §6b's two symbol tables: a name inside a quotation that names neither | `SymbolTableError` |
| (f) | unresolved names, duplicate declarations | `ScopeError` |

Every compilable corpus file is clean. The four parse-only files —
`misc-forms`, `sec4-interp`, `sec5-lookup`, `syntax3-resolver` — are
rejected with named problems, which is the point: they carry forms the
notes describe and this package does not compile (qualified names,
segment payloads, an undeclared interpreter), and the checker says so
instead of the expander failing later.

**The dictionary** (`skijack/dictionary.py`) is Tier 1's table as a
versioned artifact (`DESIDERATA.md` §5): for each name, its expansion,
its tree-atom count and a structural hash. The hash is **Merkle over the
tree** — a leaf hashes its name, an application hashes
`"(" + hash(fn) + " " + hash(arg) + ")"`, `sha256` truncated to 16 hex
digits, prefixed `skijack-1:`. Merkle rather than a printed form because
it is computable incrementally, which is exactly how
`RUNTIME-DESIGN.md` §2's jet table is meant to match ("matches expanded
subterms against a table of known combinators by structural hash"), and
because it is over the tree rather than the DAG, so two equal terms hash
alike however they were shared. One name is one expansion: registering a
name twice with different terms is refused, so two programs over
different object types cannot merge their `sp`.

**Lift** names every subterm that is an *exact structural match* of an
entry, largest first, and leaves the rest raw (`DESIDERATA.md` item 8).
`lower(lift(t)) == t` is asserted on every term of every corpus program.
Lifting the compiled interpreter recovers its own structure:

```
$ python3 -m skijack skijack/corpus/interp-whnff.ascii.ski --lift step
S (S (S (S sp (K K)) (K stepS)) (K stepK)) (K stepI)
```

and `whnfF` lifts to `Y (S (K (S (S (K S) (S (K K) hd)))) (S (K K) loop1))`
— the paper's appendix observation that a `Y`-tied supercombinator begins with the
fourteen atoms of `Y`, made mechanical. Excluding the wrappers so that
the largest match is not `loop1` recovers `Y`, `sp`, `stepS`, `stepK`,
`stepI` inside it, and excluding a step equation in turn surfaces `rb`.

Three small rules the table needs, each tested: entries under
`MIN_LIFT_SIZE` (three atoms) are tabled but never *lifted*, because
naming every `K` is not a recognition --- and the floor is three and not
one, so `Two` at two atoms is not lifted either; `S`, `K` and `I`
are reserved for the ISA, so a program whose object type declares
constructors of those names keeps real rows for them but lift and lower
leave the names to the combinators; and when two names share a term
(`dec` and `arith.dec`) lift prefers the unqualified, shorter one.

## Decisions over the specification

1. **(a) Case branches need the type declarations, so parsing is two
   pass.** A branch is `CName binder* body` and the binder count is the
   constructor's *declared* arity, so `Suc k Suc (add m k)` can only be
   split by knowing `Suc` has one field. `parser.collect_ctors` scans
   the token stream for `===` declarations first (a type declaration
   runs to the end of its logical line, which is what bounds the field
   list), then the real parse runs with that table. An undeclared
   constructor in a branch is a `ParseError` naming it.
2. **(b) `name := { … }` is a core; `name := ns{ … }` is a namespace
   literal.** The `ns` prefix is munched by the ASCII lexer as one
   `NSOPEN` token; Unicode spells it `ns{`, and its closer `}` lexes to
   the same `RBRACE` kind as `}` (`SYNTAX.md` §2 says so explicitly), so
   one grammar serves both. Since the Unicode brackets were dropped for
   ones that render everywhere, a namespace literal closes with the
   ordinary `}` in both lexicons, `UNICODE_ALIASES` is empty, and the
   table is a bijection with no exceptions at all.
3. **Core fixpoint strategy: one fixpoint per equation, not one over a
   tuple.** A self-recursive equation `f b1 … bn = body` compiles to
   `AL(f, Y fGen)` with `D(fGen, [self, b1, …, bn], body[f := self])`,
   which is the `spGen`/`sp` and `wfGen`/`whnfF` shape of
   `tower_harness.py`. A non-recursive equation is a plain `D`. This is what
   reproduces `EXAMPLES.md`'s 42 and 43 atoms for `add` and `sub`
   exactly. The cost is that **mutual recursion between two equations is
   refused** with a named error rather than mis-compiled; a tuple
   fixpoint would handle it and is the natural next step.
4. **Every lambda is lambda-lifted into its own supercombinator.** A
   case branch with binders, and a `\x.e`, become a helper `D` over the
   enclosing binders that occur free in the body, applied to those
   binders at the use site. For `add` this yields exactly the reference
   `add1 f m k = Suc (f m k)` and `addGen f m n = n m (add1 f m)`. This
   is Tier 2 of `DESIDERATA.md` §3 taken literally: supercombinators are the unit.
5. **Cell items are atoms.** `'[' expr expr+ ']'` in the grammar sketch
   is ambiguous under juxtaposition (`[3@p 2@p]` would be one
   application), so a cell's items are parsed as atoms and an
   application inside a cell is parenthesized: `[(f x) y]`. Every cell
   in the corpus is unaffected.
6. **Newlines terminate declarations and equations.** The grammar sketch is
   silent, but a core body `{ inc n = Suc n  dec n = … }` is otherwise
   ambiguous. Newlines are significant at declaration and equation level and
   invisible inside `(`, `[`, `<`/`<`, a case brace, and a namespace
   literal; core braces do *not* hide them.
7. **The lambda rule consumes exactly one `.`.** `SYNTAX.md` §9 flags
   the collision between the qualifier dot and the lambda dot. `DOT` is
   its own token; `atom` builds a qualified name from `NAME ('.' NAME)*`
   and the lambda rule eats the dot after its binder, so `\x.a.b` is
   `Lambda("x", Name("a.b"))`.
8. **A bare number is a numeral literal.** `atom := … | NUMBER | …` in
   the sketch compiles to the Scott numeral: `5` is `suc` applied five
   times to `zero`, built from the prelude's own terms, so a program that
   redefines `suc` does not change it. The literal stays an `ast.Num`
   node until codegen, so `--render` spells it as written. An axis pick
   (`2@p`) and fuel (`<t>@10`) keep their numbers as their own token
   kinds. Stage B types a literal as a numeral type (`SPEC.md` §9b), and
   a literal inside a quotation is refused.
9. **Backend names are mangled on collision with an aviary bird.** The
   kernel refuses to shadow a built-in, so an equation named `C` is defined
   as `Cc` — the form `EXAMPLES.md`'s codegen notes record. Mangling
   never changes a compiled term; `Expansion.backend` records the map.
10. **The prelude is `pair`, `hd`, `tl`.** `[a b]` compiles to
    `pair a b`, `2@p` to `hd p`, `3@p` to `tl p`, and axis `n` to the
    chain of heads and tails Nock's numbering gives (axis `2n` is the
    head of axis `n`, axis `2n+1` its tail; axis 1 is `p` itself).
    Writing `pair`, `hd` or `tl` in a program replaces the prelude's.
11. **Constructors come from the type declaration**, as
    `λ fields. λ c₁ … cₙ. cᵢ fields`. `nat === Zero | Suc nat` therefore
    produces exactly the artifact's `zero` and `suc`.
12. **Hygiene is capture avoidance.** With one global namespace,
    resolving a macro body's free names at the definition site and at
    the use site coincide, so the operative part of the hygiene rule is
    that substituting an argument into a macro body alpha-renames any
    binder of the body that would capture a name free in the argument.
    That is what is implemented and tested; a real definition-site
    scope arrives with the standard library.
    A binder is also hygienic against aviary: the host expands every
    atom of a rule's body that names a defined combinator before it
    abstracts the formals, so a formal spelled as a program name became
    that name's definition, silently when the definition came later, and
    `c1 := K` broke `Suc`. Every formal the expander gives aviary is
    `\x00b:` plus the binder, a name no source can spell, and the
    constructors' are `\x00f…` and `\x00c…`; abstraction removes them, so
    no term changes but the miscompiled ones.

13. **The object type is identified by shape, not by name.** It is the
    unique declared type with exactly one constructor carrying two fields
    of its own type — the application constructor. Every other
    constructor of that type must be a leaf. Two such constructors, a
    non-leaf non-application constructor, or two such types are each a
    named `GenerateError`. A program with no such type generates nothing,
    which is why `nat === Zero | Suc nat` is left alone (`Suc` carries
    one field, not two).
14. **The step-outcome type `O` and the result type `R` are the
    outcome-shaped declarations, first and last.** A candidate is a
    declared type other than the object type with exactly one constructor
    carrying a single field of the object type and nothing else carrying
    fields. The first candidate in declaration order is `O`, the last is
    `R`; with one candidate `O = R`, which is `whnfF`'s Maybe shape. More
    than two is refused.
15. **The loop's mapping rule.** `loop1 f m n2 = step m …` applies
    `step m` to one continuation per `O` constructor **in declaration
    order**: `O`'s term-carrying constructor continues the loop,
    `(f n2)`; `O`'s *first* terminal is "no redex", so the loop is done
    and yields `R`'s term-carrying constructor applied to the current
    term; `O`'s further terminals map one for one onto `R`'s terminals in
    order. `loop n m = n <timeout> (loop1 loop m)` peels one `Suc` per
    attempt and yields `R`'s **last** terminal at `Zero`. Hence
    `|R| = |O|`, which the generator checks. For Maybe this is
    `step m (Just m) (f n2)` and `n Nothing …`; for the T3 shape
    `step m (f n2) (RVal m) RErr` and `n RTime …` — the artifact's `wf1`
    and `wf5Abs1` exactly.
16. **Default step equations are parameterized over `O`, not hard-wired.**
    `stepS` / `stepK` / `stepI` are generated only for leaf constructors
    literally named `S`, `K`, `I` (which is what §6c asks for), and take
    their two outcome constructors from `O`: "no redex" is `O`'s first
    terminal and a contraction is wrapped in `O`'s term-carrying
    constructor. The rebuilt `x z (y z)` is spelled with the object
    type's own application constructor and its own `rb`.
17. **A core's fuel loop is its equation named `loop`, and the core's name
    denotes it.** `generate.py` adds `loop` and `loop1` only when `loop`
    is absent, and `step` only when `step` is absent, so a written one
    always wins. `loop1` without `loop` is refused. `SYNTAX.md` §3's
    `myInterp |- …` therefore has a term to name.
18. **A core is an interpreter core** when an object type is declared and
    the core writes any part of the interface: an equation named `step`,
    `loop`, or `step<C>` for a leaf `C` of the object type.
19. **Equations are scoped to their core.** A core equation's backend
    name is `core_equation`, and a name inside a core resolves to a
    sibling equation before
    anything program-level, so two interpreter cores can each have their
    own `step` while sharing one `sp`. Results are keyed `core.name`, and
    also by the bare name when it is unambiguous program-wide.
20. **`S`, `K` and `I` always mean the ISA at level 0**, even when the
    object type declares constructors of those names. That is
    `SURFACE-LANGUAGE-DESIGN.md` §6b's two symbol tables with only the
    level-0 one implemented, and `EXAMPLES.md` §4's "outside it they
    would be the level-0 combinators". It is what lets
    `omega = S I I (S I I)` sit in the same file as
    `term5 === S | K | I | App term5 term5 | Err`.
21. **`nil` and `cons` joined the prelude.** The generated walker needs
    the Scott list, and `EXAMPLES.md` §4 writes `sp m nil …` without
    declaring a list type; `SURFACE-LANGUAGE-DESIGN.md` §4 lists Scott
    lists in the standard subject. The prelude is now `pair`, `hd`, `tl`,
    `nil`, `cons`; a program may still define its own.
22. **`omega` is written in the surface, not built in**
    (`omega = S I I (S I I)`, a zero-binder top-level equation), so the one
    authored difference between `wf5Abs` and `wf5Omg` stays visible in
    the source.
23. **A closing `}` ends the last equation of a core**, so a one-equation core fits
    on a line (`wf5Abs := { stepErr acc = Errd }`). Elsewhere the
    newline rule of decision 6 is unchanged.

24. **Quoting a non-constructor name inlines it.** Inside `< >`, a leaf
    constructor of the target object type is that constructor and
    juxtaposition is the application constructor (§6b); any other
    level-0 name — `UQ`, `whnfF`, `flipA`, `Suc` — is **inlined as its
    expanded level-0 term and then quoted**, exactly as the artifact
    writes `encP(A(UP, encP(IK)))`. §6b's shared quoted subject
    `<subject>`, with library names resolving to axes into it, is
    deferred; the cost of the decision is that a name used twice inside
    one quotation is duplicated in the datum instead of shared.
25. **Nested quotation is a datum spliced as a term.** The inner `<I K>`
    of `<UQ <I K>>` compiles to its datum, which is a closed level-0
    term, which the outer quote inlines and encodes like any other. A
    nested quotation may not carry fuel or an interpreter.
26. **The target object type is the program's.** Since a program declares
    exactly one object type (decision 13), a bare `<t>` and an
    `I |- <t>@n` both quote into it; the type is not selected per
    interpreter, because two interpreters over different alphabets
    cannot share a program yet.
27. **The default interpreter is a core named `whnfF`.** §6 makes it
    `wfN`, which needs a resolver and a standard subject; with neither
    built, a bare `<t>@n` uses a core called `whnfF` and errors clearly
    if the program has none.
28. **Quotation is packaged only at a definition's right-hand side.**
    `name := <t>` (a datum) and `name := I |- <t>@n` (an executable)
    compile; a `<t>` inside an equation body still raises, because §6 makes
    the level a property of the *declaration*.
29. **Inner fuel is a numeral over a declared `nat`.** T2's `whnfF
    three <I K>` uses `three = Suc (Suc (Suc Zero))`, as the artifact
    spells it; `three = 3` compiles to the same term (decision 8). It
    compiles to the artifact's `natP(3)` exactly. Only the
    *outer* fuel of `@n` is a numeral the token table supplies.
30. **Elided fuel has no closed term.** `<t>@[]` yields a
    `Level1Program` whose `.term` raises and whose `.placeholder` carries
    a single free `\x00fuel` atom; `.with_fuel(k)` closes it and
    `run.run_policy` drives the doubling search. Keeping it out of
    `terms` keeps every term in `terms` closed over `{S,K,I}`.
31. **A loop's timeout constructor is `R`'s last *terminal*, not its last
    constructor.** For `maybe === Nothing | Just term` that is `Nothing`,
    which is second-to-last in declaration order; `run.timeout_constructor`
    computes it, and getting this wrong is what the fuel-policy milestone
    caught (see below).
32. **`fast_reduce(max_size=None)` turns the size guard off.** The guard
    rebuilds the whole term to measure it, O(nodes) per sample; at tower
    scale that costs more than the reduction it protects, and `max_steps`
    already bounds the run.

33. **A core may take parameters**, written after its name
    (`wfQ e := { ... }`). They are prepended to every equation's binder
    list and are in scope in every equation body; the core's loop is applied to
    them before its fuel, so `wfQ E |- <t>@n` is `loop E n <t>` — the
    artifact's `wfQ e n m` order. An interpreter must be applied to all
    of them.
34. **References between a core's equations stay raw**, so the parameters are
    passed explicitly (`stepScry1 e`, `f e n2`). Auto-applying them
    would break the fixpoint: `Y` ties the loop's generator, whose first
    argument is the loop itself, and the artifact passes that self raw to
    `loop1` and re-applies the parameters inside it.
35. **An equation that does not need the parameters lives at program level.**
    `scHit` takes `rest v`, not `e rest v`, which is why it is a
    top-level equation and not a core equation — and why the compiled term matches.
36. **`O` and `R` are the *last two* outcome-shaped declarations.** §6c
    says "the first is `O`, the last is `R`", which breaks as soon as a
    program also declares an oracle answer type (`oanswer` is
    outcome-shaped too). The last two agree with §6c on every program
    that has only two, and the answer type is declared before them.
37. **Outcome-shaped now allows other constructors to carry fields.** A
    type is outcome-shaped when exactly one constructor carries a single
    field *of the object type*; the rest may be nullary or carry
    something else, which is what lets `PendingN` exist. (Since Stage B the
    payload is declared as what it holds, the encoded path, so it is
    `PendingN term5`; the carrier is the *first* single-object-field
    constructor, and the blocking constructor the second payload one.)
38. **The loop mapping, extended**: an outcome constructor carrying a
    payload maps to the result constructor at the **same position**,
    which must carry as many fields, and is handed the same payload
    (`PendingN p` → `RBlockN p`). Nullary outcome constructors still map
    in order onto the result's nullary constructors other than the
    timeout, and the timeout is still the result's last nullary one.
39. **The oracle answer type is found by shape**: the outcome-shaped
    declaration that is neither `O` nor `R`, with its payload-carrying
    constructor the hit and its **last** nullary constructor the
    "not yet".
40. **The path type is found by name and shape**: a declaration called
    `path` of exactly the shape `Nil | Cons seg path` (`SYNTAX.md` §6
    fixes both). A path literal `/nat/three` is
    `Cons Nat (Cons Three Nil)`; each segment word names the `seg`
    constructor spelled with its first letter capitalized, and an unknown
    segment is an error.
41. **`?^` compiles only inside a quotation**, to the object type's
    `Scry` leaf applied to the quotation of the path term. The path's own
    constructors are level-0 names, so they are inlined and quoted like
    any other (decision 24) — which is what makes a level-1 path an
    encoded object term that resolvers can compare with `EQ5`.
42. **A namespace literal compiles to a flat `EQ5` chain**, exactly
    `scry_paths.py`'s `make_path_oracle`:
    `\p. EQ5 p <k1> (OJust <a1>) (… ONotYet)`. It needs a program-level
    `EQ5` and an oracle answer type, and each fact's value must be a
    quotation, since a fact is data. `ns{}` is the resolver that always
    answers "not yet". Mount tables are not this step.
43. **Quotation-defined names are expanded twice.** A level-0 equation may
    name a datum that a quotation defines (`oracleIfKk acc = Just encI`
    with `encI := <I>`), so pass 6 builds every datum and its environment
    alias first, then re-expands every level-0 name. A closedness guard
    now rejects any term that still holds a non-`{S,K,I}` atom — it is
    what caught this.
44. **Parentheses hide newlines**, so a long equation body may be wrapped by
    parenthesizing it. That falls out of decision 6 and is what makes
    `eqNP`'s five-continuation body readable.

45. **Stage A collects, then raises once.** `check_program` returns
    every problem; `check` raises the *first* problem's class with a
    message listing them all and `.problems` attached, so a caller can
    catch one check and still see the whole list.
46. **Arity is checked where an application denotes data** — inside a
    quotation, a path literal and a namespace key. At level 0 a Scott
    constructor *is* a function of its fields and then of its
    continuations, so `Zero c0 c1` is an ordinary case analysis and
    neither over- nor under-application means anything; in a case branch
    the parser already fixes the binder count at the arity.
47. **§5's line refuses what it can *prove* is a function**, not
    everything it cannot prove is data. An equation, a bare combinator, a
    lambda, a macro and a partially applied constructor are known
    functions; a binder's kind is unknown until Stage B, so `EQ a b`
    passes. §5 says as much: "the honest version is a type checker".
48. **The quotation body is checked by the symbol tables, not the data
    rule.** `<flipA [K I] K>` and `<UQ <I K>>` quote *supercombinators*, which the
    naive reading of §5 rule 3 would refuse — but §6a's whole point is
    that level-1 codegen expands a declaration and then quotes it. The
    check that belongs there is §6b's: every name resolves in one of the
    two tables, and a constructor of another type is saturated.
48a. **Check (e) has nothing to say at level 0.** A declared type's
    constructors are ordinary Scott constructors there, whatever type
    they belong to: the generated rebuilder *must* apply the object
    type's `App` to build encoded terms, exactly as `Suc` and `Just` are
    applied at level 0 everywhere else. Only `S`, `K` and `I` are
    reserved, and they resolve to the ISA rather than being refused. The
    level-1 half of (e) — a name that is neither a constructor of the
    object type nor a level-0 name — is the whole of the check.
49. **A written `step` must install the leaves in declaration order.**
    The one check aimed squarely at item 11's "wrong continuation order
    is silent wrong semantics"; it fires only when every continuation is
    recognizably a `step<C>` name, and stays quiet otherwise rather than
    guessing.
50. **`step<AppCtor>` is refused by name.** The application constructor
    cannot have a step equation, so `stepApp` is a typo worth catching, and
    `is_interpreter_core` looks at every constructor rather than only the
    leaves so that it is caught.
51. **The dictionary's hash is Merkle over the tree**, `sha256`
    truncated to 16 hex digits and prefixed with the table version — see
    the section above for why, and for what the runtime does with it.
52. **One name is one expansion.** Registering a name twice with
    different terms raises `DictionaryError`: the table is per-ABI, and
    two programs over different object types do not share an `sp`.
53. **Lift has three tie-breaks**, all tested: entries under three atoms
    are tabled but not lifted; `S`, `K` and `I` are reserved for the ISA;
    and among names sharing a term, the unqualified and shorter wins.
54. **The checker knows what generation will add** without generating
    it (`generate.names_generation_adds`), so it stays a pass over the
    parsed program and still does not call `sp` undefined.

55. **The prelude is `pair`, `hd`, `tl`, `nil`, `cons`, `zero`, `suc`.**
    Decision 21 listed five; the numerals joined so that a program can
    write Scott numerals without declaring `nat`. A program may still
    define its own.
56. **The capturing macro form `:=!` parses and is refused.** Decision 12
    implements hygiene for `:=*`; the capturing form is recognized by the
    lexer and the grammar and rejected by the expander with a named
    error (`test_expand::test_capturing_macro_is_refused_clearly`). The
    paper's grammar lists it; nothing stands behind it yet.
57. **Macro expansion and the fuel policy are bounded, and the bounds are
    normative.** Expansion stops with a named error after 100 nested
    unfoldings on one path, at structural depth 256, or after 200,000
    substitutions in one declaration; the elided-fuel policy starts at 8,
    doubles, and caps at 4,096, reported as the timeout outcome.

58. **Stage B is one rule, oriented.** A datum may be applied; a function
    is never a datum. Unification is `unify(expected, given)`: a given sum
    type meeting an expected arrow expands to its Scott scheme, an expected
    sum type meeting a given arrow is the error. `Zero` compiles to `K`, so
    the orientation is what makes `Suc K` an error at all.
59. **Case forms are typed nominally; hand-applied data structurally.**
    `e |> {...}` gives the scrutinee the declared type and the binders the
    field types. A datum applied to its continuations by hand, the
    interpreters' idiom, is typed by the continuations, and recursion over
    it yields a cyclic type; unification is equirecursive. This types
    `omega` too, so no `raw` escape exists.
60. **Arrows carry provenance.** An arrow a binder acquires by being
    applied is an *elimination* arrow, datum-compatible, and remembers the
    declared type it is checked against; an arrow a value was built with is
    a function. Without this the generated `loop1`, which passes `m` to
    `step` before writing `RVal m`, was refused -- the order-dependence of
    a plain oriented unifier, found in the reference interpreter itself.
61. **The blocked payload is the object type.** `PendingN term5`, not
    `PendingN path`: a level-1 path is an encoded term. The carrier is the
    first single-object-field constructor, the blocking constructor the
    second payload one (`generate._carrier`, `run.block_constructor`).
62. **The prelude's rule binders are sentinels.** `pair` bound `x`, `y`,
    `c` by those names, so a program combinator named `x` collided with the
    binder inside the host's expansion of a cell; found by Stage B's tests.

## Discrepancies found in the specification

### Resolved in the specification

These eight were reported against the first draft of `SYNTAX.md` and are
now settled by the note itself; the code follows the note, and each line
says how.

1. **The ASCII column was not injective** — `↦` and `→` both spelled
   `->`, contradicting §1 item 4. *Resolved:* §2 now spells the fact
   arrow `=>`, leaving `->` the signature arrow alone. `MAPSTO` and
   `ARROW` are separate token kinds in both lexicons, no grammar
   position has to disambiguate them, and `check_table` is a **strict
   bijection with no shared-kind exceptions** (`SHARED_KIND_ROWS` is
   gone).
2. **The equation form `=` was missing from the table.** *Resolved:* §2
   now carries an "equation" row, same spelling in both lexicons;
   maximal munch puts `===` and `=>` ahead of `=`.
3. **Arms at top level were not in the grammar**, though `EXAMPLES.md`
   §2 and §3 use them. *Resolved:* §4's `decl` now reads
   `type-decl | sig | equation | macro | core | def`. An equation is a
   top-level declaration and compiles exactly as the equation of a
   one-equation core.
4. **`@` was spent twice in ASCII** (axis pick `2@`, fuel `<t>@10`).
   *Resolved:* §4's lexing notes now state the rule this package
   implements — `<digits>@` is an axis pick, `@<digits>` or `@[]` is
   fuel — so `@` is not ambiguous and both lexicons hand the parser the
   same kinds.
5. **`}` closes both a core and a namespace literal in ASCII**, while
   Unicode had its own closer. *Resolved:* both lexicons now close a
   namespace literal with the ordinary `}`, so there is no alias and no
   exception to the bijection; `UNICODE_ALIASES` is empty.
6. **Subscript digits appear both inside identifiers** (`flipK₁`) **and
   as the fuel notation** (`<t>₁₀`). *Resolved:* §4's lexing notes now
   say they do not collide because a subscript cannot start an
   identifier, and that identifier subscripts normalize to ASCII digits
   — which is what the Unicode lexer does, so `flipK₁` and `flipK1`
   denote the same tree.
7. **Tier 1 ASCII names are ordinary identifiers in the Unicode
   lexicon**, so both `C` and `⇄` give `Name("C")`. *Resolved:* §4's
   lexing notes now state exactly this, and that the Unicode renderer
   emits the glyph. Tree round-trip is unaffected, which is the law that
   matters.
8. **`add` = 42 was given without its construction.** *Resolved:* the
   construction is now pinned here as decisions 3 and 4 below (per-equation
   `Y`-tied generator, branch lambda lifted into its own
   supercombinator), so the number is reproducible rather than
   coincidental; `sub` = 43 follows from the same two.

Six more, reported against `SURFACE-LANGUAGE-DESIGN.md` §6c and
`SYNTAX.md` §3 after step 3, now rewritten there:

9. **"One step equation per constructor" meant per *leaf*.** *Resolved:*
   §6c now reads "One step equation per leaf", and says why the application
   constructor cannot have one — it is the spine the walker descends,
   not a head that fires.
10. **§6c had no result type, though the loop needs two.** *Resolved:*
    §6c now declares "Two more types: the step outcome `O` and the
    result `R`", says the equations return `O` and the loop returns `R`, and
    says why: the loop has a timeout they cannot express.
11. **§6c did not say how the application constructor is found.**
    *Resolved:* §6c now identifies the object type by shape — the one
    type with exactly one constructor carrying two fields of its own
    type — and makes zero, two, or a non-leaf sibling an error.
12. **The default equations key off names while everything else keys off
    shape.** *Resolved:* §6c now states it as a deliberate exception —
    "the one place a name rather than a shape decides what the ISA is" —
    and says a leaf named otherwise gets no default and must be written.
13. **`SYNTAX.md` §3's written loop did not compile** (mutually
    recursive `loop`/`loop1`, and a body mixing Maybe with a three-way
    outcome). *Resolved:* §6c now spells the written loop in the
    artifact's shape, `loop1 f m n2 = step m (Just m) (f n2)` with
    `loop n m = n Nothing (loop1 loop m)`, and says it passes itself to
    its helper "rather than recursing mutually"; §3 carries that source.
14. **`EXAMPLES.md` §4 spelled constructors in lower case.**
    *Resolved:* §3 of `SYNTAX.md` and §4 of `EXAMPLES.md` now carry the
    exact sources of `skijack/corpus/interp-*.ski`, constructors
    capitalized.

Five more, reported against `SURFACE-LANGUAGE-DESIGN.md` §6, §6a and §6b
after step 4, now rewritten there:

15. **§6b's level-1 table could not be implemented**: it resolved library
    names to axes into a quoted standard subject that does not exist.
    *Resolved:* §6b now marks the shared `<subject>` as the destination
    and states inlining as the current rule — which is what this package
    does, and what makes the paper's tower counts reproduce.
16. **§6 stated the executable as `interp E n <program>`**, as if the
    resolver position were universal, though `whnfF` takes only fuel and
    program. *Resolved:* §6 now says the executable's arity is the
    interpreter's.
17. **§6's default interpreter `wfN` was unavailable** (it needs a
    resolver and the standard subject). *Resolved:* §6 now makes the
    default a program core named `whnfF` until the standard subject
    exists.
18. **`<t>` was an `atom` in the grammar but a declaration property in
    §6.** *Resolved:* `SYNTAX.md` §4 now makes quotation-with-fuel a
    declaration form, `run`, rather than an atom.
19. **Fuel semantics were fixed only in an example**, though they are the
    difference between `@40` and `@41`. *Resolved:* §6c's loop rule now
    carries them — `k` attempts, the last of which is the no-redex
    check, so `s` contractions need `s+1`. `EXAMPLES.md` §4 records the
    `answer` line as measured, with the boundary at fuel 1/2.

Three more, reported against `SURFACE-LANGUAGE-DESIGN.md` §6c and
`SYNTAX.md` §6 after step 5a, now rewritten there:

20. **§6c's "the first such declaration is `O`, the last is `R`" broke on
    a program with an oracle answer type**, which is outcome-shaped too.
    *Resolved:* §6c now says the **last two** outcome-shaped declarations
    are `O` and `R`, and defines the oracle answer type by shape.
21. **§6c's loop rule had no case for a payload-carrying outcome
    constructor**, so `PendingN p` could not reach `RBlockN p`.
    *Resolved:* §6c now extends the rule to payload-carrying
    constructors, and states the resolver as a core parameter.
22. **`SYNTAX.md` §6 required a path to be a value of the declared path
    type, though nothing is typed yet.** *Resolved:* §6 now says only
    path *literals* are accepted until Stage B.

One more, reported against `SURFACE-LANGUAGE-DESIGN.md` §6b after step
5b (items 23 and 24 below are still open, which is why this one is 25):

25. **§6b read as if a declared type's constructors had no level-0
    meaning**, so Stage A refused `App` in the generated rebuilder —
    caught by rendering `generate(parse(…))` and compiling it back as
    ordinary user source. *Resolved:* §6b's level-1 table item now says
    in a parenthetical that a declared type's constructors are ordinary
    level-0 Scott constructors, and that only `S`, `K` and `I` are
    reserved. Check (e) is relaxed to match, and
    `interp-whnff-written.*.ski` plus
    `test_the_generated_program_passes_the_checker_as_user_source` keep
    it honest.

### Still open

One point where the implementation could not follow the notes literally.
(Item 23 below was open for two rounds; `SURFACE-LANGUAGE-DESIGN.md` §5
rule 3 now carries exactly the reading decision 48 implements, so it is
resolved in the note and kept here for the record. Item 25 above was
open for one round and is likewise fixed.)

23. **§5 rule 3 read literally forbids the paper's own tower.** "A value
    of function type (a gate, a core, a supercombinator) … cannot be compared,
    quoted, or stored as a fact" — but `<flipA [K I] K>`, `<UQ <I K>>`
    and `<whnfF three <I K>>` all quote supercombinators, and they are T1 and T2.
    The rule is about turning a *live value* into data at runtime, which
    the language has no form for; compile-time quotation is §6a's
    expand-then-encode. The data check therefore runs at `EQ`, at a
    namespace fact and at a scry path, and the quotation body is checked
    by §6b's tables instead (decision 48). §5 would be clearer if it said
    so.
24. **`EQ` is in the token table with nothing behind it.** (Stage B now
    constrains its operands to data whatever the program defines it as;
    the definition is still the program's.) `SYNTAX.md`
    §2 lists `≟`/`EQ` as a Tier 1 entry and §5 builds four rules around
    it, but no standard subject supplies it, so a program that writes
    `EQ` gets an unresolved name unless it defines one. The corpus
    defines `EQ5` — structural equality over the five-constructor
    alphabet, the thing the paper actually built — and Stage A's `EQ`
    check keys on the name alone. `EQ` belongs in the standard subject,
    which is the piece of §4 this plan never reached.

### Bugs these steps found

**Step 4.** The fuel-policy milestone caught `run_policy` treating `R`'s
*last constructor* as the timeout. For the `T3` shape (`RVal | RErr |
RTime`) that is right by accident; for `maybe === Nothing | Just term`
it is `Just`, so iterative deepening stopped at the first budget and
called a timeout a success. The loop rule says "`R`'s last **terminal**"
— fixed as `run.timeout_constructor`, with a test naming both shapes.

**Step 5a.** A level-0 equation naming a quotation-defined datum
(`oracleIfKk acc = Just encI`) compiled with `encI` left as a *free
atom*, because quote definitions are built after equations. It showed up as
`oracleIfKk` differing from the paper's. Fixed by expanding every
level-0 name again once pass 6 has defined the aliases, and guarded
permanently by a closedness check that refuses any compiled term holding
a non-`{S,K,I}` atom.

**Step 3.** Adding the interpreter tests made the suite allocate enough that
`Prober.read_nat`'s memo table started returning another numeral's
answer: it was keyed by `id(node)` without holding a reference, and
CPython recycles an id as soon as its object is collected. It surfaced as
`dec 3 == 0` in one parametrization only. Fixed by storing
`(node, value)` so the node pins its own id, with an identity check on
lookup; `tests/test_probe.py` now has two regression tests for it. The
bug was latent from step 2 and never affected a compiled term — only the
reader that decodes one.

## A note on vocabulary

Three levels, named consistently in the notes and now in the code: an
**equation** `f x y = body` is what an author writes, a
**supercombinator** is the closed `Y`-tied term it compiles to, and a
**core** is the group it is declared in. The AST node is `A.Equation`,
a core entry's backend name is `core_equation`, and Stage A reports
`in core C, equation f`.

The rename cost one `__str__` rather than a hundred f-strings because
`Problem.where` is a `Site` — a structured `(kind, name, core)` with a
`.dotted` for the qualified name — instead of a pre-formatted string.
`Site` is the place to look if the vocabulary moves again.

One word is deliberately not covered by that split. `Expansion.helpers`
holds lambda-lifted supercombinators with no equation behind them, since
every lambda and every case branch produces one too; "a supercombinator
is what an equation compiles to" is therefore the common case and not
the whole rule.
