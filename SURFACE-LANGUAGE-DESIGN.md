# Design note: a supercombinator surface language over SKI

> **Status (2026-09-21).** Design note written 2026-09-16, before the implementation existed. The language it specifies is now implemented as `python/skijack`; decisions taken since are recorded in `python/NOTES.md`. Where this note and the code differ, the code and its tests are authoritative. The note is kept in place because the implementation's docstrings cite it by section.

*2026-09-16. Follow-up to the paper whose artifact is `artifact-metacircular-ski`, not part of
it. This note fixes the kernel forms, the ABI, and the compile rules
for a Hoon-like macro language whose target is closed `{S,K,I}` terms,
so that syntax can be designed against a stable target. Nothing here is
built. Where a rule is already implemented in the repository under
another name, the name is given. Syntax in examples is illustrative
only; the note is about what the forms mean and what they compile to,
not how they are spelled.*

Language name bikeshedding:
* Skilling
* Skyjack <- SKIjack
* Skiff
* Skyborn
* Skyclad <-
* Skinnydip
* SKIrocket
* Skirret
* SKIblue
* SKIdive
* SKIlark
* SKIlight
* SKIline
* SKIpilot

## 0. Thesis

Hoon is sugar over Nock plus a standard library, compiled away. The same
layering is available over SKI, with one difference that is a theorem
rather than a choice: quotation of a live term is impossible
(Proposition 3.1 of the paper, from Jay and Given-Wilson), so the line
between compile-time and runtime quotation is forced. Everything on the
encoded side of that line is closed under the calculus, including
running encoded terms, comparing them, and building cores. Everything
that would turn a live value back into data is unavailable and must be
staged. The language's design problem is to make that line visible and
comfortable.

The other difference, which is a gain, is that weak SKI reduction is
call-by-name: arguments are never forced early, `K I Ω` is `I`, and no
form needs thunking.

## 1. What already exists

- **A macro layer.** `D(name, [binders], body)` and `AL(name, term)` in
  `tower_harness.py` define named terms with binders; `expand` applies
  bracket abstraction (`aviary_kernel.abstraction`) and yields a closed
  `{S,K,I}` term. This is the compiler's back end. It has no subject, no
  types, and no surface; binders are Python strings.
- **Scott encoding** for object terms, lists, `Maybe`, and numerals, in
  the fixed continuation orders recorded in the paper's §3.1.
- **Recursion** through `Y = S (K (S I I)) (S (S (K S) K) (K (S I I)))`,
  14 atoms, with every recursive definition written as a generator that
  takes its own fixpoint as first argument (`spGen f m acc`, and so on).
  That is open recursion, and it is the equation-with-self-as-argument
  convention already.
- **Interpreters** `whnfF`, `wfQ`, `wfN` (618, 950, 1,066 atoms), the
  unquoter `UQ` (43), and equality on encoded paths `EQ5` (240).
- **The behavioral verification discipline:** every claim about a
  compiled term is checked by applying it to fresh atoms and reading
  which one it selects, never by reading combinator syntax.

## 2. Representation ABI

These decisions are the interface between the compiler and the standard
library. They are fixed here so the surface can vary without moving them.

**Pairs.** `[a b]` is the Scott pair `λc. c a b`. Projections: head
`p K`, tail `p (K I)`. Axis addressing is Nock's: axis 1 is the whole,
axis 2 the head, axis 3 the tail, axis `2n` the head of axis `n`, axis
`2n+1` its tail. An axis compiles to the corresponding chain of
projections, innermost first; cost is one projection per bit of the
axis, as in Nock.

**Names and scope.** Names are resolved in a compile-time table and are
gone before anything runs: an equation is lambda-lifted over its
parameters and over the sibling equations it calls, the group is tied
with `Y`, and what
is left is a closed term whose meaning depends on nothing around it
(`DESIDERATA.md` item 2). There is no runtime environment to address, so
names are not axes and a qualified name `a.b` is a name and not a search
path. Bracket abstraction is the closure mechanism, and it closes over
the equation's own binders, not over any subject.

**Subject.** The word is kept for exactly one thing: the single argument
the runtime applies a loaded program to at boot, which carries the
standard library (`RUNTIME-DESIGN.md` §3b, §4 below). It is an argument,
not a scope; nothing resolves into it at run time. An earlier draft of
this note made it the environment for name resolution and built §3
around that; see the two-things-do-not-transfer note in
`DESIDERATA.md` §1 for why that is gone.

**Gates** (the ◇ core dialect of §3, not what the implementation
compiles). A gate is a core `[battery [sample context]]` with one equation,
following Hoon: the battery is the compiled body, abstracted over the
core; the sample sits at axis 6 and the context at axis 7. Note that
both of those are axes into a *data* cell the gate carries, which is
`SYNTAX.md` §7's rule and not name resolution. Calling a gate with an argument
replaces the sample and pulls it: `pull(replace(gate, 6, x))`.
(A lighter dialect compiles `|=` to a plain λ by bracket abstraction
with no core; it is faster and has no `..$`. Both are available from the
same kernel; the core dialect is the one that makes Nock 9 and `%=`
meaningful.)

**Cores.** `[battery payload]` with the battery a tuple of
supercombinators. Each equation is lambda-lifted over the whole core and
receives it as an argument. The core is tied once:
`core = Y (λself. [ <sc₁[self], …, scₙ[self]> payload ])`. Pulling entry
`i` is `(πᵢ (head core)) core`. Replacing the payload (`%=`) is building
a new pair with the same battery; because the battery's entries take the
core as an argument rather than closing over the payload, no
recompilation is needed. This is the property the paper's resolver
lacks: its facts are closed over, so a new fact means re-expanding the
term on the host.

**Sum types.** A type declaration is an ordered constructor list, each constructor followed by the types of its fields (`Suc nat`); the field types are ignored by the expander and used by the type stage (`DESIDERATA.md` item 11). It
generates the constructors, each `λ fields. λ c₁ … cₙ. cᵢ fields`, and
the case form for that type, which applies a datum to `n` continuations
in declaration order. The order is part of the ABI: the paper's object
terms are the declaration `S, K, I, App(t,u)`, and every interpreter
depends on that order. Changing a declaration changes every case form
over it, which is exactly the outcome-type-growth phenomenon of the
paper stated as a compiler fact.

**Numerals.** Scott numerals for data (`zero`, `suc`), matching the fuel
convention; Church numerals only where iteration is wanted. No native
atoms exist; arithmetic is unary and O(n). This is the one place Nock is
richer at the machine level, and the language should not pretend
otherwise.

**Booleans.** `K` for yes and `K I` for no, so `?:` is application to two
continuations.

**Encoded terms.** The five-constructor encoding `S, K, I, App, Scry` of
`scry_harness.py` is the object language of the virtualizing
interpreters. A literal term in source compiles to its encoding at
compile time.

## 3. Kernel forms and their compile rules

Written as `⟦form⟧_Γ`, the compilation of a form in the compile-time
scope `Γ` (a table from names to what they denote: a binder of the
enclosing equation, a sibling equation, a constructor, a macro); `abs(x, t)` is
bracket abstraction of `t` over the binder `x`. `Γ` is a compiler data
structure and has no runtime existence — nothing in the output takes it
as an argument, and this is what item 2 of `DESIDERATA.md` means.

The rows marked ▸ are what the implementation compiles today; the rows
marked ◇ are the Hoon-shaped core dialect of §2, kept here because the
core/gate layout is still the intended shape for `%=`-style work, and
not built. Every rule that once read "compiled against the subject
extended by …" now reads as ordinary lexical binding, because that is
both what the expander does and what bracket abstraction is for.

| | form | rule |
|---|---|---|
| ▸ | name `a` | what `Γ` says: a binder (stays a variable until abstraction), a sibling equation (its supercombinator), a constructor, or an error |
| ▸ | qualified name `a.b` | a name with a dot; looked up in `Γ`, never resolved to a position (`SYNTAX.md` §7) |
| ▸ | axis pick `n@ p` | the projection chain for `n`, applied to `⟦p⟧_Γ` — a *data* cell, not a scope |
| ▸ | cell `[a b]` | `pair ⟦a⟧_Γ ⟦b⟧_Γ` |
| ▸ | literal (a term as data) | its Scott encoding, a closed term |
| ▸ | lambda `\x.e` | `abs(x, ⟦e⟧_{Γ,x})` |
| ▸ | equation `f x₁ … xₙ = body` | `abs(x₁, … abs(xₙ, ⟦body⟧_{Γ,x…}))`, lambda-lifted over the sibling equations it calls and tied with `Y` for recursion; one supercombinator, one shared node |
| ▸ | core `name params := { equations }` | the equations above, tied as a group; the name is a namespace for them (§7), not a runtime pair |
| ▸ | case `e \|> { cᵢ bᵢ }` | `⟦e⟧_Γ (λ fields. ⟦b₁⟧) … (λ fields. ⟦bₙ⟧)` in declaration order, each body compiled in `Γ` extended by its own fields as ordinary binders |
| ▸ | macro `name :=* body` | expanded at each use site at compile time; no runtime cost to reach, duplicated per use; see §3a |
| ▸ | eval `<t>@n` | `whnfF ⟦n⟧ ⟦<t>⟧`, a `Maybe`; under a virtualizing interpreter, `wfQ E …` or `wfN E …` with their outcome types |
| ▸ | scry `?^/a/b` | the leaf `Scry <path>` in the object language; stuck under host reduction, resolved only under `wfQ`/`wfN` |
| ◇ | gate `\|= body` | `core([abs(self, ⟦body⟧_self)] [placeholder payload])` per §2 |
| ◇ | call `(g x)` | `pull(replace(⟦g⟧_Γ, 6, ⟦x⟧_Γ))` |
| ◇ | pull `a:c` | `(πₐ (head ⟦c⟧_Γ)) ⟦c⟧_Γ` |
| ◇ | replace `%= c a x` | `pair (head ⟦c⟧_Γ) (set(payload, axis(a), ⟦x⟧_Γ))` |
| ◇ | pin `=+ x body` | a one-binder abstraction applied to `⟦x⟧_Γ`; the earlier draft made this an extension of a subject with a shift rule, which is exactly what item 2 no longer claims |

Everything in the table is either an application, a pair, a projection,
a Scott constructor, or bracket abstraction, so every program compiles
to a closed `{S,K,I}` term — closed outright, not closed relative to a
subject it must be applied to.

### 3a. Arms versus macros

The two definition keywords mirror Hoon's `++` and `+*`, and the cost
model decides between them. A supercombinator is one node in the DAG, shared by
every use, and costs a pull to reach: the projections of its axis plus
one application. A macro is expanded into every use site, so it costs
nothing to reach and is duplicated per use. Small things, the derived
combinators, booleans, projections, and the sugar of §3b, want to be
macros; large things, `EQ`, the interpreters, the standard subject's
library, want to be supercombinators. The kernel table above is the whole compiler;
most of a comfortable surface is macros over it: `?:` over `?-`, `=/` as
pin plus face, `|-` as a one-equation core, and so on. That is how the
compiler stays small and how the surface can grow without touching it.

**Hygiene is a decision, and the default is hygienic.** If a macro body
is expanded before its names are resolved, they bind at the use site and
capture whatever the caller has in scope, which is what Hoon's `+*` does
and is occasionally wanted. If the body's names are resolved at the
definition site, the macro is hygienic. The default is hygienic, because
a capture is invisible in the source and shows up only as a body silently
reading the wrong binding; a separate, clearly marked capturing form
(`:=!`) is available for the cases that want it.

### 3b. Derived combinators and the basis as a declaration

`B = S (K S) K`, `C = S (S (K (S (K S) K)) S) (K K)`, and `W = S S (K I)`
are values in the standard subject and macros in the surface, at no cost
to the kernel; the runtime jets them by hash (`RUNTIME-DESIGN.md` §2).

Making them *leaves of the object language* is a different decision,
and a real tradeoff. Abstraction into `{S, K}` alone is quadratic in
size; Turner's algorithm with `B` and `C` (and their primed variants) is
near-linear, and the paper's census measured the effect on the
interpreter's own core: 151 atoms over BCKW against 249 over SKI, about
40% smaller. But a leaf is not free. Each added constructor is one more
continuation in every encoded node, so every leaf encoding grows by
about two atoms, every case form over the type grows, and the
interpreter gains an equation per leaf (`B` and `C` need three arguments, `W`
two). This is the paper's outcome-type growth as an engineering cost.
Whether it pays depends on how often `B` and `C` occur in compiled
output relative to all leaves; for Turner-style abstraction they
dominate, so a net win for large programs is expected, but it is to be
measured, not assumed.

The design answer is that **the basis is a type declaration**. The
kernel dialect is `+$ term [%s] [%k] [%i] [%app t u]`, the `{S,K,I}` of
the paper's artifact and theorems, and it is the reference. An extended
dialect is another declaration, `+$ term7 [%s] [%k] [%i] [%b] [%c] [%w]
[%app t u]`, whose constructors, case form, and interpreter are
generated by the same rules. The compiler targets whichever basis the
program declares. The interpreter for the extended dialect is itself the
first serious program to write in the surface, and its size relative to
`whnfF` is the measurement the tradeoff above needs.

## 4. The standard subject

The library the runtime hands a program at boot (§2, **Subject**): a
nested pair holding, at fixed axes, the entries below. Two things follow
from item 2 of `DESIDERATA.md` and are worth stating before the list. A
*level-0* name from this library is resolved at compile time and compiles
to its term or to a shared supercombinator node — it is not projected out of anything
at run time, and nothing in a compiled program applies itself to this
pair to find its own names. What the pair is *for* is boot and level 1:
the runtime supplies it once, and its quoted image `<subject>` is the
shared library a level-1 program addresses (§6b), where projection is
legitimate because a quoted subject is data.

The entries:

- `S`, `K`, `I` as values, and `Y`;
- pairs and projections, booleans, Scott lists with fold, `Maybe`,
  numerals with successor, predecessor, addition, equality;
- `EQ` on encoded terms (the 4- and 5-constructor versions);
- `UQ`, the unquoter;
- `whnfF`, `wfQ`, `wfN` as supercombinators, the analogue of `++nock` in `hoon.hoon`;
- the constructors and case forms of the built-in types (object terms,
  outcomes, oracle answers).

Estimated size two to three thousand atoms, compiled once and shared by
reference. Its axes are the ABI; a program compiled against one layout
is not portable to another, as in Nock.

## 5. The quotation line, stated as rules

1. A literal in source is quoted at compile time. This is the only
   quotation the language performs.
2. A value of a data type (any Scott-encoded type declared in the
   language) may be compared with `EQ`, passed to `.*`, stored in a
   namespace, and re-encoded one level up by a definable data
   transformation `<t> ↦ <<t>>`.
3. A value of function type (a gate, a core, a supercombinator) can be applied and
   nothing else *at runtime*. It cannot be compared, stored as a fact,
   or reified into data by any form the language offers: no `!=`, no
   `!>`, no `.=` on functions. This does not forbid *compile-time*
   quotation of a supercombinator: `<whnfF three <I K>>` is the paper's T2, and it
   is rule 1, expand-then-encode at compile time, not a runtime
   operation on a live value. Stage A therefore applies the data check
   at `EQ`, at a namespace fact, and at a scry path, and checks a
   quotation's body by the two symbol tables of §6b instead.
4. `.*` on a computed term is available only if the term was built from
   data forms; a gate cannot be turned into a term to run.

Rule 3 is where a type system earns its keep: the compiler must know
which values are data. The cheap version is a naming convention; the
honest version is a type checker over the declarations, which is
ordinary work in the macro layer.

## 6. Execution model: level 0 and level 1

The compiler has one target, closed `{S,K,I}` terms, and one code
generator. What varies is the level a declaration runs at, and the
level is a property of the declaration, not a choice made per
expression.

**Level 0, direct.** The term is handed to the host reducer as is: the
interpreters, the standard subject, and anything runtime-facing. No
fuel, no interpreter in the loop; a `Scry` leaf is an inert atom, which
is why nothing at level 0 may use one.

**Level 1, virtualized.** The term is quoted at compile time and the
executable the host reduces is the interpreter's loop applied to its
own arguments and the encoded program: `whnfF n <program>` for the base
interpreter, `wfN E n <program>` for one that takes a resolver. The
arity is the interpreter's, not a constant of the form. Scry is live
only under an interpreter whose alphabet has `Scry` and whose loop
takes a resolver; fuel is explicit; the outcome is the interpreter's
result type. Any declaration that uses `∵` is level 1, and the compiler
packages it so without being asked. The default interpreter is a core
named `whnfF` declared in the program (or, once the standard subject
exists, the library's `wfN`); `interp ⊢ …` selects another. A
quotation with fuel is a level-1 *declaration*: it appears as a
definition's right-hand side, and a bare `<t>` (a datum) may also be
nested inside another quotation; a quotation inside an equation body is not
a form.

This is Urbit's split: the kernel runs raw Nock, userspace runs under
`+mink` with scry, and jets make the virtualization free. Here the
interpreters and library are level 0, applications are level 1, and the
runtime's first jet is the interpreter, after which a level-1 program
costs what a level-0 program does. Towers beyond level 1 are the
explicit `⟪ ⟫` form nested, for when an interpreter is to run an
interpreter (the paper's T2).

### 6a. What codegen targets, exactly

Every interpreter reimplements the ISA: its `S`, `K`, `I` equations are its
own code, reduced by the host or by the interpreter below it. So the
alphabet a level-1 program is written in is the *object type of the
interpreter it will run under*, a declared type such as
`{S, K, I, App}`, `{S, K, I, App, Scry}`, or a dialect with `B`, `C`,
`W`. The code generator therefore does two things in sequence:

1. **Expand** the declaration to a term over the target alphabet, by the
   rules of §3. At level 0 the alphabet is the host's ISA and the result
   is the executable. At level 1 the alphabet is the interpreter's object
   type; the result is a term over that alphabet, not yet executable.
2. **Quote**, at level 1 only: encode the term as Scott data over the
   declared type's constructors (`encS5 …` for a five-constructor type),
   and wrap it with the interpreter application.

Both steps emit only `{S,K,I}`; the quoted datum is pure `{S,K,I}` even
when the object alphabet has extra leaves, because a leaf is a
constructor. "Targeting the interpreter" and "targeting pure SKI" are
therefore both true, of different steps.

### 6b. Two symbol tables

Inside `⟪ ⟫` names resolve differently from outside it, and the compiler
keeps two tables:

- **The level-0 table:** names to what they denote — a binder, an equation,
  a constructor, a macro, a library entry. Resolution is compile-time and
  positional in nothing; a library name compiles to its term or to the one
  shared node for that supercombinator.
- **The level-1 table:** the object type's constructors, plus the
  *quoted* standard subject. (At level 0 a declared type's constructors
  are ordinary Scott constructors and may be applied freely; the
  interpreter's own rebuilder applies `App` to build encoded terms. The
  only names reserved at level 0 are `S`, `K`, `I`, which denote the ISA
  there even when the object type declares leaves of those names; inside
  a quotation the same three names denote the leaves.) A level-1 program does not share the
  level-0 subject (it is data at a different level); it receives the
  same library as a Scott-encoded value, `<subject>`, computed once and
  shared by reference across every level-1 program. Names inside `⟪ ⟫`
  that are library names resolve to a projection into `<subject>` —
  which is axis addressing of *data*, in the sense of `SYNTAX.md` §7,
  not name resolution against an environment, since a quoted subject is
  a Scott datum like any other; names that are constructors of the object
  type resolve to the constructors; and application inside `⟪ ⟫` is the
  `App` constructor.

**State of implementation.** The shared `<subject>` is the destination,
not yet a reachable state: there is no standard subject to quote. Until
there is, a library name inside a quotation is inlined as its expanded
level-0 term and quoted in place, exactly as the artifact writes
`encP(A(UP, encP(IK)))` for T1; a name used twice in one quotation is
therefore duplicated rather than shared, and nested quotations splice
the inner datum as an inlined term. This is what `python/` does.

This is how Arvo sits in userspace's subject. It also fixes what the
runtime's jet table must contain: the dictionary of §5 of `DESIDERATA.md`
*and its image under quotation*, since a level-1 program's use of `EQ`
is the encoded `EQ`, walked by the interpreter, until the runtime
recognizes it.

### 6c. The interpreter interface

An interpreter is a core that the compiler can put in the `interp`
position. Its interface is generated from, or checked against, three
type declarations, and the reference implementation reproduces the
paper's `whnfF`, `wf5Abs`, and `wf5Omg` from this interface atom for
atom (`python/skijack/corpus/interp-*.ski`).

- **The object type** (the alphabet), identified by shape: the one
  declared type with exactly one constructor carrying two fields of its
  own type, the application constructor; every other constructor of
  that type must be nullary, a leaf. Zero or two such constructors, a
  non-leaf non-application constructor, or two such types are errors.
  The declaration generates the constructors, the case form, the spine
  walker `sp` and the rebuilder `rb` at that arity (the paper's
  `spQ`/`rbQ` are the five-constructor instances).
- **One step equation per leaf.** The application constructor has none and
  cannot: it is the spine the walker descends, not a head that fires,
  and the walker hands the collected arguments to the leaf it reaches.
  The standard subject supplies default equations for leaves *named* `S`,
  `K`, `I`, which is the one place a name rather than a shape decides
  what the ISA is; a leaf named otherwise gets no default and must be
  written. So an interpreter that only adds a leaf writes only that
  leaf's equation, which is the paper's one-site authorship as a compiler
  convenience. If the core omits `step`, it is generated as `step m =
  sp m nil stepC₁ … stepCₙ` in declaration order.
- **Two more types: the step outcome `O` and the result `R`.** The equations
  return `O`; the loop returns `R`; they differ because the loop has a
  timeout the equations cannot express. Both are found by shape among the
  non-object types: exactly one constructor carrying one field of the
  object type; other constructors may carry other fields (a blocked
  path). Of the outcome-shaped declarations, the *last two* are `O` and
  `R` in that order; a single one serves as both (the Maybe shape of
  `whnfF`); any earlier one is an oracle answer type (below); the
  constructor counts of `O` and `R` must agree.
- **The oracle answer type**, for an interpreter that takes a resolver:
  the outcome-shaped declaration that is neither `O` nor `R`; its
  payload-carrying constructor is a hit and its last nullary
  constructor is "not yet". The resolver is a core parameter, written
  after the core's name (`wfN e ≔ { … }`), threaded to every equation, and
  applied to the loop first, so `wfN E ⊢ <t>ₙ` is `loop E n <t>`.
- **The loop, generated from `O` and `R`** unless written. Rule: peel one
  `Suc` per attempt, returning `R`'s last terminal at `Zero`; apply
  `step m` to one continuation per `O` constructor in declaration order,
  where the term-carrying constructor continues the loop with the new
  term and the remaining fuel, `O`'s first terminal (no redex) returns
  `R`'s term-carrying constructor applied to the current term, and each
  further constructor of `O` maps to the constructor of `R` at the same
  position, handed the same payload if it carries one (`PendingN p`
  becomes `RBlockN p`). For `maybe ≡ Nothing | Just term` this yields the paper's
  `wf1`/`wfGen`; for `outcome ≡ Stepped term | Done | Errd` with
  `result ≡ RVal term | RErr | RTime` it yields `wf5Abs1`/`wf5Abs`. A
  written `loop` in the core overrides the generated one; because each
  equation is tied with its own fixpoint, a written loop passes itself to its
  helper as the artifact does (`loop1 f m n2 = step m (Just m) (f n2)`,
  `loop n m = n Nothing (loop1 loop m)`) rather than recursing mutually.
- **What fuel counts.** Fuel `k` permits `k` step-attempts, and the last
  attempt must be the one that finds no redex; a term that needs `s`
  contractions therefore needs fuel `s + 1`, and fuel `s` times out.
  This is the whole difference between `<flipA [K I] K>₄₀` (`Nothing`)
  and `<…>₄₁` (`Just <I>`), and between `<K I Err>₁` (`RTime`) and
  `<K I Err>₂` (`RVal <I>`); the generated loop implements it and the
  tests pin both boundaries.
- **The core's name denotes its loop.** `whnfF ⊢ …` applies it.

Two interpreters with the same three types and different equations are the
paper's `wf5Abs`/`wf5Omg`; an interpreter with an added constructor and
a resolver parameter is `wfQ`. The conformance tests for a user
interpreter whose `S`, `K`, `I` equations claim to be the ISA are the paper's
T0–T2 counts.

## 7. Cores as the internalized namespace

The paper's blocking resolver is host-side because its facts are closed
over. Under the core ABI the resolver is `[battery facts]` where the
battery has one equation, lookup, compiled against the core, and `facts` is
an encoded list of pairs. Learning a fact is `%=` with `cons`; the
resume loop becomes a one-equation core whose equation runs `wfN` with the
resolver, inspects the outcome, and on a block pulls itself with the
extended resolver. The whole loop is then one closed term, which is the
"pure-SKI driver" the paper leaves open. The decoder from an encoded
payload back to a path is not needed inside the calculus, since the
blocked path is already encoded data; it was only ever needed to consult
a Python dict.

## 8. Self-hosting

The compiler of §3 is a function from Scott-encoded syntax trees to
Scott-encoded `{S,K,I}` terms. Both are data, so the compiler is
definable in the language and compiles to a closed term, the analogue of
`++mint` in `hoon.hoon`. Its core is bracket abstraction over encoded
terms with a variable tag, the same combinator the partial-evaluation
design (`PARTIAL-EVALUATION-DESIGN.md`, an unpublished note in the paper's working repository, Stage 4) needs to unfold under
an unknown head. Building it once serves both. Cost is unknown; a few
thousand atoms is the guess, and running it on itself is a T2-scale
computation.

## 9. Worked example

The interpreter's step function, in an illustrative syntax, with the
object-term type and the spine walker in scope:

```
+$  term  [%s] [%k] [%i] [%app t=term u=term]
+$  step  [%stepped t=term] [%done] [%errd]
++  step
  |=  m=term
  (spine m ~ step-s step-k step-i)
```

`spine` is `spQ`, the equations are `stepSQ`, `stepKQ`, `stepIQ`, and the
whole compiles to the 569-atom `step` of the paper. The fuel loop is a
`|-` over it with a Scott numeral as sample. Writing the interpreter in
the surface and checking that it compiles to a term with the same
behavior as `whnfF` (by the fresh-marker probes, and by T0's 340
contractions) is the first milestone; writing the compiler in the
surface is the second.

## 10. What is decided here and what is left to syntax

Decided: Scott pairs as cells with Nock axes addressing *data only*;
compile-time name resolution with no runtime environment, the subject
kept for the boot argument alone (§2); Hoon's gate layout for the core
dialect; cores tied with `Y`; declaration order as continuation order;
Scott numerals; the quotation rules of §5; the two modes of §6; two
definition keywords, equation and macro, with hygienic macros by default
(§3a); derived combinators as names and macros, with an extended basis
available only as a separate type declaration (§3b).

Left to syntax: runes versus S-expressions; whether lexical names exist
alongside qualified names, and what `a.b` resolves to; how declaration
order is made visible; whether `.*` is a form or a library supercombinator; how the data/function line of §5 is written;
and how the mode of §6 is marked; how the capturing macro form is
marked; and how a program declares which basis it targets.

## 11. Order of work

1. The ABI of §2 as a follow-on file: pairs, axes, cores, pull, replace,
   with fresh-marker checks. Small.
2. The standard subject of §4, compiled and measured.
3. The kernel compiler of §3 in Python over a syntax-tree data type, so
   the interpreter can be written in the surface and checked against
   `whnfF` (§9, first milestone).
4. The resolver as a core (§7): the paper's open problem closed.
4a. The BCKW dialect (§3b): its interpreter written in the surface, and
    the size and step-count comparison against `whnfF` that decides
    whether extended bases are worth their dispatch cost.
5. The compiler in the surface (§8), and the partial-evaluation Stage 4
   it enables.
