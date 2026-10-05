# SKIjack: the language specification

## Version 0.2.0

This document states the SKIjack language as the reference implementation
(`python/skijack`) compiles it confirmed by its test suite. Every rule
carries the test that pins it.

## 0. Normative Requirements

Any second implementation must agree on the ABI:

1. **The instruction set** is `S`, `K`, `I`. These names denote the
   combinators at level 0 even when an object type declares leaves of
   the same names, and they always lower back to atoms.
2. **Tier 1** — the closed terms a program may name beyond the ISA — is
   `B`, `C`, `W`, `Y`. Adding one is a version change.
3. **Declaration order is continuation order.** A Scott datum of an
   *n*-constructor type applied to *n* continuations selects the one at
   its constructor's position in the declaration. A wrong order is not
   an error but silently different behaviour, which is why it is the
   first thing the checker owes an author (§9).
4. **The dictionary's version prefix** is `skijack-1`.

Every compiled term is a closed term over `{S, K, I}`: no free
variables, no environment, no runtime name resolution. The expander
refuses to emit anything else (`test_expand::test_every_output_term_is_closed_over_S_K_I`).

## 1. Lexicon

Two lexicons, one grammar, one tree: the ASCII and Unicode spellings of
every token lex to the same kind, and the two parsers produce equal trees
(`test_parser::test_the_two_spellings_denote_the_same_tree`). The token
table is a strict bijection, checked at import: no two rows share a
kind, neither column repeats a spelling
(`test_lexicon::test_the_table_is_a_strict_bijection`).

| meaning | ASCII | Unicode | kind |
|---|---|---|---|
| macro definition | `:=*` | `≔*` | MACRO |
| capturing macro | `:=!` | `≔!` | CMACRO |
| type declaration | `===` | `≡` | TYPEDECL |
| namespace literal open | `ns{` | `ns{` | NSOPEN |
| scry | `?^` | `∵` | SCRY |
| case | `\|>` | `▹` | CASE |
| interpreter selection | `\|-` | `⊢` | TURNSTILE |
| definition | `:=` | `≔` | ASSIGN |
| fact | `=>` | `↦` | MAPSTO |
| signature arrow | `->` | `→` | ARROW |
| signature colon | `:` | `:` | COLON |
| equation | `=` | `=` | EQUALS |
| type alternative | `\|` | `\|` | ALT |
| quotation open / close | `<` `>` | `<` `>` | QOPEN QCLOSE |
| lambda | `\` | `λ` | LAMBDA |
| name qualifier | `.` | `.` | DOT |
| branch / fact separator | `;` `,` | `;` `,` | SEMI COMMA |
| path separator | `/` | `/` | SLASH |
| group, cell, block | `( )` `[ ]` `{ }` | same | |
| comment to end of line | `--` | `⍝` | |
| axis mark (after a number) | `@` | `⊑` | |
| fuel (after a quotation) | `@n`, `@[]` | subscript digits, `₍₎` | FUEL |

The five Tier 1 glyphs `∘ ⇄ ⋈ Υ ≟` are *identifiers*, not operators: they
lex to the names `B C W Y EQ`, the ASCII names are also valid identifiers
in the Unicode lexicon, and the Unicode renderer emits the glyph. A
declaration may shadow them.

**Identifiers** are `[A-Za-z_][A-Za-z0-9_']*`; the Unicode lexicon also
admits subscript digits inside an identifier (`flipK₁`), normalized to
ASCII digits so both lexicons denote the same tree. A subscript cannot
start an identifier, which keeps subscript fuel unambiguous. A
capitalized identifier is a constructor name (CNAME).

**Maximal munch:** `:=*`/`:=!` before `:=`; `===` and `=>` before `=`;
`|>`/`|-` before `|` (`test_lexicon::test_maximal_munch_ascii`). In ASCII
`<digits>@` is an axis pick and `@<digits>` or `@[]` is fuel, so `@` is
never ambiguous (`test_lexicon::test_axis_and_fuel_are_distinguished`).

**Newlines** terminate a declaration and an equation; they are invisible
inside `( )`, `[ ]`, `< >`, a case brace and a namespace literal; core
braces do *not* hide them, but a closing `}` ends the last equation of a
core so a one-equation core fits on a line.

## 2. Grammar

The parser implements this grammar. Every program in this document and
in `python/skijack/corpus` parses by it.

```
decl      := type-decl | sig | equation | macro | core | def | run
run       := NAME ':=' [expr '|-'] '<' expr '>' ('@' NUMBER | '@[]')
type-decl := NAME '===' ctor ('|' ctor)*
ctor      := CNAME TYPE*                     -- CNAME capitalized; fields are types
sig       := NAME ':' TYPE ('->' TYPE)*       -- optional; ignored by the expander
equation  := NAME NAME* '=' expr             -- inside a core, or at top level
core      := NAME NAME* ':=' '{' equation* '}'   -- parameters after the name
macro     := NAME NAME* ':=*' expr | NAME NAME* ':=!' expr
def       := NAME ':=' expr
expr      := app
app       := atom+                           -- left-associative
atom      := NAME | GLYPH | '(' expr ')'
           | '[' expr expr+ ']'              -- cell
           | '<' expr '>'                    -- quotation: a datum
           | '?^' atom                       -- scry
           | NUMBER '@' atom                 -- axis pick
           | '\' NAME '.' expr
           | expr '|>' '{' branch (';' branch)* '}'
           | 'ns{' fact (',' fact)* '}'
branch    := CNAME NAME* expr
fact      := path '=>' expr
path      := ('/' NAME)+
```

Parsing decisions that the grammar alone does not settle:

- **Parsing is two-pass.** Type declarations are collected first, because
  a case branch `CNAME binder* body` can only be split by knowing the
  constructor's declared arity. An undeclared constructor in a branch is
  a parse error naming it.
  (`test_parser::test_decision_a_branch_binders_come_from_the_declared_arity`)
- **Application is juxtaposition, left-associative, with no precedence
  table beyond parentheses.** Interpreter selection `|-` binds looser
  than application (`test_parser::test_interpreter_selection_binds_looser_than_application`).
- **Cell items are atoms**, so an application inside a cell is
  parenthesized: `[(f x) y]`.
- **A bare number is refused** in expression position: the calculus has
  no integer type. Numbers occur only in an axis pick and as fuel.
  (`test_parser::test_a_bare_number_is_refused`)
- **The lambda rule consumes exactly one dot**, so `\x.a.b` is
  `Lambda(x, Name(a.b))`.
- **`name := { … }` is a core; `name := ns{ … }` is a namespace literal.**
  `[D2]`
- **Qualified names `a.b` parse** and are looked up in the compile-time
  table, never resolved to a position; they do not yet resolve to
  anything, so a program using one is refused by the checker (§9).

## 3. Declarations

### 3.1 Types and constructors

`name === C₁ t… | C₂ t… | …` declares an ordered constructor list. Each
constructor becomes `λ fields. λ c₁ … cₙ. cᵢ fields` — the Scott encoding —
and the type's case form applies a datum to *n* continuations in
declaration order. Field types are recorded for the type stage and
ignored by the expander. **Constructor names are global**: a constructor
may not be declared twice, and may not shadow a declaration
(`test_check::test_a_constructor_may_not_shadow_a_declaration`).

`nat === Zero | Suc nat` therefore yields exactly `K` and
`S (K K) (S (K (S I)) K)`, the artifact's `zero` and `suc`.

### 3.2 Equations

`f x₁ … xₙ = body`, at top level or inside a core. Compiled by bracket
abstraction over its binders after lambda-lifting: every case branch
with binders and every `\x.e` becomes its own supercombinator over the
enclosing binders it uses `[D4]`. A self-recursive equation is tied with
its own `Y` — the first fourteen atoms of `add` are `Y`
(`test_expand::test_y_is_the_first_fourteen_atoms_of_a_recursive_arm`).
**Mutual recursion between equations is refused** with a named error
rather than mis-compiled
(`test_expand::test_mutual_recursion_is_refused_explicitly`).

### 3.3 Cores

A core is a collection of (potentially mutually recursive) equations.
`name p₁ … pₖ := { equations }`. A core's equations are scoped to it:
a name inside a core resolves to a sibling equation before anything at
program level, so two cores may each have their own `step` `[D19]`. Core
parameters are prepended to every equation's binders and are in scope in
every body `[D33]`; references between a core's equations stay raw, so
parameters are passed explicitly (`stepScry1 e`) `[D34]`. Results are
keyed `core.name`, and by the bare name when unambiguous. **A core
cannot name itself** inside its own equations; only an interpreter core's
name denotes anything, its fuel loop (§7).

### 3.4 Definitions and runs

`name := expr` defines a level-0 term. `name := <t>` defines a datum, and
`name := [interp |-] <t>@n` a level-1 executable (§6).

### 3.5 Macros

`name p… :=* body` is expanded at each use site at compile time to a
fixpoint; it has no runtime existence and no dictionary entry
(`test_expand::test_the_macro_leaves_no_runtime_trace`). Expansion is
hygienic: substituting an argument alpha-renames any binder of the body
that would capture a name free in the argument
(`test_expand::test_macro_substitution_avoids_capture`). A partially
applied macro is an error. Expansion is bounded: 100 nested unfoldings
on one path, structural depth 256, and 200,000 substitutions per
declaration, each reported as a named error rather than a hang.
**The capturing form `:=!` parses and is refused**: it is not implemented
(`test_expand::test_capturing_macro_is_refused_clearly`).

### 3.6 Signatures

`name : T -> T …` is parsed and kept on the tree, ignored by the
expander, and checked by Stage B (§9b): the inferred type must have the
declared one as an instance. A signature names declared types only;
type variables and type applications are not spellable in one
(`test_types::test_a_signature_is_checked`).

## 4. Expressions and the representation ABI

- **Cells.** `[a b]` is the Scott pair `λc. c a b`, compiled as
  `pair a b`; `[a b c]` is right-nested (`test_expand::test_cells_of_three_are_right_nested`).
- **Axes address cells, never names.** `n@p` is Nock's numbering: axis 2
  is the head, 3 the tail, `2n` the head of axis `n`, `2n+1` its tail;
  it compiles to the chain of `hd`/`tl` projections
  (`test_expand::test_axis_chain_follows_nocks_numbering`). A term's
  application tree is code and cannot be addressed.
- **The prelude** is `pair`, `hd`, `tl`, `nil`, `cons`, `zero`, `suc`.
  A program that defines one of these replaces the prelude's.
- **Numeral operations** join the prelude only in a program that names
  one without defining it (`expand.NAT_NAMES`), so no other program's
  terms change: `natAdd`, `natSub` (truncated at zero) and `natMul` on
  Scott numerals of any type declared `Zero | Suc t`, and the tests
  `natIfEq m n x y` and `natIfLe m n x y`, which are `x` when `m = n`
  (`m <= n`) and `y` otherwise, so that no boolean type is assumed. Each
  is `Y` of a generator over the numerals' cases, as the expander ties
  any recursion (`test_nat`). `natMul` is defined by `natAdd`, so naming
  `natMul` installs `natAdd` too. A runtime may run them natively on numerals
  it holds as numbers (§9 of `RUNTIME-DESIGN.md`).
- **Booleans** are `K` for yes and `K I` for no.
- **Numerals** are Scott numerals; there is no integer type. Fuel `@n`
  is the one place the token table supplies a numeral; an inner numeral
  is written in the surface (`three = Suc (Suc (Suc Zero))`).
- **Case.** `e |> { C₁ b… body₁; C₂ b… body₂; … }` applies `e` to one
  continuation per constructor **in declaration order, not source
  order** (`test_expand::test_case_uses_declaration_order_not_source_order`).
  It must be complete, repeat no constructor, and name one type (§9 b).
- **Lambda.** `\x.e` is bracket abstraction of `e` over `x`.
- **Backend names** (mangling on collision with a host bird, the
  `\x00`-prefixed sentinels) are not normative: no source program can
  spell them and no emitted term contains them. The spec here draws a
  between what a second implementation must reproduce and what is merely
  how this implementation happens to work internally. (Python's
  `aviary-kernel` does not permit redefinition of its birds but the names
  do not reach the output in any case.)

### 4.1 Kernels: the door

A **kernel** is a value of one shape, Arvo's, which the runtime reads
without knowing any name in the program. It is a door, a cell
`[battery state]`, and the battery is a cell of three arms:

| axis of the kernel | holds | signature |
|---|---|---|
| 4 | `poke` | `kernel -> event -> [effects kernel']` |
| 10 | `peek` | `kernel -> path -> answer` |
| 11 | `load` | `kernel -> old-state -> kernel'` |
| 3 | the state | — |

So a kernel is written `[[poke [peek load]] state]`.

- **Pull.** The runtime selects an arm by axis and applies it to the
  whole kernel, then to the argument: `(4@k) k ev`. This is Nock 9's
  convention, `[9 axis 0 1]` with the core as its own subject. An arm
  reaches its own battery as `2@k` and its state as `3@k`, so no arm
  needs a name for its own kernel, and §3.3's rule that a core cannot
  name itself costs nothing here.
- **Poke** returns a whole kernel. A kernel that keeps its battery
  returns `[(2@k) state']`; one that upgrades returns a different battery,
  which is how the kernel replaces its own code.
- **Load** puts the receiving kernel's battery over a state it did not
  build. The runtime upgrades by pulling `load` from the new kernel with
  the old kernel's state (`3@k`), and the new battery migrates it.
- **Selection is not inspection.** An axis applies a selector to a Scott
  pair; the runtime never reads a term's application tree, so a kernel is
  as opaque to the runtime as any other value (§7 of
  `SURFACE-LANGUAGE-DESIGN.md`).
- **Boot.** A program the runtime boots as a kernel reduces, applied to
  the initial subject, to this shape (`RUNTIME-DESIGN.md` §3b).

Events, effects, paths, answers and states are the program's own types;
the shape fixes only where the arms and the state sit
(`test_examples::test_a_runtime_can_poke_the_kernel_with_events_it_builds`).

**Entropy.** A kernel gets randomness only as event data; no term
reduces to fresh bits. A runtime that offers entropy does so only to a
kernel booted for it (Avon: `avon boot --entropy`), and for such a kernel
fixes three more shapes, after Arvo's `(quip card _this)`:

- **Effects are a list** (`nil`, `cons`) of cells `[tag data]`, `tag` a
  numeral.
- **Events are cells `[tag data]`.** Tag `0` belongs to the runtime: it
  accepts an outside event only when probing shows a cell whose tag is a
  successor, and refuses any other, so that no event source chooses a
  kernel's bits.
- **A request is the effect `[0 id]`,** `id` a numeral the kernel
  chooses. The runtime answers each, in the list's order, with its own
  event `[0 [id bits]]`, `bits` a list of 128 Booleans; a reply's own
  requests are answered in turn, up to a bound the runtime sets (Avon:
  16 for one outside event). Boot answers a request of its own: the
  first event is `[0 [0 bits]]`.

The runtime reads these shapes by probing, as it reads a kernel, and
logs each reply before applying it, so a replayed kernel sees the same
bits. Every other effect passes through untouched, and a kernel booted
without entropy keeps its effects and events entirely its own. Entropy
comes on request rather than with every event because most events need
none, and a proof of a poke carries its whole event as private witness
(`avon/docs/DESIGN.md` §9.1).

## 5. Names and tiers

Names resolve in a compile-time table and are gone before anything runs.
A binder of the enclosing equation (or a core parameter) shadows
everything, since it stays a variable until bracket abstraction removes
it. Otherwise a name resolves, in this order: `S`, `K`, `I` to the ISA,
unconditionally; then a sibling equation of the enclosing core; then a
program-level name — declarations and the prelude share one namespace,
and a program's own definition of a prelude name replaces the prelude's;
then a Tier 1 built-in. Anything else is unresolved, a checker error
(§9 f); free variables do not exist at runtime.

`EQ` is in the token table as the name of equality on data and both
checkers key their data rules on that name (§9 c, §9b), **but no
definition stands behind it**: a program that uses `EQ` must define it,
as the corpus defines `EQ5`. It belongs to the standard subject, which is
unbuilt (§11).

## 6. Levels, quotation and fuel

A declaration runs at one of two levels, and the level is a property of
the declaration.

**Level 0** hands the term to the host reducer as is: no fuel, no
interpreter, and a `Scry` leaf is an inert atom.

**Level 1** quotes the program at compile time and reduces the
interpreter's loop applied to its parameters, its fuel and the encoded
program: `interp p… n <t>`. The arity is the interpreter's; an
interpreter must be applied to all its parameters
(`test_quote::test_an_interpreter_must_get_all_its_parameters`). The
default interpreter is a core named `whnfF` in the program.

**Quotation `<t>`** encodes `t` into the program's object type (§7),
which is unique. Inside the brackets a name is a constructor of
the object type if it is one, and otherwise any level-0 name is inlined
as its expanded term and encoded in place; juxtaposition is the
application constructor; a constructor of another type must be
saturated (§9 e). A quotation may nest, and a nested quotation carries
neither fuel nor an interpreter. **A parameter cannot be quoted**
— `f x = <x>` is refused, since `x` names neither table
(`test_level1::test_a_level0_name_may_be_quoted_but_a_parameter_may_not`):
quotation is available only for terms known before anything runs, which
is the reify/eval line stated as a rule. A quotation appears only at a
definition's right-hand side; one inside an equation body is refused.

**Fuel** `k` permits `k` step-attempts, the last of which must be the
no-redex check: a run of `s` contractions needs fuel `s + 1` and times
out at `s` (`test_level1::test_the_fuel_boundary_is_where_examples_says`).
**Elided fuel `@[]`** is a runtime policy, not a compile-time value: the
budget starts at 8 and doubles until the run produces something other
than a timeout or reaches the cap of 4,096, which is reported as the
timeout outcome and never hidden
(`test_level1::test_the_cap_is_reported_not_hidden`). A program with
elided fuel has no closed term until a budget is supplied.

## 7. The interpreter interface

An interpreter is a core the compiler can place in the `interp`
position. Its interface is generated from, or checked against, the
program's type declarations; the reference implementation reproduces
the paper's `whnfF`, `wf5Abs`, `wf5Omg`, `wfQ` and `wfN` from it atom
for atom (`test_interpreter`, `test_scry`).

- **The object type** is identified by shape: the unique declared type
  with exactly one constructor carrying two fields of its own type (the
  application constructor); every other constructor is a leaf. Zero or
  two such constructors, a non-leaf non-application constructor, or two
  such types are each a named error
  (`test_generate::test_object_type_is_found_by_shape` and the three
  refusal tests beside it). A program with no such type generates
  nothing.
- **`O` and `R`.** A type is *outcome-shaped* when one of its
  constructors carries a single field of the object type; the first such
  constructor is the carrier, and a later one is a payload constructor
  (`PendingN term5`: the blocked path, declared as what it holds, since a
  level-1 path is an encoded term). Of the
  outcome-shaped declarations, the **last two** in declaration order are
  the step outcome `O` and the result `R`; a single one serves
  as both (the Maybe shape); an earlier one is the oracle answer type;
  `|O| = |R|` is checked (`test_generate::test_t3_shape_takes_the_last_two_outcome_shaped_declarations`).
- **The oracle answer type** is the outcome-shaped declaration that is
  neither `O` nor `R`: its payload-carrying constructor is the hit, its
  last nullary constructor is "not yet".
- **The interpreter core** is any core that writes `step`, `loop`, or
  `step<C>` for a leaf `C`. Generation adds, for each interpreter
  core, what it does not write: the spine walker `sp`, the rebuilder
  `rb`, default step equations for leaves *named* `S`, `K`, `I` — the
  one place a name rather than a shape decides what the ISA is —
  `step m = sp m nil stepC₁ … stepCₙ` in declaration order, and `loop`
  with `loop1`. A written `step` or `loop` always wins
  (`test_generate::test_a_written_step_or_loop_is_not_replaced`);
  `loop1` without `loop` is refused. Everything generated is surface
  syntax that renders and re-parses, and compiles identically when kept
  as user source (`test_check::test_the_generated_program_passes_the_checker_as_user_source`).
- **The loop rule.** `loop n m` peels one `Suc` per attempt and yields
  `R`'s **last terminal** at `Zero`. `loop1` applies `step m` to
  one continuation per `O` constructor in declaration order: the
  term-carrying constructor continues with the new term and the
  remaining fuel; `O`'s first terminal (no redex) yields `R`'s
  term-carrying constructor applied to the current term; each further
  constructor of `O` maps to `R`'s constructor **at the same position**,
  handed the same payload if it carries one (`PendingN p` → `RBlockN p`).
- **The core's name denotes its loop** (`test_generate::test_the_core_name_denotes_its_fuel_loop`),
  and a resolver enters as a core parameter, applied before the fuel:
  `wfN E |- <t>@n` is `loop E n <t>`.
- **A written `step`** must hand over one continuation per leaf and
  install them in declaration order; `step<App>` is refused by name.

## 8. Scry and namespaces

- **`?^` compiles only inside a quotation**, to the object type's
  `Scry` leaf applied to the encoded path; at level 0 it is refused
  (`test_check::test_a_scry_outside_a_quotation_is_rejected`).
- **The path type** is found by name and shape: a declaration `path`
  of exactly the form `Nil | Cons seg path`. A path literal
  `/a/b` denotes `Cons A (Cons B Nil)`, each segment naming the `seg`
  constructor spelled with its first letter capitalized; the segment
  constructors must be nullary; an unknown segment is an error. Only
  path *literals* are accepted, and the type stage does not change that:
  a scry path and a namespace key are quoted at compile time, and a
  path-typed *expression* is a level-0 term whose value exists only at
  run time, so accepting it would be reification. Segment payloads are
  refused likewise.
- **A namespace literal** `ns{ /p => <q>, … }` compiles to a flat chain of
  `EQ5` comparisons in fact order, answering the oracle type's hit at
  the first match and its "not yet" otherwise. It requires a
  program-level `EQ5` and an oracle answer type; each fact's value must
  be a quotation (`test_check::test_a_namespace_fact_must_be_data`);
  `ns{}` always answers "not yet". Lookup cost is linear in a fact's
  position (about fifteen thousand contractions per probe on the
  reference reducer): a namespace literal is an association list.
- **Blocking.** Under an interpreter whose outcome and result types
  carry a second payload constructor — `PendingN term5` mapping to
  `RBlockN term5`, the encoded path that blocked — a scry with no fact
  blocks and the
  driver re-runs the program from scratch under a namespace that only
  grows; a fact once learned is never withdrawn, which is what makes
  replay sound. Fuel is spent again on each replay.
- **A scry is a redex, not an effect**: a lookup the reduction discards
  is never performed, and one left unforced under a term already in
  weak head normal form comes back unread
  (`test_scry::test_a_discarded_lookup_is_never_performed`).

## 9. Stage A: what the checker refuses

The checker runs before expansion, collects every problem, and raises
once with the first problem's class and the whole list attached.
It rejects and never rewrites: for every accepted program the emitted
term is the same with the check on or off
(`test_check::test_checking_never_changes_the_terms`).

| | check | class |
|---|---|---|
| a | constructor arity where an application denotes data: inside a quotation, a path literal, a namespace key | `ArityError` |
| b | case completeness, repetition, mixed types, and a written `step`'s order | `CaseError` / `InterfaceError` |
| c | the data rule: an operand of `EQ`, the argument of a quotation, a namespace key, a scry path may not be a **provable** function — a lambda, a bare combinator, a macro, an equation with binders, a core, a namespace literal, an under-applied constructor | `DataError` |
| d | the interpreter interface of §7 | `InterfaceError` |
| e | inside a quotation, a name that is neither a constructor of the object type nor a level-0 name; at level 0 every declared type's constructors are ordinary and only the ISA is reserved | `SymbolTableError` |
| f | unresolved names; duplicate declarations | `ScopeError` |

Stage A's data rule establishes one direction only: no accepted program
holds a provable function in a data position. With binders untyped here,
a bound variable's kind is unknown, so `f x = EQ x PTrue` with
`g := f K` passes Stage A; Stage B catches it (§9b). A quotation's body
is checked by the symbol tables, not the data rule, because level-1
codegen is expand-then-encode and quotes supercombinators by design.

## 9b. Stage B: the type discipline

Stage B runs after generation and before codegen, over macro-expanded
bodies, and like Stage A it collects every problem, raises once with
class `TypeMismatchError`, rejects and never rewrites
(`test_types::test_type_checking_never_changes_the_terms`). It is
Hindley–Milner over the declared sum types and function types, with one
rule that is the whole discipline:

**A datum may be applied; a function is never a datum.** Every declared
type is Scott-encoded, so a value of type `T` *is* its own case analysis
and may be applied to one continuation per constructor. Unification is
therefore oriented, `unify(expected, given)`: a *given* sum type meeting
an *expected* arrow expands to its Scott scheme, and an *expected* sum
type meeting a *given* arrow is the error. `Zero` compiles to `K`, so a
symmetric rule would accept `Suc K`; the orientation is what makes it an
error (`test_types::test_a_function_is_not_a_datum`).

- **Case forms are typed nominally.** In `e |> { C b… body; … }` the
  scrutinee has the branches' declared type, each binder has its
  declared field type, and the branches agree on one result. `add m n =
  n |> { Zero m; Suc k (Suc (add m k)) }` is `nat -> nat -> nat`, and
  `add K Zero` is an error (`test_types::test_a_case_gives_its_scrutinee_the_declared_type`).
- **Elimination arrows.** A datum applied by hand to its continuations,
  as the interpreters do (`args h (rb1 rb h)`), is typed by those
  continuations. An arrow a *binder* acquires by being applied is an
  *elimination* arrow: datum-compatible, and once checked against a
  declared type it remembers it. An arrow a value was *built* with — a
  lambda, a combinator, a partially applied constructor — is a function.
  So a binder may be used as a datum and as its own case in either
  order, and a function passed where either use expected a datum is
  refused in either order (`test_types::test_a_binder_used_as_case_then_as_datum_still_refuses_a_function`
  and its mirror).
- **Recursion over a datum applied by hand yields a cyclic type**, and
  unification is equirecursive, so those are admitted — as is
  `omega = S I I (S I I)`, with no escape hatch
  (`test_types::test_omega_is_typed_without_an_escape`). The nominal
  form is the stronger check, and the one to write when the check is
  wanted.
- **The operands of `EQ`** carry a data constraint: a type variable so
  marked may be bound to a sum type and never to a built arrow. That is
  how `f x = EQ x PTrue` with `g := f K` is refused although `x` is a
  bare binder (`test_types::test_an_operand_of_eq_may_not_be_a_function_through_a_binder`).
- **Level 1.** A quotation `<t>` has the program's object type; a
  namespace literal has type `object -> answer`; a run `interp p… |-
  <t>@n` applies the interpreter's loop to its parameters, then to
  `fuel` and the datum, and has the result type `R`.
- **The prelude and the ISA** have schemes: `pair : a -> b -> cell a b`,
  `hd`, `tl`, `nil : list a`, `cons`, `zero : fuel`, `suc`;
  `natAdd`, `natSub`, `natMul : a -> a -> a` and `natIfEq`,
  `natIfLe : a -> a -> b -> b -> b`, which serve any numeral type, so
  their operands are only tied to one type; `S`, `K`,
  `I`, `B`, `C`, `W`, `Y` their standard ones. An axis pick projects
  through nested cells and nothing else
  (`test_types::test_an_axis_picks_into_a_cell_and_nothing_else`).
- **Signatures** are checked (§3.6). **Every compilable corpus program
  type-checks unchanged** (`test_types::test_every_compilable_corpus_file_is_well_typed`).

What Stage B does not do: a declared type has no parameters and a
signature cannot name a type variable, so polymorphism is inferred and
never written; the standard subject is still unbuilt, so `EQ` still has
to be defined by the program.

## 10. The dictionary

Tier 1's table as a versioned artifact: for each name its expansion, its
atom count and a structural hash. The hash is Merkle over the tree — a
leaf hashes its name, an application hashes `"(" + hash(fn) + " " +
hash(arg) + ")"` — `sha256` truncated to 16 hex digits, prefixed
`skijack-1:`; equal trees hash alike however they were shared
(`test_dictionary::test_equal_trees_hash_alike_however_they_were_shared`).
One name is one expansion: registering a name twice with different terms
is refused. **Lift** names every subterm that is an exact
structural match of an entry, largest first, and leaves the rest raw;
`lower ∘ lift = id` on every corpus term. Entries under three atoms are
tabled but never lifted; `S`, `K`, `I` are never lifted; among names
sharing a term the unqualified, shorter one wins. This is the
operation a runtime's jet table performs.

## 11. What is refused or unbuilt

Stated explicitly:

- mutual recursion between equations (§3.2); the capturing macro `:=!`
  (§3.5); a bare number in expression position (§2); a quotation inside
  an equation body (§6); a core naming itself (§3.3); `step<App>` (§7);
  two object types, or two interpreters over different alphabets in one
  program (§7);
- qualified names resolve to nothing; segment payloads and path-typed
  expressions are refused; mount tables are not built (§8);
- there is no integer type (§4), no standard subject and therefore no
  `EQ` and no shared quoted library — a name used twice inside one
  quotation is duplicated in the datum (§5, §6);
- a declared type has no parameters, and a signature names declared
  types only (§9b); the pre-0.2.0 spelling of a blocked payload,
  `PendingN path`, is refused, since what it holds is an encoded term
  (§7, `test_types::test_the_blocked_payload_is_declared_as_what_it_holds`).

## 12. Laws the implementation is held to

For every corpus program `P` and each lexicon `L`, with `M` the other:

- `parse_L(render_L(parse_L(P))) = parse_L(P)` and
  `parse_M(render_M(parse_L(P))) = parse_L(P)`; rendering is idempotent
  (`test_roundtrip`).
- `expand ∘ render = lower`: rendering is canonical.
- `lower ∘ lift = id` on every compiled term (`test_dictionary`).
- Checking is erasure, Stage A and Stage B alike: expansion is the same
  with the checkers on or off (`test_check::test_checking_never_changes_the_terms`,
  `test_types::test_type_checking_never_changes_the_terms`).
- Every emitted term is closed over `{S, K, I}`.
- Values are read behaviourally — by applying a term to fresh marker
  atoms and observing which comes back — never by inspecting combinator
  syntax (`test_probe`).
- The paper's artifacts are reproduced atom for atom: `whnfF` 618,
  `wf5Abs` 768, `wf5Omg` 771, `wfQ` 950, `wfN` 1,066, `EQ5` 240, and
  T0/T1/T2 at 340, 91,556 and 504,930 contractions (`test_interpreter`,
  `test_level1`, `test_scry`).

## 13. A complete program

Everything above, in eight lines that compile to the paper's base
interpreter and run a term under it:

```skijack
term === S | K | I | App term term
maybe === Nothing | Just term
nat === Zero | Suc nat

whnfF := {
  step m = sp m nil stepS stepK stepI
}

three = Suc (Suc (Suc Zero))
answer := whnfF |- <I K>@3
```

`whnfF` is 618 atoms; `answer` reaches `Just <K>` in 340 contractions.
