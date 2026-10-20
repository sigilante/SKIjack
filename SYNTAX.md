# Syntax direction

> **Status (2026-09-21).** Design note written 2026-09-16, before the implementation existed. The language it specifies is now implemented as `python/skijack`; decisions taken since are recorded in `python/NOTES.md`. Where this note and the code differ, the code and its tests are authoritative. The note is kept in place because the implementation's docstrings cite it by section.

*2026-09-16. Decisions taken on the surface, ahead of a grammar. Sits
under `DESIDERATA.md` (what the language must be) and beside
`SURFACE-LANGUAGE-DESIGN.md` (what forms exist and what they compile to).
This note fixes the shape of the notation and the rule that keeps its two
spellings one language.*

## 1. Decisions

1. **Hybrid form.** Definitions are written as equations in the Turner and
   Miranda style, which is the artifact's own `D(name, binders, body)`
   form and the aviary kernel's cell language. Tier 1 combinators are
   named identifiers with an optional glyph spelling, usable tacitly
   inside equations. Cores are blocks of equations under a name.
   Quotation and virtualized evaluation are the two bracketed forms.
2. **Cores stay.** The goal is a machine shop, not coverage of every SKI
   term. A core is a named block of equations with an implicit self
   binder; equations call each other by name; the block compiles to the `Y`-tied
   tuple of `SURFACE-LANGUAGE-DESIGN.md` §2.
3. **Application is juxtaposition, left-associative, always.** SKI's
   native order. Glyphs are identifiers, not operators: there is no
   APL evaluation order, no precedence table beyond parentheses, and a
   glyph applied to arguments means exactly what the same name applied
   to them means.
4. **Two lexicons, one syntax.** An ASCII spelling and a decorated
   Unicode spelling of the same tokens. The grammar, the syntax tree,
   the expander, and the laws are shared; only the lexer and the
   renderer are doubled. The token table is a bijection, so
   `render_A ∘ parse_U` and `render_U ∘ parse_A` are total and invert
   each other on the tree.

## 2. The token table (draft)

The bijection between spellings. Every row must be unambiguous in both
columns; the ASCII column must not collide with identifiers or with
each other under maximal-munch lexing. This table is the whole
difference between the two interfaces.

| meaning | Unicode | ASCII | notes |
|---|---|---|---|
| definition | `≔` | `:=` | a top-level definition: a core, or a name for an expression |
| equation | `=` | `=` | `name binders = body`, inside a core or at top level; same in both lexicons |
| macro definition | `≔*` | `:=*` | expanded per use, hygienic |
| capturing macro | `≔!` | `:=!` | the marked non-hygienic form |
| quotation (compile time) | `<t>` | `<t>` | emits the Scott encoding; a datum, not run; the paper's notation |
| virtualized evaluation | `<t>ₙ` | `<t>@n` | the quotation run under the default interpreter with fuel `n`; the only place scry is live |
| interpreter selection | `I ⊢ <t>ₙ` | `I \|- <t>@n` | run under interpreter core `I` instead of the default; a resolver is a parameter of the interpreter |
| fact | `p ↦ v` | `p => v` | inside a namespace literal; `=>` so that `->` is the signature arrow alone and the table stays a bijection |
| namespace literal | `ns{/a/b ↦ v, …}` | `ns{/a/b => v, ...}` | keys are path literals; compiles to a resolver core with a mount table (§6); it closes with the ordinary `}` in both lexicons |
| scry | `∵/a/b` | `?^/a/b` | the `Scry` leaf applied to a path; the argument must be of the declared path type (§6) |
| axis pick | `2⊑` `3⊑` | `2@` `3@` | projection by Nock axis; head is `2@`, tail `3@` |
| cell | `[a b]` | `[a b]` | Scott pair; right-nested when more than two |
| qualified name | `a.b` | `a.b` | a dotted name, resolved in the compile-time name table (`whnfF.step` is a core's equation); it addresses a *name*, never a position |
| lambda (local abstraction) | `λx.e` | `\x.e` | bracket-abstracted on the spot; for one-off closures, not equations |
| case | `e ▹ { c₁ b₁ ; c₂ b₂ }` | `e \|> { c1 b1 ; c2 b2 }` | one branch per constructor, in declaration order |
| type declaration | `τ ≡ C₁ \| C₂ σ ρ \| …` | `t === C1 \| C2 s r \| ...` | constructors capitalized and followed by their field *types*; order is the ABI |
| signature (optional) | `f : σ → τ` | `f : s -> t` | ignored by the expander; checked by the type stage (`DESIDERATA.md` item 11) |
| core | `name params ≔ { equations }` | `name params := { equations }` | block of equations with implicit self; parameters after the name (a resolver, for an interpreter) are threaded to every equation and applied to the loop first; same in both lexicons |
| composition (`B`) | `∘` | `B` | Tier 1 glyphs; the ASCII spelling is the name |
| swap (`C`) | `⇄` | `C` | |
| duplicate (`W`) | `⋈` | `W` | |
| fixpoint (`Y`) | `Υ` | `Y` | |
| equality on data | `≟` | `EQ` | refused on function types |
| comment | `⍝` | `--` | to end of line |

Rows above the glyph section are structure; rows in the glyph section
are Tier 1 dictionary entries and grow with the dictionary. `S`, `K`,
`I` are spelled the same in both lexicons.

Two rules for adding a row: the Unicode spelling must be a single code
point or a bracket pair, so the renderer never has to decide how to
break it; and the ASCII spelling must be typeable without a dead key,
so the ASCII interface is the one that works everywhere.

## 3. Example, both spellings

A two-fact resolver and a run under it, the paper's §6.3 example re-cast with typed paths (§6).

Unicode:
```
seg  ≡ Nat | Two | Three
path ≡ Nil | Cons seg path
resolve ≔ ns{/nat/two ↦ <I>, /nat/three ↦ <K>}
answer  ≔ wfN resolve ⊢ <∵/nat/three>₁₀
```

ASCII:
```
seg  === Nat | Two | Three
path === Nil | Cons seg path
resolve := ns{/nat/two => <I>, /nat/three => <K>}
answer  := wfN resolve |- <?^/nat/three>@10
```

A user interpreter with one added constructor, and a program run under
it, in ASCII (the Unicode spelling differs only in `≡`, `≔`, `⊢`, and the
brackets). This is the source the reference implementation compiles to
the paper's `wf5Abs` (768 atoms) and `wf5Omg` (771), atom for atom:
```
term5 === S | K | I | App term5 term5 | Err
outcome === Stepped term5 | Done | Errd
result === RVal term5 | RErr | RTime

omega = S I I (S I I)

wf5Abs := { stepErr acc = Errd }
wf5Omg := { stepErr acc = omega }

answer := wf5Abs |- <K I Err>@5
```
`App` is the application constructor by shape; `S`, `K`, `I` are leaves
with default equations; `Err` is the leaf the user writes an equation for; `step`
and the loop are generated from the three declarations
(`SURFACE-LANGUAGE-DESIGN.md` §6c). The base interpreter itself is
```
term === S | K | I | App term term
maybe === Nothing | Just term
whnfF := { step m = sp m nil stepS stepK stepI }
```
which compiles to the paper's 618-atom `whnfF` exactly; with the loop
written out instead of generated,
```
whnfF := {
  step m       = sp m nil stepS stepK stepI
  loop1 f m n2 = step m (Just m) (f n2)
  loop n m     = n Nothing (loop1 loop m)
}
```
compiles to the same term. Inside `< >` the names `K`, `I`, `Err` are
constructors of `term5` and juxtaposition is `App`; outside it, `S`,
`K`, `I` are always the level-0 combinators, which is why `omega` can
share a file with the declaration.

## 4. Grammar

*This is the grammar the parser implements, as `SPEC.md` §2 states it;
the sketch that stood here listed a bare `NUMBER` atom, a postfix axis
pick and cells of expressions, none of which survived implementation
(`python/NOTES.md`, decisions 5 and 8).*

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
The ASCII grammar is this grammar with the table's substitutions. Both
parsers produce the same tree type; the tree has no lexicon field.

Lexing notes that the table implies but should be stated: in ASCII,
`<digits>@` is an axis pick and `@<digits>` or `@[]` is fuel, so `@` is
not ambiguous; Unicode identifiers may contain subscript digits
(`flipK₁`), which normalize to ASCII digits and cannot start an
identifier, so they do not collide with subscript fuel; and a Tier 1
combinator's ASCII name (`C`) is also a valid identifier in the Unicode
lexicon, so `C` and `⇄` denote the same name and the Unicode renderer
emits the glyph.

## 5. What the two-lexicon rule costs and buys

- **Costs:** every new form needs two spellings chosen together, and
  the ASCII side is the binding constraint (no collisions with
  identifiers or with `<`, `|`, `@`, `->` as used elsewhere). The table
  above already spends `<` on quotation, which rules out `<` as a
  comparison; that is acceptable because comparison is `EQ` on data
  only.
- **Buys:** the manuscript, the notebook, and the source share one
  text in the Unicode spelling; the ASCII spelling works in any editor,
  terminal, and diff; `lift` can emit either; and a program's identity
  is its tree, so the choice of spelling is a rendering preference, not
  a dialect.

## 6. Scry namespace discipline

The paper's artifact accepts any term as a path, because that was the
honest description of what was built. The language does not inherit
that. A path is a value of a declared path type, and the scry form is
refused on anything else.

- **Path type.** The standard library declares `path ≡ nil | cons seg
  path`, a list of segments, and `seg` as an enumerated tag type (with
  a data payload where a segment needs one, as Nock's `care` and
  `desk` do). Because `path` is a Tier 1 data type, it is comparable
  with `EQ`, storable in a namespace, and quotable; a function can never
  be a path, which is the quotation line of `SURFACE-LANGUAGE-DESIGN.md`
  §5 applied to lookups.
- **Segments, not terms.** Nock's paths are lists of atoms and the
  namespace is routed by prefix (vane, care, desk, and so on). The same
  shape here: the first segment selects a resolver, the rest is that
  resolver's business. A resolver core therefore carries a mount table,
  a list of `(seg, resolver)` pairs, and the top-level resolver is
  dispatch on the head segment followed by a pull on the mounted core
  with the tail. This is how a namespace becomes hierarchical instead
  of a flat dictionary, and it is the structure the paper's `EQ5`
  chain lacks.
- **Syntax.** The scry form takes a path literal or a path-typed
  expression: `∵/a/b/c` in Unicode, `?^/a/b/c` in ASCII, where `/`
  separates segments. The program declares `seg` (the segment tags,
  capitalized constructors, with a payload where a segment needs one)
  and `path ≡ Nil | Cons seg path`; a segment word in a literal denotes
  the `seg` constructor whose name is that word with its first letter
  capitalized, so `/nat/three` is `Cons Nat (Cons Three Nil)`, and an
  unknown segment is an error. Inside a quotation the path is quoted
  like any other datum, so a level-1 path is an encoded object term and
  resolvers compare paths by `EQ5` on encodings, as the paper does. A
  namespace literal's keys are path literals. `∵` applied to anything
  not of type `path` is a compile error, not a runtime block; until the
  type stage exists (`DESIDERATA.md` item 11, Stage B) only a path
  *literal* is accepted, checked structurally, and a path-typed
  expression is refused.
- **Paths are still syntactic.** Equality of paths is structural
  equality of segment lists; nothing is normalized, which keeps the
  paper's argument about the word problem intact and keeps lookups
  cheap.
- **What this costs.** One type declaration in the standard library,
  one check in the expander, and a mount-table convention for resolver
  cores. What it buys is that the namespace is a namespace: prefix
  routing, a place for authority (who answers which prefix), and the
  possibility of a runtime-provided root resolver (`RUNTIME-DESIGN.md`
  §4, step 5) with a fixed, typed interface.

## 7. Axes address cells, not terms

`2@` and `3@` do not reach into a combinator. A term's application tree
is code, and Proposition 3.1 says nothing in the calculus can inspect it.
Axes address *cells*: `[a b]` is the Scott pair `λc. c a b`, whose only
operation is to hand its components to a selector, so `2@p` is `p K`
(head), `3@p` is `p (K I)` (tail), and axis `n` is the chain of heads
and tails Nock's numbering gives (`6@p` is the head of the tail).

Names are not axes, and this is where the language parts company with
Nock rather than merely restricting it. A dotted name `a.b` is a
qualified name looked up in the compile-time table, not a search path
into a runtime environment: there is no environment to search, because
bracket abstraction closed every term before the program ran
(`DESIDERATA.md` item 2). So axes do one job and names do another, and
neither reaches into the other's. This is the paper's disanalogy made
concrete: in Nock the noun tree is the formula, axes address code and
data alike, and names are axes; here axes address data only, code is
opaque, and names are resolved and gone by the time anything runs.

## 8. Atoms and free variables

The calculus has no atoms but `S`, `K`, `I`. The `X1`, `X2` of the
verification probes are host-level uninterpreted constants used at the
metalevel to observe a term; they are admitted in the test harness and
nowhere in the language. Free variables do not exist at runtime: bracket
abstraction closes every term, so there is no environment at all, and an
unresolved name at compile time is an error. A numeral literal `5` is
sugar for the Scott numeral `suc (suc (suc (suc (suc zero))))`, so the
language still sticks to the three atoms. (A binary Scott-encoded
numeral type with runtime jets, in the manner of Vere's atoms, is the
obvious later addition; it is deliberately not here.)

## 9. Open items

- Whether subscript fuel (`<t>₁₀`) or a suffix form (`<t>@10`, as in
  ASCII) is better in the Unicode lexicon; the ASCII `@10` is fixed.
- Whether the case form `▹` is needed at all once types generate their
  own case functions (a datum applied to continuations is already a
  case); it may be a macro.
- The glyph choices for `B`, `C`, `W` are placeholders; the constraint
  is single code points that do not collide with APL's meanings for the
  same glyphs, since an APL reader will bring those.
- Whether qualified names use `.` or something that does not collide
  with `λx.e`; the lambda dot is the likelier one to change. Also what
  `a.b` resolves *to*: the equation names the dictionary already carries
  (`whnfF.step`) are the obvious target, and today the parser accepts
  the dotted name while the expander rejects it as unresolved.
