# SKIjack-0: the self-hosted front end's language

**SKIjack-0 is the subset of SKIjack that the self-hosted front end
compiles, and this note specifies its compilation term for term.** The front
end is written in SKIjack-0 itself, so compiling its own source is a fixed
point: the terms it produces must be the terms `expand_program` produces,
hash for hash (`DESIDERATA.md` §6, item 5; `avon/docs/DESIGN.md` §20.3).

Two implementations are checked against `expand_program`:

- `python/skijack/spec0.py`, written from this note rather than from
  `expand.py`: `tests/test_spec0.py` requires the same term for every name,
  on the corpus programs in the subset, on the compiler core, and on a
  thousand random programs;
- the front end in SKIjack-0, run in Avon.

## 1. The subset

- **Declarations.** A type, `name === C1 t* | C2 t* | …`; an equation,
  `name b* = expr`; a definition, `name := expr`. No cores, macros,
  signatures, quotations, scries or namespace literals.
- **Expressions.** A name, application by juxtaposition, `( e )`, a cell
  `[ e1 e2 … ]` (two or more items), a pick `n@atom` (n ≥ 1), a case
  `e |> { C b* body ; … }` naming each constructor of one type exactly
  once, a lambda `\x. e`. No qualified names (`a.b`), no numbers but in a
  pick.
- **Names.** No binder -- of an equation, a lambda or a case branch -- is
  `S`, `K` or `I`: the expander would confuse it with the combinator. No
  program name is an aviary bird (`B`, `C`, `W`, `Y`, …), which the
  expander would resolve to the bird.
- **Lexicon.** ASCII only.

## 2. Lexing

Characters are ASCII. Space, tab and carriage return separate tokens; a
comment runs from `--` to the end of the line. A newline is a token, and
consecutive newlines are one. The tokens, the longest spelling first:

| token | spelling |
|---|---|
| a pick | digits then `@`, as `2@` |
| type declaration | `===` |
| case | `\|>` |
| definition | `:=` |
| equation | `=` |
| alternative | `\|` |
| lambda, its dot | `\`, `.` |
| separators, groups | `;` `(` `)` `[` `]` `{` `}` |
| a name | a letter or `_`, then letters, digits, `_` and `'` |

## 3. Parsing

A first pass reads every type declaration -- a name, `===`, then
constructors separated by `|`, each a name followed by its field types, to
the end of the line -- and records each constructor's type, index and
arity. A case branch takes as many binders as its constructor has fields.

A program is declarations separated by newlines; a declaration opens with
a run of names and the operator after it says which it is. Inside `( )`,
`[ ]` and a case's `{ }`, newlines are ignored.

```
expr   = app ( "|>" "{" branch ( ";" branch )* "}" )*
app    = atom atom*
atom   = name | "(" expr ")" | "[" atom atom+ "]" | n "@" atom | "\" name "." expr
branch = Ctor name{arity} expr
```

Application associates to the left, and a case applies to the whole
application before it: `f x |> { … }` is a case on `f x`. A lambda's body,
and a branch's body, extend as far as an expression can.

## 4. Expansion

Every name of the program -- constructor, equation, definition -- and the
seven prelude names compiles to a closed term of `S`, `K` and `I`. The
compilation is a set of **rules**, a rule being formal parameters and a
body, and a term per rule.

**The prelude**, each overridden by a program declaration of the name:

| rule | formals | body |
|---|---|---|
| `pair` | x y c | `c x y` |
| `hd` | p | `p K` |
| `tl` | p | `p (K I)` |
| `nil` | n c | `n` |
| `cons` | h t n c | `c h t` |
| `zero` | z s | `z` |
| `suc` | n z s | `s n` |

**A constructor** `C`, index `i` of a type with `n` constructors, with `k`
fields: formals `f0 … f(k-1) c0 … c(n-1)`, body `c_i f0 … f(k-1)`.

**Desugaring**, before code generation:

- a cell `[e1 e2 … en]` is `pair e1 (pair e2 (… en))`;
- a pick `n@e` applies `hd` for each bit 0 and `tl` for each bit 1 of `n`
  below its leading 1, most significant first: `10@e` is `hd (tl (hd e))`;
- a case is the scrutinee applied to one continuation per constructor, in
  the type's declaration order: a branch with binders `b1 … bk` is the
  lambda `\b1. … \bk. body`, one without is its body.

**Code generation** turns a desugared body into a rule body, given the
**scope**, the binders in order. A name in scope is that variable; `S`,
`K`, `I` are the combinators; any other name refers to its rule, and a name
with no rule is an error. **A lambda is lifted**: the chain `\p1. … \pm.
body` becomes a new rule whose formals are the scope's variables free in
the body, in scope order, then `p1 … pm`, and whose body is the body
generated in that scope; the lambda is replaced by that rule applied to
those captured variables.

**Recursion.** An equation depends on the equations it names outside its
own binders. The equations fall into groups, each a maximal set of
equations that reach one another, ordered by declaration.

- An equation in a group of one that does not reach itself is a rule:
  its binders, and its body generated with them as the scope.
- One that does is `Y gen`, `Y` aviary's `S (K (S I I)) (S (S (K S) K)
  (K (S I I)))`: `gen`'s formals are a fresh variable for the equation
  itself, then its binders, and its body names itself by that variable.
- A group of `n` equations shares one fixpoint. Rules `tuple x0 … x(n-1)
  c = c x0 … x(n-1)`, `pick_j x0 … x(n-1) = x_j` and `sel_j t = t pick_j`;
  for each member `j`, `code_j` with formals a fresh variable `g` then its
  binders, and its body with every member `m` named as `sel_m g`; `gen t =
  tuple (code_0 t) … (code_(n-1) t)`; the group is `Y gen`, and member `j`
  is `sel_j` of the group. A lambda in a member's body captures `g` when it
  names a member.

**A definition** `name := expr` is its expression, generated in the empty
scope.

**The term of a rule** is its body with every reference replaced by that
rule's term, then abstracted over its formals, the last first:
`[f1] … [fk] body`, by aviary's bracket abstraction with eta --
`[x]x = I`; `[x]E = K E` when `x` is not free in `E`; `[x](E x) = E` when
`x` is not free in `E`; `[x](E F) = S [x]E [x]F`. The front end's own
abstraction is `tests/selfhost/abstract.ascii.ski` in Avon, checked
against aviary's on every abstraction of the corpus.

## 5. What the front end reads and writes

The front end reads the program as a list of characters, each a
constructor of a 128-way character type, and writes, for each name in
declaration order and then the prelude's, the name and its term as an
encoded term. `avon/tests/selfhost/` holds the drivers and the fixed-point
check.
