# Examples

> **Status (2026-09-21).** Design note written 2026-09-16, before the implementation existed. The language it specifies is now implemented as `python/skijack`; decisions taken since are recorded in `python/NOTES.md`. Where this note and the code differ, the code and its tests are authoritative. The note is kept in place because the implementation's docstrings cite it by section.

*2026-09-16. Every example is given in both spellings of `SYNTAX.md`, then
its codegen as produced by the reference expander (`aviary-kernel`'s
bracket abstraction, the same one the paper's artifact uses), then the
behavioral check that was actually run: values were read by applying
results to fresh marker atoms, never by reading combinator syntax. Atom
counts are tree-atoms. Where a number is not given, it was not measured.*

## 1. Numerals: increment, decrement, addition, subtraction

Numerals are Scott numerals, a declared type like any other. Applying a
numeral to two continuations is a case analysis: `Zero` selects the
first, `Suc m` hands `m` to the second. That is why decrement is one
case and no recursion.

Unicode:
```
nat ≡ Zero | Suc nat

arith ≔ {
  inc n   = Suc n
  dec n   = n ▹ { Zero  Zero ; Suc m  m }
  add m n = n ▹ { Zero  m    ; Suc k  Suc (add m k) }
  sub m n = n ▹ { Zero  m    ; Suc k  sub (dec m) k }
}
```

ASCII:
```
nat === Zero | Suc nat

arith := {
  inc n   = Suc n
  dec n   = n |> { Zero  Zero ; Suc m  m }
  add m n = n |> { Zero  m    ; Suc k  Suc (add m k) }
  sub m n = n |> { Zero  m    ; Suc k  sub (dec m) k }
}
```

`add` and `sub` recurse through the core's implicit self; `sub` reaches
`dec` by name because they share the core. Subtraction is truncated.

**Codegen.** The case form is application of the datum to its
continuations, so `dec n = n ▹ {…}` is `n Zero I` before abstraction.

| equation | atoms | term |
|---|---|---|
| `Zero` | 1 | `K` |
| `Suc` | 8 | `S (K K) (S (K (S I)) K)` |
| `inc` | 8 | `S (K K) (S (K (S I)) K)`, identical to `Suc`: the abstraction algorithm η-reduces `λn. Suc n` |
| `dec` | 7 | `S (S I (K K)) (K I)` |
| `add` | 42 | `Y`-tied; the first fourteen atoms are `Y` |
| `sub` | 43 | `Y`-tied |

A tail-recursive addition, `add m n = n ▹ { Zero m ; Suc k  add (Suc m) k }`,
is 44 atoms and takes 179 contractions to read out `add 2 3` against
173 for the version above; under call-by-name there is no reason to
prefer it.

**Checks run:** `inc 2 = 3`; `dec 3 = 2`; `dec 0 = 0`; `add 2 3 = 5`;
`add 0 4 = 4`; `sub 5 2 = 3`; `sub 2 5 = 0`. `dec 3` reaches weak head
normal form in 15 host contractions.

**Quoted:** `<inc>` is 268 atoms, `<dec>` 227, `<add>` 1,548. The level-1
tax is about 32 atoms per application node of the level-0 term, the
size of the `App` constructor's encoding.

## 2. A combinator three ways: `C`

`C f x y = f y x`, swap the arguments of a binary function.

Unicode / ASCII (identical, no glyph used):
```
C f x y = f y x               -- as an equation: one shared term, applied at runtime
flip f x y ≔* f y x           -- as a macro: rewritten at the use site   (ASCII: :=*)

flipK₁ x y = C K x y          -- uses it
flipK₂ x y = flip K x y       -- uses the macro
```

| definition | atoms | term |
|---|---|---|
| `C` | 10 | `S (S (K S) (S (K K) S)) (K K)` |
| `flipK₁` (equation) | 11 | `S (S (K S) (S (K K) S)) (K K) K` |
| `flipK₂` (macro) | 5 | `S (K (S K)) K` |

Both `flipK` variants applied to `X1 X2` reduce to `X2`; `C K X1 X2`
reduces to `X2`. The macro version is smaller because `C` never exists
at runtime, the rewrite happened in the source; the equation's version
is one shared node reused by every caller. This is the
supercombinator-versus-macro cost model of
`SURFACE-LANGUAGE-DESIGN.md` §3a: macros erase combinators,
supercombinators share them.

## 3. A macro over pairs, and level 0 versus level 1

`swap p ≔* [3@p 2@p]` swaps a cell; `2@` and `3@` are the head and tail
projections on a Scott pair (`SYNTAX.md` §7).

Unicode:
```
swap p ≔* [3⊑p 2⊑p]
flipA q = swap q
```

ASCII:
```
swap p :=* [3@p 2@p]
flipA q = swap q
```

Macro expansion rewrites the equation to `pair (tl q) (hd q)`; the macro is
gone. Then:

- **Level 0 (unquoted):** `flipA` is 29 atoms,
  `S (S (K (S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K))) (S I (K (K I)))) (S I (K K))`.
  `flipA [X1 X2] K` reduces to `X2`. The program `flipA [K I] K` reduces to
  `I` in 40 host contractions.
- **Level 1 (quoted):** `<flipA>` is 1,057 atoms; the program
  `<flipA [K I] K>` is 1,809 atoms for a 49-atom program;
  `whnfF 41 <flipA [K I] K>` reaches weak head normal form in 29,191
  host contractions. Fuel 40 times out: fuel `k` permits `k`
  step-attempts of which the last must be the no-redex check.

## 4. A user interpreter with one added constructor

Unicode:
```
term5 ≡ S | K | I | App term5 term5 | Err
outcome ≡ Stepped term5 | Done | Errd
result ≡ RVal term5 | RErr | RTime

omega = S I I (S I I)

wf5Abs ≔ { stepErr acc = Errd }
wf5Omg ≔ { stepErr acc = omega }
answer ≔ wf5Abs ⊢ <K I Err>₅
```

ASCII:
```
term5 === S | K | I | App term5 term5 | Err
outcome === Stepped term5 | Done | Errd
result === RVal term5 | RErr | RTime

omega = S I I (S I I)

wf5Abs := { stepErr acc = Errd }
wf5Omg := { stepErr acc = omega }
answer := wf5Abs |- <K I Err>@5
```

The object type is found by shape (`App` is the one constructor with two
fields of its own type); its declaration generates the five
constructors, the case form, and this arity's `sp` and `rb`. `stepS`,
`stepK`, `stepI` are the default equations for the leaves of those names;
`step` and the fuel loop are generated from the three declarations
(`SURFACE-LANGUAGE-DESIGN.md` §6c). `stepErr` is the one equation each core
writes, and the two cores differ in nothing else.

**Measured** (`python/tests/test_interpreter.py`): `wf5Abs` compiles to
768 atoms and `wf5Omg` to 771, each definition byte-identical to the
paper's hand-written terms (`st5Abs` 684, `st5Omg` 687, `sp5` 166,
`rb5` 81, `q5S` 275, `q5K` 121, `q5I` 107, the two equations 4 and 7, `omega`
6). With the paper's encoder and fuel 20 the T3 table reproduces
exactly: `Err` and `Err K` give ERR under `wf5Abs` and host divergence
under `wf5Omg`; `K I Err` and `I K` give VAL under both, with identical
contraction counts (574 and 438); `Ω` gives TIME under both (10,130).
The base interpreter, `term ≡ S | K | I | App term term`, `maybe ≡
Nothing | Just term`, `whnfF ≔ { step m = sp m nil stepS stepK stepI }`,
compiles to the paper's 618-atom `whnfF` byte for byte, with every
intermediate definition identical (`step` 569, `sp` 126, `rb` 74,
`stepS` 237, `stepK` 105, `stepI` 92), and `whnfF 3 <I K>` reaches weak
head normal form in exactly 340 host contractions, decoding to
`Just <K>`. The `answer` line is measured too: it peels to `RVal` and
decodes to `I` in 574 host contractions at fuel 5, and to `RVal` at fuel
2 as well, since `K I Err` needs one contraction plus the no-redex
check; fuel 1 gives `RTime`.

## 5. A value lookup

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

Inside `< >` the alphabet is `wfN`'s object type `{S, K, I, App, Scry}`;
`/nat/three` is `Cons Nat (Cons Three Nil)`, a value of the declared path
type, quoted like any other datum; `?^` wraps it in `Scry`. The
namespace literal compiles to a resolver that compares the incoming path
against each key with `EQ5` on the encodings, answering `OJust` for the
first match and `ONotYet` otherwise. `wfN resolve` is the blocking loop
applied to that resolver; the `I` equation fires, the walker finds `Scry` in
head position and applies the resolver to the path, and `OJust <K>`
splices and reduction continues to `<K>`. A path with no fact blocks,
and the driver re-runs from the top once the fact is added, which is
sound because the namespace is append-only.

## 6. `whnfF` in SKIjack itself

Two honest versions. The short one leaves the machinery to the compiler:

```
term === S | K | I | App term term
maybe === Nothing | Just term
whnfF := { step m = sp m nil stepS stepK stepI }
```

The long one is the same interpreter with nothing generated, every equation
written in the surface. It is exactly the text the compiler emits for
the short one (`render(generate(parse …))`), so the two are one program;
the Unicode spelling differs only in `≡`, `|`, and `≔`:

```
term === S | K | I | App term term
maybe === Nothing | Just term
whnfF := {
  step m = sp m nil stepS stepK stepI
  loop1 f m n2 = step m (Just m) (f n2)
  loop n m = n Nothing (loop1 loop m)
}
resS acc c0 c1 c2 = c0 acc
resK acc c0 c1 c2 = c1 acc
resI acc c0 c1 c2 = c2 acc
spApp f acc t u = f t (cons u acc)
sp m acc = m (resS acc) (resK acc) (resI acc) (spApp sp acc)
rb1 f h x xs = f (App h x) xs
rb h args = args h (rb1 rb h)
stepI1 x rest = Just (rb x rest)
stepI args = args Nothing stepI1
stepK2 x y rest = Just (rb x rest)
stepK1 x r = r Nothing (stepK2 x)
stepK args = args Nothing stepK1
stepS3 x y z rest = Just (rb (App (App x z) (App y z)) rest)
stepS2 x y r2 = r2 Nothing (stepS3 x y)
stepS1 x r = r Nothing (stepS2 x)
stepS args = args Nothing stepS1
```

Reading it top to bottom: `sp` walks a term to its head leaf, handing
each leaf's continuation the accumulated argument list and pushing each
application's argument onto that list; `rb` re-applies a list of
arguments to a head; each `step` equation takes the argument list, returns
`Nothing` when it has too few arguments (the head is in weak head normal
form), and otherwise performs one contraction as data (`App (App x z)
(App y z)` is the `S` rule) and rebuilds; `step` installs the three equations
in the declaration order of the leaves; `loop` peels one `Suc` per
attempt and returns `Nothing` at `Zero`; `loop1` runs a step and either
returns the current term as the value or continues with the rebuilt one.
`Y` ties `sp`, `rb`, and `loop`, each passing itself to its helper. Only
`nil`, `cons`, `Zero`, `Suc`, and `Y` come from the prelude.

**Measured.** The short program compiles to the paper's 618-atom `whnfF`
byte for byte, with every one of these twenty definitions identical to
the artifact's; `whnfF 3 <I K>` reaches weak head normal form in exactly
340 host contractions. The long program is that compilation rendered
back to source, and compiling it as plain user source with generation
switched off gives the same 618-atom term byte for byte, with `sp`,
`rb`, and the three equations each identical to the hand-written originals,
and T0 at 340 (`python/skijack/corpus/interp-whnff-written.*.ski`, both
spellings). Parsing that file back gives the same tree as generating
from the short source, so the two cannot drift apart.

## 7. What was measured and what was not

Measured, in this order, on the reference expander and reducer:
sections 1 to 4 in full, and the level-1 line of section 3 (29,191
contractions at fuel 41, `Nothing` at 40), T1 (91,556) and T2 (504,930)
from surface source. Section 5 describes the paper's verified
mechanism in the surface's notation and has not been compiled from that
notation; resolver-taking interpreters and the namespace literal are
the next step, after which section 5 becomes a measured statement.
Sections 8 to 10 below were measured in full; their numbers are pinned by
`python/tests/test_examples.py`.


## 8. Words to numbers, two ways

Unicode:
```
nat ≡ Zero | Suc nat
word ≡ One | Two | Three

toNum w = w ▹ { One (Suc Zero); Two (Suc (Suc Zero)); Three (Suc (Suc (Suc Zero))) }
three ≔ toNum Three

term5 ≡ S | K | I | App term5 term5 | Scry
path ≡ Nil | Cons word path
bool ≡ PTrue | PFalse

oanswer ≡ OJust term5 | ONothing | ONotYet
outcome ≡ SteppedN term5 | DoneN | ErrdN | PendingN term5
result ≡ RValN term5 | RErrN | RTimeN | RBlockN term5

pAnd p q = p q PFalse
pKKF = K (K PFalse)
eqApp2P e t u t2 u2 = pAnd (e t t2) (e u u2)
eqApp1P e n t u = n PFalse PFalse PFalse (eqApp2P e t u) PFalse
eqNP e m n = (m (n PTrue  PFalse PFalse pKKF PFalse)
                (n PFalse PTrue  PFalse pKKF PFalse)
                (n PFalse PFalse PTrue  pKKF PFalse)
                (eqApp1P e n)
                (n PFalse PFalse PFalse pKKF PTrue))
EQ5 m = eqNP EQ5 m

scHitN rest v = SteppedN (rb v rest)

wfN e ≔ {
  stepScry1 p rest = e p (scHitN rest) ErrdN (PendingN p)
  stepScry args    = args DoneN (stepScry1 e)
}

nums ≔ ns{/one ↦ <Suc Zero>, /two ↦ <Suc (Suc Zero)>, /three ↦ <Suc (Suc (Suc Zero))>}
n3 ≔ wfN nums ⊢ <∵/three>₁₀
```

ASCII:
```
nat === Zero | Suc nat
word === One | Two | Three

toNum w = w |> { One (Suc Zero); Two (Suc (Suc Zero)); Three (Suc (Suc (Suc Zero))) }
three := toNum Three

term5 === S | K | I | App term5 term5 | Scry
path === Nil | Cons word path
bool === PTrue | PFalse

oanswer === OJust term5 | ONothing | ONotYet
outcome === SteppedN term5 | DoneN | ErrdN | PendingN term5
result === RValN term5 | RErrN | RTimeN | RBlockN term5

pAnd p q = p q PFalse
pKKF = K (K PFalse)
eqApp2P e t u t2 u2 = pAnd (e t t2) (e u u2)
eqApp1P e n t u = n PFalse PFalse PFalse (eqApp2P e t u) PFalse
eqNP e m n = (m (n PTrue  PFalse PFalse pKKF PFalse)
                (n PFalse PTrue  PFalse pKKF PFalse)
                (n PFalse PFalse PTrue  pKKF PFalse)
                (eqApp1P e n)
                (n PFalse PFalse PFalse pKKF PTrue))
EQ5 m = eqNP EQ5 m

scHitN rest v = SteppedN (rb v rest)

wfN e := {
  stepScry1 p rest = e p (scHitN rest) ErrdN (PendingN p)
  stepScry args    = args DoneN (stepScry1 e)
}

nums := ns{/one => <Suc Zero>, /two => <Suc (Suc Zero)>, /three => <Suc (Suc (Suc Zero))>}
n3 := wfN nums |- <?^/three>@10
```

One declaration serves both levels: `word` is the type the case
dispatches on and the segment type the paths are made of. Constructor
names are global, so it could not have been two types.

At level 0, `toNum` is a case on the constructor and compiles to 58 atoms;
`three` is 61 atoms and reaches its numeral in 10 contractions, read back
behaviourally as 3. At level 1 the same three facts as a namespace literal
are 6,691 atoms, the run `n3` is 9,081, and fetching `three` takes 22,280
contractions -- and what comes back is the *encoding* of `Suc (Suc (Suc
Zero))`, `K (S (K (S I)) K ...)`, not a numeral the program can add to.
Same mapping, two orders of magnitude apart. A namespace literal is an
association list: the cheap thing is the declaration, not the lookup.

## 9. Full ASCII as a type, and a digit parser

Unicode:
```
nat ≡ Zero | Suc nat
ascii ≡ C0 | C1 | C2 | C3 | C4 | C5 | C6 | C7 | C8 | C9 | C10 | C11 | C12 | C13 | C14 | C15 | C16 | C17 | C18 | C19 | C20 | C21 | C22 | C23 | C24 | C25 | C26 | C27 | C28 | C29 | C30 | C31 | C32 | C33 | C34 | C35 | C36 | C37 | C38 | C39 | C40 | C41 | C42 | C43 | C44 | C45 | C46 | C47 | C48 | C49 | C50 | C51 | C52 | C53 | C54 | C55 | C56 | C57 | C58 | C59 | C60 | C61 | C62 | C63 | C64 | C65 | C66 | C67 | C68 | C69 | C70 | C71 | C72 | C73 | C74 | C75 | C76 | C77 | C78 | C79 | C80 | C81 | C82 | C83 | C84 | C85 | C86 | C87 | C88 | C89 | C90 | C91 | C92 | C93 | C94 | C95 | C96 | C97 | C98 | C99 | C100 | C101 | C102 | C103 | C104 | C105 | C106 | C107 | C108 | C109 | C110 | C111 | C112 | C113 | C114 | C115 | C116 | C117 | C118 | C119 | C120 | C121 | C122 | C123 | C124 | C125 | C126 | C127
chars ≡ Nil | Cons ascii chars

isDigit c = c ▹ { C0 (K I); C1 (K I); C2 (K I); C3 (K I); C4 (K I); C5 (K I); C6 (K I); C7 (K I); C8 (K I); C9 (K I); C10 (K I); C11 (K I); C12 (K I); C13 (K I); C14 (K I); C15 (K I); C16 (K I); C17 (K I); C18 (K I); C19 (K I); C20 (K I); C21 (K I); C22 (K I); C23 (K I); C24 (K I); C25 (K I); C26 (K I); C27 (K I); C28 (K I); C29 (K I); C30 (K I); C31 (K I); C32 (K I); C33 (K I); C34 (K I); C35 (K I); C36 (K I); C37 (K I); C38 (K I); C39 (K I); C40 (K I); C41 (K I); C42 (K I); C43 (K I); C44 (K I); C45 (K I); C46 (K I); C47 (K I); C48 K; C49 K; C50 K; C51 K; C52 K; C53 K; C54 K; C55 K; C56 K; C57 K; C58 (K I); C59 (K I); C60 (K I); C61 (K I); C62 (K I); C63 (K I); C64 (K I); C65 (K I); C66 (K I); C67 (K I); C68 (K I); C69 (K I); C70 (K I); C71 (K I); C72 (K I); C73 (K I); C74 (K I); C75 (K I); C76 (K I); C77 (K I); C78 (K I); C79 (K I); C80 (K I); C81 (K I); C82 (K I); C83 (K I); C84 (K I); C85 (K I); C86 (K I); C87 (K I); C88 (K I); C89 (K I); C90 (K I); C91 (K I); C92 (K I); C93 (K I); C94 (K I); C95 (K I); C96 (K I); C97 (K I); C98 (K I); C99 (K I); C100 (K I); C101 (K I); C102 (K I); C103 (K I); C104 (K I); C105 (K I); C106 (K I); C107 (K I); C108 (K I); C109 (K I); C110 (K I); C111 (K I); C112 (K I); C113 (K I); C114 (K I); C115 (K I); C116 (K I); C117 (K I); C118 (K I); C119 (K I); C120 (K I); C121 (K I); C122 (K I); C123 (K I); C124 (K I); C125 (K I); C126 (K I); C127 (K I) }
digitValue c = c ▹ { C0 Zero; C1 Zero; C2 Zero; C3 Zero; C4 Zero; C5 Zero; C6 Zero; C7 Zero; C8 Zero; C9 Zero; C10 Zero; C11 Zero; C12 Zero; C13 Zero; C14 Zero; C15 Zero; C16 Zero; C17 Zero; C18 Zero; C19 Zero; C20 Zero; C21 Zero; C22 Zero; C23 Zero; C24 Zero; C25 Zero; C26 Zero; C27 Zero; C28 Zero; C29 Zero; C30 Zero; C31 Zero; C32 Zero; C33 Zero; C34 Zero; C35 Zero; C36 Zero; C37 Zero; C38 Zero; C39 Zero; C40 Zero; C41 Zero; C42 Zero; C43 Zero; C44 Zero; C45 Zero; C46 Zero; C47 Zero; C48 Zero; C49 (Suc Zero); C50 (Suc (Suc Zero)); C51 (Suc (Suc (Suc Zero))); C52 (Suc (Suc (Suc (Suc Zero)))); C53 (Suc (Suc (Suc (Suc (Suc Zero))))); C54 (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))); C55 (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))); C56 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))); C57 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))); C58 Zero; C59 Zero; C60 Zero; C61 Zero; C62 Zero; C63 Zero; C64 Zero; C65 Zero; C66 Zero; C67 Zero; C68 Zero; C69 Zero; C70 Zero; C71 Zero; C72 Zero; C73 Zero; C74 Zero; C75 Zero; C76 Zero; C77 Zero; C78 Zero; C79 Zero; C80 Zero; C81 Zero; C82 Zero; C83 Zero; C84 Zero; C85 Zero; C86 Zero; C87 Zero; C88 Zero; C89 Zero; C90 Zero; C91 Zero; C92 Zero; C93 Zero; C94 Zero; C95 Zero; C96 Zero; C97 Zero; C98 Zero; C99 Zero; C100 Zero; C101 Zero; C102 Zero; C103 Zero; C104 Zero; C105 Zero; C106 Zero; C107 Zero; C108 Zero; C109 Zero; C110 Zero; C111 Zero; C112 Zero; C113 Zero; C114 Zero; C115 Zero; C116 Zero; C117 Zero; C118 Zero; C119 Zero; C120 Zero; C121 Zero; C122 Zero; C123 Zero; C124 Zero; C125 Zero; C126 Zero; C127 Zero }

ten = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))))
add m n = n ▹ { Zero m; Suc k (Suc (add m k)) }
mul m n = n ▹ { Zero Zero; Suc k (add m (mul m k)) }

go acc ds = ds ▹ { Nil acc; Cons d rest (go (add (mul acc ten) (digitValue d)) rest) }
parseDigits ds = go Zero ds

twelve   ≔ parseDigits (Cons C49 (Cons C50 Nil))
fortyTwo ≔ parseDigits (Cons C52 (Cons C50 Nil))
yes ≔ isDigit C55
no  ≔ isDigit C65
```

ASCII:
```
nat === Zero | Suc nat
ascii === C0 | C1 | C2 | C3 | C4 | C5 | C6 | C7 | C8 | C9 | C10 | C11 | C12 | C13 | C14 | C15 | C16 | C17 | C18 | C19 | C20 | C21 | C22 | C23 | C24 | C25 | C26 | C27 | C28 | C29 | C30 | C31 | C32 | C33 | C34 | C35 | C36 | C37 | C38 | C39 | C40 | C41 | C42 | C43 | C44 | C45 | C46 | C47 | C48 | C49 | C50 | C51 | C52 | C53 | C54 | C55 | C56 | C57 | C58 | C59 | C60 | C61 | C62 | C63 | C64 | C65 | C66 | C67 | C68 | C69 | C70 | C71 | C72 | C73 | C74 | C75 | C76 | C77 | C78 | C79 | C80 | C81 | C82 | C83 | C84 | C85 | C86 | C87 | C88 | C89 | C90 | C91 | C92 | C93 | C94 | C95 | C96 | C97 | C98 | C99 | C100 | C101 | C102 | C103 | C104 | C105 | C106 | C107 | C108 | C109 | C110 | C111 | C112 | C113 | C114 | C115 | C116 | C117 | C118 | C119 | C120 | C121 | C122 | C123 | C124 | C125 | C126 | C127
chars === Nil | Cons ascii chars

isDigit c = c |> { C0 (K I); C1 (K I); C2 (K I); C3 (K I); C4 (K I); C5 (K I); C6 (K I); C7 (K I); C8 (K I); C9 (K I); C10 (K I); C11 (K I); C12 (K I); C13 (K I); C14 (K I); C15 (K I); C16 (K I); C17 (K I); C18 (K I); C19 (K I); C20 (K I); C21 (K I); C22 (K I); C23 (K I); C24 (K I); C25 (K I); C26 (K I); C27 (K I); C28 (K I); C29 (K I); C30 (K I); C31 (K I); C32 (K I); C33 (K I); C34 (K I); C35 (K I); C36 (K I); C37 (K I); C38 (K I); C39 (K I); C40 (K I); C41 (K I); C42 (K I); C43 (K I); C44 (K I); C45 (K I); C46 (K I); C47 (K I); C48 K; C49 K; C50 K; C51 K; C52 K; C53 K; C54 K; C55 K; C56 K; C57 K; C58 (K I); C59 (K I); C60 (K I); C61 (K I); C62 (K I); C63 (K I); C64 (K I); C65 (K I); C66 (K I); C67 (K I); C68 (K I); C69 (K I); C70 (K I); C71 (K I); C72 (K I); C73 (K I); C74 (K I); C75 (K I); C76 (K I); C77 (K I); C78 (K I); C79 (K I); C80 (K I); C81 (K I); C82 (K I); C83 (K I); C84 (K I); C85 (K I); C86 (K I); C87 (K I); C88 (K I); C89 (K I); C90 (K I); C91 (K I); C92 (K I); C93 (K I); C94 (K I); C95 (K I); C96 (K I); C97 (K I); C98 (K I); C99 (K I); C100 (K I); C101 (K I); C102 (K I); C103 (K I); C104 (K I); C105 (K I); C106 (K I); C107 (K I); C108 (K I); C109 (K I); C110 (K I); C111 (K I); C112 (K I); C113 (K I); C114 (K I); C115 (K I); C116 (K I); C117 (K I); C118 (K I); C119 (K I); C120 (K I); C121 (K I); C122 (K I); C123 (K I); C124 (K I); C125 (K I); C126 (K I); C127 (K I) }
digitValue c = c |> { C0 Zero; C1 Zero; C2 Zero; C3 Zero; C4 Zero; C5 Zero; C6 Zero; C7 Zero; C8 Zero; C9 Zero; C10 Zero; C11 Zero; C12 Zero; C13 Zero; C14 Zero; C15 Zero; C16 Zero; C17 Zero; C18 Zero; C19 Zero; C20 Zero; C21 Zero; C22 Zero; C23 Zero; C24 Zero; C25 Zero; C26 Zero; C27 Zero; C28 Zero; C29 Zero; C30 Zero; C31 Zero; C32 Zero; C33 Zero; C34 Zero; C35 Zero; C36 Zero; C37 Zero; C38 Zero; C39 Zero; C40 Zero; C41 Zero; C42 Zero; C43 Zero; C44 Zero; C45 Zero; C46 Zero; C47 Zero; C48 Zero; C49 (Suc Zero); C50 (Suc (Suc Zero)); C51 (Suc (Suc (Suc Zero))); C52 (Suc (Suc (Suc (Suc Zero)))); C53 (Suc (Suc (Suc (Suc (Suc Zero))))); C54 (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))); C55 (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))); C56 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))); C57 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))); C58 Zero; C59 Zero; C60 Zero; C61 Zero; C62 Zero; C63 Zero; C64 Zero; C65 Zero; C66 Zero; C67 Zero; C68 Zero; C69 Zero; C70 Zero; C71 Zero; C72 Zero; C73 Zero; C74 Zero; C75 Zero; C76 Zero; C77 Zero; C78 Zero; C79 Zero; C80 Zero; C81 Zero; C82 Zero; C83 Zero; C84 Zero; C85 Zero; C86 Zero; C87 Zero; C88 Zero; C89 Zero; C90 Zero; C91 Zero; C92 Zero; C93 Zero; C94 Zero; C95 Zero; C96 Zero; C97 Zero; C98 Zero; C99 Zero; C100 Zero; C101 Zero; C102 Zero; C103 Zero; C104 Zero; C105 Zero; C106 Zero; C107 Zero; C108 Zero; C109 Zero; C110 Zero; C111 Zero; C112 Zero; C113 Zero; C114 Zero; C115 Zero; C116 Zero; C117 Zero; C118 Zero; C119 Zero; C120 Zero; C121 Zero; C122 Zero; C123 Zero; C124 Zero; C125 Zero; C126 Zero; C127 Zero }

ten = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))))
add m n = n |> { Zero m; Suc k (Suc (add m k)) }
mul m n = n |> { Zero Zero; Suc k (add m (mul m k)) }

go acc ds = ds |> { Nil acc; Cons d rest (go (add (mul acc ten) (digitValue d)) rest) }
parseDigits ds = go Zero ds

twelve   := parseDigits (Cons C49 (Cons C50 Nil))
fortyTwo := parseDigits (Cons C52 (Cons C50 Nil))
yes := isDigit C55
no  := isDigit C65
```

A character is a datum and dispatch on it is one case. The constructors
cost 128 to 379 atoms each (`C127` is a chain of `K`s, `C0` the longest
selector); `isDigit`, a 128-way case to a boolean, is 503 atoms, and
`digitValue`, a 128-way case to a numeral, is 745. `parseDigits` folds a
list of characters most-significant-first with its own `add` (42) and `mul`
(77): `"12"` reads back as 12 in 592 contractions and `"42"` as 42;
`isDigit C55` answers yes and `isDigit C65` no, read by applying the
boolean to two marker atoms.

This is the tokenization half of a parser, which the paper's character
table (section 8.1 of the SKIjack paper) leaves unbuilt: there, a
character resolved by lookup to the term it denotes; here, a character is
cased on and a string of them folds to a value. The other form was
measured so as not to be guessed at: as a namespace, a 26-fact table is
216,673 atoms and looking up its last entry costs 1,012,197 contractions
(82 seconds on the reference reducer). Full ASCII is a type or it is
nothing.

## 10. An event type and a kernel

Unicode:
```
nat ≡ Zero | Suc nat
event ≡ Tick | Poke nat
effect ≡ Log nat
effects ≡ Nil | Cons effect effects

add m n = n ▹ { Zero m; Suc k (Suc (add m k)) }

poke k ev = ev ▹ { Tick [Nil [(2⊑k) (Suc (3⊑k))]]; Poke n [(Cons (Log (3⊑k)) Nil) [(2⊑k) (add (3⊑k) n)]] }
peek k p = 3⊑k
load k old = [(2⊑k) old]

kernel ≔ [[poke [peek load]] Zero]
```

ASCII:
```
nat === Zero | Suc nat
event === Tick | Poke nat
effect === Log nat
effects === Nil | Cons effect effects

add m n = n |> { Zero m; Suc k (Suc (add m k)) }

poke k ev = ev |> { Tick [Nil [(2@k) (Suc (3@k))]]; Poke n [(Cons (Log (3@k)) Nil) [(2@k) (add (3@k) n)]] }
peek k p = 3@k
load k old = [(2@k) old]

kernel := [[poke [peek load]] Zero]
```

The kernel is a door in Arvo's shape (SPEC.md §4.1): a cell
`[battery state]` whose battery holds `poke`, `peek` and `load` at axes 4,
10 and 11. The runtime knows those axes and no names. It pulls an arm by
axis and applies it to the whole kernel, as Nock 9 does: `(4@k) k ev`. An
arm reaches its battery as `2@k` and its state as `3@k`, so `poke` returns
a whole new kernel, `[effects [(2@k) state']]`, without naming itself.

The loop, from the runtime's side, is in `tests/test_examples.py`. The
runtime builds each event from the program's own constructors (`Tick` is
1 atom, `Poke` 8, `Log` 5), pulls `poke` (217 atoms) from the kernel
(300), installs the kernel from the tail of the result, and reads the
effects from its head. `Tick` from state 0 gives state 1 and no effects;
`Poke 5` gives state 6 and `Cons (Log 1) Nil`; `Tick` again gives 7.
`peek` reads 7 through the same pull. `load`, pulled from the first kernel
with an earlier kernel's state, puts the battery over that state, which is
the upgrade path.

The contraction counts are 61, 108 and 135, and they grow. The runtime
installs the kernel as the last poke left it, so the state is an
unreduced application of the one before, and the reference host, which
shares no work, reduces the whole history again on every poke: a `Tick`
costs 34 more contractions per earlier event. The same loop under update
in place (`avon/bench/strategies.py`'s `whnf_share`) costs 61, 66, 63 and
then 63 per `Tick` for as long as it runs. A kernel loop belongs in a
sharing runtime; the reference host's counts for it are conformance data,
not a cost model.
