"""The full language's front end (front1.ascii.ski), checked in Avon.

    python3 -m skijack.selfhost.run1 --avon PATH [--corpus [--expect M]] [--edges]
                                     [--random N] [--random1 N] [--no-fixed-point]
                                     [--templates [--data] [--fix]]

front1 is the self-hosted front end for the whole of SKIjack, built in
milestones (avon docs/WORKLIST.md, Stage 8): M1 cores, macros,
signatures and the Tier 1 birds; M2 interpreter generation; M3
quotation; M4 scries and namespace literals.  Its reference is the
expander with checking off, `skijack.compile(text, check=False)`:
checking only refuses, and never changes a term (DESIDERATA.md item 11),
so the terms of every program the expander accepts are what front1 must
give, hash for hash.  A term holding a name the expander left unresolved,
a free atom, counts as a refusal: Stage B refuses it ("unresolved name").

The comparison is as a map, a name to its term's §5 hash: Python's
output order follows dict insertion, which is not normative
(skijack/abi.py).  front1 may print a name twice, a core equation's bare
name after a top-level name of the same spelling; the later line wins,
as the later assignment does in expand.py.

- `--corpus`: every program in python/skijack/corpus, reporting which
  agree; `--expect M` fails unless milestone M's programs all agree.
- `--edges`: run0's edge programs and each milestone's, against the full
  reference; where aviary's environment decides (AVIARY), the difference
  is M5's.
- `--random N`: run0's random SKIjack-0 programs.
- `--random1 N`: random programs of the full language: macros, cores,
  birds, object types and their interpreter cores, datums and level-1
  runs.
- The fixed point: front1 compiling its own source.
"""

from __future__ import annotations

import argparse
import functools
import pathlib
import random
import subprocess
import sys
import tempfile
import time
from typing import Dict, List, Optional, Tuple

from aviary_kernel.abstraction import ExpansionError
from aviary_kernel.terms import Atom
from aviary_kernel.environment import DefinitionError

import skijack
from skijack.dictionary import structural_hash
from skijack.errors import SkijackError
from skijack.export import jam
from skijack.templates import templates, write as write_templates, write_words

from .run0 import Deep, EDGES, TERMS, _H

HERE = pathlib.Path(__file__).resolve().parent
FRONT = HERE / "front1.ascii.ski"
CORPUS = HERE.parent / "corpus"

#: the corpus programs each milestone brings to agreement, cumulatively
MILESTONES = {
    "M0": ("ascii-digits", "kernel-events"),
    "M1": ("sec1-nat", "sec2-c", "sec3-swap"),
    "M2": ("interp-whnff", "interp-whnff-written", "interp-whnff-written-loop",
           "interp-t3", "scry-wfn"),
    "M3": ("level1-flipa", "tower", "scry-wfq"),
    "M4": ("scry-ns", "scry-block", "parse-chars", "words-to-numbers"),
}

#: edges where aviary's environment, under the expander, decides: it
#: refuses a binder named as a defined name or a built-in, a binder twice
#: and a recursion's name rebound, and reads a binder named as a later
#: definition as the definition.  front1 takes each binder as a binder.
#: Stage A does not classify these; they are M5's (refusal parity)
AVIARY = frozenset((
    "a binder named as an equation", "an equation's own name its binder",
    "a lambda shadowing a recursion", "a branch shadowing a recursion",
    "a binder twice", "a lambda capturing a binder twice", "a member shadowed",
    "a bird bound", "natAdd a binder", "a macro's binders twice",
    "a binder named as a later definition", "a definition named as a generated binder"))

#: identity macros: m_k makes 2^(k+1) - 1 substitutions and leaves its
#: argument, so a sum of them meets the 200,000-substitution limit exactly
_ID = "m0 x :=* x\n" + "".join(f"m{i+1} x :=* m{i} (m{i} x)\n" for i in range(16))
_WORK = "m16 (m15 (m10 (m9 (m7 (m5 (m1 (m0 (m0 Zero))))))))"   # 199,999

#: M1's edges: cores, macros, signatures, the birds, the numeral operations
EDGES1: Dict[str, str] = {
    # signatures, and the tokens around them
    "a signature": _H + "succ : nat -> nat\nf := Suc\n",
    "a signature of one type": _H + "z : nat\nf := Zero\n",
    "a signature of two names": _H + "f g : nat\nf := Zero\n",
    "a signature's arrow at the end": _H + "f : nat ->\n",
    "an arrow outside a signature": _H + "f x = x -> x\n",
    "a colon alone": _H + "f := Zero :\n",
    "a star alone": _H + "f := * Zero\n",
    "a bang alone": _H + "f := ! Zero\n",
    "a minus alone": _H + "f := - Zero\n",
    # the birds
    "each bird": _H + "fB := B\nfC := C\nfW := W\nfY := Y\n",
    "a bird applied": _H + "f x = B Suc Suc x\n",
    "an equation named C": _H + "C f x y = f y x\ng x y = C K x y\n",
    "a definition named Y": _H + "Y := Zero\nf := Y\n",
    "a bird bound": _H + "f W = W\n",
    "a recursion beside Y": _H + "f n = n |> { Zero Zero ; Suc k (f k) }\ng := Y f\n",
    # macros
    "a macro": _H + "twice f x :=* f (f x)\ng := twice Suc Zero\n",
    "a macro of no parameters": _H + "z :=* Zero\nf := Suc z\n",
    "a macro applied past its parameters": _H + "id x :=* x\nf := id Suc Zero\n",
    "a macro partly applied": _H + "two f x :=* f x\ng := two Suc\n",
    "a macro of parameters bare": _H + "two f x :=* f x\ng := two\n",
    "a capturing macro used": _H + "m x :=! x\ng := m Zero\n",
    "a capturing macro unused": _H + "m x :=! x\ng := Zero\n",
    "a capturing macro bare, no parameters": _H + "m :=! Zero\ng := m\n",
    "a macro redefined": _H + "m :=* Zero\nm :=* Suc Zero\ng := m\n",
    "a macro named as an equation": _H + "f x = x\nf :=* Zero\ng := f\nh x = f\n",
    "a macro using a macro": _H + "a x :=* Suc x\nb x :=* a (a x)\ng := b Zero\n",
    "a macro's free name, the use site's": _H + "m :=* y\nf y = m\n",
    "a macro's free name, unbound": _H + "m :=* y\nf x = m\n",
    "a binder named as a later definition": _H + "f g = g\ng := Zero\n",
    "a macro's lambda capture avoided": _H + "m x :=* \\y. x y\nf y = m y\n",
    "a macro's case capture avoided": _H + "m x :=* \\n. n |> { Zero x ; Suc k x }\nf k = m k\n",
    "a macro's lambda, no capture": _H + "m x :=* \\y. y x\nf z = m z\n",
    "a macro's binders twice": _H + "m x :=* \\y. \\y. x\nf z = m z\n",
    "a macro's parameter twice": _H + "m x x :=* x\nf := m Zero (Suc Zero)\n",
    "a lambda hiding a macro": _H + "m :=* Zero\nf := \\m. m\n",
    "a branch hiding a macro": _H + "m :=* Zero\nf n = n |> { Zero m ; Suc m m }\n",
    "a binder not hiding a macro": _H + "m :=* Zero\nf m = m\n",
    "a macro in a cell": _H + "m x :=* [x x]\nf y = 2@(m y)\n",
    "a macro in a pick": _H + "m x :=* 3@x\nf y = m [y y y]\n",
    "a macro inside a case": _H + "m x :=* Suc x\nf n = n |> { Zero (m Zero) ; Suc k (m k) }\n",
    "a macro's argument a macro": _H + "s x :=* Suc x\nf := s (s Zero)\n",
    "a macro unfolding forever": _H + "m :=* m\nf := m\n",
    "a macro unfolding 100 deep": _H + "".join(f"m{i} :=* Suc m{i+1}\n" for i in range(99)) + "m99 :=* Zero\nf := m0\n",
    "a macro unfolding 101 deep": _H + "".join(f"m{i} :=* Suc m{i+1}\n" for i in range(100)) + "m100 :=* Zero\nf := m0\n",
    "a macro doubling to depth 256": _H + "m0 x :=* Suc x\n" + "".join(f"m{i+1} x :=* m{i} (m{i} x)\n" for i in range(8)) + "f := m8 Zero\n",
    "199,999 substitutions": _H + _ID + "f := " + _WORK + "\n",
    "200,000 substitutions": _H + _ID + "f := m0 (" + _WORK + ")\n",
    "200,000 substitutions over two bodies": _H + _ID + "f := " + _WORK + "\ng := m0 (m0 Zero)\n",
    "nesting 256 deep": _H + "f x = " + "(Suc " * 256 + "x" + ")" * 256 + "\n",
    "nesting 257 deep": _H + "f x = " + "(Suc " * 257 + "x" + ")" * 257 + "\n",
    "a long spine": _H + "f x = x" + " x" * 300 + "\n",
    # cores
    "a core": _H + "c := {\n  a x = Suc x\n  b x = a (a x)\n}\n",
    "a core with parameters": _H + "c p q := {\n  a x = p x\n  b = a q\n}\n",
    "a core on one line": _H + "c := { a x = x }\n",
    "an empty core": _H + "c := {\n}\n",
    "a core's recursion": _H + "c := {\n  f n = n |> { Zero Zero ; Suc k (f k) }\n}\n",
    "a core's mutual pair": _H + "c := {\n  ev n = n |> { Zero Yes ; Suc k (od k) }\n  od n = n |> { Zero No ; Suc k (ev k) }\n}\n",
    "a core calling the top": _H + "t x = Suc x\nc := {\n  a x = t x\n}\n",
    "the top calling a core": _H + "c := {\n  a x = x\n}\nt x = a x\n",
    "a core's name and the top's": _H + "a x = Zero\nc := {\n  a x = Suc x\n  b x = a x\n}\ng := a\n",
    "two cores, one name": _H + "c := {\n  a x = x\n}\nd := {\n  a x = Suc x\n}\n",
    "a core twice": _H + "c := {\n  a x = x\n}\nc := {\n  b x = x\n}\n",
    "an equation twice in a core": _H + "c := {\n  a x = x\n  a y = y\n}\n",
    "a core's sibling shadowed": _H + "c := {\n  a x = x\n  b a = a\n}\n",
    "a definition in a core": _H + "c := {\n  a x = x\n  b := Zero\n}\n",
    "a core's sibling under a lambda": _H + "c := {\n  a x = x\n  b y = \\a. a y\n}\n",
    "a core's parameter shadowing a sibling": _H + "c a := {\n  a x = x\n  b x = a x\n}\n",
    "a core's loop": _H + "c := {\n  loop x = Suc x\n}\nf := c Zero\n",
    "a core's loop and a top name": _H + "c := Zero\nc := {\n  loop x = Suc x\n}\n",
    "a core's equation named pair": _H + "c := {\n  pair x y = x\n  f x = [x x]\n}\n",
    "a core's equation named S": _H + "c := {\n  S x = x\n  f x = S x\n}\n",
    "a core's binder S": _H + "c S := {\n  f x = x\n}\n",
    "a core's binder S, no equations": _H + "c S := {\n}\n",
    "a core with a macro": _H + "m x :=* Suc x\nc := {\n  a x = m x\n}\n",
    "a core with a signature inside": _H + "c := {\n  a : nat\n  a x = x\n}\n",
    "a core not closed": _H + "c := {\n  a x = x\n",
    "a core's brace then text": _H + "c := {\n  a x = x\n} f\n",
    "a core across a case": _H + "c := {\n  a x = x |> {\n Zero Zero ;\n Suc k k }\n}\n",
    "a core, a newline before its brace": _H + "c :=\n{\n  a x = x\n}\n",
    "a mutual pair across a core": _H + "t n = n |> { Zero Yes ; Suc k (c.a k) }\nc := {\n  a n = n |> { Zero No ; Suc k (t k) }\n}\n",
    "a recursion through a core": _H + "t n = n |> { Zero Yes ; Suc k (u k) }\nu n = t n\nc := {\n  a n = t n\n}\n",
    # the numeral operations
    "natAdd": _H + "f := natAdd\n",
    "natSub": _H + "f := natSub\n",
    "natMul": _H + "f := natMul\n",
    "natIfEq": _H + "f := natIfEq\n",
    "natIfLe": _H + "f := natIfLe\n",
    "all five": _H + "f := [natAdd natSub natMul natIfEq natIfLe]\n",
    "natAdd defined": _H + "natAdd x = x\nf := natAdd\n",
    "natAdd defined, natMul named": _H + "natAdd x = x\nf := natMul\n",
    "natAdd a constructor": "nat === Zero | Suc nat\nop === natAdd\nf := natMul\n",
    "natAdd a binder": _H + "f natAdd = natAdd\n",
    "natAdd in a macro": _H + "m :=* natAdd\n",
    "suc redefined, natAdd": _H + "suc x = x\nf := natAdd\n",
    "natAdd a core's equation": _H + "c := {\n  natAdd x = x\n}\nf := natSub\ng := natAdd\n",
}


_T = "term === S | K | I | App term term\n"
_M = "maybe === Nothing | Just term\n"
_C = "c := {\n  step m = sp m nil stepS stepK stepI\n}\n"
#: M2's edges: object types, loop types, interpreter cores, generated names
EDGES2: Dict[str, str] = {
    # finding the object type and the loop's types
    "an object type alone": _T,
    "an object type and an outcome": _T + _M,
    "two object types": _T + "tm === A | B | Ap tm tm\n" + _M,
    "two application constructors": "term === S | App term term | Ap term term\n" + _M,
    "an object type with a field": "term === S | V nat | App term term\nnat === Zero | Suc nat\n" + _M,
    "an object type of leaves A and B": "term === A | B | App term term\n" + _M,
    "an application of one field": "term === S | App term\n" + _M,
    "an outcome of one constructor": _T + "one === Just term\n",
    "an outcome and a result": _T + "outcome === Stepped term | Done | Errd\nresult === RVal term | RErr | RTime\n",
    "an outcome and a result of other sizes": _T + "outcome === Stepped term | Done\nresult === RVal term | RErr | RTime\n",
    "a result without a leaf": _T + "outcome === Stepped term | Done\nresult === RVal term | RV2 term\n",
    "an outcome without a leaf": _T + "outcome === Stepped term | Pend term\nresult === RVal term | RTime\n",
    "a payload mapped": _T + "outcome === Stepped term | Done | Pend term\nresult === RVal term | RTime | RBlock term\n",
    "a payload unmatched": _T + "outcome === Stepped term | Done | Pend term\nresult === RVal term | RBlock term | RTime\n",
    "no spare leaf": _T + "outcome === Stepped term | Done | Errd | Odd\nresult === RVal term | RErr | RTime | RX term\n",
    "three outcome-shaped types": _T + "ans === OJust term | ONo\n" + "outcome === Stepped term | Done | Errd\nresult === RVal term | RErr | RTime\n",
    "an outcome carrying two terms": _T + "pr === Two term term | None\n" + _M,
    # interpreter cores
    "a core writing step": _T + _M + _C,
    "a core writing loop": _T + _M + "c := {\n  loop n m = n Nothing (\\x. Just m)\n}\n",
    "a core writing loop1 alone": _T + _M + "c := {\n  loop1 f m n2 = m\n}\n",
    "a core writing a leaf's step": _T + _M + "c := {\n  stepS args = args Nothing (\\x. Nothing)\n}\n",
    "a core writing the application's step": _T + _M + "c := {\n  stepApp args = args\n}\n",
    "a core writing neither": _T + _M + "c := {\n  other m = m\n}\n",
    "a core with parameters writing a step": _T + _M + "c p := {\n  stepI args = p args\n}\n",
    "an interpreter core's name applied": _T + _M + _C + "g1 := c (Suc Zero) S\nnat === Zero | Suc nat\n",
    "two interpreter cores": _T + _M + _C + "d := {\n  stepK args = args Nothing (\\x. Nothing)\n}\n",
    # the program's own names first
    "the program's sp": _T + _M + "sp m acc = m\n",
    "the program's rb, a macro": _T + _M + "rb h args :=* h\n",
    "the program's stepI": _T + _M + "stepI args = args\n",
    "a constructor named sp": _T + _M + "w === sp | rb\n",
    "a definition named resS": _T + _M + "resS := S\n",
    "a macro named as a binder": _T + _M + "x :=* K\n",
    "a macro named acc": _T + _M + "acc :=* I\n",
    "a macro named nil": _T + _M + _C + "nil :=* K\n",
    "eleven leaves": "term === L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9 | L10 | App term term\n" + _M,
    "twelve leaves, a macro c10": "term === L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9 | L10 | L11 | App term term\n" + _M + "c10 :=* K\n",
    "a core loop and a top loop": _T + _M + _C + "loop := I\n",
    "a core named as a definition": _T + _M + "c := I\n" + _C,
    "a definition named as a generated binder": _T + _M + "r := K\n",
}

_Q = ("term === S | K | I | App term term\nmaybe === Nothing | Just term\nnat === Zero | Suc nat\n"
      "whnfF := {\n  step m = sp m nil stepS stepK stepI\n}\n")
_QE = ("term === S | K | I | App term term | Err\noutcome === Stepped term | Done | Errd\n"
      "result === RVal term | RErr | RTime\nnat === Zero | Suc nat\n")
#: M3's edges: datums, nesting, level-1 runs, what a quotation may name
EDGES3: Dict[str, str] = {
    "a datum": _Q + "d := <K I>\n",
    "a datum of a lambda": _Q + "d := <\\x. x K>\n",
    "a datum of a case": _Q + "d := <\\n. n |> { Zero K ; Suc k I }>\n",
    "a datum of a cell": _Q + "d := <[K I S]>\n",
    "a datum of a level-0 name": _Q + "g1 x = Suc x\nd := <g1>\n",
    "a datum of a datum before": _Q + "b := <K>\na := <b>\n",
    "a datum of a datum after": _Q + "a := <b>\nb := <K>\n",
    "a datum of itself": _Q + "d := <d>\n",
    "a datum through a definition, after": _Q + "g := d\nq := <g>\nd := <K>\n",
    "a datum through a definition, before": _Q + "g := d\nd := <K>\nq := <g>\n",
    "a datum of a level-1 run": _Q + "r := <K I>@3\nd := <r>\n",
    "a level-0 name of a datum after": _Q + "g := d\nd := <K I>\n",
    "a level-0 name of a level-1 run": _Q + "g := r\nr := <K I>@3\n",
    "a nested quotation": _Q + "d := <K <I>>\n",
    "a nested quotation, deeper": _Q + "d := <K <I <S>>>\n",
    "a nested quotation's binder": _Q + "d := <\\x. <x>>\n",
    "a nested quotation with fuel": _Q + "d := <K <I>@2>\n",
    "a nested quotation with an interpreter": _Q + "d := <K (whnfF |- <I>)>\n",
    "a quotation in an equation": _Q + "f x = <x>\n",
    "a quotation applied": _Q + "d := <K> I\n",
    "a quotation in a macro, used": _Q + "mq :=* <K>\nd := mq\n",
    "a quotation in a macro, unused": _Q + "mq :=* <K>\nd := <I>\n",
    "a macro inside a quotation": _Q + "mq x :=* x K\nd := <mq I>\n",
    "a macro hidden inside a quotation": _Q + "mq :=* K\nd := <\\mq. mq>\n",
    "a macro inside a nested quotation under its binder": _Q + "mq :=* K\nd := <\\mq. <mq>>\n",
    "a leaf named as a binder": _Q + "d := <\\S. S>\n",
    "a level-1 run": _Q + "r := <K I>@3\n",
    "a level-1 run, fuel 0": _Q + "r := <K I>@0\n",
    "a level-1 run, fuel 12": _Q + "r := <S K K I>@12\n",
    "a level-1 run, fuel elided": _Q + "r := <K I>@[]\n",
    "a level-1 run, interpreter named": _Q + "r := whnfF |- <K I>@2\n",
    "a level-1 run, interpreter without fuel": _Q + "r := whnfF |- <K I>\n",
    "a level-1 run, no whnfF": "term === S | K | I | App term term\nmaybe === Nothing | Just term\nnat === Zero | Suc nat\nr := <K I>@3\n",
    "a level-1 run, an unknown interpreter": _Q + "r := foo |- <K I>@3\n",
    "a level-1 run, an interpreter without a loop": _Q + "c := {\n  q x = x\n}\nr := c |- <K I>@3\n",
    "an interpreter with a parameter": _QE + "w e := {\n  stepErr acc = e\n}\nr := w Errd |- <K Err>@4\n",
    "an interpreter missing its parameter": _QE + "w e := {\n  stepErr acc = e\n}\nr := w |- <K Err>@4\n",
    "an interpreter with a datum parameter": _QE + "w e := {\n  stepErr acc = e\n}\nd := <Err>\nr := w (Stepped d) |- <K Err>@4\n",
    "a leaf Err": _QE + "d := <K Err>\n",
    "an ISA name with no leaf of it": "term === A | B | App term term\nmaybe === Nothing | Just term\nd := <A S>\n",
    "a quotation without an object type": "nat === Zero | Suc nat\nd := <K>\n",
    "zero redefined, a level-1 run": _Q + "zero := Suc Zero\nr := <K>@2\n",
    "suc redefined, a level-1 run": _Q + "suc x = x\nr := <K>@2\n",
    "two answer types": _Q + "a1 === A1 term | A0\na2 === B1 term | B0\nd := <K>\n",
    "a path type misshapen": _Q + "path === Nil | Cons nat\nd := <K>\n",
    "a path type": _Q + "seg === Nat | Two\npath === Nil | Cons seg path\nd := <K>\n",
    "a core equation named as a datum": _Q + "c := {\n  d x = x\n}\nd := <K>\n",
    "a core named as a datum, with a loop": _Q + "d := {\n  loop n m = m\n}\nd := <K>\n",
    "a fuel token after a newline": _Q + "r := (<K>\n@3)\n",
    "a fuel token alone": _Q + "f := Zero @3\n",
    "a turnstile alone": _Q + "f := K |- I\n",
    "a quotation across lines": _Q + "d := <K\n I>\n",
    "a newline before its close": _Q + "d := <K I\n>\n",
}

_P = (CORPUS / "scry-ns.ascii.ski").read_text()
_B = _P[:_P.index("resolve := ")]          # scry-ns's types, EQ5 and wfN
_NOP = _B.replace("path === Nil | Cons seg path\n", "")
_NOEQ = _B.replace("EQ5 m = eqNP EQ5 m\n", "")
#: M4's edges: scries, paths, namespace literals, their tokens
EDGES4: Dict[str, str] = {
    "a scry quoted": _B + "qz := <?^/nat/three>\n",
    "a scry of two segments and a cell": _B + "qz := <[?^/nat ?^/two/three]>\n",
    "a scry unquoted": _B + "qz := ?^/nat\n",
    "a scry in an equation": _B + "fz x = ?^/nat\n",
    "a scry with a payload": _B + "qz := <?^/nat[K]/two>\n",
    "a scry of an unknown segment": _B + "qz := <?^/four>\n",
    "a scry of a constructor of another type": _B + "qz := <?^/pTrue>\n",
    "a scry of a capital tag": _B + "qz := <?^/Nat>\n",
    "a scry without a path type": _NOP + "qz := <?^/nat>\n",
    "a scry without a Scry leaf": _B.replace("| Scry\n", "\n").replace("stepScry1 p rest = e p (scHitN rest) ErrdN (PendingN p)\n  stepScry args    = args DoneN (stepScry1 e)\n", "stepI args = args DoneN DoneN\n") + "qz := <?^/nat>\n",
    "a scry nested": _B + "qz := <K <?^/nat>>\n",
    "a scry without a slash": _B + "qz := <?^nat>\n",
    "a scry, a newline before a slash": _B + "qz := <?^/nat\n/two>\n",
    "a scry, a newline after a slash": _B + "qz := <?^/\nnat>\n",
    "a scry, a newline before a cell": _B + "qz := <K ?^/nat\n[K I]>\n",
    "a scry, a cell after": _B + "qz := <K ?^/nat [K I]>\n",
    "a scry run": _B + "rz := wfN (\\p. ONotYet) |- <?^/nat/three>@10\n",
    "a literal": _B + "rz := ns{/nat/two => <I>}\n",
    "an empty literal": _B + "rz := ns{}\n",
    "a literal of three facts": _B + "rz := ns{/nat => <I>, /two => <K>, /three/nat => <S K>}\n",
    "a literal used": _B + "rz := ns{/nat => <I>}\naz := wfN rz |- <?^/nat>@10\n",
    "a literal used before it": _B + "az := wfN rz |- <?^/nat>@10\nrz := ns{/nat => <I>}\n",
    "a literal quoted after": _B + "rz := ns{/nat => <I>}\nqz := <rz>\n",
    "a literal quoted before": _B + "qz := <rz>\nrz := ns{/nat => <I>}\n",
    "a literal's value a datum before": _B + "dz := <K>\nrz := ns{/nat => <dz>}\n",
    "a literal's value a datum after": _B + "rz := ns{/nat => <dz>}\ndz := <K>\n",
    "a literal's value not quoted": _B + "rz := ns{/nat => I}\n",
    "a literal's value with fuel": _B + "rz := ns{/nat => <I>@3}\n",
    "a literal's key with a payload": _B + "rz := ns{/nat[K] => <I>}\n",
    "a literal without EQ5": _NOEQ + "rz := ns{/nat => <I>}\n",
    "a literal without an answer type": _B.replace("oanswer === OJust term5 | ONothing | ONotYet\n", "") + "rz := ns{/nat => <I>}\n",
    "a literal, EQ5 a datum before": _NOEQ + "EQ5 := <K>\nrz := ns{/nat => <I>}\n",
    "a literal, EQ5 a datum after": _NOEQ + "rz := ns{/nat => <I>}\nEQ5 := <K>\n",
    "a literal, EQ5 a definition": _NOEQ + "EQ5 := K\nrz := ns{/nat => <I>}\n",
    "a literal, EQ5 naming a datum": _NOEQ + "dz := <K>\nEQ5 := dz\nrz := ns{/nat => <I>}\n",
    "a literal, EQ5 a core's equation": _NOEQ + "cz := {\n  EQ5 m = m\n}\nrz := ns{/nat => <I>}\n",
    "a literal, OJust a core's equation": _B + "cz := {\n  OJust m = m\n}\nrz := ns{/nat => <I>}\n",
    "a literal inside a quotation": _B + "qz := <ns{/nat => <I>}>\n",
    "a literal in an equation": _B + "fz x = ns{/nat => <I>}\n",
    "a literal across lines": _B + "rz := ns{/nat => <I>,\n/two => <K>}\n",
    "a literal, a newline first": _B + "rz := ns{\n/nat => <I>}\n",
    "a literal, a newline before its brace": _B + "rz := ns{/nat => <I>\n}\n",
    "a literal with a trailing comma": _B + "rz := ns{/nat => <I>,}\n",
    "ns, a name": _B + "ns := K\nqz := ns\n",
    "ns, a name before a brace": _B + "cz := {\n  f ns = ns\n}\n",
    "a fact arrow alone": _B + "fz := K => I\n",
    "a comma alone": _B + "fz := K , I\n",
    "a slash alone": _B + "fz := K / I\n",
    "a caret alone": _B + "fz := ^K\n",
    "a question mark alone": _B + "fz := ?K\n",
}


def _program1(rng: random.Random) -> str:
    """A random M1 program: macros, cores and equations over three types.
    Binder names come from a small pool, so that substitution must rename
    and binders hide macros; core equations share names across cores and
    with the top level, so that siblings and bare names are exercised."""
    lines = ["nat === Zero | Suc nat", "bool === Yes | No", "tr === Leaf | Node tr nat tr"]
    ctors = {"nat": [("Zero", 0), ("Suc", 1)], "bool": [("Yes", 0), ("No", 0)],
             "tr": [("Leaf", 0), ("Node", 3)]}
    tops = [f"e{i}" for i in range(rng.randint(1, 4))]
    macros: Dict[str, int] = {}
    pool = ["u", "v", "w"]

    def expr(scope, calls, depth):
        r = rng.random()
        if depth <= 0 or r < 0.2:
            atoms = list(scope) + ["S", "K", "I", "Zero", "Yes", "Leaf", "pair", "B", "C"]
            atoms += [m for m, k in macros.items() if k == 0 and m in calls]
            return rng.choice(atoms)
        if r < 0.45:
            f = rng.choice(calls + ["Suc", "Node", "pair", "W"])
            n = macros.get(f, rng.randint(1, 2))
            n += rng.random() < 0.2
            near = [q for q in scope if q in pool]
            args = " ".join(f"({rng.choice(near) if near and rng.random() < 0.5 else expr(scope, calls, depth - 1)})"
                            for _ in range(n))
            return f"{f} {args}".strip()
        if r < 0.58:
            t = rng.choice(list(ctors))
            branches = []
            for c, k in ctors[t]:
                bs = rng.sample(pool, k) if rng.random() < 0.5 else [f"b{depth}{c.lower()}{j}" for j in range(k)]
                branches.append(f"{c} {' '.join(bs)} ({expr(scope + bs, calls, depth - 1)})".replace("  ", " "))
            return f"({expr(scope, calls, depth - 1)}) |> {{ {' ; '.join(branches)} }}"
        if r < 0.72:
            q = rng.choice(pool + [f"l{depth}"] + (list(macros)[:1] if rng.random() < 0.1 else []))
            return f"(\\{q}. {expr(scope + [q], calls, depth - 1)})"
        if r < 0.8:
            return "[" + " ".join(f"({expr(scope, calls, depth - 1)})" for _ in range(rng.randint(2, 3))) + "]"
        if r < 0.88:
            return f"{rng.randint(1, 7)}@({expr(scope, calls, depth - 1)})"
        return f"({expr(scope, calls, depth - 1)}) ({expr(scope, calls, depth - 1)})"

    for i in range(rng.randint(1, 4)):
        ps = ["x", "y"][: rng.randint(0, 2)]
        body = expr(ps, tops + list(macros), 3)
        if ps and rng.random() < 0.6:            # a binder over a parameter: capture
            q = rng.choice(pool)
            body = rng.choice([f"\\{q}. {ps[0]} ({body})",
                               f"{ps[-1]} |> {{ Zero ({ps[0]}) ; Suc {q} ({ps[0]} {q}) }}"])
        macros[f"m{i}"] = len(ps)
        lines.append(f"m{i} {' '.join(ps)} :=* {body}".replace("  ", " "))
    calls = tops + list(macros)
    cores = []
    for k in range(rng.randint(0, 2)):
        params = [f"cp{k}"] if rng.random() < 0.5 else []
        eqs = rng.sample(["q0", "q1", "loop", tops[0]], rng.randint(1, 3))
        body = []
        for e in eqs:
            bs = rng.sample(pool, rng.randint(0, 2)) if rng.random() < 0.5 else [f"{e}x{j}" for j in range(rng.randint(0, 2))]
            body.append(f"  {e} {' '.join(bs)} = {expr(params + bs, calls + eqs, 3)}".replace("  =", " =").replace("   ", "  "))
        lines.append(f"c{k} {' '.join(params)} := {{".replace("  ", " "))
        lines.extend(body)
        lines.append("}")
        if "loop" in eqs:
            cores.append(f"c{k}")
    for n in tops:
        bs = rng.sample(pool, rng.randint(0, 2)) if rng.random() < 0.5 else [f"{n}x{j}" for j in range(rng.randint(1, 3))]
        lines.append(f"{n} {' '.join(bs)} = {expr(bs, calls + cores, 4)}".replace("  =", " ="))
    lines.append(f"d0 := {expr([], calls + cores, 3)}")
    return "\n".join(lines) + "\n"


#: object types, their loop's types and interpreter cores, for _program2
_OBJECTS = ["term === S | K | I | App term term",
            "term === S | K | I | App term term | Err",
            "term === A | B | App term term"]
_OUTCOMES = [["maybe === Nothing | Just term"],
             ["outcome === Stepped term | Done | Errd", "result === RVal term | RErr | RTime"],
             ["outcome === Stepped term | Done | Pend term",
              "result === RVal term | RTime | RBlock term"]]
_CORES = ["ci := {\n  step m = sp m nil stepS stepK stepI\n}",
          "ci p := {\n  stepS args = p args\n}",
          "ci := {\n  stepK args = args Nothing (\\x. Nothing)\n  loop n m = n Nothing (\\k. Just m)\n}",
          "ci := {\n  stepErr acc = Errd\n}"]


def _program2(rng: random.Random) -> str:
    """A random program of the full language so far: _program1's, and
    usually an object type, its loop's types, perhaps an interpreter core,
    and datums and level-1 runs quoting the program's names, the object
    type's leaves, lambdas and nested quotations."""
    lines = _program1(rng).rstrip("\n").split("\n")
    if rng.random() < 0.3:
        return "\n".join(lines) + "\n"
    obj = rng.choice(_OBJECTS)
    extra = [obj] + rng.choice(_OUTCOMES)
    if rng.random() < 0.5:
        extra.append(rng.choice(_CORES))
    whnf = obj == _OBJECTS[0] and rng.random() < 0.6
    if whnf:
        extra.append("whnfF := {\n  step m = sp m nil stepS stepK stepI\n}")
    lines[3:3] = extra
    leaves = obj.split("===")[1].replace("| App term term", "").replace("|", " ").split()
    tops = [l.split()[0] for l in lines if l.startswith("e") and " = " in l]
    datums: List[str] = []

    # binders are fresh, as a binder twice in one chain is aviary's refusal
    # (AVIARY); a nested quotation names no datum, as each level of quoting
    # multiplies a datum's size
    def qexpr(scope, depth, outer=True):
        r = rng.random()
        if depth <= 0 or r < 0.35:
            pool = list(scope) + leaves + tops + ["S", "K", "I"]
            if outer:
                pool += datums
                if rng.random() < 0.05:
                    pool.append(f"qd{len(datums) + 1}")      # a datum not yet declared
            return rng.choice(pool)
        if r < 0.65:
            return f"({qexpr(scope, depth - 1, outer)}) ({qexpr(scope, depth - 1, outer)})"
        if r < 0.8:
            q = f"u{len(scope)}"
            return f"(\\{q}. {qexpr(scope + [q], depth - 1, outer)})"
        if r < 0.9:
            return f"<{qexpr([], depth - 1, False)}>"
        return f"[({qexpr(scope, depth - 1, outer)}) ({qexpr(scope, depth - 1, outer)})]"

    for i in range(rng.randint(1, 3)):
        lines.append(f"qd{i} := <{qexpr([], 3)}>")
        datums.append(f"qd{i}")
        if whnf and rng.random() < 0.5:
            fuel = rng.choice(["@0", "@3", "@7", "@[]", ""])
            interp = "whnfF |- " if rng.random() < 0.3 or not fuel else ""
            lines.append(f"lr{i} := {interp}<{qexpr([], 2)}>{fuel}")
    return "\n".join(lines) + "\n"


def aviary_refuses(text: str) -> bool:
    """Whether the expander's refusal is aviary's environment's (AVIARY)."""
    try:
        with Deep():
            skijack.compile(text, lexicon="ascii", check=False)
    except (DefinitionError, ExpansionError):
        return True
    except SkijackError:
        return False
    return False


Result = Optional[Dict[str, str]]


@functools.lru_cache(maxsize=1)
def expansion():
    with Deep():
        return skijack.compile(FRONT.read_text(), lexicon="ascii")


@functools.lru_cache(maxsize=1)
def term_dir() -> pathlib.Path:
    d = pathlib.Path(tempfile.mkdtemp(prefix="front1-"))
    t = expansion().terms
    for name in TERMS:
        (d / f"{name}.skit").write_bytes(jam(t[name]))
    with Deep():
        write_templates(templates(expansion()), d / "templates.tsv", d / "template_terms.tsv")
        write_words(expansion(), d / "words.tsv")
    return d


def run_avon(avon: str, text: str, extra: Tuple[str, ...] = ()) -> Tuple[str, Result]:
    """front1's contraction count and its map from names to hashes (None if
    it refused), the later of two lines for one name winning."""
    with tempfile.NamedTemporaryFile("w", suffix=".ski", delete=False) as f:
        f.write(text)
    try:
        p = subprocess.run([avon, "front0", *extra, str(term_dir()), f.name],
                           capture_output=True, text=True)
    finally:
        pathlib.Path(f.name).unlink()
    steps = next((l.split()[1] for l in p.stderr.splitlines() if l.startswith("contractions ")), None)
    if p.returncode != 0 or steps is None:
        raise RuntimeError(f"avon front0 failed: {p.stderr.strip()[:400]}")
    if p.stdout.strip() == "RErr":
        return steps, None
    out: Dict[str, str] = {}
    for line in p.stdout.splitlines():
        name, h = line.split("\t")
        out[name] = h
    return steps, out


def reference(text: str) -> Result:
    """The expander's terms with checking off, hashed; None if it refuses,
    which it may do from the host reducer too: a binder named S, K or I is
    refused by aviary's environment (docs/SKIJACK-0.md §1)."""
    try:
        with Deep():
            e = skijack.compile(text, lexicon="ascii", check=False)
    except (SkijackError, DefinitionError, ExpansionError):
        return None
    if not all(_closed(t) for t in e.terms.values()):
        return None
    return {n: structural_hash(t) for n, t in e.terms.items()}


def _closed(t) -> bool:
    """No atom but S, K and I: no name the expander left unresolved."""
    stack = [t]
    while stack:
        x = stack.pop()
        if isinstance(x, Atom):
            if x.name not in ("S", "K", "I"):
                return False
        else:
            stack.extend((x.fn, x.arg))
    return True


def compare(got: Result, ref: Result) -> str:
    """'' if front1 did what the expander did, else what differs."""
    if got is None or ref is None:
        if got is None and ref is None:
            return ""
        return f"the expander {'refuses' if ref is None else 'accepts'}, front1 does not"
    if set(got) != set(ref):
        return (f"names differ: front1 only {sorted(set(got) - set(ref))[:8]}, "
                f"the expander only {sorted(set(ref) - set(got))[:8]}")
    bad = [n for n in ref if got[n] != ref[n]]
    return f"terms differ: {bad[:12]}" if bad else ""


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--avon", required=True)
    ap.add_argument("--corpus", action="store_true")
    ap.add_argument("--expect", default="", help="fail unless this milestone's corpus agrees")
    ap.add_argument("--edges", action="store_true")
    ap.add_argument("--random", type=int, default=0)
    ap.add_argument("--random1", type=int, default=0, help="random programs of the full language")
    ap.add_argument("--seed", type=int, default=20260928)
    ap.add_argument("--no-fixed-point", action="store_true")
    ap.add_argument("--templates", action="store_true")
    ap.add_argument("--data", action="store_true")
    ap.add_argument("--fix", action="store_true")
    a = ap.parse_args(argv)
    if (a.data or a.fix) and not a.templates:
        ap.error("--data and --fix need --templates")
    extra: Tuple[str, ...] = (f"--templates={term_dir()}",) if a.templates else ()
    extra += ("--data",) if a.data else ()
    extra += ("--fix",) if a.fix else ()
    fail = 0
    if a.corpus:
        agree = set()
        for f in sorted(CORPUS.glob("*.ascii.ski")):
            stem = f.name[: -len(".ascii.ski")]
            text = f.read_text()
            why = compare(run_avon(a.avon, text, extra)[1], reference(text))
            if why:
                print(f"  {stem}: {why}")
            else:
                agree.add(stem)
        print(f"corpus: {len(agree)} of {len(list(CORPUS.glob('*.ascii.ski')))} agree")
        if a.expect:
            keys = list(MILESTONES)
            want = [p for k in keys[: keys.index(a.expect) + 1] for p in MILESTONES[k]]
            missing = [p for p in want if p not in agree]
            if missing:
                print(f"FAIL {a.expect}: {missing} do not agree")
                fail += 1
    if a.edges:
        bad = deferred = 0
        edges = {**EDGES, **EDGES1, **EDGES2, **EDGES3, **EDGES4}
        for what, text in edges.items():
            why = compare(run_avon(a.avon, text, extra)[1], reference(text))
            if why and what in AVIARY:
                deferred += 1
            elif why:
                print(f"  edge {what}: {why}")
                bad += 1
        print(f"edges: {len(edges) - bad - deferred} of {len(edges)} as the expander has them, "
              f"{deferred} of aviary's left to M5")
        fail += bad
    if a.random:
        sys.path.insert(0, str(HERE.parent.parent / "tests"))
        from test_spec0 import _program
        rng, bad = random.Random(a.seed), 0
        for i in range(a.random):
            text = _program(rng)
            why = compare(run_avon(a.avon, text, extra)[1], reference(text))
            if why:
                print(f"FAIL random program {i}: {why}\n{text}")
                bad += 1
        print(f"random: {a.random - bad} of {a.random} agree")
        fail += bad
    if a.random1:
        rng, bad, deferred, accepted = random.Random(a.seed), 0, 0, 0
        for i in range(a.random1):
            text = _program2(rng)
            ref = reference(text)
            try:
                why = compare(run_avon(a.avon, text, extra)[1], ref)
            except RuntimeError as e:
                why = str(e)[:200]
            accepted += ref is not None
            if why and ref is None and aviary_refuses(text):
                deferred += 1
            elif why:
                print(f"FAIL random1 program {i}: {why}\n{text}")
                bad += 1
        print(f"random1: {a.random1 - bad - deferred} of {a.random1} agree "
              f"({accepted} accepted by the expander), {deferred} of aviary's left to M5")
        fail += bad
    if not a.no_fixed_point:
        t0 = time.time()
        text = FRONT.read_text()
        steps, got = run_avon(a.avon, text, extra)
        why = compare(got, reference(text))
        if why:
            print(f"FAIL fixed point: {why}")
            fail += 1
        else:
            print(f"fixed point: front1 gives all {len(got)} of its own names their terms "
                  f"({int(steps):,} contractions, {time.time() - t0:.0f}s)")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
