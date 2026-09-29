"""Running the SKIjack-0 front end in a reducer, and checking it.

    python3 -m skijack.selfhost.run0 --avon PATH [--random N] [--edges]

The front end (``front0.ascii.ski``) is a term: applied to a program's
characters, it reduces to every name's closed term.  This module compiles
it with this package, hands ``render markers (front text)`` to a reducer
that shares -- Avon's ``reduce --strategy=share`` -- in the printed form,
and reads the printed normal form back into terms.  ``render``
(``render0.ascii.ski``) turns the result into a tree of marker atoms, so
the normal form is the result written out.

The checks, each against ``skijack.spec0`` and so against the expander:

- the fixed point: the front end compiling its own source gives every
  name's term, hash for hash (``docs/SKIJACK-0.md`` §5);
- ``--random N``: N random programs of ``tests/test_spec0.py``'s kind;
- ``--edges``: the programs of :data:`EDGES`, which the front end must
  accept or refuse as spec0 does.

A call of the non-sharing reference reducer would recompute every shared
value, which the front end has many of; it serves for the lexer's tests
only (``tests/test_front0.py``).
"""

from __future__ import annotations

import argparse
import functools
import pathlib
import random
import subprocess
import sys
import time
from typing import Dict, List, Optional, Tuple

from aviary_kernel.terms import App, Atom, Term

import skijack
from skijack.dictionary import structural_hash
from skijack.errors import SkijackError
from skijack.parser import parse
from skijack.spec0 import Subset0Error, compile0, in_subset

HERE = pathlib.Path(__file__).resolve().parent
FRONT = HERE / "front0.ascii.ski"
RENDER = HERE / "render0.ascii.ski"

#: the marker atoms, in the order of render0.ascii.ski's cell
MARKS = ["cd", "hi", "lo", "nn", "nc", "zz", "su", "ts", "tk", "ti", "tv", "ta",
         "on", "oc", "ok", "er"]


class Deep:
    """The expander and the decoder recurse on term depth."""

    def __enter__(self):
        self.old = sys.getrecursionlimit()
        sys.setrecursionlimit(max(self.old, 1_000_000))

    def __exit__(self, *exc):
        sys.setrecursionlimit(self.old)


@functools.lru_cache(maxsize=1)
def compiled() -> Dict[str, Term]:
    """front0 with the renderer appended.  The markers `render` applies are
    atoms, not data, which the type checker refuses, so this compiles
    unchecked; :func:`check_front_term` shows `front` is the checked
    compile's."""
    with Deep():
        src = FRONT.read_text() + RENDER.read_text()
        return skijack.compile(src, lexicon="ascii", check=False).terms


def check_front_term() -> None:
    with Deep():
        checked = skijack.compile(FRONT.read_text(), lexicon="ascii").terms["front"]
    if structural_hash(checked) != structural_hash(compiled()["front"]):
        raise AssertionError("appending the renderer changed the front end's term")


def encode(text: str) -> Term:
    """A program as the front end reads it: a list of 7-bit codes."""
    t = compiled()
    codes = {}
    out = t["SNil"]
    for ch in reversed(text):
        n = ord(ch)
        if n > 127:
            raise ValueError(f"not ASCII: {ch!r}")
        if n not in codes:
            c = t["Code"]
            for i in range(7):
                c = App(c, t["Hi" if (n >> (6 - i)) & 1 else "Lo"])
            codes[n] = c
        out = App(App(t["SCons"], codes[n]), out)
    return out


def cell(xs: List[Term]) -> Term:
    t = compiled()
    out = xs[-1]
    for x in reversed(xs[:-1]):
        out = App(App(t["pair"], x), out)
    return out


def printed(term: Term) -> str:
    """The printed form, `f a b` with parenthesized arguments, without
    recursion."""
    out: List[str] = []
    stack: list = [term]
    while stack:
        x = stack.pop()
        if isinstance(x, str):
            out.append(x)
        elif isinstance(x, Atom):
            out.append(x.name)
        else:
            args = []
            while isinstance(x, App):
                args.append(x.arg)
                x = x.fn
            stack.append(")")
            for a in args:                      # the last argument first
                stack.append(a)
                stack.append(" ")
            stack.append(x)
            stack.append("(")
    return "".join(out)


def job(text: str) -> str:
    """The term a reducer normalizes: `render markers (front text)`."""
    t = compiled()
    return printed(App(App(t["render"], cell([Atom(m) for m in MARKS])),
                       App(t["front"], encode(text))))


def run_avon(avon: str, text: str, fuel: int = 10 ** 12) -> Tuple[str, str]:
    """Avon's status line and printed normal form."""
    p = subprocess.run([avon, "reduce", "--strategy=share", f"--fuel={fuel}",
                        "--budget=200000000", "--max-nodes=1000000000"],
                       input=job(text), capture_output=True, text=True)
    if p.returncode not in (0, 1) or not p.stdout:
        raise RuntimeError(f"avon failed: {p.stderr.strip()[:400]}")
    status, _, body = p.stdout.partition("\n")
    return status, body


# ------------------------------------------------------------- decoding

def _tree(s: str):
    """The printed form to nested lists: an application is [head, args...]."""
    stack: list = [[]]
    for tok in s.replace("(", " ( ").replace(")", " ) ").split():
        if tok == "(":
            stack.append([])
        elif tok == ")":
            x = stack.pop()
            stack[-1].append(x[0] if len(x) == 1 else x)
        else:
            stack[-1].append(tok)
    top = stack[0]
    return top[0] if len(top) == 1 else top


def _split(x):
    return (x, []) if isinstance(x, str) else (x[0], x[1:])


def _name(x) -> str:
    out = []
    while True:
        h, a = _split(x)
        if h == "nn":
            return "".join(out)
        if h != "nc":
            raise ValueError(f"not a name: {h}")
        cd, bits = _split(a[0])
        if cd != "cd" or len(bits) != 7:
            raise ValueError("not a code")
        out.append(chr(int("".join("1" if b == "hi" else "0" for b in bits), 2)))
        x = a[1]


def _term(x) -> Term:
    out: list = []
    stack = [x]
    while stack:
        y = stack.pop()
        if y is None:                           # an application's two parts are done
            f_arg = out.pop()
            out.append(App(out.pop(), f_arg))
            continue
        h, a = _split(y)
        if h in ("ts", "tk", "ti") and not a:
            out.append(Atom(h[1].upper()))
        elif h == "ta" and len(a) == 2:
            stack.extend([None, a[1], a[0]])
        else:
            raise ValueError(f"not a closed term: {h}")
    return out[0]


def decode(status: str, body: str) -> Optional[List[Tuple[str, Term]]]:
    """Every name and its term, or None if the front end refused."""
    if not status.startswith("NORMAL"):
        raise RuntimeError(f"the reducer stopped: {status}")
    h, a = _split(_tree(body))
    if h == "er" and not a:
        return None
    if h != "ok":
        raise ValueError(f"not a result: {h}")
    out, x = [], a[0]
    while True:
        h, a = _split(x)
        if h == "on":
            return out
        out.append((_name(a[0]), _term(a[1])))
        x = a[2]


# --------------------------------------------------------------- checks

def reference(text: str) -> Optional[Dict[str, Term]]:
    """spec0's names and terms, or None if spec0 refuses the program."""
    with Deep():
        try:
            prog = parse(text, "ascii")
            if in_subset(prog):
                return None
            return compile0(prog)
        except (SkijackError, Subset0Error):
            return None


def compare(got, ref) -> str:
    """'' if the front end did what spec0 did, else what differs."""
    if got is None or ref is None:
        if got is None and ref is None:
            return ""
        return f"spec0 {'refuses' if ref is None else 'accepts'}, the front end does not"
    if [n for n, _ in got] != list(ref):
        return f"names differ: {[n for n, _ in got][:8]}... against {list(ref)[:8]}..."
    bad = [n for n, t in got if structural_hash(t) != structural_hash(ref[n])]
    return f"terms differ: {bad}" if bad else ""


_H = "nat === Zero | Suc nat\nbool === Yes | No\n"

#: programs at the edges of the subset: what each exercises, and its text
EDGES: Dict[str, str] = {
    "an unresolved name": _H + "f := g\n",
    "an undeclared bird": _H + "f := B\n",
    "a declared bird": _H + "B x = x\nf := B Zero\n",
    "a binder S": _H + "f S = S\n",
    "a lambda's K": _H + "f := \\K. K\n",
    "a branch's I": _H + "f n = n |> { Zero Zero ; Suc I I }\n",
    "a case missing a constructor": _H + "f n = n |> { Zero Zero }\n",
    "a case naming one twice": _H + "f n = n |> { Zero Zero ; Suc k k ; Zero Zero }\n",
    "a case over two types": _H + "f n = n |> { Zero Zero ; Yes Zero }\n",
    "a case out of order": _H + "f n = n |> { Suc k k ; Zero Zero }\n",
    "a case on a case": _H + "f n = n |> { Zero Yes ; Suc k No } |> { Yes Zero ; No n }\n",
    "a lambda's body a case": _H + "f := \\n. n |> { Zero Zero ; Suc k k }\n",
    "pick 0": _H + "f n = 0@n\n",
    "pick 1": _H + "f n = 1@n\n",
    "pick 13": _H + "f n = 13@n\n",
    "a cell of one": _H + "f n = [n]\n",
    "an undeclared constructor": _H + "f n = n |> { Zero Zero ; Succ k k }\n",
    "a type with two names": "nat bat === Zero | Suc nat\n",
    "a definition with binders": _H + "f x := x\n",
    "a quotation": _H + "f := <I>\n",
    "a number": _H + "f := 12\n",
    "a qualified name": _H + "f := a.b\n",
    "an equation twice": _H + "f x = x\nf x = Zero\n",
    "an equation and a definition": _H + "f x = x\nf := Zero\n",
    "an equation named as a constructor": _H + "Zero x = x\n",
    "a constructor twice": _H + "t === Zero | One\n",
    "a type twice": _H + "nat === One | Two\n",
    "an equation without binders": _H + "f = Suc Zero\ng := f\n",
    "pair declared": _H + "pair x y = x\nf := [Zero Zero]\n",
    "hd declared": _H + "hd p = p\nf n = 2@n\n",
    "suc a definition": _H + "suc := Zero\nf := suc\n",
    "S declared": _H + "S := K\nf := S\n",
    "a binder named as an equation": _H + "f x = x\ng f = f Zero\n",
    "a lambda shadowing a binder": _H + "g x = \\x. x\n",
    "an equation's own name its binder": _H + "f f = f\n",
    "a lambda shadowing a recursion": _H + "f x = x |> { Zero (\\f. f) ; Suc k (f k) }\n",
    "a branch shadowing a recursion": _H + "f x = x |> { Zero Zero ; Suc f (f Zero) }\n",
    "a binder twice": _H + "f x x = x\n",
    "a lambda capturing a binder twice": _H + "f x x = \\y. x y\n",
    "a mutual pair": _H + "ev n = n |> { Zero Yes ; Suc k (od k) }\nod n = n |> { Zero No ; Suc k (ev k) }\n",
    "a member shadowed": _H + ("ev n = n |> { Zero Yes ; Suc od (od Zero) }\n"
                               "od n = n |> { Zero No ; Suc k (ev k) }\nx := ev\n"),
    "a mutual pair of lambdas": _H + ("ev n = \\z. n |> { Zero z ; Suc k (od k z) }\n"
                                      "od n = \\z. n |> { Zero z ; Suc k (ev k z) }\n"),
    "a mutual three": _H + ("a n = n |> { Zero Yes ; Suc k (b k) }\nb n = n |> { Zero No ; Suc k (c k) }\n"
                            "c n = n |> { Zero Yes ; Suc k (a k) }\nd := [a b c]\n"),
    "a definition cycle": _H + "d := e\ne := d\n",
    "a definition its own": _H + "d := d\n",
    "a cycle through an equation": _H + "f x = d\nd := f\n",
    "a definition chain": _H + "d := e\ne := Suc Zero\n",
    "a newline in parentheses": _H + "f n = (Suc\n n)\n",
    "a newline before the outer )": _H + "f n = (Suc n\n)\n",
    "a newline before an inner )": _H + "f n = (Suc (Suc n\n))\n",
    "a newline before ]": _H + "f n = [n n\n]\n",
    "a newline after (": _H + "f n = (\nSuc n)\n",
    "a comment before )": _H + "f n = (Suc n -- x\n)\n",
    "a comment inside": _H + "f n = (Suc -- x\n n)\n",
    "newlines in a case": _H + "f n = n |> {\n Zero Zero ;\n Suc k k }\n",
    "a newline before }": _H + "f n = n |> { Zero Zero ; Suc k k\n}\n",
    "a newline before an inner }": _H + "f n = (n |> { Zero Zero ; Suc k k\n})\n",
    "a newline before {": _H + "f n = n |>\n { Zero Zero ; Suc k k }\n",
    "a type declared after use": "f n = n |> { Zero Zero ; Suc k k }\nnat === Zero | Suc nat\n",
    "a type name as a value": _H + "f := nat\n",
    "comments": _H + "f n = n -- the same\n-- a line\ng := f\n",
    "blank lines": "\n\n" + _H + "\n\nf := Zero\n\n",
    "no final newline": _H + "f := Zero",
    "nothing": "",
    "types only": _H,
    "a tab and a return": _H + "f\tn = n\r\n",
    "a semicolon at the top": _H + "f := Zero ; g\n",
}


def fixed_point(avon: str) -> Tuple[str, str, int]:
    """What differs ('' if nothing), Avon's status line, and the names."""
    text = FRONT.read_text()
    ref = reference(text)
    if ref is None:
        return "spec0 refuses the front end's own source", "", 0
    with Deep():
        e = skijack.compile(text, lexicon="ascii")
    differ = [n for n in ref if structural_hash(ref[n]) != structural_hash(e.terms[n])]
    if differ:
        return f"spec0 and the expander differ on the front end: {differ}", "", 0
    status, body = run_avon(avon, text)
    return compare(decode(status, body), ref), status, len(ref)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--avon", required=True, help="the avon binary")
    ap.add_argument("--random", type=int, default=0, help="random programs to check")
    ap.add_argument("--seed", type=int, default=20260928)
    ap.add_argument("--edges", action="store_true", help="check the edge programs")
    ap.add_argument("--no-fixed-point", action="store_true")
    a = ap.parse_args(argv)
    fail = 0
    check_front_term()
    if a.edges:
        for what, text in EDGES.items():
            why = compare(decode(*run_avon(a.avon, text)), reference(text))
            if why:
                print(f"FAIL {what}: {why}")
                fail += 1
        print(f"edges: {len(EDGES) - fail} of {len(EDGES)} as spec0 has them")
    if a.random:
        sys.path.insert(0, str(HERE.parent.parent / "tests"))
        from test_spec0 import _program
        rng, bad = random.Random(a.seed), 0
        for i in range(a.random):
            text = _program(rng)
            why = compare(decode(*run_avon(a.avon, text)), reference(text))
            if why:
                print(f"FAIL random program {i}: {why}\n{text}")
                bad += 1
        print(f"random: {a.random - bad} of {a.random} agree")
        fail += bad
    if not a.no_fixed_point:
        t0 = time.time()
        why, status, n = fixed_point(a.avon)
        if why:
            print(f"FAIL fixed point: {why}")
            fail += 1
        else:
            print(f"fixed point: the front end gives all {n} of its own names "
                  f"their terms ({status}, {time.time() - t0:.0f}s)")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
