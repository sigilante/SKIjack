"""Running the SKIjack-0 front end in Avon, and checking it.

    python3 -m skijack.selfhost.run0 --avon PATH [--random N] [--edges]
    python3 -m skijack.selfhost.run0 --avon PATH --profile [FILE]

The front end (``front0.ascii.ski``) is a term: applied to a program's
characters, it reduces to every name's closed term.  This module compiles
it with this package and writes it, with the constructors that build its
input, as SKIT files; ``avon front0`` builds the input, reduces in share
mode, and reads the result by probing into a line per name, the name and
its term's §5 hash.

The checks, each against ``skijack.spec0`` and so against the expander:

- the fixed point: the front end compiling its own source gives every
  name's term, hash for hash (``docs/SKIJACK-0.md`` §5);
- ``--random N``: N random programs of ``tests/test_spec0.py``'s kind;
- ``--edges``: the programs of :data:`EDGES`, which the front end must
  accept or refuse as spec0 does.

``--profile`` runs the front end on FILE (default: its own source) with
``avon front0 --profile``, which charges each contraction to the named
term whose code it runs, and totals the rows by equation: a lifted lambda
(``f~lambda2``) and a recursion's body (``f.body``) count as ``f``.

A call of the non-sharing reference reducer would recompute every shared
value, which the front end has many of; it serves for the lexer's tests
only (``tests/test_front0.py``).
"""

from __future__ import annotations

import argparse
import functools
import pathlib
import random
import re
import subprocess
import sys
import tempfile
import time
from typing import Dict, List, Optional, Tuple

from aviary_kernel.terms import App, Term

import skijack
from skijack.dictionary import structural_hash
from skijack.errors import SkijackError
from skijack.export import jam
from skijack.parser import parse
from skijack.spec0 import Subset0Error, compile0, in_subset
from skijack.templates import templates, write as write_templates

HERE = pathlib.Path(__file__).resolve().parent
FRONT = HERE / "front0.ascii.ski"

#: the terms avon front0 reads, as DIR/<name>.skit
TERMS = ("front", "SCons", "SNil", "Code", "Lo", "Hi")


class Deep:
    """The expander recurses on term depth."""

    def __enter__(self):
        self.old = sys.getrecursionlimit()
        sys.setrecursionlimit(max(self.old, 1_000_000))

    def __exit__(self, *exc):
        sys.setrecursionlimit(self.old)


@functools.lru_cache(maxsize=1)
def expansion():
    with Deep():
        return skijack.compile(FRONT.read_text(), lexicon="ascii")


def compiled() -> Dict[str, Term]:
    return expansion().terms


@functools.lru_cache(maxsize=1)
def term_dir() -> pathlib.Path:
    """A directory of the SKIT files avon front0 reads, and the front end's
    supercombinator templates (skijack.templates) for --templates."""
    d = pathlib.Path(tempfile.mkdtemp(prefix="front0-"))
    t = compiled()
    for name in TERMS:
        (d / f"{name}.skit").write_bytes(jam(t[name]))
    with Deep():
        write_templates(templates(expansion()), d / "templates.tsv",
                        d / "template_terms.tsv")
    return d


Result = Optional[List[Tuple[str, str]]]


def run_avon(avon: str, text: str, extra: Tuple[str, ...] = ()) -> Tuple[str, Result, str]:
    """Avon's contraction count, every name and its term's hash (None if the
    front end refused), and its stderr."""
    with tempfile.NamedTemporaryFile("w", suffix=".ski", delete=False) as f:
        f.write(text)
    try:
        p = subprocess.run([avon, "front0", *extra, str(term_dir()), f.name],
                           capture_output=True, text=True)
    finally:
        pathlib.Path(f.name).unlink()
    m = re.search(r"^contractions (\d+)$", p.stderr, re.M)
    if p.returncode != 0 or not m:
        raise RuntimeError(f"avon front0 failed: {p.stderr.strip()[:400]}")
    if p.stdout.strip() == "RErr":
        return m.group(1), None, p.stderr
    rows = [tuple(line.split("\t")) for line in p.stdout.splitlines()]
    return m.group(1), [(n, h) for n, h in rows], p.stderr


# -------------------------------------------------------------- profile

def _atoms(t: Term) -> int:
    n, stack = 0, [t]
    while stack:
        x = stack.pop()
        if isinstance(x, App):
            stack += [x.fn, x.arg]
        else:
            n += 1
    return n


#: a term smaller than this is generic -- `K K` is a dozen case branches --
#: so naming it would take code from the equation it is written in
MIN_ATOMS = 6


def names_file(path: pathlib.Path) -> int:
    """Every rule of the front end of MIN_ATOMS atoms or more, labelled, as
    `rule TAB label TAB hash` lines for Avon's --profile."""
    with Deep():
        internals: Dict[str, Term] = {}
        compile0(parse(FRONT.read_text(), "ascii"), internals)
        lines = [f"rule\t{k}\t{structural_hash(v)}" for k, v in internals.items()
                 if _atoms(v) >= MIN_ATOMS]
    path.write_text("\n".join(lines) + "\n")
    return len(lines)


def equation_of(label: str) -> str:
    """The equation a profile row's code belongs to."""
    return "/".join(sorted({re.sub(r"(~lambda\d+|\.body)$", "", part)
                            for part in label.split("/")}))


def profile(avon: str, text: str, names: pathlib.Path) -> Tuple[str, List[Tuple[int, str]]]:
    """Avon's contractions, and its profile rows: contractions and label."""
    steps, _got, err = run_avon(avon, text, (f"--profile={names}",))
    rows = []
    for line in err.splitlines():
        m = re.match(r"\s*(\d+)\s+[\d.]+\s+(.*)$", line)
        if m:
            rows.append((int(m.group(1)), m.group(2)))
    return steps, rows


def print_profile(steps: str, rows: List[Tuple[int, str]], top: int = 40) -> None:
    total = sum(c for c, _ in rows)
    by_eq: Dict[str, int] = {}
    for c, label in rows:
        by_eq[equation_of(label)] = by_eq.get(equation_of(label), 0) + c
    print(f"{int(steps):,} contractions; {total:,} charged")
    print("\nby equation (its lambdas and recursion body included):")
    for eq, c in sorted(by_eq.items(), key=lambda kv: -kv[1])[:top]:
        print(f"{c:>15,} {100 * c / total:6.2f}%  {eq}")
    print("\nby rule:")
    for c, label in rows[:top]:
        print(f"{c:>15,} {100 * c / total:6.2f}%  {label}")


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


def compare(got: Result, ref: Optional[Dict[str, Term]]) -> str:
    """'' if the front end did what spec0 did, else what differs."""
    if got is None or ref is None:
        if got is None and ref is None:
            return ""
        return f"spec0 {'refuses' if ref is None else 'accepts'}, the front end does not"
    if [n for n, _ in got] != list(ref):
        return f"names differ: {[n for n, _ in got][:8]}... against {list(ref)[:8]}..."
    bad = [n for n, h in got if h != structural_hash(ref[n])]
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
    """What differs ('' if nothing), Avon's contractions, and the names."""
    text = FRONT.read_text()
    ref = reference(text)
    if ref is None:
        return "spec0 refuses the front end's own source", "", 0
    with Deep():
        e = skijack.compile(text, lexicon="ascii")
    differ = [n for n in ref if structural_hash(ref[n]) != structural_hash(e.terms[n])]
    if differ:
        return f"spec0 and the expander differ on the front end: {differ}", "", 0
    steps, got, _err = run_avon(avon, text)
    return compare(got, ref), steps, len(ref)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--avon", required=True, help="the avon binary")
    ap.add_argument("--random", type=int, default=0, help="random programs to check")
    ap.add_argument("--seed", type=int, default=20260928)
    ap.add_argument("--edges", action="store_true", help="check the edge programs")
    ap.add_argument("--no-fixed-point", action="store_true")
    ap.add_argument("--profile", nargs="?", const="", metavar="FILE",
                    help="profile the front end on FILE (default: its own source)")
    a = ap.parse_args(argv)
    if a.profile is not None:
        text = pathlib.Path(a.profile).read_text() if a.profile else FRONT.read_text()
        names = pathlib.Path(tempfile.mkdtemp()) / "front0.names.tsv"
        names_file(names)
        steps, rows = profile(a.avon, text, names)
        print_profile(steps, rows)
        return 0
    fail = 0
    if a.edges:
        for what, text in EDGES.items():
            why = compare(run_avon(a.avon, text)[1], reference(text))
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
            why = compare(run_avon(a.avon, text)[1], reference(text))
            if why:
                print(f"FAIL random program {i}: {why}\n{text}")
                bad += 1
        print(f"random: {a.random - bad} of {a.random} agree")
        fail += bad
    if not a.no_fixed_point:
        t0 = time.time()
        why, steps, n = fixed_point(a.avon)
        if why:
            print(f"FAIL fixed point: {why}")
            fail += 1
        else:
            print(f"fixed point: the front end gives all {n} of its own names "
                  f"their terms ({int(steps):,} contractions, {time.time() - t0:.0f}s)")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
