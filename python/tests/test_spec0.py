"""SKIjack-0's specification (docs/SKIJACK-0.md) against the expander.

``skijack.spec0`` implements the subset's expansion from the
specification; ``expand_program`` is the expander.  They must give the
same term for every name: on the corpus programs the subset admits, on
the compiler core the front end is built on, and on random programs that
mix types, cases, cells, picks, lambdas, self-recursion, mutually
recursive groups and definitions.  Checking only rejects, so random
programs compile with it off.
"""

import random
import sys

import pytest
from aviary_kernel.abstraction import ExpansionError

import skijack
from skijack import corpus
from skijack.dictionary import structural_hash
from skijack.errors import SkijackError
from skijack.parser import parse
from skijack.spec0 import Subset0Error, compile0, in_subset

@pytest.fixture(autouse=True)
def _deep_recursion():
    """The expanders recurse on term depth; raised for these tests only,
    and restored, since other tests depend on the default."""
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 100_000))
    yield
    sys.setrecursionlimit(old)


def agree(src, check=True):
    prog = parse(src, "ascii")
    assert in_subset(prog) is None
    ref = compile0(prog)
    e = skijack.compile(src, lexicon="ascii", check=check)
    differ = [n for n in ref if structural_hash(ref[n]) != structural_hash(e.terms[n])]
    assert not differ, differ
    return len(ref)


@pytest.mark.parametrize("stem", ["kernel-events", "ascii-digits"])
def test_the_subset_corpus_programs_agree(stem):
    assert agree(corpus.read(stem, "ascii")) > 10


def test_the_programs_outside_the_subset_are_named():
    for stem, why in [("tower", "Core"), ("sec2-c", "Macro"), ("misc-forms", "Sig")]:
        assert in_subset(parse(corpus.read(stem, "ascii"), "ascii")) == why
    with pytest.raises(Subset0Error):
        compile0(parse("f S = S\n", "ascii"))


@pytest.mark.parametrize("src", [
    "f x = x\nf x = x\n",
    "nat === Zero | Suc nat\nZero x = x\n",
    "nat === Zero | Suc nat\nnat === One\n",
    "d := e\ne := d\n",
    "f x = d\nd := f\n",
])
def test_what_the_expander_refuses_spec0_refuses(src):
    with pytest.raises((SkijackError, ExpansionError)):
        skijack.compile(src, lexicon="ascii", check=False)
    with pytest.raises(Subset0Error):
        compile0(parse(src, "ascii"))


def _program(rng):
    """A random SKIjack-0 program."""
    lines = ["nat === Zero | Suc nat", "bool === Yes | No",
             "tr === Leaf | Node tr nat tr"]
    ctors = {"nat": [("Zero", 0), ("Suc", 1)], "bool": [("Yes", 0), ("No", 0)],
             "tr": [("Leaf", 0), ("Node", 3)]}
    names = [f"e{i}" for i in range(rng.randint(2, 6))]
    arity = {n: rng.randint(1, 3) for n in names}

    def expr(scope, depth):
        r = rng.random()
        if depth <= 0 or r < 0.25:
            pool = list(scope) + ["S", "K", "I", "Zero", "Yes", "No", "Leaf", "pair", "hd", "tl"]
            return rng.choice(pool)
        if r < 0.45:
            f = rng.choice(names + ["Suc", "Node", "pair", "cons"])
            args = " ".join(f"({expr(scope, depth - 1)})" for _ in range(rng.randint(1, 3)))
            return f"{f} {args}"
        if r < 0.6:
            t = rng.choice(list(ctors))
            branches = []
            for c, k in ctors[t]:
                bs = [f"b{depth}{c.lower()}{j}" for j in range(k)]
                branches.append(f"{c} {' '.join(bs)} ({expr(scope + bs, depth - 1)})".replace("  ", " "))
            return f"({expr(scope, depth - 1)}) |> {{ {' ; '.join(branches)} }}"
        if r < 0.7:
            p = f"l{depth}{rng.randint(0, 9)}"
            return f"(\\{p}. {expr(scope + [p], depth - 1)})"
        if r < 0.8:
            return "[" + " ".join(f"({expr(scope, depth - 1)})" for _ in range(rng.randint(2, 3))) + "]"
        if r < 0.9:
            return f"{rng.randint(1, 13)}@({expr(scope, depth - 1)})"
        return f"({expr(scope, depth - 1)}) ({expr(scope, depth - 1)})"

    for n in names:
        bs = [f"{n}x{j}" for j in range(arity[n])]
        lines.append(f"{n} {' '.join(bs)} = {expr(bs, 4)}")
    lines.append(f"d0 := {expr([], 3)}")
    return "\n".join(lines) + "\n"


def test_random_programs_agree():
    rng = random.Random(20260928)
    groups = recursive = 0
    for _ in range(1000):
        src = _program(rng)
        agree(src, check=False)
        groups += "Group" in "".join(skijack.compile(src, lexicon="ascii", check=False).env.definitions)
    assert groups > 0, "no program had a mutually recursive group"
