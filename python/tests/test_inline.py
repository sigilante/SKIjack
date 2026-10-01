"""The inlining pass (skijack.inline): off by default; on, other terms with
the same values, no work copied, nothing captured."""

import random
import sys

import pytest
from aviary_kernel.environment import Environment
from aviary_kernel.reduce import reduce
from aviary_kernel.terms import App, Atom

import skijack
from skijack import corpus
from skijack.dictionary import structural_hash
from skijack.expand import _fresh, expand_macros, free_names, substitute
from skijack.inline import inline_bodies, uses
from skijack.parser import parse
from skijack import ast as A

HEAD = """bool === False | True
nat  === Zero | Suc nat
list === Nil | Cons bool list
pr   === Pr bool bool
and x y = x |> { False False ; True y }
or x y = x |> { False y ; True True }
not x = x |> { False True ; True False }
implies x y = x |> { False True ; True y }
"""


@pytest.fixture(autouse=True)
def _deep_recursion():
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 100_000))
    yield
    sys.setrecursionlimit(old)


def _value(t):
    """A boolean's value, read by applying it to two markers."""
    r = reduce(App(App(t, Atom("ff")), Atom("tt")), Environment(), whnf_only=True,
               max_steps=10**6, max_size=10**8).term
    return r.name


def _bodies(src):
    """The top-level equations' bodies before and after the pass."""
    prog = parse(HEAD + src, "ascii")
    eqs = {d.name: (d.binders, expand_macros(d.body, {}))
           for d in prog.decls if isinstance(d, A.Equation)}
    ctors = {}
    for d in prog.decls:
        if isinstance(d, A.TypeDecl):
            for i, c in enumerate(d.ctors):
                ctors[c.name] = (d.name, i, len(c.fields))
    new, _ = inline_bodies(eqs, {}, ctors, substitute, free_names, _fresh)
    return eqs, new


def test_off_by_default_the_terms_are_unchanged():
    src = HEAD + "f x y = and (implies x y) (not y)\n"
    a, b = skijack.compile(src), skijack.compile(src, inline=False)
    assert {n: structural_hash(t) for n, t in a.terms.items()} == \
           {n: structural_hash(t) for n, t in b.terms.items()}
    c = skijack.compile(src, inline=True)
    assert structural_hash(c.terms["f"]) != structural_hash(a.terms["f"])


def test_small_calls_are_unfolded_and_their_cases_simplified():
    _, new = _bodies("f x y = and (implies x y) (not y)\n")
    body = new["f"]
    assert not free_names(body) & {"and", "implies", "not"}
    # and (implies x y) r: a case on x, and in its True branch a case on y
    assert isinstance(body, A.Case) and body.scrutinee == A.Name("x")


def test_every_function_keeps_its_values():
    src = """f x y = and (implies x y) (not y)
g x y = or (not x) (and x y)
h p = p |> { Pr a b and (or a b) (not (and a b)) }
k x = Pr x (not x) |> { Pr a b and a (not b) }
"""
    plain, inl = skijack.compile(HEAD + src), skijack.compile(HEAD + src, inline=True)
    for x in ("False", "True"):
        for y in ("False", "True"):
            for name, args in (("f", [x, y]), ("g", [x, y]), ("h", [f"Pr {x} {y}"]), ("k", [x])):
                def run(exp):
                    t = exp.terms[name]
                    for a in args:
                        parts = a.split()
                        v = exp.terms[parts[0]]
                        for q in parts[1:]:
                            v = App(v, exp.terms[q])
                        t = App(t, v)
                    return _value(t)
                assert run(plain) == run(inl), (name, args)


def test_an_argument_used_twice_or_under_a_lambda_is_not_copied():
    _, new = _bodies("""dup x = Pr x x
lam x = \\z. x
g y = dup (not y)
h y = dup y
m y = lam (not y)
""")
    assert "dup" in free_names(new["g"])          # (not y) would be copied
    assert "dup" not in free_names(new["h"])      # a name costs nothing to copy
    assert "lam" in free_names(new["m"])          # under a lambda: once per call


def test_recursive_functions_and_constants_are_not_unfolded():
    _, new = _bodies("""len xs = xs |> { Nil Zero ; Cons x r Suc (len r) }
c = not True
f xs = len xs
g x = and c x
""")
    assert "len" in free_names(new["f"])
    assert "c" in free_names(new["g"])


def test_a_callee_global_bound_at_the_call_is_not_captured():
    _, new = _bodies("""useNot x = not x
f not = useNot not
""")
    # f's binder `not` would capture useNot's global `not`
    assert "useNot" in free_names(new["f"])


def test_case_of_case_renames_an_inner_binder_the_alternatives_use():
    src = """sel p x = p |> { Pr a b a } |> { False x ; True not x }
"""
    plain, inl = skijack.compile(HEAD + src), skijack.compile(HEAD + src, inline=True)
    for a in ("False", "True"):
        for b in ("False", "True"):
            for x in ("False", "True"):
                def run(exp):
                    pr = App(App(exp.terms["Pr"], exp.terms[a]), exp.terms[b])
                    return _value(App(App(exp.terms["sel"], pr), exp.terms[x]))
                assert run(plain) == run(inl)


def test_uses_counts_branches_as_one_and_lambdas_as_many():
    x = A.Name("x")
    case = A.Case(A.Name("s"), (("False", (), x), ("True", (), x)))
    assert uses(case, "x") == 1
    assert uses(A.Lambda("z", x), "x") == 2
    assert uses(A.App(x, x), "x") == 2
    assert uses(A.Lambda("x", x), "x") == 0


def test_the_corpus_and_random_programs_compile_with_it():
    n = 0
    for stem in sorted({p.name.split(".")[0] for p in corpus.DIR.glob("*.ascii.ski")}):
        try:
            skijack.compile(corpus.read(stem, "ascii"))
        except Exception:
            continue                                # refused without it too
        skijack.compile(corpus.read(stem, "ascii"), inline=True)
        n += 1
    assert n > 10
    sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent))
    from test_spec0 import _program
    rng = random.Random(20260929)
    for _ in range(100):
        skijack.compile(_program(rng), check=False, inline=True)   # as test_spec0 does
