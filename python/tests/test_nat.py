"""The prelude's numeral operations (expand.NAT_NAMES) and words.tsv
(templates.write_words), which Avon's data jets read (avon docs/DESIGN.md
§6.10)."""

import sys

import pytest
from aviary_kernel.abstraction import expand as ski_expand
from aviary_kernel.environment import Environment
from aviary_kernel.reduce import reduce
from aviary_kernel.terms import App, Atom

import skijack
from skijack.dictionary import structural_hash
from skijack.expand import NAT_NAMES
from skijack.templates import WORD_OPS, check, templates, write_words

NAT = "bool === False | True\nnat === Zero | Suc nat\n"


@pytest.fixture(autouse=True)
def _deep_recursion():
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 100_000))
    yield
    sys.setrecursionlimit(old)


def _compile(body: str):
    return skijack.compile(NAT + body, lexicon="ascii")


def _num(exp, n):
    t = exp.terms["Zero"]
    for _ in range(n):
        t = App(exp.terms["Suc"], t)
    return t


def _value(t, env):
    """A numeral's value, read by applying it to two markers."""
    n = 0
    while True:
        r = reduce(App(App(t, Atom("zz")), Atom("ss")), env, whnf_only=True,
                   max_steps=10**7, max_size=10**9).term
        if r == Atom("zz"):
            return n
        assert isinstance(r, App) and r.fn == Atom("ss")
        t, n = r.arg, n + 1


def _choice(t, env):
    return reduce(App(App(t, Atom("xx")), Atom("yy")), env, whnf_only=True,
                  max_steps=10**7, max_size=10**9).term


def test_the_operations_compute_on_small_numerals():
    exp = _compile("a = natAdd\ns = natSub\nm = natMul\ne = natIfEq\nl = natIfLe\n")
    env = Environment()
    for x in range(4):
        for y in range(4):
            ap = lambda n: App(App(exp.terms[n], _num(exp, x)), _num(exp, y))
            assert _value(ap("a"), env) == x + y
            assert _value(ap("s"), env) == max(x - y, 0)
            assert _value(ap("m"), env) == x * y
            assert _choice(ap("e"), env) == Atom("xx" if x == y else "yy")
            assert _choice(ap("l"), env) == Atom("xx" if x <= y else "yy")


def test_a_program_naming_none_is_compiled_as_before():
    """No prelude rule, template or name is added unless a program names an
    operation, so a program's terms, templates and exports do not change."""
    exp = _compile("x = Suc Zero\n")
    assert not set(NAT_NAMES) & set(exp.terms)
    assert not any(n.startswith("nat") for n in exp.env.definitions)
    assert not any(t.name.startswith("nat") for t in templates(exp))


def test_only_the_named_operations_and_their_needs_are_installed():
    exp = _compile("m = natMul\n")
    assert "natMul" in exp.terms and "natAdd" not in exp.terms
    assert exp.env.lookup("natAdd") is not None     # natMul's successor case adds
    assert exp.env.lookup("natSub") is None


def test_the_operations_templates_abstract_to_their_terms():
    exp = _compile("a = natAdd\ns = natSub\nm = natMul\ne = natIfEq\nl = natIfLe\n")
    nat = [t for t in templates(exp) if t.name.startswith("nat")]
    assert len(nat) >= 10
    assert all(check(t) for t in nat)


def test_words_lists_the_prelude_operations_by_hash(tmp_path):
    exp = _compile("e = natIfEq\nm = natMul\n")
    assert write_words(exp, tmp_path / "words.tsv") == 3      # natAdd too
    rows = [ln.split("\t") for ln in (tmp_path / "words.tsv").read_text().splitlines()]
    assert [r[1] for r in rows] == ["add", "mul", "ifeq"]
    for h, op, atoms, term in rows:
        name = {v: k for k, v in WORD_OPS.items()}[op]
        assert h == structural_hash(ski_expand(Atom(name), exp.env))
        assert int(atoms) > 0 and term


def test_a_program_defining_its_own_operation_keeps_it(tmp_path):
    """A program's own natAdd is its code: not the prelude's, and not listed
    in words.tsv, whose operations a runtime replaces with native ones."""
    exp = _compile("natAdd m n = m\nx = natAdd Zero (Suc Zero)\n")
    assert exp.rule_kinds.get("natAdd", ("",))[0] != "prelude"
    assert write_words(exp, tmp_path / "words.tsv") == 0
    assert not (tmp_path / "words.tsv").exists()
