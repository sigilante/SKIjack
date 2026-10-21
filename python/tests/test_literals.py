"""Numeral literals (SPEC.md §4): ``5`` is the Scott numeral
``suc (suc (suc (suc (suc zero))))`` of a numeral type.

The tests hold the literal to its hand-spelled twin: the same terms,
with and without the inliner, and the same value when run."""

import sys

import pytest
from aviary_kernel.environment import Environment
from aviary_kernel.reduce import reduce
from aviary_kernel.terms import App, Atom

import skijack
from skijack import ast as A
from skijack.check import check_program
from skijack.expand import PRELUDE_NAMES, SUC_TERM, ZERO_TERM, numeral
from skijack.parser import parse, parse_expr_text
from skijack.render import render
from skijack.spec0 import in_subset
from skijack.typecheck import typecheck_program

NAT = "nat === Zero | Suc nat\n"

LITERAL = NAT + """\
five = 5
none = 0
seven = natAdd 5 2
pred n = n |> { Zero Zero ; Suc m m }
four = pred 5
same = natIfEq 3 3 Zero (Suc Zero)
"""

SPELLED = NAT + """\
five = Suc (Suc (Suc (Suc (Suc Zero))))
none = Zero
seven = natAdd (Suc (Suc (Suc (Suc (Suc Zero))))) (Suc (Suc Zero))
pred n = n |> { Zero Zero ; Suc m m }
four = pred (Suc (Suc (Suc (Suc (Suc Zero)))))
same = natIfEq (Suc (Suc (Suc Zero))) (Suc (Suc (Suc Zero))) Zero (Suc Zero)
"""


@pytest.fixture(autouse=True)
def _deep_recursion():
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 100_000))
    yield
    sys.setrecursionlimit(old)


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


def _stage_b(text):
    return [p.message for p in typecheck_program(parse(text, "ascii"), PRELUDE_NAMES)]


# ----------------------------------------------------------------- terms

@pytest.mark.parametrize("inline", [False, True])
def test_a_literal_compiles_to_its_hand_spelled_twin(inline):
    lit = skijack.compile(LITERAL, lexicon="ascii", inline=inline)
    twin = skijack.compile(SPELLED, lexicon="ascii", inline=inline)
    assert set(lit.terms) == set(twin.terms)
    for name in twin.terms:
        assert lit.terms[name] == twin.terms[name], name


def test_a_literal_is_the_prelude_numeral():
    exp = skijack.compile(NAT + "x = 3\n", lexicon="ascii")
    assert exp.terms["Zero"] == ZERO_TERM == Atom("K")
    assert exp.terms["Suc"] == SUC_TERM
    assert exp.terms["x"] == App(SUC_TERM, App(SUC_TERM, App(SUC_TERM, ZERO_TERM)))
    assert exp.terms["x"] == numeral(3)


def test_a_program_that_defines_suc_does_not_change_a_literal():
    exp = skijack.compile("suc n = n\nzero = I\nx = 2\n", lexicon="ascii")
    assert exp.terms["x"] == numeral(2)


def test_a_literal_runs_to_its_value():
    exp = skijack.compile(LITERAL, lexicon="ascii")
    env = Environment()
    assert [_value(exp.terms[n], env) for n in ("none", "five", "seven", "four")] \
        == [0, 5, 7, 4]


def test_a_literal_is_the_size_of_its_numeral():
    """8n + 1 atoms: the literal is unary, as the numeral is."""
    exp = skijack.compile(NAT + "x = 200\n", lexicon="ascii")
    from aviary_kernel.terms import size
    assert size(exp.terms["x"]) == 8 * 200 + 1


# ---------------------------------------------------------------- syntax

def test_both_lexicons_render_a_literal_as_written():
    tree = parse(LITERAL, "ascii")
    for lx in ("ascii", "unicode"):
        assert parse(render(tree, lx), lx) == tree


def test_fuel_and_picks_keep_their_numbers():
    assert parse_expr_text("<t>@10") == A.Quote(A.Name("t"), 10)
    assert parse_expr_text("<t>₁₀", "unicode") == A.Quote(A.Name("t"), 10)
    assert parse_expr_text("3@p 3") == A.App(A.Pick(3, A.Name("p")), A.Num(3))


def test_a_literal_is_read_in_base_ten():
    assert parse_expr_text("007") == A.Num(7)
    assert parse_expr_text("10") == A.Num(10)


def test_a_literal_is_outside_skijack_0():
    assert in_subset(parse(NAT + "x = 1\n", "ascii")) == "Num"


def test_a_literal_inside_a_quotation_is_refused():
    text = "term === S | K | I | App term term\nt := <S 3>\n"
    problems = check_program(parse(text, "ascii"), PRELUDE_NAMES)
    assert any("the literal 3 inside a quotation" in p.message for p in problems)


# ---------------------------------------------------------------- Stage B

def test_a_literal_defaults_to_the_one_declared_numeral_type():
    assert _stage_b(LITERAL) == []
    assert _stage_b(NAT + "bool === F | T\nx = 3\n") == []


def test_with_no_numeral_type_declared_a_literal_is_fuel():
    assert _stage_b("x = suc 4\ny = natAdd 2 3\n") == []


def test_with_two_numeral_types_the_context_must_say_which():
    two = NAT + "n2 === Z2 | S2 n2\n"
    assert _stage_b(two + "x = Suc 3\ny = S2 3\nz = natAdd x 1\n") == []
    (msg,) = _stage_b(two + "x = 3\n")
    assert "could be any of nat, n2" in msg
    assert "a signature does not choose" in msg


def test_a_literal_where_another_type_is_expected_is_refused():
    (msg,) = _stage_b(NAT + "bool === F | T\nx = 3 |> { F Zero ; T Zero }\n")
    assert "the literal 3 where a value of type bool is expected" in msg


def test_a_definition_is_not_polymorphic_in_a_literal():
    """``inc`` settles on nat before it is generalized, so ``inc T`` fails."""
    (msg,) = _stage_b(NAT + "bool === F | T\ninc x = natAdd x 1\ny = inc T\n")
    assert "expected nat, found bool" in msg


def test_the_largest_literal_compiles_at_the_default_recursion_limit():
    """9,999 levels deep, past Python's default limit of 1,000: the
    expander raises the limit while it runs and puts it back."""
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(1000)
    try:
        exp = skijack.compile(NAT + "x := 9999\n", lexicon="ascii")
        assert sys.getrecursionlimit() == 1000
    finally:
        sys.setrecursionlimit(old)
    assert exp.sizes["x"] == 8 * 9999 + 1
