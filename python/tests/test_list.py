"""The prelude's list operations (expand.LIST_NAMES), on any list type, and
their list constraint (typecheck)."""

import sys

import pytest
from aviary_kernel.environment import Environment
from aviary_kernel.reduce import reduce
from aviary_kernel.terms import App, Atom

import skijack
from skijack.expand import LIST_NAMES
from skijack.templates import check, templates, write_words
from skijack.typecheck import TypeMismatchError

TYPES = ("nat === Zero | Suc nat\n"
         "text === TNil | TCons nat text\n"
         "bool === F | T\n")
OPS = ("len = listLength\nat = listAt\napp = listAppend\n"
       "tk = listTake\ndr = listDrop\n")


@pytest.fixture(autouse=True)
def _deep_recursion():
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 100_000))
    yield
    sys.setrecursionlimit(old)


def _compile(body: str):
    return skijack.compile(TYPES + body, lexicon="ascii")


def _num(exp, n):
    t = exp.terms["Zero"]
    for _ in range(n):
        t = App(exp.terms["Suc"], t)
    return t


def _list(exp, xs):
    t = exp.terms["TNil"]
    for x in reversed(xs):
        t = App(App(exp.terms["TCons"], _num(exp, x)), t)
    return t


def _whnf(t, env):
    return reduce(t, env, whnf_only=True, max_steps=10**7, max_size=10**9).term


def _value(t, env):
    """A numeral's value, read by applying it to two markers."""
    n = 0
    while True:
        r = _whnf(App(App(t, Atom("zz")), Atom("ss")), env)
        if r == Atom("zz"):
            return n
        assert isinstance(r, App) and r.fn == Atom("ss")
        t, n = r.arg, n + 1


def _elements(t, env):
    """A list's elements, each a numeral, read by applying it to markers."""
    out = []
    while True:
        r = _whnf(App(App(t, Atom("nn")), Atom("cc")), env)
        if r == Atom("nn"):
            return out
        assert isinstance(r, App) and isinstance(r.fn, App) and r.fn.fn == Atom("cc")
        out.append(_value(r.fn.arg, env))
        t = r.arg


LISTS = [[], [5], [1, 2], [3, 0, 4]]


def test_the_operations_compute_on_small_lists():
    exp = _compile(OPS)
    env = Environment()
    ap = lambda name, *args: _fold(exp.terms[name], args)
    for xs in LISTS:
        lx = _list(exp, xs)
        assert _value(ap("len", lx), env) == len(xs)
        for k in range(len(xs) + 2):
            got = _whnf(App(App(ap("at", lx, _num(exp, k)), Atom("dd")), Atom("zz")), env)
            if k < len(xs):
                assert _value(ap("at", lx, _num(exp, k), Atom("dd")), env) == xs[k]
            else:
                assert got == App(Atom("dd"), Atom("zz"))      # past the end: d
            assert _elements(ap("tk", lx, _num(exp, k)), env) == xs[:k]
            assert _elements(ap("dr", lx, _num(exp, k)), env) == xs[k:]
        for ys in LISTS:
            assert _elements(ap("app", lx, _list(exp, ys)), env) == xs + ys


def _fold(f, args):
    for a in args:
        f = App(f, a)
    return f


def test_a_result_list_is_the_program_s_own_type():
    """nil and cons are every list type's constructors, so an operation's
    result is a value of the operand's type: a program cases on it."""
    exp = _compile(OPS + "hd l = l |> { TNil Zero; TCons h t h }\n"
                   "x := hd (listDrop (TCons 1 (TCons 2 TNil)) 1)\n"
                   "y := hd (listAppend TNil (TCons 3 TNil))\n")
    env = Environment()
    assert _value(exp.terms["x"], env) == 2
    assert _value(exp.terms["y"], env) == 3


def test_a_program_naming_none_is_compiled_as_before():
    exp = _compile("x = TCons Zero TNil\n")
    assert not set(LIST_NAMES) & set(exp.terms)
    assert not any(n.startswith("list") for n in exp.env.definitions)
    assert exp.env.lookup("\x00nil") is None


def test_only_the_named_operations_are_installed():
    exp = _compile("d = listDrop\n")
    assert "listDrop" in exp.terms
    for other in ("listLength", "listAt", "listAppend", "listTake", "natAdd"):
        assert exp.env.lookup(other) is None


def test_the_operations_templates_abstract_to_their_terms():
    exp = _compile(OPS)
    ts = [t for t in templates(exp) if t.name.startswith("list")]
    assert len(ts) >= 12
    assert all(check(t) for t in ts)


def test_words_lists_no_list_operation_yet(tmp_path):
    """A runtime replaces only the operations words.tsv names, and none
    runs lists natively yet."""
    exp = _compile(OPS)
    assert write_words(exp, tmp_path / "words.tsv") == 0


def test_a_program_defining_its_own_operation_keeps_it():
    exp = _compile("listLength l = Zero\nx = listLength (TCons 1 TNil)\n")
    assert exp.rule_kinds.get("listLength", ("",))[0] != "prelude"
    assert _value(exp.terms["x"], Environment()) == 0


# ------------------------------------------------------------ the typing

def refuses(src, match):
    with pytest.raises(TypeMismatchError, match=match):
        skijack.compile(TYPES + src)


def test_the_element_is_the_list_type_s():
    """listAt gives the list's element: a text's is a nat, so the default
    must be one, and the result is one."""
    _compile("x := listAt (TCons 1 TNil) 0 Zero\ny := Suc (listAt (TCons 1 TNil) 0 Zero)\n")
    refuses("x := listAt (TCons 1 TNil) 0 T\n", "expected (nat|bool), found (bool|nat)")
    refuses("bits === BNil | BCons bool bits\nx := Suc (listAt (BCons T BNil) 0 F)\n",
            "expected (nat|bool), found (bool|nat)")


def test_a_list_operation_refuses_other_data():
    refuses("x := listLength T\n", "expected a list, found bool")
    refuses("x := listLength (Suc Zero)\n", "expected a list, found nat")


def test_a_list_operation_refuses_a_function():
    refuses("x := listLength I\n", "a function .* where a list is expected")


def test_the_index_is_a_numeral():
    refuses("x := listTake (TCons 1 TNil) T\n", "expected a numeral, found bool")


def test_the_list_constraint_holds_through_an_alias_and_a_binder():
    refuses("len = listLength\nx := len T\n", "expected a list, found bool")
    refuses("first l = listAt l 0 Zero\nx := first T\n", "expected (a list|text), found bool")
    _compile("first l = listAt l 0 Zero\nx := first (TCons 2 TNil)\n")


def test_two_list_types_are_not_one():
    refuses("prog === Done | Then bool prog\nx := listAppend TNil (Then T Done)\n",
            "expected (text|prog), found (prog|text)")


def test_the_prelude_s_list_is_a_list():
    exp = _compile("x := listLength (cons Zero (cons Zero nil))\ny := listAt (cons 4 nil) 0 Zero\n")
    env = Environment()
    assert _value(exp.terms["x"], env) == 2 and _value(exp.terms["y"], env) == 4
    refuses("x := Suc (listAt (cons T nil) 0 F)\n", "expected (nat|bool), found (bool|nat)")
