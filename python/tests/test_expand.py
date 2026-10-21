"""Codegen: the exact terms and sizes recorded in EXAMPLES.md.

Every expected value below is a measurement of the reference expander
(aviary-kernel's bracket abstraction), quoted from EXAMPLES.md sections
1 to 3.
"""

import pytest

from aviary_kernel.terms import pretty

from skijack.check import CaseError, ScopeError
from skijack.expand import ExpandError, axis_chain, expand_program
from skijack.parser import parse, parse_ascii

from conftest import EXPANDABLE, source

LEXICONS = ["ascii", "unicode"]


@pytest.fixture(scope="module")
def built():
    out = {}
    for stem in EXPANDABLE:
        for lx in LEXICONS:
            out[(stem, lx)] = expand_program(parse(source(stem, lx), lx))
    return out


def check(built, stem, lx, name, atoms, term):
    e = built[(stem, lx)]
    assert pretty(e.term(name)) == term, name
    assert e.size(name) == atoms, name


# ------------------------------------------------- EXAMPLES.md section 1

SECTION1 = [
    ("Zero", 1, "K"),
    ("Suc", 8, "S (K K) (S (K (S I)) K)"),
    ("inc", 8, "S (K K) (S (K (S I)) K)"),
    ("dec", 7, "S (S I (K K)) (K I)"),
]


@pytest.mark.parametrize("lx", LEXICONS)
@pytest.mark.parametrize("name,atoms,term", SECTION1,
                         ids=[r[0] for r in SECTION1])
def test_section1_exact_terms(built, lx, name, atoms, term):
    check(built, "sec1-nat", lx, name, atoms, term)


@pytest.mark.parametrize("lx", LEXICONS)
def test_inc_is_identical_to_suc(built, lx):
    e = built[("sec1-nat", lx)]
    assert pretty(e.term("inc")) == pretty(e.term("Suc"))


@pytest.mark.parametrize("lx", LEXICONS)
@pytest.mark.parametrize("name,atoms", [("add", 42), ("sub", 43)])
def test_section1_reference_sizes(built, lx, name, atoms):
    """The reference construction of EXAMPLES.md (per-equation generator tied
    with Y).  The probes are mandatory; these sizes are a reference."""
    assert built[("sec1-nat", lx)].size(name) == atoms


@pytest.mark.parametrize("lx", LEXICONS)
def test_y_is_the_first_fourteen_atoms_of_a_recursive_arm(built, lx):
    e = built[("sec1-nat", lx)]
    y = "S (K (S I I)) (S (S (K S) K) (K (S I I)))"
    assert pretty(e.term("add")).startswith(y)
    assert pretty(e.term("sub")).startswith(y)


# ------------------------------------------------- EXAMPLES.md section 2

SECTION2 = [
    ("C", 10, "S (S (K S) (S (K K) S)) (K K)"),
    ("flipK1", 11, "S (S (K S) (S (K K) S)) (K K) K"),
    ("flipK2", 5, "S (K (S K)) K"),
]


@pytest.mark.parametrize("lx", LEXICONS)
@pytest.mark.parametrize("name,atoms,term", SECTION2,
                         ids=[r[0] for r in SECTION2])
def test_section2_exact_terms(built, lx, name, atoms, term):
    check(built, "sec2-c", lx, name, atoms, term)


@pytest.mark.parametrize("lx", LEXICONS)
def test_the_macro_leaves_no_runtime_trace(built, lx):
    assert "flip" not in built[("sec2-c", lx)].terms


# ------------------------------------------------- EXAMPLES.md section 3

FLIPA = ("S (S (K (S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K))) "
         "(S I (K (K I)))) (S I (K K))")


@pytest.mark.parametrize("lx", LEXICONS)
def test_section3_flipA(built, lx):
    check(built, "sec3-swap", lx, "flipA", 29, FLIPA)


@pytest.mark.parametrize("lx", LEXICONS)
def test_section3_prelude(built, lx):
    check(built, "sec3-swap", lx, "pair", 17,
          "S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K)")
    check(built, "sec3-swap", lx, "hd", 4, "S I (K K)")
    check(built, "sec3-swap", lx, "tl", 5, "S I (K (K I))")


# ------------------------------------------------------- the passes

def test_axis_chain_follows_nocks_numbering():
    assert axis_chain(1) == []
    assert axis_chain(2) == ["hd"]
    assert axis_chain(3) == ["tl"]
    assert axis_chain(6) == ["tl", "hd"]     # the head of the tail
    assert axis_chain(7) == ["tl", "tl"]
    with pytest.raises(ExpandError):
        axis_chain(0)


def test_axis_six_is_the_head_of_the_tail():
    e = expand_program(parse_ascii("f c = 6@c\ng c = hd (tl c)\n"))
    assert pretty(e.term("f")) == pretty(e.term("g"))


def test_cells_of_three_are_right_nested():
    e = expand_program(parse_ascii("f a b c = [a b c]\n"
                                   "g a b c = pair a (pair b c)\n"))
    assert pretty(e.term("f")) == pretty(e.term("g"))


def test_case_uses_declaration_order_not_source_order():
    forward = expand_program(parse_ascii(
        "nat === Zero | Suc nat\nf n = n |> { Zero Zero ; Suc m m }\n"))
    shuffled = expand_program(parse_ascii(
        "nat === Zero | Suc nat\nf n = n |> { Suc m m ; Zero Zero }\n"))
    assert pretty(forward.term("f")) == pretty(shuffled.term("f")) \
        == "S (S I (K K)) (K I)"


def test_incomplete_case_is_refused():
    """Stage A check (b)."""
    with pytest.raises(CaseError, match="missing branch"):
        expand_program(parse_ascii(
            "nat === Zero | Suc nat\nf n = n |> { Zero Zero }\n"))


def test_partial_application_of_a_macro_is_an_error():
    with pytest.raises(ExpandError, match="partial application of a macro"):
        expand_program(parse_ascii("flip f x y :=* f y x\ng a = flip K a\n"))


def test_capturing_macro_is_refused_clearly():
    with pytest.raises(ExpandError, match="capturing form is not implemented"):
        expand_program(parse_ascii("m x :=! K x\ng a = m a\n"))


def test_macro_substitution_avoids_capture():
    """The macro's body binds ``x``; handing it an argument that mentions
    ``x`` must not capture it: ``m x`` is ``\\x'. x x'``, not ``\\x. x x``."""
    e = expand_program(parse_ascii("m f :=* \\x. f x\ng x = m x\n"))
    direct = expand_program(parse_ascii("h y = \\z. y z\n"))
    captured = expand_program(parse_ascii("h y = \\z. z z\n"))
    assert e.term("g") == direct.term("h")
    assert e.term("g") != captured.term("h")


def test_unresolved_name_is_an_error():
    """Stage A check (f)."""
    with pytest.raises(ScopeError, match="unresolved name"):
        expand_program(parse_ascii("f x = x nowhere\n"))


def _yes_no(term):
    from aviary_kernel.terms import App, Atom
    from skijack.run import run_level0
    return run_level0(App(App(term, Atom("yes")), Atom("no")), 200_000).term.name


def test_mutual_recursion_ties_one_fixpoint_per_group():
    """A group of mutually recursive equations is one fixpoint: its
    generator returns the tuple of the members' codes, each taking the
    group, and a member is its projection."""
    from skijack.probe import Prober
    e = expand_program(parse_ascii(
        "nat  === Zero | Suc nat\n"
        "bool === Yes | No\n"
        "even n = n |> { Zero Yes ; Suc k (odd k) }\n"
        "odd  n = n |> { Zero No ; Suc k (even k) }\n"
        "a3 n = n |> { Zero Zero ; Suc k (Suc (b3 k)) }\n"
        "b3 n = n |> { Zero Zero ; Suc k (c3 k) }\n"
        "c3 n = n |> { Zero Zero ; Suc k (a3 k) }\n"))
    pr = Prober(e)
    from aviary_kernel.terms import App
    for k in range(7):
        assert _yes_no(App(e.terms["even"], pr.nat(k))) == ("yes" if k % 2 == 0 else "no")
        assert _yes_no(App(e.terms["odd"], pr.nat(k))) == ("no" if k % 2 == 0 else "yes")
        assert pr.read_nat(App(e.terms["a3"], pr.nat(k))) == (k + 2) // 3


def test_mutual_recursion_inside_a_core():
    from skijack.probe import Prober
    from aviary_kernel.terms import App
    e = expand_program(parse_ascii(
        "nat === Zero | Suc nat\n"
        "bool === Yes | No\n"
        "c := {\n"
        "  ev n = n |> { Zero Yes ; Suc m (od m) }\n"
        "  od n = n |> { Zero No ; Suc m (ev m) }\n"
        "}\n"))
    pr = Prober(e)
    assert [_yes_no(App(e.terms["c.ev"], pr.nat(k))) for k in range(4)] == ["yes", "no", "yes", "no"]


def test_a_self_recursive_equation_is_compiled_as_before():
    """A group of one keeps its own fixpoint, Y nameGen: no term the
    corpus compiled before changes (the conformance export is compared
    byte for byte)."""
    e = expand_program(parse_ascii(
        "nat === Zero | Suc nat\n"
        "add m n = n |> { Zero m ; Suc k (Suc (add m k)) }\n"))
    assert e.sizes["add"] == 42


def test_quotation_without_an_object_type_is_refused():
    """A quoted term is written in some interpreter's alphabet, so the
    program must declare one (SURFACE-LANGUAGE-DESIGN.md section 6a)."""
    with pytest.raises(ExpandError, match="quotation needs an object type"):
        expand_program(parse_ascii("p := <K>\n"))


def test_quotation_inside_an_arm_body_is_still_refused():
    """Step 4 packages quotation only at a top-level definition."""
    with pytest.raises(ExpandError, match="a quotation stands only as the whole right side"):
        expand_program(parse_ascii(
            "term === S | K | I | App term term\n"
            "maybe === Nothing | Just term\n"
            "f x = <K> x\n"))


def test_an_arm_may_shadow_a_builtin_bird_name():
    e = expand_program(parse_ascii("C f x y = f y x\n"))
    assert e.backend["C"] == "Cc"
    assert e.size("C") == 10


def _nat_of(e, name):
    import sys
    from skijack.probe import Prober
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 100_000))
    try:
        return Prober(e).read_nat(e.terms[name])
    finally:
        sys.setrecursionlimit(old)


_NAT = "nat === Zero | Suc nat\n"
_ADD = "add m n = n |> { Zero m ; Suc k (Suc (add m k)) }\n"


@pytest.mark.parametrize("src,name,want", [
    (_NAT + "r := (\\g. g) (Suc Zero)\ng := Zero\n", "r", 1),
    (_NAT + "g := Zero\nr := (\\g. g) (Suc Zero)\n", "r", 1),
    (_NAT + "p n = n |> { Zero Zero ; Suc g g }\ng = Suc (Suc Zero)\nq := p (Suc Zero)\n", "q", 0),
    (_NAT + "f g = g\nr := f (Suc Zero)\ng := Zero\n", "r", 1),
    (_NAT + _ADD + "f x y = y\nt := add 2 3\n", "t", 5),
    (_NAT + "ev n = n |> { Zero Zero ; Suc k (od k) }\n"
            "od n = n |> { Zero (Suc Zero) ; Suc k (ev k) }\ng = Suc (Suc Zero)\nt := ev 3\n", "t", 1),
    (_NAT + "t := Suc Zero\nc1 := K\nf0 := I\n", "t", 1),
], ids=["lambda, global after", "lambda, global before", "branch, global after",
        "equation binder, global after", "a recursion's own parameter",
        "a group's own parameter", "a constructor's binders"])
def test_a_binder_is_never_a_program_name(src, name, want):
    """A binder shadows everything (SPEC.md §5), whichever program name
    shares its spelling and wherever that name is defined: aviary expands
    a rule body's defined names before abstracting its formals, so the
    expander gives every formal a name no source can spell."""
    assert _nat_of(expand_program(parse_ascii(src)), name) == want


def test_a_repeated_binder_binds_its_last_occurrence():
    e = expand_program(parse_ascii(_NAT + "f x x = x\nt := f Zero (Suc Zero)\n"
                                   "m x :=* \\y. \\y. x\ng z = m z\nu := g 1 2 3\n"))
    assert (_nat_of(e, "t"), _nat_of(e, "u")) == (1, 1)


@pytest.mark.parametrize("src", ["f S = S\n", "f x = \\K. x\n",
                                 _NAT + "f n = n |> { Zero Zero ; Suc I I }\n"])
def test_a_binder_named_S_K_or_I_is_refused(src):
    """S, K and I always name the ISA, so such a binder could never be
    used; both checks and the unchecked expander refuse it by name."""
    with pytest.raises(ScopeError, match="a binder named"):
        expand_program(parse_ascii(src))
    with pytest.raises(ExpandError, match="a binder named"):
        expand_program(parse_ascii(src), check=False)


def test_every_output_term_is_closed_over_S_K_I(built):
    from aviary_kernel.terms import free_vars
    for key, e in built.items():
        for name, t in e.terms.items():
            assert free_vars(t) <= {"S", "K", "I"}, (key, name)


def test_a_program_may_name_a_combinator_after_a_prelude_binder():
    """The prelude's rules once bound ``x``, ``y``, ``c`` (pair) and ``p``
    (hd, tl) by those names, so a program combinator called ``x`` collided
    with the binder inside the host's expansion of a cell.  The binders
    are sentinels now; the terms are unchanged, which the pinned sizes
    elsewhere in this suite prove."""
    for src in ("nat === Zero | Suc nat\nx := [Zero Zero]\n",
                "nat === Zero | Suc nat\np := 2@[Zero Zero]\n",
                "nat === Zero | Suc nat\nc := 3@[Zero (Suc Zero)]\n",
                "nat === Zero | Suc nat\nf n = [n n]\nq := f Zero\n"):
        e = expand_program(parse_ascii(src))
        assert all(name in e.terms for name in ("x", "p", "c", "f", "q") if name in src.split())


def test_the_expander_refuses_to_emit_a_free_name(monkeypatch):
    """SPEC.md §0: the expander refuses to emit a term that is not closed
    over S, K and I.  Resolution refuses an unresolved name first, so the
    host is made to hand back an open term for one name."""
    import importlib
    from aviary_kernel.terms import App, Atom
    X = importlib.import_module("skijack.expand")
    real = X._ski_expand

    def leaky(t, env):
        out = real(t, env)
        return App(out, Atom("ghost")) if t == Atom("x") else out
    monkeypatch.setattr(X, "_ski_expand", leaky)
    with pytest.raises(ExpandError, match="free name.*ghost"):
        expand_program(parse_ascii("x := K\n"))


@pytest.mark.parametrize("src,match", [
    ("f x = <K>\n", "a quotation stands only as the whole right side of a definition"),
    ("f x = K ?^/nat\n", r"'\?\^' compiles only inside a quotation"),
    ("f x = ns{/nat => <K>}\n", "a namespace literal stands only as the whole right side"),
    ("m x :=* <?^/nat>\nq := m K\n", "a macro's body or argument holds a scry"),
])
def test_a_misplaced_level_1_form_is_refused_by_its_rule(src, match):
    """Each form is refused with the place SPEC.md gives it, with checking
    off too, where the expander's own refusal is the one a caller sees."""
    from skijack import corpus
    head = corpus.read("scry-ns").split("resolve := ")[0]
    with pytest.raises(ExpandError, match=match):
        expand_program(parse_ascii(head + src), check=False)
