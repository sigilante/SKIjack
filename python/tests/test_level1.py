"""The level-1 run: EXAMPLES.md sections 3 and 4, and the paper's tower.

Every number here was measured on this expander against the artifact's
own counts.  Values are read behaviorally throughout: the result is
peeled by probing with one marker per result constructor, and a quoted
payload is decoded by probing with one marker per object constructor --
never by reading combinator syntax.
"""

import pytest
from aviary_kernel.terms import App, Atom, pretty

from skijack.expand import expand_program
from skijack.parser import parse
from skijack.render import render_ascii
from skijack.run import (decode, peel, run_level0, run_level1, run_policy,
                         timeout_constructor)

from conftest import source

LEXICONS = ["ascii", "unicode"]
CAP = 2_000_000


@pytest.fixture(scope="module")
def built():
    out = {}
    for stem in ("level1-flipa", "tower"):
        for lx in LEXICONS:
            out[(stem, lx)] = expand_program(parse(source(stem, lx), lx))
    out[("t3", "ascii")] = expand_program(parse(
        source("interp-t3", "ascii")
        + "answer := wf5Abs |- <K I Err>@5\n"
          "starved := wf5Abs |- <K I Err>@1\n", "ascii"))
    return out


def run_and_read(exp, name, max_steps=CAP, fuel=None):
    """(constructor, decoded payload or None, contractions)."""
    p = exp.level1[name]
    out = run_level1(p, max_steps, fuel=fuel)
    assert out.whnf, f"{name}: {out.status.value} after {out.steps}"
    ctor, fields = peel(out.term, p.result_type, max_steps=max_steps)
    payload = None
    if fields:
        payload = render_ascii(decode(fields[0], p.object_type,
                                      max_steps=max_steps))
    return ctor, payload, out.steps


# ------------------------------------------- EXAMPLES.md section 4

def test_the_answer_line_of_examples_section_4(built):
    """`answer := wf5Abs |- <K I Err>@5` reduces to `RVal <I>`: the K equation
    fires on the encoded K and discards the encoded Err, which never
    reaches head position."""
    ctor, payload, steps = run_and_read(built[("t3", "ascii")], "answer")
    assert (ctor, payload) == ("RVal", "I")
    assert steps == 574


def test_the_same_program_starved_of_fuel_times_out(built):
    """`K I Err` needs two step-attempts -- one contraction and the
    no-redex check -- so `@1` is the largest budget that times out."""
    assert run_and_read(built[("t3", "ascii")], "starved")[0] == "RTime"


@pytest.mark.parametrize("fuel,want", [(0, "RTime"), (1, "RTime"),
                                       (2, "RVal"), (5, "RVal")])
def test_the_fuel_boundary_is_where_examples_says(built, fuel, want):
    """EXAMPLES.md section 3: "fuel k permits k step-attempts of which the
    last must be the no-redex check"."""
    assert run_and_read(built[("t3", "ascii")], "answer", fuel=fuel)[0] == want


# ------------------------------------------- EXAMPLES.md section 3

@pytest.mark.parametrize("lx", LEXICONS)
def test_the_quoted_flipA_program_runs_in_29191_contractions(built, lx):
    ctor, payload, steps = run_and_read(built[("level1-flipa", lx)], "answer")
    assert steps == 29191
    assert (ctor, payload) == ("Just", "I")


@pytest.mark.parametrize("lx", LEXICONS)
def test_fuel_40_times_out(built, lx):
    """EXAMPLES.md section 3: "Fuel 40 times out"."""
    assert run_and_read(built[("level1-flipa", lx)], "short")[0] == "Nothing"


@pytest.mark.parametrize("lx", LEXICONS)
def test_the_level_0_program_still_reduces_in_40_contractions(built, lx):
    """The same program at level 0, for the contrast section 3 draws."""
    e = built[("level1-flipa", lx)]
    prog = App(App(e.term("flipA"),
                   App(App(e.term("pair"), Atom("K")), Atom("I"))), Atom("K"))
    out = run_level0(prog, 10_000, whnf_only=False)
    assert (pretty(out.term), out.steps) == ("I", 40)


# ------------------------------------------------------- T0 and T1

@pytest.mark.parametrize("lx", LEXICONS)
def test_T0_as_a_level_1_declaration(built, lx):
    ctor, payload, steps = run_and_read(built[("tower", lx)], "t0")
    assert (ctor, payload, steps) == ("Just", "K", 340)


@pytest.mark.parametrize("lx", LEXICONS)
def test_T1_emulator_over_unquoter(built, lx):
    """The paper's T1: whnfF 120 <UQ <I K>>."""
    ctor, payload, steps = run_and_read(built[("tower", lx)], "t1")
    assert steps == 91556
    assert (ctor, payload) == ("Just", "K")


def test_the_surface_UQ_is_the_artifacts_43_atom_unquoter(built, oracle):
    e = built[("tower", "ascii")]
    assert e.sizes["UQ"] == 43
    assert pretty(e.term("UQ")) == pretty(oracle.term("UQ"))


def test_three_is_the_artifacts_scott_numeral(built, oracle):
    """`three = Suc (Suc (Suc Zero))`, spelled as the artifact spells it;
    the literal `3` is the same term (test_literals)."""
    e = built[("tower", "ascii")]
    assert pretty(e.term("three")) == pretty(oracle.natP(3))


# ------------------------------------------------------------- T2

@pytest.mark.slow
def test_T2_the_tower(built, oracle):
    """The paper's T2, the prize: whnfF 500 <whnfF 3 <I K>>, half a
    million host contractions.  Run once, ASCII only -- the Unicode
    spelling is asserted to compile to the same datum in test_quote.py.
    """
    e = built[("tower", "ascii")]
    p = e.level1["t2"]
    out = run_level1(p, 5_000_000)
    assert out.whnf
    assert out.steps == 504930
    ctor, fields = peel(out.term, p.result_type, max_steps=5_000_000)
    assert ctor == "Just" and len(fields) == 1

    # The payload is the quotation of the *level-0* answer, `just <K>`.
    # Unquote it with the surface UQ and read it behaviorally; `pretty`
    # is never called, because the tree unfolding of a shared graph this
    # size is enormous.
    uq = run_level0(App(e.term("UQ"), fields[0]), 5_000_000)
    assert uq.whnf and uq.steps == 178
    m = run_level0(App(App(uq.term, Atom("mNo")), Atom("mJu")), 5_000_000)
    assert _head(m.term).name == "mJu"          # it is a level-0 Just
    inner = run_level0(
        App(App(App(App(m.term.arg, Atom("cS")), Atom("cK")), Atom("cI")),
            Atom("cA")), 5_000_000)
    assert _head(inner.term).name == "cK"       # carrying the encoded K


def _head(t):
    while isinstance(t, App):
        t = t.fn
    return t


# ------------------------------------------------------ fuel policy

@pytest.mark.parametrize("lx", LEXICONS)
def test_the_fuel_policy_deepens_iteratively(built, lx):
    """RUNTIME-DESIGN.md section 3c: elided fuel means runtime policy --
    doubling the budget until a value or a cap."""
    e = built[("level1-flipa", lx)]
    p = e.level1["policy"]
    assert p.fuel == "policy"
    r = run_policy(p, start=8, cap=4096, max_steps=CAP)
    assert r.budgets == (8, 16, 32, 64)
    assert r.budget == 64 and not r.timed_out
    assert r.constructor == "Just"
    assert render_ascii(decode(r.payload, p.object_type)) == "I"
    assert r.steps == 29191          # the same run as an explicit @41


def test_the_cap_is_reported_not_hidden(built):
    e = built[("level1-flipa", "ascii")]
    r = run_policy(e.level1["policy"], start=2, cap=8, max_steps=CAP)
    assert r.timed_out and r.budget is None
    assert r.budgets == (2, 4, 8)
    assert r.constructor == "Nothing"


def test_the_timeout_constructor_is_the_last_terminal_not_the_last_ctor(built):
    """For `maybe === Nothing | Just term` the loop's timeout is
    `Nothing`, which is *not* last in declaration order."""
    flipa = built[("level1-flipa", "ascii")]
    assert timeout_constructor(flipa.level1["answer"].result_type) == "Nothing"
    t3 = built[("t3", "ascii")]
    assert timeout_constructor(t3.level1["answer"].result_type) == "RTime"


# ------------------------------- the paper's reify/eval boundary (S12)

def test_a_level0_name_may_be_quoted_but_a_parameter_may_not():
    """The Limitations section's worked example.

    `<k2>` and `<I K>` compile because the compiler knows before
    anything runs which term the quotation contains.  `<x>` does not,
    because `x` is bound while something runs -- and the datum it asks
    for is exactly the one `<k2>` already emits.  The line is *when* the
    term is known, not what it is.
    """
    import skijack
    from skijack import corpus
    from skijack.errors import SkijackError

    base = corpus.read("interp-whnff")
    named = skijack.compile(base + "k2 = K K\nq := whnfF |- <k2>@10\n")
    assert named.sizes["k2"] == 2
    assert named.sizes["q"] == 741

    written = skijack.compile(base + "q2 := whnfF |- <I K>@10\n")
    assert written.sizes["q2"] == 739

    with pytest.raises(SkijackError) as excinfo:
        skijack.compile(base + "f x = <x>\ng := f I\n")
    msg = " ".join(str(excinfo.value).split())
    assert "names neither table" in msg
    assert "not a level-0 name" in msg
