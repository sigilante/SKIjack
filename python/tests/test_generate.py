"""generate.py: shape discovery and the forms a type declaration makes.

Structural only -- nothing here reduces a term; test_interpreter.py runs
the compiled interpreters.
"""

import pytest

from aviary_kernel.terms import pretty

from skijack import ast as A
from skijack.expand import expand_program
from skijack.generate import (GenerateError, find_loop_types,
                              find_object_type, generate, is_interpreter_core)
from skijack.parser import parse, parse_ascii
from skijack.render import render

from conftest import source

TERM = "term === S | K | I | App term term\n"
MAYBE = "maybe === Nothing | Just term\n"


# ------------------------------------------------------- the object type

def test_object_type_is_found_by_shape():
    obj = find_object_type(parse_ascii(TERM + MAYBE))
    assert obj is not None
    assert obj.name == "term"
    assert obj.app.name == "App"
    assert [c.name for c in obj.leaves] == ["S", "K", "I"]


def test_object_type_of_the_five_constructor_alphabet():
    obj = find_object_type(parse_ascii(
        "term5 === S | K | I | App term5 term5 | Err\n"))
    assert obj.app.name == "App"
    assert [c.name for c in obj.leaves] == ["S", "K", "I", "Err"]
    assert obj.leaf_index("Err") == 3


def test_no_object_type_in_an_ordinary_program():
    assert find_object_type(parse_ascii(source("sec1-nat", "ascii"))) is None
    assert find_object_type(parse_ascii(source("sec2-c", "ascii"))) is None


def test_nat_is_not_mistaken_for_an_object_type():
    """`Suc nat` has one field, not two, so nat has no application
    constructor and nothing is generated for it."""
    assert find_object_type(parse_ascii("nat === Zero | Suc nat\n")) is None


def test_two_application_constructors_are_refused():
    with pytest.raises(GenerateError, match="exactly one, the application"):
        find_object_type(parse_ascii("t === S | App t t | Ap2 t t\n"))


def test_a_non_leaf_non_application_constructor_is_refused():
    with pytest.raises(GenerateError, match="every constructor must be a"):
        find_object_type(parse_ascii("t === S | App t t | Tag nat\n"))


def test_two_object_types_are_refused():
    with pytest.raises(GenerateError, match="more than one object type"):
        find_object_type(parse_ascii("t === S | App t t\nu === K | Ap u u\n"))


# --------------------------------------------------- the loop's two types

def test_maybe_shape_is_one_type_serving_as_both():
    p = parse_ascii(TERM + MAYBE)
    lt = find_loop_types(p, find_object_type(p))
    assert lt.same
    assert (lt.stepped.name, lt.done.name) == ("Just", "Nothing")
    assert (lt.value.name, lt.timeout.name) == ("Just", "Nothing")
    assert lt.o_rest == ()
    assert lt.mapping == (("Nothing", "Just"),)


def test_t3_shape_takes_the_last_two_outcome_shaped_declarations():
    p = parse_ascii(source("interp-t3", "ascii"))
    lt = find_loop_types(p, find_object_type(p))
    assert not lt.same
    assert lt.outcome.name == "outcome" and lt.result.name == "result"
    assert lt.stepped.name == "Stepped" and lt.done.name == "Done"
    assert [c.name for c in lt.o_rest] == ["Errd"]
    assert lt.value.name == "RVal" and lt.timeout.name == "RTime"
    assert lt.mapping == (("Done", "RVal"), ("Errd", "RErr"))


def test_missing_outcome_type_is_refused():
    p = parse_ascii(TERM)
    with pytest.raises(GenerateError, match="no step-outcome type"):
        find_loop_types(p, find_object_type(p))


def test_mismatched_outcome_and_result_sizes_are_refused():
    p = parse_ascii(TERM + "o === Step term | Done | Errd\nr === V term | T\n")
    with pytest.raises(GenerateError, match="one result constructor per"):
        find_loop_types(p, find_object_type(p))


# ----------------------------------------------------------- what it emits

def test_is_interpreter_core():
    p = parse_ascii(source("interp-t3", "ascii"))
    obj = find_object_type(p)
    cores = [d for d in p.decls if isinstance(d, A.Core)]
    assert [c.name for c in cores] == ["wf5Abs", "wf5Omg"]
    assert all(is_interpreter_core(c, obj) for c in cores)
    plain = parse_ascii(TERM + MAYBE + "c := {\n  f x = x\n}\n").decls[-1]
    assert not is_interpreter_core(plain, obj)


def test_generation_adds_the_walker_rebuilder_and_default_arms():
    g = generate(parse_ascii(source("interp-whnff", "ascii")))
    names = {d.name for d in g.decls if isinstance(d, A.Equation)}
    assert {"sp", "rb", "spApp", "rb1", "resS", "resK", "resI"} <= names
    assert {"stepS", "stepS1", "stepS2", "stepS3",
            "stepK", "stepK1", "stepK2", "stepI", "stepI1"} <= names


def test_generation_fills_each_core_with_step_and_loop():
    g = generate(parse_ascii(source("interp-t3", "ascii")))
    cores = {d.name: d for d in g.decls if isinstance(d, A.Core)}
    for name in ("wf5Abs", "wf5Omg"):
        equations = {x.name for x in cores[name].equations}
        assert {"stepErr", "step", "loop", "loop1"} <= equations


def test_a_written_step_or_loop_is_not_replaced():
    g = generate(parse_ascii(source("interp-whnff-written-loop", "ascii")))
    core = [d for d in g.decls if isinstance(d, A.Core)][0]
    loops = [x for x in core.equations if x.name == "loop"]
    steps = [x for x in core.equations if x.name == "step"]
    assert len(loops) == len(steps) == 1
    # the written loop, verbatim: loop n m = n Nothing (loop1 loop m)
    assert loops[0].binders == ("n", "m")


def test_a_user_definition_overrides_a_generated_one():
    src = TERM + MAYBE + "rb1 f h x xs = f (App h x) xs\n" + \
        "whnfF := {\n  step m = sp m nil stepS stepK stepI\n}\n"
    g = generate(parse_ascii(src))
    assert len([d for d in g.decls
                if isinstance(d, A.Equation) and d.name == "rb1"]) == 1


def test_loop1_without_loop_is_refused():
    src = TERM + MAYBE + "c := {\n  step m = sp m nil stepS stepK stepI\n" \
        "  loop1 f m n2 = step m (Just m) (f n2)\n}\n"
    with pytest.raises(GenerateError, match="writes 'loop1' but not 'loop'"):
        generate(parse_ascii(src))


def test_generated_forms_are_surface_syntax_and_round_trip():
    """Everything generate.py emits is an ordinary declaration, so the
    expanded program renders and re-parses like hand-written source."""
    for lx in ("ascii", "unicode"):
        g = generate(parse(source("interp-t3", lx), lx))
        assert parse(render(g, lx), lx) == g


def test_the_core_name_denotes_its_fuel_loop():
    e = expand_program(parse_ascii(source("interp-t3", "ascii")))
    assert pretty(e.term("wf5Abs")) == pretty(e.term("wf5Abs.loop"))
    assert pretty(e.term("wf5Omg")) == pretty(e.term("wf5Omg.loop"))


def test_two_cores_get_their_own_step_and_differ_only_there():
    e = expand_program(parse_ascii(source("interp-t3", "ascii")))
    assert pretty(e.term("wf5Abs.step")) != pretty(e.term("wf5Omg.step"))
    assert pretty(e.term("wf5Abs.stepErr")) != pretty(e.term("wf5Omg.stepErr"))
    # everything they share is one node: same walker, same ISA equations
    for shared in ("sp", "rb", "stepS", "stepK", "stepI"):
        assert shared in e.terms


def test_S_K_and_I_are_the_ISA_at_level_zero():
    """term5 declares constructors named S, K and I, and `omega` still
    means the combinators (EXAMPLES.md section 4, SURFACE-LANGUAGE-DESIGN
    section 6b)."""
    e = expand_program(parse_ascii(source("interp-t3", "ascii")))
    assert pretty(e.term("omega")) == "S I I (S I I)"
    assert e.sizes["omega"] == 6
    assert pretty(e.term("S")) != "S"        # the constructor is a term


def test_the_remaining_terminals_map_in_order_and_never_onto_the_timeout():
    """`OErr` is O's third constructor and `RTime` R's third, but the
    timeout is returned at Zero fuel and nowhere else: O's remaining
    terminals map in order onto R's terminals other than the timeout."""
    p = parse_ascii(TERM + "out === OStep term | ONone | OErr\n"
                           "res === RErr | RVal term | RTime\n")
    lt = find_loop_types(p, find_object_type(p))
    assert lt.mapping == (("ONone", "RVal"), ("OErr", "RErr"))
    assert lt.timeout.name == "RTime"
