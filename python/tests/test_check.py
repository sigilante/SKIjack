"""Stage A: one positive test per check, and the corpus clean.

`DESIDERATA.md` item 11 lists Stage A as constructor arity; case
completeness and order; data versus function at the four positions; the
interpreter interface; the two symbol tables.  Each is exercised below by
a program it rejects, with the error class and the message asserted.
"""

import pytest
from aviary_kernel.terms import pretty

from skijack.check import (ArityError, CaseError, CheckError, DataError,
                           InterfaceError, ScopeError, SymbolTableError,
                           check, check_program)
from skijack.expand import PRELUDE_NAMES, expand_program, program_prelude
from skijack.parser import parse, parse_ascii

from conftest import ALL_SOURCES, EXPANDABLE, INTERPRETERS, source

#: the corpus files the compiler handles end to end
COMPILABLE = tuple(EXPANDABLE) + tuple(INTERPRETERS) + (
    "level1-flipa", "tower", "scry-wfq", "scry-wfn", "scry-ns", "scry-block",
    "parse-chars", "words-to-numbers", "ascii-digits", "kernel-events",
    "literals")

#: the rest are parse-only: they use forms the notes describe and this
#: package does not compile (wings, segment payloads, an undeclared
#: interpreter), so Stage A rejects them, which is itself the point
PARSE_ONLY = ("misc-forms", "sec4-interp", "sec5-lookup", "syntax3-resolver")



def test_the_corpus_is_the_compilable_and_the_parse_only_files():
    """The counts corpus/__init__.py and the README state: 22 programs,
    18 compiled and 4 refused."""
    from skijack import corpus
    assert set(COMPILABLE) | set(PARSE_ONLY) == set(corpus.names())
    assert (len(corpus.names()), len(COMPILABLE), len(PARSE_ONLY)) == (22, 18, 4)


NAT = "nat === Zero | Suc nat\n"
TERM = "term === S | K | I | App term term\n"
MAYBE = "maybe === Nothing | Just term\n"
INTERP = "whnfF := {\n  step m = sp m nil stepS stepK stepI\n}\n"
BOOL = "bool === PTrue | PFalse\nEQ a b = PTrue\n"


def problems(src, lexicon="ascii"):
    program = parse(src, lexicon)
    return check_program(program, program_prelude(program))


def rejects(src, kind, match):
    with pytest.raises(kind, match=match) as exc:
        check(parse(src, "ascii"), PRELUDE_NAMES)
    return exc.value


# ------------------------------------------------- the corpus is clean

@pytest.mark.parametrize("stem", COMPILABLE)
@pytest.mark.parametrize("lexicon", ["ascii", "unicode"])
def test_every_compilable_corpus_file_is_clean(stem, lexicon):
    assert problems(source(stem, lexicon), lexicon) == []


@pytest.mark.parametrize("stem", PARSE_ONLY)
def test_the_parse_only_corpus_is_rejected_for_stated_reasons(stem):
    """These files carry forms from the notes that are not compiled yet.
    Stage A says so instead of the expander crashing later."""
    got = problems(source(stem, "ascii"))
    assert got, stem
    assert all(issubclass(p.kind, CheckError) for p in got)


def test_checking_never_changes_the_terms():
    """DESIDERATA.md item 11: "the expander's output is the same whether
    checking is on or off"."""
    for stem in COMPILABLE:
        src = source(stem, "ascii")
        on = expand_program(parse_ascii(src), check=True)
        off = expand_program(parse_ascii(src), check=False)
        assert sorted(on.terms) == sorted(off.terms), stem
        for name in on.terms:
            assert pretty(on.terms[name]) == pretty(off.terms[name]), \
                f"{stem}:{name}"


def test_problems_are_reported_together():
    """Not one at a time: every problem is collected, the message lists
    them all, and the class raised is the first one's."""
    src = TERM + MAYBE + INTERP + "a = nope1\nb = nope2\nc = nope3\n"
    exc = rejects(src, ScopeError, "3 Stage A problems")
    assert len(exc.problems) == 3
    assert [str(p.where) for p in exc.problems] == [
        "equation a", "equation b", "equation c"]
    assert [p.where.dotted for p in exc.problems] == ["a", "b", "c"]
    assert "nope3" in str(exc)


# ------------------------------------------------- (a) constructor arity

def test_a_constructor_must_be_saturated_inside_a_quotation():
    """Inside < > a constructor of a non-object type denotes data, so a
    partial application is a function (§5 rule 3)."""
    rejects(TERM + MAYBE + INTERP + NAT + "d := <Suc>\n",
            ArityError, "takes 1 field.* but is given 0")


def test_an_over_applied_constructor_inside_a_quotation_is_rejected():
    rejects(TERM + MAYBE + INTERP + NAT + "d := <Suc Zero Zero>\n",
            ArityError, "takes 1 field.* but is given 2")


def test_a_path_segment_constructor_must_be_nullary():
    src = ("term5 === S | K | I | App term5 term5 | Scry\n"
           "maybe === Nothing | Just term5\n"
           "seg === Nat term5\npath === Nil | Cons seg path\n"
           "c := { stepScry args = args Nothing Nothing }\n"
           "d := <?^/nat>\n")
    rejects(src, ArityError, "a segment tag is nullary")


# --------------------------------------- (b) case completeness and order

def test_an_incomplete_case_is_rejected():
    rejects(NAT + "f n = n |> { Zero Zero }\n",
            CaseError, "missing branch.*for Suc")


def test_a_repeated_case_branch_is_rejected():
    rejects(NAT + "f n = n |> { Zero Zero ; Zero Zero ; Suc m m }\n",
            CaseError, "branch 'Zero' appears twice")


def test_a_case_may_not_mix_two_types():
    src = NAT + "bool === PTrue | PFalse\n" \
        "f n = n |> { Zero Zero ; PFalse Zero }\n"
    rejects(src, CaseError, "branch 'PFalse' is a constructor of 'bool'")


def test_an_undeclared_constructor_in_a_branch_is_rejected_by_the_parser():
    """The parser needs the arity to split the branch at all, so this one
    is caught a step earlier -- see test_parser.py."""
    from skijack.parser import ParseError
    with pytest.raises(ParseError, match="undeclared constructor"):
        parse_ascii("f n = n |> { Nope n }\n")


# ------------------------------------------- (c) data versus function

def test_EQ_refuses_an_arm():
    rejects(TERM + MAYBE + INTERP + BOOL + "g x = x\nf = EQ g g\n",
            DataError, "argument 1 of 'EQ' is the equation 'g'")


def test_EQ_refuses_a_bare_combinator():
    rejects(TERM + MAYBE + INTERP + BOOL + NAT + "d := <Zero>\nf = EQ K d\n",
            DataError, "argument 1 of 'EQ' is the combinator 'K'")


def test_EQ_refuses_a_partially_applied_constructor():
    rejects(TERM + MAYBE + INTERP + BOOL + NAT + "d := <Zero>\nf = EQ Suc d\n",
            DataError, "applied to 0 of its 1 field")


def test_EQ_allows_a_binder_because_Stage_A_cannot_know():
    """§5's line needs types; Stage A refuses what it can *prove* is a
    function and leaves the rest to Stage B."""
    assert problems(TERM + MAYBE + INTERP + BOOL + "same a b = EQ a b\n") == []


def test_a_namespace_fact_must_be_data():
    rejects(source("scry-ns", "ascii") + "r := ns{/nat/two => I}\n",
            DataError, "must be data")


def test_a_scry_outside_a_quotation_is_rejected():
    rejects(source("scry-ns", "ascii") + "f x = ?^/nat/two\n",
            DataError, "live only inside a quotation")


# ---------------------------------------- (d) the interpreter interface

def test_the_application_constructor_has_no_step_arm():
    src = TERM + MAYBE + "c := {\n  stepApp args = args Nothing Nothing\n}\n"
    rejects(src, InterfaceError, "has no step equation")


def test_a_written_step_must_install_the_leaves_in_declaration_order():
    """The most dangerous mistake in the design: a wrong continuation
    order is silent wrong semantics (DESIDERATA.md item 11)."""
    src = TERM + MAYBE + "c := {\n  step m = sp m nil stepK stepS stepI\n}\n"
    rejects(src, InterfaceError, "declaration order is the ABI")


def test_a_written_step_must_hand_over_one_arm_per_leaf():
    src = TERM + MAYBE + "c := {\n  step m = sp m nil stepS stepK\n}\n"
    rejects(src, InterfaceError, "but the object type has 3 leaves")


def test_a_written_loop_takes_the_fuel_and_the_term():
    src = TERM + MAYBE + ("c := {\n  step m = sp m nil stepS stepK stepI\n"
                          "  loop n = n Nothing Nothing\n}\n")
    rejects(src, InterfaceError, "two binders after the core's parameters")


def test_loop1_without_loop_is_rejected():
    src = TERM + MAYBE + ("c := {\n  step m = sp m nil stepS stepK stepI\n"
                          "  loop1 f m n2 = step m (Just m) (f n2)\n}\n")
    rejects(src, InterfaceError, "write both or neither")


def test_an_interpreter_must_be_applied_to_its_parameters():
    rejects(source("scry-wfq", "ascii") + "bad := wfQ |- <I K>@3\n",
            InterfaceError, "takes 1 parameter")


# ------------------------------------------- (e) the two symbol tables

def test_an_object_type_constructor_is_an_ordinary_level_0_name():
    """§6b, corrected: a declared type's constructors are ordinary Scott
    constructors at level 0.  The generated rebuilder applies the object
    type's `App` to build encoded terms, exactly as `Suc` and `Just` are
    applied at level 0 everywhere else."""
    assert problems(source("interp-t3", "ascii")
                    + "mkErr = Err\nmkApp t u = App t u\n") == []


def test_S_K_and_I_at_level_0_are_the_ISA():
    """The three reserved names: at level 0 they are the combinators,
    which is what lets `omega = S I I (S I I)` share a file with
    `term5 === S | K | I | App term5 term5 | Scry`."""
    from skijack.expand import expand_program
    from aviary_kernel.terms import pretty
    assert problems(source("interp-t3", "ascii")) == []
    e = expand_program(parse_ascii(source("interp-t3", "ascii")))
    assert pretty(e.term("omega")) == "S I I (S I I)"


def test_the_generated_program_passes_the_checker_as_user_source():
    """Everything generate.py emits is ordinary surface syntax, so
    rendering it and checking it as hand-written source must be clean --
    which is what caught the old reading of check (e)."""
    from skijack.generate import generate
    from skijack.render import render
    for lexicon in ("ascii", "unicode"):
        g = generate(parse(source("interp-whnff", lexicon), lexicon))
        assert check_program(parse(render(g, lexicon), lexicon),
                             PRELUDE_NAMES) == []


def test_a_name_in_neither_table_is_rejected():
    rejects(TERM + MAYBE + INTERP + "d := <nope>\n",
            SymbolTableError, "names neither table")


def test_the_message_names_which_table_was_searched():
    exc = rejects(TERM + MAYBE + INTERP + "d := <nope>\n",
                  SymbolTableError, "names neither table")
    msg = str(exc)
    assert "object type 'term'" in msg and "level-0 name" in msg


# --------------------------------- (f) unresolved names and duplicates

def test_an_unresolved_name_is_rejected():
    rejects("f x = x nowhere\n", ScopeError, "unresolved name 'nowhere'")


def test_a_duplicate_declaration_is_rejected():
    rejects("f x = x\nf y = y\n", ScopeError, "'f' is declared twice")


def test_a_constructor_may_not_shadow_a_declaration():
    rejects(NAT + "Zero x = x\n", ScopeError, "'Zero' is declared twice")


def test_a_core_may_not_define_an_arm_twice():
    src = TERM + MAYBE + ("c := {\n  step m = sp m nil stepS stepK stepI\n"
                          "  step m = sp m nil stepS stepK stepI\n}\n")
    rejects(src, ScopeError, "equation 'step' is defined twice")
