"""Stage B, the type discipline: what it refuses, what it must accept.

The corpus is the oracle: every compilable program type-checks unchanged
and compiles to the same terms with the check on or off.  The refusals
are the ones DESIDERATA.md item 11 and SPEC.md promise.
"""

import pytest
from aviary_kernel.terms import pretty

import skijack
from skijack import corpus
from skijack.expand import expand_program
from skijack.parser import parse
from skijack.typecheck import TypeMismatchError, typecheck_program

from conftest import EXPANDABLE, INTERPRETERS, source

COMPILABLE = tuple(EXPANDABLE) + tuple(INTERPRETERS) + (
    "level1-flipa", "tower", "scry-wfq", "scry-wfn", "scry-ns", "scry-block",
    "parse-chars", "words-to-numbers", "ascii-digits", "kernel-events",
    "literals")

NAT = "nat === Zero | Suc nat\n"
BOOL = "bool === PTrue | PFalse\nEQ a b = PTrue\n"


def refuses(src, match):
    with pytest.raises(TypeMismatchError, match=match) as exc:
        skijack.compile(src)
    return exc.value


# ------------------------------------------------ the corpus is the oracle

@pytest.mark.parametrize("stem", COMPILABLE)
@pytest.mark.parametrize("lexicon", ["ascii", "unicode"])
def test_every_compilable_corpus_file_is_well_typed(stem, lexicon):
    skijack.compile(source(stem, lexicon), lexicon=lexicon)


@pytest.mark.parametrize("stem", COMPILABLE)
def test_type_checking_never_changes_the_terms(stem):
    src = source(stem, "ascii")
    on = expand_program(parse(src, "ascii"), check=True)
    off = expand_program(parse(src, "ascii"), check=False)
    assert sorted(on.terms) == sorted(off.terms)
    for name in on.terms:
        assert pretty(on.terms[name]) == pretty(off.terms[name]), name


# ------------------------------------------------- the rule, both directions

def test_a_function_is_not_a_datum():
    """Zero compiles to K, so only the orientation makes this an error."""
    refuses(NAT + "x := Suc K\n", "function .* where a value of type nat is expected")


def test_a_case_gives_its_scrutinee_the_declared_type():
    refuses(NAT + "add m n = n |> { Zero m; Suc k (Suc (add m k)) }\nx := add K Zero\n",
            "function .* where a value of type nat is expected")


def test_a_datum_may_be_applied_as_its_own_case():
    e = skijack.compile(NAT + "isZero n = n K (K (K I))\nyes := isZero Zero\n")
    assert "isZero" in e.terms


def test_a_binder_used_as_datum_then_as_case_is_one_datum():
    e = skijack.compile(NAT + "both n = [(Suc n) (n Zero Suc)]\nx := both Zero\n")
    assert "both" in e.terms


def test_a_binder_used_as_case_then_as_datum_still_refuses_a_function():
    refuses(NAT + "both n = [(n Zero Suc) (Suc n)]\nx := both K\n",
            "function .* where a value of type nat is expected")


def test_a_binder_used_as_datum_then_as_case_still_refuses_a_function():
    refuses(NAT + "both n = [(Suc n) (n Zero Suc)]\nx := both K\n",
            "function .* where a value of type nat is expected")


def test_branches_must_agree():
    refuses(NAT + BOOL + "f n = n |> { Zero PTrue; Suc k Zero }\n",
            "expected bool, found nat")


# --------------------------------------------------- the EQ data constraint

def test_an_operand_of_eq_may_not_be_a_function_through_a_binder():
    """SPEC section 9: the second stage catches what Stage A cannot."""
    refuses(BOOL + "f x = EQ x PTrue\ng := f K\n",
            "operand of 'EQ' is a function|function .* where a datum")


def test_an_operand_of_eq_may_be_a_datum_through_a_binder():
    e = skijack.compile(NAT + BOOL + "f x = EQ x PTrue\ng := f Zero\n")
    assert "g" in e.terms


# ---------------------------------------------------- cells, axes, signatures

def test_an_axis_picks_into_a_cell_and_nothing_else():
    e = skijack.compile(NAT + "second p = 3@p\nx := second [Zero (Suc Zero)]\n")
    assert "second" in e.terms
    refuses(NAT + "y := 2@Zero\n", "expected \\(cell")


def test_a_signature_is_checked():
    e = skijack.compile(NAT + "succ : nat -> nat\nsucc n = Suc n\n")
    assert "succ" in e.terms
    refuses(NAT + "succ : nat -> nat\nsucc n = K\n", "declared nat -> nat")


# ------------------------------------------------- self-application, blocking

def test_omega_is_typed_without_an_escape():
    """Equirecursive unification admits S I I (S I I)."""
    e = skijack.compile("omega = S I I (S I I)\n")
    assert e.sizes["omega"] == 6


def test_the_blocked_payload_is_declared_as_what_it_holds():
    """A level-1 path is an encoded term; the old spelling is refused."""
    src = source("scry-wfn", "ascii")
    assert "PendingN term5" in src and "RBlockN term5" in src
    old = src.replace("PendingN term5", "PendingN path").replace("RBlockN term5", "RBlockN path")
    refuses(old, "expected path, found term5")


def test_problems_are_collected_then_raised_once():
    problems = typecheck_program(parse(NAT + "a := Suc K\nb := Suc I\n", "ascii"))
    assert [p.where.name for p in problems] == ["a", "b"]
    assert all(p.kind is TypeMismatchError for p in problems)
