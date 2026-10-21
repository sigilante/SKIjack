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


# ------------------------------------------- what the review found (Wizard)

@pytest.mark.parametrize("arg", ["(Zero W)", "(I (Zero W))", "(Zero (I W))",
                                 "(Zero (B K))", "((I Zero) W)", "(Zero Zero)"])
def test_a_datum_applied_short_of_its_continuations_is_a_function(arg):
    """`Zero W` is `K W`, a function of one more argument: a datum applied
    to fewer continuations than its type has constructors is never a datum
    of that type, so Suc refuses it, as it refuses `Suc K`."""
    refuses(NAT + f"t := Suc {arg}\n", "where a value of type nat is expected")


def test_a_datum_applied_to_all_its_continuations_is_still_accepted():
    skijack.compile(NAT + "f x = Suc (x Zero (\\k. k))\na := f Zero\n"
                          "pred x = x Zero (\\k. k)\nb := Suc (pred (Suc Zero))\n")


def test_one_use_of_a_name_does_not_commit_another():
    """A monomorphic scheme is copied for each use: `f Zero` is refused and
    `f I`, which is Suc Zero, is accepted, in either order."""
    for order in ("a := f Zero\nb := f I\n", "b := f I\na := f Zero\n"):
        problems = typecheck_program(parse(NAT + "f x = Suc (x Zero)\n" + order, "ascii"))
        assert [p.where.name for p in problems] == ["a"]


@pytest.mark.parametrize("body", ["natIfEq I I Zero Zero", "natAdd K Zero",
                                  "natSub Zero (K I)"])
def test_a_numeral_operation_refuses_a_function(body):
    refuses(NAT + f"z := Suc ({body})\n",
            "a function .* where a (numeral|value of type nat) is expected")


def test_a_numeral_operation_refuses_other_data():
    refuses(NAT + "bool === F | T\nc := natIfEq T F Zero (Suc Zero)\n",
            "expected a numeral, found bool")


def test_the_numeral_constraint_holds_through_an_alias_and_a_binder():
    refuses(NAT + "add = natAdd\nz := Suc (add I I)\n", "where a numeral is expected")
    refuses(NAT + "bool === F | T\ninc x = natAdd x 1\ny := inc T\n",
            "expected (a numeral|nat), found bool")
    refuses(NAT + "bool === F | T\ninc x = natAdd x x\ny := inc T\n",
            "expected a numeral, found bool")
    skijack.compile(NAT + "add = natAdd\ninc x = natAdd x 1\nz := Suc (add (inc 1) 2)\n")


@pytest.mark.parametrize("use", ["eq = EQ\ng := eq K I\n", "ap e = e K I\ng := ap EQ\n",
                                 "g := EQ [K I] [I K]\n", "g := EQ (cons K nil) nil\n"])
def test_the_data_constraint_holds_through_an_alias_a_cell_and_a_list(use):
    refuses(NAT + "bool === F | T\nEQ x y = T\n" + use, "an operand of 'EQ' is a function")


def test_EQ_on_data_through_an_alias_is_accepted():
    skijack.compile(NAT + "bool === F | T\nEQ x y = T\neq = EQ\n"
                          "g := eq [Zero Zero] (cons Zero nil)\n")


def test_stage_b_refuses_what_it_cannot_settle_instead_of_crashing(monkeypatch):
    """However a declaration's inference runs, Stage B ends in problems,
    never a RecursionError (SPEC.md §9b)."""
    import importlib
    T = importlib.import_module("skijack.typecheck")
    real = T._Types.unify

    def deep(self, expected, given, seen=None):
        if isinstance(T.resolve(expected), T.TCon) and T.resolve(expected).name == "nat":
            raise RecursionError
        return real(self, expected, given, seen)
    monkeypatch.setattr(T._Types, "unify", deep)
    problems = typecheck_program(parse(NAT + "t := Suc Zero\nu := I\n", "ascii"))
    assert [p.where.name for p in problems] == ["t"]
    assert "could not settle" in problems[0].message
