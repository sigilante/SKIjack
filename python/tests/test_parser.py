"""The one grammar, and the two decisions of the README."""

import pytest

from skijack import ast as A
from skijack.parser import (ParseError, collect_ctors, parse_ascii,
                            parse_expr_text, parse_unicode)
from skijack.lexicon import lex_ascii

from conftest import ALL_SOURCES, source


@pytest.mark.parametrize("stem,lexicon,path",
                         ALL_SOURCES, ids=[f"{s}.{lx}" for s, lx, _ in ALL_SOURCES])
def test_every_corpus_file_parses(stem, lexicon, path):
    tree = (parse_ascii if lexicon == "ascii" else parse_unicode)(
        path.read_text(encoding="utf-8"))
    assert isinstance(tree, A.Program) and tree.decls


@pytest.mark.parametrize("stem", sorted({s for s, _, _ in ALL_SOURCES}))
def test_the_two_spellings_denote_the_same_tree(stem):
    assert parse_ascii(source(stem, "ascii")) == \
        parse_unicode(source(stem, "unicode"))


def test_application_is_left_associative():
    e = parse_expr_text("f x y")
    assert e == A.App(A.App(A.Name("f"), A.Name("x")), A.Name("y"))
    assert parse_expr_text("f (x y)") == \
        A.App(A.Name("f"), A.App(A.Name("x"), A.Name("y")))


def test_cell_is_flat_in_the_tree():
    assert parse_expr_text("[a b c]") == \
        A.Cell((A.Name("a"), A.Name("b"), A.Name("c")))


def test_pick_takes_one_atom():
    assert parse_expr_text("3@p 2@p") == \
        A.App(A.Pick(3, A.Name("p")), A.Pick(2, A.Name("p")))


def test_decision_a_branch_binders_come_from_the_declared_arity():
    tree = parse_ascii(
        "nat === Zero | Suc nat\n"
        "f n = n |> { Zero Zero ; Suc k Suc (f k) }\n")
    equation = tree.decls[1]
    assert isinstance(equation, A.Equation)
    case = equation.body
    assert isinstance(case, A.Case)
    assert [(c, bs) for c, bs, _ in case.branches] == [("Zero", ()),
                                                       ("Suc", ("k",))]


def test_decision_a_undeclared_constructor_is_a_clear_error():
    with pytest.raises(ParseError, match="undeclared constructor 'Nope'"):
        parse_ascii("f n = n |> { Nope n }\n")


def test_collect_ctors_records_order_and_arity():
    t = collect_ctors(lex_ascii("term5 === S | K | I | App term5 term5 | Err"))
    assert t["S"] == ("term5", 0, 0)
    assert t["App"] == ("term5", 3, 2)
    assert t["Err"] == ("term5", 4, 0)


def test_decision_b_core_versus_namespace_literal():
    core = parse_ascii("c := {\n  f x = x\n}\n").decls[0]
    assert isinstance(core, A.Core) and core.equations[0].name == "f"
    ns = parse_ascii("c := ns{/a/b => K}\n").decls[0]
    assert isinstance(ns, A.Def) and isinstance(ns.expr, A.NsLit)


def test_the_two_arrows_are_different_token_kinds():
    """'=>' is the fact arrow, '->' the signature arrow; neither position
    has to disambiguate the other (SYNTAX.md section 2)."""
    ns = parse_ascii("c := ns{/a/b => K}\n").decls[0]
    assert ns.expr == A.NsLit(((A.Path((A.Seg("a"), A.Seg("b"))), A.Name("K")),))
    with pytest.raises(ParseError, match="expected MAPSTO"):
        parse_ascii("c := ns{/a/b -> K}\n")
    with pytest.raises(ParseError):
        parse_ascii("f : s => t\n")


def test_top_level_arm_keeps_its_binders():
    d = parse_ascii("C f x y = f y x\n").decls[0]
    assert d == A.Equation("C", ("f", "x", "y"),
                      A.App(A.App(A.Name("f"), A.Name("y")), A.Name("x")))


def test_signature_is_parsed_and_kept():
    d = parse_ascii("add : nat -> nat -> nat\n").decls[0]
    assert d == A.Sig("add", ("nat", "nat", "nat"))


def test_interpreter_selection_binds_looser_than_application():
    d = parse_ascii("a := wfN r |- <K>@10\n").decls[0]
    assert d.expr == A.Quote(A.Name("K"), 10,
                             A.App(A.Name("wfN"), A.Name("r")))


def test_lambda_consumes_exactly_one_dot_and_wings_keep_the_rest():
    assert parse_expr_text("\\x.a.b") == A.Lambda("x", A.Name("a.b"))
    assert parse_expr_text("r.a.b") == A.Name("r.a.b")


def test_every_ascii_corpus_file_is_seven_bit():
    """front1 reads a program as 7-bit codes, so an ASCII spelling holds
    nothing else, comments included."""
    for stem, lx, path in ALL_SOURCES:
        if lx == "ascii":
            assert path.read_bytes().isascii(), path.name


def test_a_bare_number_is_a_literal():
    assert parse_expr_text("f 3") == A.App(A.Name("f"), A.Num(3))
    assert parse_expr_text("f 3", "unicode") == A.App(A.Name("f"), A.Num(3))


def test_a_number_before_the_axis_mark_is_still_a_pick():
    assert parse_expr_text("2@p") == A.Pick(2, A.Name("p"))
    assert parse_expr_text("2⊑p", "unicode") == A.Pick(2, A.Name("p"))
    assert parse_expr_text("2@3") == A.Pick(2, A.Num(3))


def test_newline_ends_an_application():
    tree = parse_ascii("f x = x\ng y = y\n")
    assert len(tree.decls) == 2
