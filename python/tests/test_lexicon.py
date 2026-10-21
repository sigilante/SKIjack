"""The token table, and that both lexers produce the same token kinds."""

import pytest

from skijack.lexicon import (COMMENT, UNICODE_ALIASES, LexError, TOKEN_TABLE,
                             check_table, lex, lex_ascii, lex_unicode)


def kinds(toks):
    return [t.kind for t in toks]


def values(toks):
    return [(t.kind, t.value) for t in toks if t.kind in ("IDENT", "NUMBER",
                                                          "AXIS", "FUEL")]


def test_table_is_checked_at_import():
    check_table()          # already run at import; run again explicitly


def test_maximal_munch_ascii():
    assert kinds(lex_ascii("a :=* b"))[:4] == ["IDENT", "MACRO", "IDENT",
                                               "NEWLINE"]
    assert kinds(lex_ascii("a :=! b"))[1] == "CMACRO"
    assert kinds(lex_ascii("a := b"))[1] == "ASSIGN"
    assert kinds(lex_ascii("a === b"))[1] == "TYPEDECL"
    assert kinds(lex_ascii("a => b"))[1] == "MAPSTO"
    assert kinds(lex_ascii("a = b"))[1] == "EQUALS"
    assert kinds(lex_ascii("a -> b"))[1] == "ARROW"
    assert kinds(lex_ascii("a |> b"))[1] == "CASE"
    assert kinds(lex_ascii("a |- b"))[1] == "TURNSTILE"
    assert kinds(lex_ascii("a | b"))[1] == "ALT"
    assert kinds(lex_ascii("a : b"))[1] == "COLON"


def test_comments_run_to_end_of_line():
    assert kinds(lex_ascii("a -- b c\nd")) == ["IDENT", "NEWLINE", "IDENT",
                                               "NEWLINE", "EOF"]
    assert kinds(lex_unicode("a ⍝ b c\nd")) == ["IDENT", "NEWLINE", "IDENT",
                                                "NEWLINE", "EOF"]
    assert COMMENT["ascii"] == "--" and COMMENT["unicode"] == "⍝"


PAIRS = [
    ("nat === Zero | Suc nat", "nat ≡ Zero | Suc nat"),
    ("n |> { Zero Zero ; Suc m m }", "n ▹ { Zero Zero ; Suc m m }"),
    ("swap p :=* [3@p 2@p]", "swap p ≔* [3⊑p 2⊑p]"),
    ("a := ns{/k/two => <I>, /k/three => <K>}",
     "a ≔ ns{/k/two ↦ <I>, /k/three ↦ <K>}"),
    ("b := wfN r |- <?^/k/three>@10", "b ≔ wfN r ⊢ <∵/k/three>₁₀"),
    ("c := <I ?^/k/x>@[]", "c ≔ <I ∵/k/x>₍₎"),
    ("f : s -> t", "f : s → t"),
    ("g x = \\z.x z", "g x = λz.x z"),
    ("h = B C W Y EQ", "h = ∘ ⇄ ⋈ Υ ≟"),
]


@pytest.mark.parametrize("asc,uni", PAIRS)
def test_both_lexers_agree_on_kinds_and_values(asc, uni):
    ta, tu = lex_ascii(asc), lex_unicode(uni)
    assert kinds(ta) == kinds(tu)
    assert values(ta) == values(tu)


def test_unicode_identifier_subscripts_normalize():
    assert [t.value for t in lex_unicode("flipK₁") if t.kind == "IDENT"] \
        == ["flipK1"]


def test_axis_and_fuel_are_distinguished():
    assert [(t.kind, t.value) for t in lex_ascii("2@p")][:2] == \
        [("AXIS", 2), ("IDENT", "p")]
    assert [(t.kind, t.value) for t in lex_ascii("<x>@7")][3] == ("FUEL", 7)
    assert [(t.kind, t.value) for t in lex_ascii("<x>@[]")][3] == \
        ("FUEL", "policy")


def test_the_table_is_a_strict_bijection():
    """No row shares a kind with another and neither column repeats a
    spelling, so kind <-> spelling is a bijection in each column.  There
    are no shared-kind exceptions."""
    rows = [r for r in TOKEN_TABLE if r.structural]
    kinds_ = [r.kind for r in rows]
    assert len(kinds_) == len(set(kinds_))
    assert len({r.ascii for r in rows}) == len(rows)
    assert len({r.unicode for r in rows}) == len(rows)
    assert not hasattr(__import__("skijack.lexicon", fromlist=["x"]),
                       "SHARED_KIND_ROWS")


def test_the_two_arrows_have_their_own_rows():
    fact = [r for r in TOKEN_TABLE if r.kind == "MAPSTO"]
    sig = [r for r in TOKEN_TABLE if r.kind == "ARROW"]
    assert len(fact) == len(sig) == 1
    assert (fact[0].ascii, fact[0].unicode) == ("=>", "↦")
    assert (sig[0].ascii, sig[0].unicode) == ("->", "→")


def test_there_are_no_non_row_spellings():
    """Every spelling in either lexicon is a row of the table.  The
    namespace literal opens with its own token and closes with the
    ordinary block closer in both lexicons, so nothing needs an alias and
    the bijection has no exceptions."""
    assert UNICODE_ALIASES == {}
    assert kinds(lex_unicode("ns{/a/b ↦ K}")) == [
        "NSOPEN", "SLASH", "IDENT", "SLASH", "IDENT", "MAPSTO", "IDENT",
        "RBRACE", "NEWLINE", "EOF"]
    assert kinds(lex_ascii("ns{/a/b => K}")) == kinds(lex_unicode("ns{/a/b ↦ K}"))


def test_unknown_character_is_an_error():
    with pytest.raises(LexError):
        lex_ascii("a ≔ b")


@pytest.mark.parametrize("lexicon", ["ascii", "unicode"])
@pytest.mark.parametrize("text", ["f 10000", "f 00001", "12345@p", "f " + "1" * 5000],
                         ids=["five", "five, zeros first", "an axis of five", "5,000"])
def test_a_number_has_at_most_four_digits(text, lexicon):
    """A literal is unary, so an unbounded number is an unbounded compile;
    the fifth digit is refused where it stands (SPEC.md §1)."""
    if lexicon == "unicode":
        text = text.replace("@", "⊑")
    with pytest.raises(LexError, match="at most 4 digits"):
        lex(text, lexicon)


def test_fuel_has_at_most_four_digits():
    with pytest.raises(LexError, match="at most 4 digits"):
        lex_ascii("<t>@12345")
    with pytest.raises(LexError, match="at most 4 digits"):
        lex_unicode("<t>₁₂₃₄₅")
    assert [t.value for t in lex_ascii("<t>@9999") if t.kind == "FUEL"] == [9999]
