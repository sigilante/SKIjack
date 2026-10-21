"""The token table of ``SYNTAX.md`` §2, as data, plus the two lexers.

One row per meaning, carrying the ASCII and the Unicode spelling.  Both
lexers emit the *same* token kinds, so one grammar (``parser.py``) serves
both interfaces and the tree has no lexicon field.

At import time the table is checked (see :func:`check_table`) as a
**strict bijection, with no exceptions**:

* every row has its own token kind -- no two rows share one;
* the ASCII column is injective and the Unicode column is injective, so
  ``kind <-> spelling`` is a bijection in each column and
  ``render_A ∘ parse_U`` inverts ``render_U ∘ parse_A`` on the tree
  (``SYNTAX.md`` §1 item 4);
* maximal munch is unambiguous: whenever one spelling is a proper prefix
  of another, the lexer's ordering tries the longer one first (so
  ``:=*`` and ``:=!`` come before ``:=``, ``===`` and ``=>`` before
  ``=``, and ``|>`` and ``|-`` before ``|``).

The one spelling outside the table is the Unicode namespace-literal
closer ``}``, which ``SYNTAX.md`` §2 states is the *same token kind* as
``}`` rather than a row of its own; it is declared in
:data:`UNICODE_ALIASES` and checked to collide with nothing.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import List, Optional, Tuple, Union

__all__ = [
    "Row", "TOKEN_TABLE", "Token", "LexError", "MAX_DIGITS",
    "lex_ascii", "lex_unicode", "lex", "check_table",
    "ascii_spelling", "unicode_spelling", "GLYPH_NAMES", "UNICODE_ALIASES",
]


from .errors import SkijackError

class LexError(SkijackError):
    pass


@dataclass(frozen=True)
class Row:
    """One row of the token table.

    ``kind`` is the token kind both lexers emit.  ``structural`` marks the
    rows above the glyph section of ``SYNTAX.md`` §2; the glyph rows are
    Tier 1 dictionary entries whose ASCII spelling *is* the name, so they
    lex as identifiers and are only a rendering preference.
    """
    meaning: str
    kind: str
    ascii: str
    unicode: str
    structural: bool = True
    note: str = ""


#: Extra spellings that are *not* rows.  There are none.  The Unicode
#: lexicon exists to give one glyph to each of ASCII's multi-character
#: operators (``|-``, ``:=``, ``===``, ``=>``, ``->``, ``?^``, ``|>``,
#: ``@10``); where ASCII already uses a single unambiguous character the
#: two lexicons agree, so quotation is ``<t>`` and a namespace literal is
#: ``ns{...}`` in both, and nothing needs an alias.
UNICODE_ALIASES: dict = {}


TOKEN_TABLE: Tuple[Row, ...] = (
    # --- structure --------------------------------------------------------
    Row("macro definition",      "MACRO",     ":=*", "≔*"),
    Row("capturing macro",       "CMACRO",    ":=!", "≔!"),
    Row("type declaration",      "TYPEDECL",  "===", "≡"),
    Row("namespace literal open","NSOPEN",    "ns{", "ns{"),
    Row("scry",                  "SCRY",      "?^",  "∵"),
    Row("case",                  "CASE",      "|>",  "▹"),
    Row("interpreter selection", "TURNSTILE", "|-",  "⊢"),
    Row("definition",            "ASSIGN",    ":=",  "≔"),
    Row("fact",                  "MAPSTO",    "=>",  "↦",
        note="inside a namespace literal; '=>' keeps '->' the signature "
             "arrow alone, so the table is a bijection"),
    Row("signature arrow",       "ARROW",     "->",  "→"),
    Row("signature colon",       "COLON",     ":",   ":"),
    Row("equation",              "EQUALS",    "=",   "=",
        note="name binders = body, inside a core or at top level"),
    Row("type alternative",      "ALT",       "|",   "|"),
    Row("quotation open",        "QOPEN",     "<",   "<"),
    Row("quotation close",       "QCLOSE",    ">",   ">"),
    Row("lambda",                "LAMBDA",    "\\",  "λ"),
    Row("name qualifier",        "DOT",       ".",   ".",
        note="a.b is a qualified name looked up in the name table, not a "
             "path into a runtime environment (SYNTAX.md 7)"),
    Row("branch separator",      "SEMI",      ";",   ";"),
    Row("fact separator",        "COMMA",     ",",   ","),
    Row("path separator",        "SLASH",     "/",   "/"),
    Row("group open",            "LPAREN",    "(",   "("),
    Row("group close",           "RPAREN",    ")",   ")"),
    Row("cell open",             "LBRACK",    "[",   "["),
    Row("cell close",            "RBRACK",    "]",   "]"),
    Row("block open",            "LBRACE",    "{",   "{"),
    Row("block close",           "RBRACE",    "}",   "}",
        note="also closes a namespace literal, in both lexicons"),
    # --- Tier 1 glyphs (identifiers, not operators) -----------------------
    Row("composition (B)",       "IDENT",     "B",   "∘",   structural=False),
    Row("swap (C)",              "IDENT",     "C",   "⇄",   structural=False),
    Row("duplicate (W)",         "IDENT",     "W",   "⋈",   structural=False),
    Row("fixpoint (Y)",          "IDENT",     "Y",   "Υ",   structural=False),
    Row("equality on data",      "IDENT",     "EQ",  "≟",   structural=False),
)

#: comment-to-end-of-line markers, one per lexicon
COMMENT = {"ascii": "--", "unicode": "⍝"}

#: axis-pick markers: the spelling that follows the number (``2@`` / ``2⊑``)
AXIS_MARK = {"ascii": "@", "unicode": "⊑"}

#: Unicode name of every Tier 1 glyph, keyed by the canonical (ASCII) name
GLYPH_NAMES = {r.ascii: r.unicode for r in TOKEN_TABLE if not r.structural}
#: and the reverse, used by the Unicode lexer
_GLYPH_TO_NAME = {r.unicode: r.ascii for r in TOKEN_TABLE if not r.structural}


def ascii_spelling(kind: str) -> str:
    for r in TOKEN_TABLE:
        if r.kind == kind:
            return r.ascii
    raise KeyError(kind)


def unicode_spelling(kind: str) -> str:
    for r in TOKEN_TABLE:
        if r.kind == kind:
            return r.unicode
    raise KeyError(kind)


# ------------------------------------------------------------------ checking

def _operator_rows() -> List[Row]:
    return [r for r in TOKEN_TABLE if r.structural]


def _ordered(column: str) -> List[Tuple[str, str]]:
    """(spelling, kind) pairs in the order the lexer tries them: longest
    spelling first, which is exactly maximal munch.  For Unicode the
    table's rows are followed by :data:`UNICODE_ALIASES`."""
    out = [(getattr(r, column), r.kind) for r in _operator_rows()]
    if column == "unicode":
        out += list(UNICODE_ALIASES.items())
    out.sort(key=lambda p: -len(p[0]))
    return out


def check_table() -> None:
    """Assert the properties the two-lexicon rule depends on.

    The bijection check is strict: no row shares a kind with another, and
    neither column repeats a spelling.  There are no exceptions.
    """
    rows = _operator_rows()
    # 1. kinds are unique across rows: no two meanings share a token kind
    kinds = [r.kind for r in rows]
    assert len(kinds) == len(set(kinds)), (
        "two rows share a token kind: "
        + str(sorted(k for k in set(kinds) if kinds.count(k) > 1)))
    # 2. each column is injective, so kind <-> spelling is a bijection
    for column in ("ascii", "unicode"):
        spellings = [getattr(r, column) for r in rows]
        dupes = sorted({s for s in spellings if spellings.count(s) > 1})
        assert not dupes, f"{column} column is not injective: {dupes}"
    # 3. the one non-row spelling names an existing kind and collides with
    #    nothing in the Unicode column
    for alias, kind in UNICODE_ALIASES.items():
        assert kind in set(kinds), f"alias {alias!r} names no token kind"
        assert alias not in [r.unicode for r in TOKEN_TABLE], (
            f"alias {alias!r} duplicates a table spelling")
    for column in ("ascii", "unicode"):
        # 4. maximal munch: a proper prefix must be tried after its extension
        order = _ordered(column)
        index = {sp: i for i, (sp, _) in enumerate(order)}
        for sp, _ in order:
            for other, _ in order:
                if other != sp and other.startswith(sp):
                    assert index[other] < index[sp], (
                        f"{column}: {sp!r} would shadow {other!r} under "
                        f"maximal munch")
        # 5. the comment marker must not be shadowed either
        cm = COMMENT[column]
        for sp, _ in order:
            assert not (cm.startswith(sp) and sp != cm), (
                f"{column}: operator {sp!r} shadows the comment marker {cm!r}")
    # 6. glyph rows: single code point on the Unicode side, typeable ASCII
    for r in TOKEN_TABLE:
        if not r.structural:
            assert len(r.unicode) == 1, (
                f"glyph {r.meaning}: Unicode spelling must be one code point")
            assert r.ascii.isascii() and r.ascii.isalnum(), (
                f"glyph {r.meaning}: ASCII spelling must be a plain name")


check_table()


# ------------------------------------------------------------------- lexing

@dataclass(frozen=True)
class Token:
    kind: str
    value: Union[str, int, None]
    line: int
    col: int

    @property
    def text(self) -> str:
        """The value of a token that carries a name or spelling."""
        if not isinstance(self.value, str):
            raise TypeError(f"{self.kind} token at {self.line}:{self.col} carries no text")
        return self.value

    @property
    def number(self) -> int:
        """The value of a NUMBER or AXIS token."""
        if isinstance(self.value, bool) or not isinstance(self.value, int):
            raise TypeError(f"{self.kind} token at {self.line}:{self.col} carries no number")
        return self.value

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        return f"{self.kind}({self.value!r})@{self.line}:{self.col}"


_ASCII_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
#: Unicode identifiers may carry subscript digits (``flipK₁``); they are
#: normalized to ASCII digits so the two lexicons agree on the tree.  A
#: subscript can never *start* an identifier, which is what keeps the
#: subscript-fuel notation ``«t»₁₀`` unambiguous.
_UNI_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'₀-₉]*")
_NUMBER = re.compile(r"[0-9]+")
_ASCII_AXIS = re.compile(r"([0-9]+)@")
_UNI_AXIS = re.compile(r"([0-9]+)⊑")
_ASCII_FUEL = re.compile(r"@(?:([0-9]+)|(\[\]))")
_UNI_FUEL = re.compile(r"(?:([₀-₉]+)|(₍₎))")

_SUBDIGITS = {chr(0x2080 + i): str(i) for i in range(10)}

#: the most digits a number may have -- a literal, an axis or fuel -- so
#: the largest is 9,999.  A literal is unary, `n` costs 8n + 1 atoms, and
#: the self-hosted front ends build a number in unary as they read it, so
#: an unbounded number is an unbounded compile; four digits bound a
#: literal at 79,993 atoms and every lexer can refuse the fifth digit
#: without reading the rest (SPEC.md §1).
MAX_DIGITS = 4


def _number(digits: str, line: int, col: int) -> int:
    """A digit run's value, refused past :data:`MAX_DIGITS`."""
    if len(digits) > MAX_DIGITS:
        raise LexError(
            f"line {line}, column {col}: a number has at most {MAX_DIGITS} "
            f"digits, so the largest is {10 ** MAX_DIGITS - 1:,}; this one has "
            f"{len(digits):,}")
    return int(_desub(digits))


def _desub(text: str) -> str:
    return "".join(_SUBDIGITS.get(c, c) for c in text)


def lex(text: str, lexicon: str) -> List[Token]:
    """Tokenize ``text`` in ``lexicon`` ("ascii" or "unicode")."""
    if lexicon not in ("ascii", "unicode"):
        raise ValueError(f"unknown lexicon {lexicon!r}")
    ops = _ordered(lexicon)
    comment = COMMENT[lexicon]
    ident_re = _ASCII_IDENT if lexicon == "ascii" else _UNI_IDENT
    axis_re = _ASCII_AXIS if lexicon == "ascii" else _UNI_AXIS
    fuel_re = _ASCII_FUEL if lexicon == "ascii" else _UNI_FUEL

    out: List[Token] = []
    i, line, bol = 0, 1, 0
    n = len(text)
    while i < n:
        c = text[i]
        col = i - bol + 1
        if c == "\n":
            if out and out[-1].kind != "NEWLINE":
                out.append(Token("NEWLINE", "\n", line, col))
            i += 1
            line += 1
            bol = i
            continue
        if c in " \t\r":
            i += 1
            continue
        if text.startswith(comment, i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        m = axis_re.match(text, i)
        if m:
            out.append(Token("AXIS", _number(m.group(1), line, col), line, col))
            i = m.end()
            continue
        m = fuel_re.match(text, i)
        if m:
            digits, policy = m.group(1), m.group(2)
            value: Union[str, int] = "policy" if policy else _number(digits, line, col)
            out.append(Token("FUEL", value, line, col))
            i = m.end()
            continue
        if lexicon == "unicode" and c in _GLYPH_TO_NAME:
            out.append(Token("IDENT", _GLYPH_TO_NAME[c], line, col))
            i += 1
            continue
        hit = None
        for sp, kind in ops:
            if text.startswith(sp, i):
                hit = (sp, kind)
                break
        if hit is not None:
            sp, kind = hit
            out.append(Token(kind, sp, line, col))
            i += len(sp)
            continue
        m = ident_re.match(text, i)
        if m:
            out.append(Token("IDENT", _desub(m.group(0)), line, col))
            i = m.end()
            continue
        m = _NUMBER.match(text, i)
        if m:
            out.append(Token("NUMBER", _number(m.group(0), line, col), line, col))
            i = m.end()
            continue
        raise LexError(f"line {line}, column {col}: unexpected character {c!r}")
    if out and out[-1].kind != "NEWLINE":
        out.append(Token("NEWLINE", "\n", line, i - bol + 1))
    out.append(Token("EOF", None, line, i - bol + 1))
    return out


def lex_ascii(text: str) -> List[Token]:
    return lex(text, "ascii")


def lex_unicode(text: str) -> List[Token]:
    return lex(text, "unicode")
