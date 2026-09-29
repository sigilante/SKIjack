"""The SKIjack-0 front end (docs/SKIJACK-0.md).

``skijack/selfhost/front0.ascii.ski`` is compiled by this package.  Its
lexer runs here in the reference reducer, its tokens against
``skijack.lexicon``'s.  The whole front end needs a reducer that shares:
with ``AVON`` naming an avon binary, the last tests run it through
``skijack.selfhost.run0`` -- the edge programs, random programs, and the
fixed point, the front end compiling its own source -- and otherwise
skip.  ``avon/tests/front0_check.sh`` runs the same checks at full size.
"""

import functools
import os
import pathlib
import random
import sys

import pytest
from aviary_kernel.terms import App

import skijack
from skijack.dictionary import structural_hash
from skijack.lexicon import lex
from skijack.parser import parse
from skijack.run import peel
from skijack.selfhost import run0, tables
from skijack.spec0 import compile0, in_subset

SOURCE = pathlib.Path(skijack.__file__).parent / "selfhost" / "front0.ascii.ski"


@pytest.fixture(autouse=True)
def _deep_recursion():
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 200_000))
    yield
    sys.setrecursionlimit(old)


@functools.lru_cache(maxsize=1)
def front():
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 200_000))
    try:
        src = SOURCE.read_text()
        e = skijack.compile(src, lexicon="ascii")
        decls = {d.name: d for d in parse(src, "ascii").decls if hasattr(d, "ctors")}
        return e, decls
    finally:
        sys.setrecursionlimit(old)


STEPS = 50_000_000


def code_term(e, n):
    t = e.terms["Code"]
    for i in range(7):
        t = App(t, e.terms["Hi" if (n >> (6 - i)) & 1 else "Lo"])
    return t


def encode(text):
    e, _ = front()
    t = e.terms["SNil"]
    for ch in reversed(text):
        t = App(App(e.terms["SCons"], code_term(e, ord(ch))), t)
    return t


def fields(t, tname):
    _e, decls = front()
    return peel(t, decls[tname], max_steps=STEPS)


def nat(t):
    n = 0
    while True:
        c, f = fields(t, "nat")
        if c == "Zero":
            return n
        n, t = n + 1, f[0]


def code(t):
    _c, bits = fields(t, "code")
    v = 0
    for b in bits:
        v = 2 * v + (fields(b, "bit")[0] == "Hi")
    return v


def name(t):
    out = []
    while True:
        c, f = fields(t, "name")
        if c == "NNil":
            return "".join(out)
        out.append(chr(code(f[0])))
        t = f[1]


def tokens(t):
    out = []
    while True:
        c, f = fields(t, "toks")
        if c == "TNil":
            return out
        k, tf = fields(f[0], "tok")
        if k == "TName":                    # the lexer's identifiers are raw
            _raw, (n,) = fields(tf[0], "ident")
            out.append(("IDENT", name(n)))
        elif k == "TAxis":
            out.append(("AXIS", nat(tf[0])))
        else:
            out.append((k, None))
        t = f[1]


#: this front end's token kinds, as skijack.lexicon names them
KINDS = {"TTypeDecl": "TYPEDECL", "TCase": "CASE", "TAssign": "ASSIGN", "TEq": "EQUALS",
         "TAlt": "ALT", "TLam": "LAMBDA", "TDot": "DOT", "TSemi": "SEMI", "TLP": "LPAREN",
         "TRP": "RPAREN", "TLB": "LBRACK", "TRB": "RBRACK", "TLC": "LBRACE", "TRC": "RBRACE",
         "TNl": "NEWLINE"}


def reference_tokens(text):
    out = []
    for t in lex(text, "ascii"):
        if t.kind == "EOF":
            break
        out.append((t.kind, t.value if t.kind in ("IDENT", "AXIS") else None))
    return out


def normal(toks):
    """Newlines collapsed and none leading, as skijack.lexicon emits them."""
    out = []
    for k, v in toks:
        k = KINDS.get(k, k)
        if k == "NEWLINE" and (not out or out[-1][0] == "NEWLINE"):
            continue
        out.append((k, v))
    return out


def lexed(text):
    e, _ = front()
    return normal(tokens(App(e.terms["lx"], encode(text))))


@pytest.mark.parametrize("text", [
    "nat === Zero | Suc nat\n",
    "add m n = n |> { Zero m ; Suc k (Suc (add m k)) }\n",
    "poke k ev = [(2@k) (Suc (3@k))] -- a comment\n\nf := \\x. x'_1\n",
    "k := [[poke [peek load]] Zero]\ng a = 10@a\n",
])
def test_the_lexer_agrees(text):
    assert lexed(text) == reference_tokens(text)


def test_the_lexer_marks_what_is_not_skijack_0():
    assert ("TBad", None) in lexed("f := <I>\n")
    assert ("TBad", None) in lexed("f := 12\n")


def test_the_generated_declarations_are_current():
    text = SOURCE.read_text()
    begin, end = "-- BEGIN GENERATED\n", "-- END GENERATED\n"
    assert text[text.index(begin) + len(begin):text.index(end)] == tables.generated()


def test_the_front_end_is_in_the_subset_and_spec0_agrees_on_it():
    src = SOURCE.read_text()
    prog = parse(src, "ascii")
    assert in_subset(prog) is None
    ref = compile0(prog)
    e, _ = front()
    assert [n for n in ref if structural_hash(ref[n]) != structural_hash(e.terms[n])] == []
    assert len(ref) > 300


AVON = os.environ.get("AVON")
needs_avon = pytest.mark.skipif(not AVON, reason="AVON names no avon binary")


@needs_avon
@pytest.mark.parametrize("what", list(run0.EDGES))
def test_an_edge_program_is_accepted_or_refused_as_spec0_has_it(what):
    text = run0.EDGES[what]
    assert run0.compare(run0.run_avon(AVON, text)[1], run0.reference(text)) == ""


@needs_avon
def test_random_programs_compile_as_spec0_has_them():
    from test_spec0 import _program
    rng = random.Random(1)
    for _ in range(50):
        text = _program(rng)
        assert run0.compare(run0.run_avon(AVON, text)[1], run0.reference(text)) == ""


@needs_avon
def test_the_front_end_compiles_itself():
    why, _steps, n = run0.fixed_point(AVON)
    assert why == "" and n > 300, why


@needs_avon
def test_the_profile_charges_every_contraction_to_a_row(tmp_path):
    names = tmp_path / "front0.names.tsv"
    assert run0.names_file(names) > 300
    steps, rows = run0.profile(AVON, run0.EDGES["a mutual pair"], names)
    assert sum(c for c, _ in rows) == int(steps)
    assert "eqCode" in {run0.equation_of(label) for _, label in rows}
