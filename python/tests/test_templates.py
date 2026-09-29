"""Supercombinator templates (skijack.templates): each rule's formals and
open body, a hint beside the pure SKI term that it abstracts back to."""

import pathlib
import random
import sys

import pytest
from aviary_kernel.abstraction import bracket_abstract
from aviary_kernel.terms import App, Atom

import skijack
from skijack import corpus
from skijack.dictionary import structural_hash
from skijack.parser import parse
from skijack.spec0 import compile0
from skijack.templates import (BApp, Ref, Var, check, is_eta, templates,
                               write)

FRONT = pathlib.Path(skijack.__file__).parent / "selfhost" / "front0.ascii.ski"


@pytest.fixture(autouse=True)
def _deep_recursion():
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 1_000_000))
    yield
    sys.setrecursionlimit(old)


def compilable():
    stems = sorted({p.name.split(".")[0] for p in corpus.DIR.glob("*.ascii.ski")})
    for stem in stems:
        try:
            yield stem, skijack.compile(corpus.read(stem, "ascii"), lexicon="ascii")
        except Exception:                       # Stage A refusals
            continue


def test_every_corpus_template_abstracts_to_its_term():
    n = 0
    for stem, exp in compilable():
        for t in templates(exp):
            assert check(t), (stem, t.name)
            n += 1
    assert n > 700


def test_every_rule_is_a_template_or_an_eta_template():
    """No body is open: each variable is one of its rule's formals."""
    for stem, exp in compilable():
        names = {t.name for t in templates(exp)}
        for name, d in exp.env.definitions.items():
            if d.builtin or d.is_alias or not d.formals or name in names:
                continue
            body = d.body
            for f in reversed(d.formals):       # η: G f1 .. fk, G closed
                assert isinstance(body, App) and body.arg == Atom(f), (stem, name)
                body = body.fn


def test_templates_change_no_term():
    src = corpus.read("kernel-events", "ascii")
    exp = skijack.compile(src, lexicon="ascii")
    before = {n: structural_hash(t) for n, t in exp.terms.items()}
    templates(exp)
    assert {n: structural_hash(t) for n, t in exp.terms.items()} == before
    fresh = skijack.compile(src, lexicon="ascii")
    assert {n: structural_hash(t) for n, t in fresh.terms.items()} == before


def test_the_front_ends_templates_are_spec0s_rules():
    src = FRONT.read_text()
    ts = templates(skijack.compile(src, lexicon="ascii"))
    internals: dict = {}
    compile0(parse(src, "ascii"), internals)
    spec = {structural_hash(v) for v in internals.values()}
    assert all(check(t) for t in ts)
    assert [t.label for t in ts if t.key_hash not in spec] == []
    assert len(ts) > 900


def test_random_programs_templates_are_spec0s_rules():
    sys.path.insert(0, str(pathlib.Path(__file__).parent))
    from test_spec0 import _program
    rng = random.Random(20260929)
    for _ in range(60):
        src = _program(rng)
        ts = templates(skijack.compile(src, lexicon="ascii", check=False))
        internals: dict = {}
        compile0(parse(src, "ascii"), internals)
        spec = {structural_hash(v) for v in internals.values()}
        assert all(check(t) for t in ts)
        assert all(t.key_hash in spec for t in ts)


def test_an_eta_rule_is_left_out():
    src = ("nat === Zero | Suc nat\n"
           "g n = n |> { Zero Zero ; Suc k k }\n"
           "f x = g x\n")                        # η: compiles to g itself
    exp = skijack.compile(src, lexicon="ascii")
    by = {t.label: t for t in templates(exp)}
    assert "f" not in by and "g" in by


def test_the_expander_never_repeats_a_formal():
    """aviary refuses a rule with a repeated formal, so every template's
    formals are distinct (the file allows a repeat, the last binding, as
    lean-ski does)."""
    for stem, exp in compilable():
        for t in templates(exp):
            assert len(set(t.formals)) == len(t.formals), (stem, t.name)


def _printed(text):
    """The printed form: juxtaposition to the left, parentheses."""
    stack: list = [[]]
    for tok in text.replace("(", " ( ").replace(")", " ) ").split():
        if tok == "(":
            stack.append([])
            continue
        if tok == ")":
            items = stack.pop()
            t = items[0]
            for x in items[1:]:
                t = App(t, x)
            stack[-1].append(t)
            continue
        stack[-1].append(Atom(tok))
    items = stack[0]
    t = items[0]
    for x in items[1:]:
        t = App(t, x)
    return t


def _read_back(tdir):
    """The files parsed the way a runtime reads them: each body rebuilt with
    its references resolved through template_terms.tsv."""
    terms = {}
    for line in (tdir / "template_terms.tsv").read_text().splitlines():
        h, _atoms, text = line.split("\t")
        terms[h] = _printed(text)
    out = []
    for line in (tdir / "templates.tsv").read_text().splitlines():
        key, kind, label, k, formals, body = line.split("\t")
        toks = body.replace("`", " ` ").split()
        pos = [0]

        def build():
            tok = toks[pos[0]]
            pos[0] += 1
            if tok == "`":
                f = build()
                return App(f, build())
            if tok.startswith("v"):
                return Atom("\x00v" + tok[1:])
            if tok.startswith("#"):
                return terms["skijack-1:" + tok[1:]]
            return Atom(tok)
        term = build()
        assert pos[0] == len(toks)
        fs = [int(x) for x in formals.split(",")]
        assert len(fs) == int(k)
        out.append((key, fs, term))
    return out


def test_the_files_read_back_to_their_keys(tmp_path):
    exp = skijack.compile(corpus.read("kernel-events", "ascii"), lexicon="ascii")
    ts = templates(exp)
    n, m = write(ts, tmp_path / "templates.tsv", tmp_path / "template_terms.tsv")
    assert n == len(ts) and m > 0
    rows = _read_back(tmp_path)
    assert len(rows) == len(ts)
    for key, fs, term in rows:
        for f in reversed(fs):
            term = bracket_abstract("\x00v" + str(f), term)
        assert structural_hash(term) == key


def test_template_bodies_hold_only_formals_references_and_combinators():
    exp = skijack.compile(FRONT.read_text(), lexicon="ascii")
    for t in templates(exp):
        assert not is_eta(t)
        stack = [t.body]
        while stack:
            x = stack.pop()
            if isinstance(x, BApp):
                stack += [x.fn, x.arg]
            elif isinstance(x, Var):
                assert x.n in t.formals
            elif isinstance(x, Ref):
                assert structural_hash(x.term)
            else:
                assert x.name in ("S", "K", "I")
