"""The full language's front end, built in milestones (avon docs/WORKLIST.md,
Stage 8): M1 cores, macros, signatures, the Tier 1 birds and the numeral
operations; M2 interpreter generation; M3 quotation; M4 scries, paths and
namespace literals.  The checkers, M5 and M6, are to come.

``skijack/selfhost/front1.ascii.ski`` is compiled by this package, with
checking.  With ``AVON`` naming an avon binary, the last tests run it
through ``skijack.selfhost.run1`` against the expander with checking off:
the corpus, each milestone's edge programs, random programs and the fixed
point; otherwise they skip.  ``avon/tests/front1_check.sh`` runs the same
checks at full size.
"""

import functools
import os
import pathlib
import random
import sys

import pytest

import skijack
from skijack.selfhost import run1, tables

SOURCE = pathlib.Path(skijack.__file__).parent / "selfhost" / "front1.ascii.ski"
CORPUS = pathlib.Path(skijack.__file__).parent / "corpus"


@pytest.fixture(autouse=True)
def _deep_recursion():
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 200_000))
    yield
    sys.setrecursionlimit(old)


def test_the_generated_declarations_are_current():
    text = SOURCE.read_text()
    begin, end = "-- BEGIN GENERATED\n", "-- END GENERATED\n"
    try:
        tables.select("front1")
        want = tables.generated()
    finally:
        tables.select("front0")
    assert text[text.index(begin) + len(begin):text.index(end)] == want


@functools.lru_cache(maxsize=1)
def front():
    return skijack.compile(SOURCE.read_text(), lexicon="ascii")


def test_the_front_end_compiles_with_checking():
    assert "front" in front().terms


EDGES = {**run1.EDGES1, **run1.EDGES2, **run1.EDGES3, **run1.EDGES4}


def test_the_aviary_edges_are_edges():
    assert run1.AVIARY <= set(run1.EDGES) | set(EDGES)


AVON = os.environ.get("AVON")
needs_avon = pytest.mark.skipif(not AVON, reason="AVON names no avon binary")


@needs_avon
@pytest.mark.parametrize("stem", [s for m in run1.MILESTONES.values() for s in m])
def test_a_corpus_program_compiles_as_the_expander_has_it(stem):
    text = (CORPUS / f"{stem}.ascii.ski").read_text()
    assert run1.compare(run1.run_avon(AVON, text)[1], run1.reference(text)) == ""


@needs_avon
@pytest.mark.parametrize("what", [w for w in EDGES if w not in run1.AVIARY])
def test_an_edge_is_accepted_or_refused_as_the_expander_has_it(what):
    text = EDGES[what]
    assert run1.compare(run1.run_avon(AVON, text)[1], run1.reference(text)) == ""


@needs_avon
def test_random_programs_compile_as_the_expander_has_them():
    rng = random.Random(20261005)
    for _ in range(20):
        text = run1._program2(rng)
        ref = run1.reference(text)
        why = run1.compare(run1.run_avon(AVON, text)[1], ref)
        assert why == "" or (ref is None and run1.aviary_refuses(text)), text


@needs_avon
def test_the_front_end_compiles_itself():
    text = SOURCE.read_text()
    _steps, got = run1.run_avon(AVON, text)
    assert run1.compare(got, run1.reference(text)) == ""
