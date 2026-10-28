"""The full language's front end, built in milestones (avon docs/WORKLIST.md,
Stage 8): M1 cores, macros, signatures, the Tier 1 birds and the numeral
operations; M2 interpreter generation; M3 quotation; M4 scries, paths and
namespace literals; Lit numeral literals; M5 Stage A, each refusal with
its class; M6 Stage B.

``skijack/selfhost/front1.ascii.ski`` is compiled by this package, with
checking.  With ``AVON`` naming an avon binary, the last tests run it
through ``skijack.selfhost.run1`` against Stage A, Stage B and then the
expander with checking off: the corpus, each milestone's edge programs, random
programs and the fixed point, and front1's own templates against
``skijack.templates``; otherwise they skip.
``avon/tests/front1_check.sh`` runs the same checks at full size.
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


EDGES = {**run1.EDGES, **run1.EDGES1, **run1.EDGES2, **run1.EDGES3, **run1.EDGES4,
         **run1.EDGESL, **run1.EDGESB, **run1.EDGES5, **run1.EDGES6}


@pytest.mark.parametrize("what", list(run1.STAGEA) + list(run1.STAGEB))
def test_each_checker_edge_is_classed_as_it_says(what):
    """The reference itself, without Avon: each of M5's and M6's edges gets
    the class it was written for, so the edges test what they name."""
    want, text = {**run1.STAGEA, **run1.STAGEB}[what]
    ref = run1.reference(text)
    assert (None if isinstance(ref, dict) else run1.CLASSES[ref]) == want


AVON = os.environ.get("AVON")
needs_avon = pytest.mark.skipif(not AVON, reason="AVON names no avon binary")


@needs_avon
@pytest.mark.parametrize("stem", [s for m in run1.MILESTONES.values() for s in m])
def test_a_corpus_program_compiles_as_the_expander_has_it(stem):
    text = (CORPUS / f"{stem}.ascii.ski").read_text()
    assert run1.compare(run1.run_avon(AVON, text)[1], run1.reference(text)) == ""


@needs_avon
@pytest.mark.parametrize("stem", ["literals", "scry-ns"])
def test_a_corpus_program_emits_the_expanders_templates(stem):
    # front1's own templates, ROk's second field, as Avon's front0 --emit
    # writes them: every key skijack.templates gives, with one of its bodies
    text = (CORPUS / f"{stem}.ascii.ski").read_text()
    got = run1.emitted(AVON, text)
    assert got is not None
    why, _ = run1.compare_templates(got, run1.python_templates(text))
    assert why == ""


@needs_avon
@pytest.mark.parametrize("what", list(EDGES))
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
        assert why == "", text


@needs_avon
def test_random_typed_programs_compile_as_the_expander_has_them():
    """Stage B's accepting paths: programs typed as they are written."""
    rng = random.Random(20261027)
    for _ in range(20):
        text = run1._program6(rng)
        assert run1.compare(run1.run_avon(AVON, text)[1], run1.reference(text)) == "", text


@needs_avon
def test_the_front_end_compiles_itself():
    """With templates and data jets: the same terms, from fewer contractions
    and in a third of the memory, as Stage B's run would take more than 12
    GB without them."""
    text = SOURCE.read_text()
    _steps, got = run1.run_avon(AVON, text, (f"--templates={run1.term_dir()}", "--data"))
    assert run1.compare(got, run1.reference(text)) == ""
