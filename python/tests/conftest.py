import os
import pathlib

import skijack

import pytest

# the corpus ships inside the package: it is the conformance suite, and
# `pip install skijack` should carry the examples the paper cites.
CORPUS = pathlib.Path(skijack.__file__).parent / "corpus"

#: every corpus file, as (stem, lexicon, path)
ALL_SOURCES = sorted(
    (p.name.split(".")[0], p.name.split(".")[1], p)
    for p in CORPUS.glob("*.ski")
)

#: stems the expander can compile end to end with no quotation.  EXAMPLES.md
#: 1-3 need no generation; the interpreter stems exercise generate.py.
#: test_check.COMPILABLE adds the rest of the compiling corpus.
EXPANDABLE = ("sec1-nat", "sec2-c", "sec3-swap")
INTERPRETERS = ("interp-whnff", "interp-whnff-written-loop",
                "interp-whnff-written", "interp-t3")


def source(stem: str, lexicon: str) -> str:
    return (CORPUS / f"{stem}.{lexicon}.ski").read_text(encoding="utf-8")


@pytest.fixture(scope="session")
def corpus():
    return {(s, lx): p.read_text(encoding="utf-8") for s, lx, p in ALL_SOURCES}


#: the paper's artifact, used read-only as the test oracle.  Its module
#: body is executed with the ``__main__`` block split off, which is the
#: whole of the dependency: nothing is written back and the artifact's
#: own Environment is never handed to the expander.
#: Where the first paper's artifact lives.  Overridable, because a third
#: of this suite is the cross-check against it and that third is the part
#: that establishes the compiler's output is *correct* rather than merely
#: self-consistent.  When the path is wrong those tests skip, and a
#: silent skip of the oracle is worse than a loud failure -- see
#: ``pytest_sessionstart`` below.
ARTIFACT_DIR = pathlib.Path(
    os.environ.get("SKIJACK_ARTIFACT_DIR",
                   pathlib.Path(__file__).resolve().parent / "artifact")).expanduser()
ARTIFACT = ARTIFACT_DIR / "tower_harness.py"


def pytest_sessionstart(session):
    """Refuse to run a suite whose oracle is absent, unless asked.

    Without this the suite reports success on any machine but the
    author's while quietly dropping every comparison against the
    hand-built artifact.  Set ``SKIJACK_ARTIFACT_DIR`` to the checkout,
    or ``SKIJACK_ALLOW_SKIP=1`` to accept the reduced suite knowingly.
    """
    if ARTIFACT.exists() or os.environ.get("SKIJACK_ALLOW_SKIP") == "1":
        return
    raise pytest.UsageError(
        f"the oracle artifact is not at {ARTIFACT_DIR}.\n"
        f"Roughly a third of this suite compares compiled terms against "
        f"the hand-built artifact of the companion paper; without it "
        f"those tests skip and the remainder checks the compiler only "
        f"against itself.\n"
        f"A copy is vendored at tests/artifact; unset SKIJACK_ARTIFACT_DIR to use\n"
        f"it, or point it at a checkout of artifact-metacircular-ski, or "
        f"SKIJACK_ALLOW_SKIP=1 to run the reduced suite deliberately.")


def _load(path):
    """Execute an artifact module's body with its ``__main__`` block split
    off, from the artifact's own directory (``scry_harness.py`` reads
    ``tower_harness.py`` by relative path).  Read-only: nothing is written
    back, and the artifact's Environment is never handed to the expander.
    """
    if not path.exists():                          # pragma: no cover
        pytest.skip(f"artifact not present at {path}")
    src = path.read_text(encoding="utf-8")
    # the first *statement* occurrence, not the one inside a string literal
    head = src.split("\nif __name__")[0]
    ns = {"__name__": "skijack_test_oracle"}
    cwd = os.getcwd()
    try:
        os.chdir(ARTIFACT_DIR)
        exec(compile(head, str(path), "exec"), ns)
    finally:
        os.chdir(cwd)
    return ns


@pytest.fixture(scope="session")
def oracle():
    ns = _load(ARTIFACT)

    from aviary_kernel.abstraction import expand as _x

    class Oracle:
        env = ns["env"]
        natP = staticmethod(ns["natP"])
        encP = staticmethod(ns["encP"])
        enc = staticmethod(ns["enc"])
        enc5 = staticmethod(ns["enc5"])
        OMEGA = ns["OMEGA"]

        @staticmethod
        def term(name):
            """The artifact's closed {S,K,I} term for one of its names."""
            return _x(ns["a"](name), ns["env"])

        @staticmethod
        def enc5P(t):
            return _x(ns["enc5"](t), ns["env"])

    return Oracle()


@pytest.fixture(scope="session")
def scry_oracle():
    """`scry_harness.py`, `scry_namespace.py` and `scry_paths.py`, which
    build on one another: loading the last brings in all three."""
    ns = _load(ARTIFACT_DIR / "scry_paths.py")

    from aviary_kernel.abstraction import expand as _x

    class ScryOracle:
        env = ns["env"]
        natP = staticmethod(ns["natP"])
        encQ = staticmethod(ns["encQ"])
        Scry = staticmethod(ns["Scry"])
        WQ = ns["WQ"]
        WN = ns["WN"]
        EQ5 = ns["EQ5"]

        @staticmethod
        def term(name):
            return _x(ns["a"](name), ns["env"])

        @staticmethod
        def encQP(t):
            return _x(ns["encQ"](t), ns["env"])

    return ScryOracle()
