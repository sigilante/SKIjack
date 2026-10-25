"""Avon as the reducer (skijack.avon).

Without Avon: the DAG encoding keeps sharing and aliases every atom; a
term with a live aviary bird is left to aviary; same_term compares trees.
With ``AVON`` naming an avon binary: Avon's copy mode gives aviary's
status, count and term on the cases that differ most between reducers --
fuel spent exactly at a normal form, fuel 0, normal form against weak head
normal form, skijack's own NUL-named markers, and a shared result.
"""

import os

import pytest
from aviary_kernel.environment import Environment
from aviary_kernel.terms import App, Atom

from skijack import avon as A
from skijack.probe import _aviary_reduce

S, K, I = Atom("S"), Atom("K"), Atom("I")
AVON = os.environ.get("AVON")
needs_avon = pytest.mark.skipif(not AVON, reason="needs AVON, an avon binary")


def ap(*ts):
    r = ts[0]
    for t in ts[1:]:
        r = App(r, t)
    return r


def test_the_encoding_keeps_sharing_and_aliases_atoms():
    x = Atom("\x00r0")
    sk = ap(S, K)
    line, back = A._encode(ap(sk, sk, x))
    assert line == "dag 0=S 1=K 2=0.1 3=2.2 4=v0 5=3.4 @5"
    assert back == {"v0": x}
    t = A._decode(line, back)
    assert A.same_term(t, ap(sk, sk, x))
    assert t.fn.fn is t.fn.arg            # the shared S K read back shared
    assert t.arg is x                     # the caller's own atom


def test_a_deep_term_encodes_without_recursion():
    t = Atom("a")
    for _ in range(200_000):
        t = App(t, K)
    line, back = A._encode(t)
    assert A.same_term(A._decode(line, back), t)


def test_a_live_bird_is_left_to_aviary():
    env = Environment()
    assert A._leaves_avon_can_run(ap(S, K, Atom("x")), env)
    assert not A._leaves_avon_can_run(ap(Atom("B"), K, K), env)   # B is a combinator here
    assert not A._leaves_avon_can_run(ap(Atom("Y"), K), env)


def test_same_term():
    assert A.same_term(ap(S, K), ap(Atom("S"), Atom("K")))
    assert not A.same_term(ap(S, K), ap(K, S))
    assert not A.same_term(S, ap(S, K))


CASES = [
    (ap(S, K, K, Atom("x")), True, 10),
    (ap(K, Atom("a"), Atom("b")), True, 1),       # the fuel spent exactly at the end
    (ap(K, Atom("a"), Atom("b")), True, 0),       # no fuel at all
    (ap(S, I, I, ap(S, I, I)), True, 5),          # no normal form
    (ap(S, I, I, ap(S, I, I)), False, 7),
    (ap(Atom("a"), ap(S, K, K, Atom("y"))), False, 100),   # normal form reduces the argument
    (ap(Atom("a"), ap(S, K, K, Atom("y"))), True, 100),    # weak head normal form does not
    (ap(S, ap(K, Atom("\x00c0")), I, Atom("\x00c1")), True, 100),
    (ap(S, I, I, ap(K, Atom("a"), Atom("b"))), False, 100),  # a shared result
]


@needs_avon
@pytest.mark.parametrize("term,whnf,fuel", CASES)
def test_avon_gives_aviary_s_run(term, whnf, fuel):
    env = Environment()
    r = A.AvonReducer(AVON)
    try:
        got = r.reduce(term, env, whnf_only=whnf, max_steps=fuel)
    finally:
        r.close()
    want = _aviary_reduce(term, env, whnf_only=whnf, max_steps=fuel, max_size=10 ** 9)
    assert (got.status, got.steps) == (want.status, want.steps)
    assert A.same_term(got.term, want.term)


@needs_avon
def test_a_term_with_a_bird_is_not_sent():
    r = A.AvonReducer(AVON)
    try:
        assert r.reduce(ap(Atom("B"), K, K, Atom("x")), Environment()) is None
        assert r.runs == 0
    finally:
        r.close()


def _nf(term):
    """The normal form as aviary gives it."""
    return _aviary_reduce(term, Environment(), whnf_only=False, max_steps=10 ** 6,
                          max_size=10 ** 9).term


@needs_avon
@pytest.mark.parametrize("term", [t for t, whnf, fuel in CASES if fuel >= 10 and not
                                  A.same_term(t, ap(S, I, I, ap(S, I, I)))])
def test_share_mode_reaches_aviary_s_normal_form(term):
    r = A.AvonReducer(AVON, "share")
    try:
        got = r.reduce(term, Environment(), whnf_only=False, max_steps=10 ** 6)
    finally:
        r.close()
    assert got.status.name == "NORMAL" and A.same_term(got.term, _nf(term))


@needs_avon
def test_share_mode_computes_a_shared_argument_once():
    """S I I x uses x twice: copy mode reduces it twice, share mode once."""
    x = ap(S, K, K, ap(S, K, K, ap(S, K, K, Atom("y"))))
    term = ap(S, I, I, x)
    steps = {}
    for strategy in A.STRATEGIES:
        r = A.AvonReducer(AVON, strategy)
        try:
            steps[strategy] = r.reduce(term, Environment(), whnf_only=False).steps
        finally:
            r.close()
    assert steps["share"] < steps["copy"]


def test_an_unknown_strategy_is_refused():
    with pytest.raises(A.AvonError, match="copy or share"):
        A.AvonReducer("avon", "lazy")


def test_check_takes_copy_mode_alone(monkeypatch):
    monkeypatch.setattr(A, "_mode", None)
    monkeypatch.setattr(A, "_reducer", None)
    monkeypatch.setenv("SKIJACK_REDUCER", "check")
    monkeypatch.setenv("AVON", "avon")
    monkeypatch.setenv("SKIJACK_AVON_STRATEGY", "share")
    with pytest.raises(A.AvonError, match="takes SKIJACK_AVON_STRATEGY=copy"):
        A.reducer()
