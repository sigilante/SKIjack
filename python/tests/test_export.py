"""The conformance export for Avon (`avon/DESIGN.md` §10.1): the container
is Avon's wire format bit for bit, and the exported targets carry the
values and counts the rest of this suite asserts -- the paper's T3 and scry
tables, the tower, EXAMPLES.md section 4's fuel boundary.
"""

import pytest
from aviary_kernel.terms import App, Atom

from skijack.export import jam, targets

S, K, I = Atom("S"), Atom("K"), Atom("I")


def bits(container: bytes) -> str:
    assert container[:8] == b"SKIT\x01\x00\x00\x00"
    assert container[8:12] == b"\x00\x00\x00\x00"          # no atoms
    n = int.from_bytes(container[12:20], "little")
    body = container[20:]
    assert len(body) == (n + 7) // 8
    return "".join(str(body[i // 8] >> (i % 8) & 1) for i in range(n))


def test_jam_is_avons_bitstring():
    """Avon's tests/test_wire.c pins the same codes."""
    assert bits(jam(S)) == "00"
    assert bits(jam(K)) == "01"
    assert bits(jam(I)) == "10"
    assert bits(jam(App(S, K))) == "110001"
    assert bits(jam(App(S, App(K, I)))) == "1100110110"


def test_jam_refuses_atoms():
    with pytest.raises(ValueError):
        jam(App(I, Atom("X")))


@pytest.fixture(scope="module")
def rows():
    return {r[0]: r for r in targets()}


def outcome(rows, ident):
    _id, _term, _cap, status, steps, _r, _o, ctor, payload = rows[ident]
    return status, steps, ctor, payload


def test_the_T3_table(rows):
    """test_interpreter.py's T3_TABLE, with CAP as a FUEL status."""
    want = {
        "err": (("WHNF", 127, "RErr"), ("FUEL", 400_000, "-")),
        "err_k": (("WHNF", 222, "RErr"), ("FUEL", 400_000, "-")),
        "k_i_err": (("WHNF", 574, "RVal"), ("WHNF", 574, "RVal")),
        "i_k": (("WHNF", 438, "RVal"), ("WHNF", 438, "RVal")),
        "omega": (("WHNF", 10_130, "RTime"), ("WHNF", 10_130, "RTime")),
    }
    for label, (absorbing, hiding) in want.items():
        assert outcome(rows, f"t3.{label}.wf5Abs")[:3] == absorbing
        assert outcome(rows, f"t3.{label}.wf5Omg")[:3] == hiding


def test_the_scry_table(rows):
    """test_scry.py's SCRY_TABLE."""
    want = {"qBase": ("RVal", "K"), "qBaseN": ("RVal", "K"),
            "qHit": ("RVal", "K"), "qMiss": ("RErr", "-"),
            "qBareN": ("RErr", "-"), "qBareA": ("RVal", "K"),
            "qUnsat": ("RVal", "Scry"), "qLazy": ("RVal", "K"),
            "qIfKhit": ("RVal", "I"), "qIfKmiss": ("RErr", "-"),
            "qOmega": ("RTime", "-")}
    for name, (ctor, payload) in want.items():
        assert outcome(rows, f"scry-wfq.{name}")[2:] == (ctor, payload)


def test_the_tower_and_the_fuel_boundary(rows):
    assert outcome(rows, "tower.t0") == ("WHNF", 340, "Just", "K")
    assert outcome(rows, "tower.t1") == ("WHNF", 91_556, "Just", "K")
    assert outcome(rows, "tower.t2")[:3] == ("WHNF", 504_930, "Just")
    assert [outcome(rows, f"examples4.answer.fuel{f}")[2]
            for f in (0, 1, 2, 5)] == ["RTime", "RTime", "RVal", "RVal"]
    assert outcome(rows, "examples4.answer.fuel5") == ("WHNF", 574, "RVal", "I")


def test_every_declaration_is_a_target(rows):
    assert len(rows) == 45
    assert outcome(rows, "parse-chars.apply")[:3] == ("WHNF", 62_199, "RValN")
