"""The reference drivers (RUNTIME-DESIGN.md section 3e): kernels run as
programs over a fixed world.  These runs are the oracle Avon's drivers
are checked against.  A card list holds cells of different types, which
Stage B has no type for, so these kernels compile with checking off.
"""

import pytest

import skijack
from skijack.drivers import (DriverError, World, byte_list, cell, nat,
                             read_nat, replay, run_kernel)
from skijack.run import run_level0
from aviary_kernel.terms import App, Atom

DOOR = """
peek k p = 3@k
load k old = [(2@k) old]
"""

# Greets, then copies standard input to standard output 64 bytes a read,
# and exits 0 at its end.  Every event is a reply [0 [id answer]]: id 0
# is boot's, id 1 a read's.
ECHO = DOOR + """
hi = cons 104 (cons 105 (cons 10 nil))
more = cons [2 [1 [0 64]]] nil
echo bs h t = cons [1 [1 bs]] more
onRead bs = bs (cons [5 0] nil) (echo bs)
answer id a = id (cons [1 [1 hi]] more) (K (onRead a))
poke k ev = [(answer (6@ev) (7@ev)) [(2@k) (3@k)]]
kernel := [[poke [peek load]] 0]
"""

# Writes its name, the first argument, asks for HOME (id 2) and writes it or "?",
# asks for the step count (id 3) and keeps it as its state, then exits 7.
# The write after the exit card is never performed, and the card [9 0]
# is no driver's, so it passes through.
SHOW = DOOR + """
hi = cons 104 (cons 105 (cons 10 nil))
nl = cons 10 nil
home = cons 72 (cons 79 (cons 77 (cons 69 nil)))
unset = cons 63 (cons 10 nil)
first h t = h
onBoot a = cons [1 [1 ((2@a) nil first)]] (cons [1 [1 nl]] (cons [9 0] (cons [3 [2 home]] nil)))
shown h t = cons [1 [1 h]] (cons [4 3] nil)
onEnv v = v (cons [1 [2 unset]] (cons [4 3] nil)) shown
onSteps n = cons [5 7] (cons [1 [1 hi]] nil)
p2 a q = q (onEnv a) (K (onSteps a))
p1 a p = p nil (p2 a)
pick id a = id (onBoot a) (p1 a)
s2 a s q = q s (K a)
s1 a s p = p s (s2 a s)
st id a s = id s (s1 a s)
poke k ev = [(pick (6@ev) (7@ev)) [(2@k) (st (6@ev) (7@ev) (3@k))]]
kernel := [[poke [peek load]] 0]
"""

# Asks for 128 bits (id 1) and writes how many of them are 1 as that many
# bytes "1", then exits 0: boot's own 128 bits are in its answer's tail.
BITS = DOOR + """
one = cons 49 nil
count bs = bs nil countc
countc b t = b (cons [1 [1 one]] (count t)) (count t)
onBoot a = cons [0 1] nil
onBits bs = listAppend (count bs) (cons [5 0] nil)
answer id a = id (onBoot a) (K (onBits a))
poke k ev = [(answer (6@ev) (7@ev)) [(2@k) (3@k)]]
kernel := [[poke [peek load]] 0]
"""

# Asks for the step count (id 1) and exits with it as its status.
STEPS = DOOR + """
answer id a = id (cons [4 1] nil) (K (cons [5 a] nil))
poke k ev = [(answer (6@ev) (7@ev)) [(2@k) (3@k)]]
kernel := [[poke [peek load]] 0]
"""


def kernel(src):
    return skijack.compile(src, check=False).terms["kernel"]


def state(k):
    hd = App(App(Atom("S"), Atom("I")), App(Atom("K"), Atom("K")))
    tl = App(App(Atom("S"), Atom("I")), App(Atom("K"), App(Atom("K"), Atom("I"))))
    return read_nat(App(tl, k))


def test_the_encodings_are_the_piers():
    """The host builds what Avon's pier builds: a cell is S (S I (K x)) (K y),
    nil K, cons K [h t], the numerals over SUC, a Boolean K or K I."""
    for n in (0, 1, 7, 255):
        assert read_nat(nat(n)) == n
    assert read_nat(nat(300), 255) is None
    r = run_level0(App(App(cell(Atom("x"), Atom("y")), Atom("c")), Atom("z")),
                   whnf_only=False)
    assert repr(r.term) == repr(App(App(App(Atom("c"), Atom("x")), Atom("y")), Atom("z")))
    assert repr(byte_list(b"")) == repr(Atom("K"))


def test_echo_copies_input_to_output_and_exits_0():
    r = run_kernel(kernel(ECHO), World(stdin=b"hello, world\n" * 10))
    assert r.stdout == b"hi\n" + b"hello, world\n" * 10
    assert (r.status, r.stderr, r.passed) == (0, b"", [])
    # boot, reads of 64, 64 and 2 bytes, and the end of input
    assert (r.pokes, r.steps) == (5, 630)


def test_reading_is_read2s_not_a_lines():
    """Each read answers at most max bytes, whatever the input holds; the
    end of input is nil, and empty input is the end at once."""
    r = run_kernel(kernel(ECHO), World(stdin=b"x" * 200))
    assert r.stdout == b"hi\n" + b"x" * 200 and r.pokes == 6
    r = run_kernel(kernel(ECHO), World())
    assert (r.stdout, r.pokes) == (b"hi\n", 2)


def test_arguments_environment_steps_and_exit():
    w = World(argv=[b"show", b"arg1"], env={b"HOME": b"/home/k\n"})
    r = run_kernel(kernel(SHOW), w)
    assert (r.stdout, r.stderr, r.status) == (b"show\n/home/k\n", b"", 7)
    assert len(r.passed) == 1 and read_nat(App(App(r.passed[0], Atom("K")), Atom("K"))) is None
    # the step count is the pokes' contractions when the walk reached the
    # card: boot's and the environment reply's, and the kernel keeps it
    assert r.pokes == 3 and 0 < state(r.kernel) < r.steps


def test_an_unset_variable_differs_from_an_empty_one():
    r = run_kernel(kernel(SHOW), World(argv=[b"show"]))
    assert (r.stdout, r.stderr) == (b"show\n", b"?\n")
    r = run_kernel(kernel(SHOW), World(argv=[b"show"], env={b"HOME": b""}))
    assert (r.stdout, r.stderr) == (b"show\n", b"")


def test_replay_performs_nothing_and_reaches_the_same_kernel():
    w = World(argv=[b"show", b"a"], env={b"HOME": b"h"})
    r = run_kernel(kernel(SHOW), w)
    k = replay(kernel(SHOW), r.log)
    assert state(k) == state(r.kernel) and len(r.log) == r.pokes


def test_entropy_comes_from_the_world_and_only_with_it():
    bits = bytes([0b1011, 0]) + bytes(14)
    w = World(entropy=bytes(16) + bits)
    r = run_kernel(kernel(BITS), w)
    assert (r.stdout, r.status) == (b"111", 0)
    # without entropy the request is no driver's card: it passes through
    r = run_kernel(kernel(BITS), World())
    assert (r.stdout, len(r.passed), r.pokes) == (b"", 1, 1)
    with pytest.raises(DriverError):
        run_kernel(kernel(BITS), World(entropy=bytes(16)))


def test_the_step_count_is_the_pokes_contractions_when_the_walk_reaches_it():
    """One poke, boot's, before the request is taken: the count is its
    contractions, and the run exits with it."""
    r = run_kernel(kernel(STEPS), World())
    # boot's poke takes 52 contractions and the reply's 89
    assert (r.status, r.steps, r.pokes) == (52, 141, 2)
