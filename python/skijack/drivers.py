"""The reference drivers: a kernel run as a program (``RUNTIME-DESIGN.md``
§3e, ``SPEC.md`` §4.1).

A kernel booted with drivers does I/O by emitting cards ``[tag data]``,
and the host performs them.  This module is that host, in Python, over a
fixed :class:`World` of input bytes, arguments, an environment and
entropy, so a run is a function of its world.  It is the oracle that
Avon's drivers are checked against.

Every shape is read behaviourally, by applying a term to marker atoms,
and every term the host builds is the canonical Scott encoding Avon's
pier builds (``avon/src/pier.c``, ``avon/src/kernel.c``):

- a cell ``[x y]`` is ``λc. c x y``, read with ``hd = S I (K K)`` and
  ``tl = S I (K (K I))``;
- a list is ``nil = K`` or ``cons h t = K [h t]``;
- a numeral is ``Zero = K`` or ``Suc n``, ``SUC = S (K K) (S (K (S I)) K)``;
- a Boolean is ``K`` (true) or ``K I`` (false).

The walk is FIFO.  The host walks a poke's cards in list order, performs a
write when it reaches it, and answers a request with a reply poked then
and there; the reply's own cards queue behind those not yet walked.  An
exit card ends the run.  A card that is not one of these shapes passes
through untouched.  Every answer is logged before it is applied, and
:func:`replay` applies a log without performing anything.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field
from typing import Deque, List, Mapping, Optional, Sequence, Tuple

from aviary_kernel.environment import Environment
from aviary_kernel.reduce import Status
from aviary_kernel.terms import App, Atom, Term

from .errors import SkijackError
from .probe import fast_reduce

__all__ = ["World", "Run", "DriverError", "run_kernel", "replay",
           "TAG_ENTROPY", "TAG_WRITE", "TAG_READ", "TAG_ENV", "TAG_STEPS",
           "TAG_EXIT", "nat", "byte_list", "cell", "read_nat"]

TAG_ENTROPY, TAG_WRITE, TAG_READ, TAG_ENV, TAG_STEPS, TAG_EXIT = range(6)

#: the kernel's arms, by axis (SPEC.md §4.1)
POKE = 4

#: a probe's bound: a card whose fields do not settle within it is no card
PROBE_STEPS = 1_000_000

#: entropy's draw, as §9.1 of Avon's DESIGN.md has it
ENTROPY_BYTES = 16


class DriverError(SkijackError):
    pass


S, K, I = Atom("S"), Atom("K"), Atom("I")


def _ap(*ts: Term) -> Term:
    r = ts[0]
    for t in ts[1:]:
        r = App(r, t)
    return r


HD = _ap(S, I, _ap(K, K))
TL = _ap(S, I, _ap(K, _ap(K, I)))
SUC = _ap(S, _ap(K, K), _ap(S, _ap(K, _ap(S, I)), K))
FALSE = _ap(K, I)


def cell(x: Term, y: Term) -> Term:
    """``[x y]``, the Scott pair ``λc. c x y``, as the pier builds it."""
    return _ap(S, _ap(S, I, _ap(K, x)), _ap(K, y))


def cons(h: Term, t: Term) -> Term:
    return _ap(K, cell(h, t))


NIL = K


def nat(n: int) -> Term:
    t: Term = K
    for _ in range(n):
        t = App(SUC, t)
    return t


def term_list(items: Sequence[Term]) -> Term:
    t: Term = NIL
    for x in reversed(items):
        t = cons(x, t)
    return t


def byte_list(b: bytes) -> Term:
    return term_list([nat(x) for x in b])


def bits_list(b: bytes) -> Term:
    """Bit ``8i + j`` is bit ``j`` of byte ``i``, least significant first."""
    return term_list([K if b[i // 8] >> (i % 8) & 1 else FALSE
                      for i in range(8 * len(b))])


# ------------------------------------------------------------ probing

def _peel(t: Term, nctors: int) -> Optional[Tuple[int, List[Term]]]:
    """Which of ``nctors`` constructors ``t`` is, and its fields: ``t``
    applied to one marker per constructor, reduced to weak head normal
    form.  None for anything else, or a probe that does not settle."""
    marks = [Atom(f"\x00d{i}") for i in range(nctors)]
    r = fast_reduce(_ap(t, *marks), Environment(), whnf_only=True,
                    max_steps=PROBE_STEPS)
    if r.status not in (Status.WHNF, Status.NORMAL):
        return None
    head, args = r.term, []
    while isinstance(head, App):
        args.append(head.arg)
        head = head.fn
    args.reverse()
    names = [m.name for m in marks]
    if not isinstance(head, Atom) or head.name not in names:
        return None
    return names.index(head.name), args


def _pair(t: Term) -> Optional[Tuple[Term, Term]]:
    p = _peel(t, 1)
    return (p[1][0], p[1][1]) if p and len(p[1]) == 2 else None


def read_nat(t: Term, limit: Optional[int] = None) -> Optional[int]:
    """A numeral's value, or None if ``t`` is not one, or passes ``limit``."""
    n = 0
    while True:
        p = _peel(t, 2)
        if p is None:
            return None
        ctor, fields = p
        if ctor == 0 and not fields:
            return n
        if ctor != 1 or len(fields) != 1:
            return None
        n += 1
        if limit is not None and n > limit:
            return None
        t = fields[0]


def _read_list(t: Term) -> Optional[List[Term]]:
    out: List[Term] = []
    while True:
        p = _peel(t, 2)
        if p is None:
            return None
        ctor, fields = p
        if ctor == 0 and not fields:
            return out
        if ctor != 1 or len(fields) != 2:
            return None
        out.append(fields[0])
        t = fields[1]


def _read_bytes(t: Term) -> Optional[bytes]:
    items = _read_list(t)
    if items is None:
        return None
    out = bytearray()
    for x in items:
        v = read_nat(x, 255)
        if v is None:
            return None
        out.append(v)
    return bytes(out)


def _normal(t: Term) -> Optional[Term]:
    r = fast_reduce(t, Environment(), whnf_only=False, max_steps=PROBE_STEPS)
    return r.term if r.status is Status.NORMAL else None


# ------------------------------------------------------------ the run

@dataclass
class World:
    """Everything a run reads: standard input, the arguments (the program's
    name first), the environment, and the entropy to draw, 16 bytes a
    draw, or None for a kernel booted without entropy."""
    stdin: bytes = b""
    argv: Sequence[bytes] = (b"kernel",)
    env: Mapping[bytes, bytes] = field(default_factory=dict)
    entropy: Optional[bytes] = None


@dataclass
class Run:
    """What a run did.  ``status`` is the exit card's code, or 0 when the
    queue emptied; ``log`` holds every reply event, in the order applied,
    as ``replay`` takes them; ``steps`` counts the pokes' contractions."""
    stdout: bytes
    stderr: bytes
    status: int
    kernel: Term
    log: List[Term]
    steps: int
    pokes: int
    passed: List[Term]


def _poke(kernel: Term, event: Term, fuel: int) -> Tuple[Term, Term, int]:
    arm = kernel
    for bit in bin(POKE)[3:]:
        arm = App(TL if bit == "1" else HD, arm)
    r = fast_reduce(_ap(arm, kernel, event), Environment(), whnf_only=True,
                    max_steps=fuel)
    if r.status not in (Status.WHNF, Status.NORMAL):
        raise DriverError(f"a poke did not reach weak head normal form "
                          f"({r.status.value} after {r.steps} contractions)")
    return App(HD, r.term), App(TL, r.term), r.steps


def _reply(rid: Term, answer: Term) -> Term:
    return cell(K, cell(rid, answer))


def boot_event(world: World) -> Term:
    """``[0 [0 [argv bits]]]``: boot's own reply, ``bits`` the first draw,
    or nil without entropy."""
    bits = (bits_list(world.entropy[:ENTROPY_BYTES])
            if world.entropy is not None else NIL)
    argv = term_list([byte_list(a) for a in world.argv])
    return _reply(K, cell(argv, bits))


def run_kernel(kernel: Term, world: World, *, fuel: int = 10 ** 7) -> Run:
    """Run ``kernel`` with drivers in ``world``: boot's reply first, then
    every card in FIFO order until an exit card or an empty queue.
    ``fuel`` bounds each poke, and nothing else bounds the run."""
    out, err = bytearray(), bytearray()
    stdin = world.stdin
    draws = 1 if world.entropy is not None else 0
    log: List[Term] = []
    passed: List[Term] = []
    steps = pokes = 0
    queue: Deque[Term] = deque()

    def apply(event: Term) -> None:
        nonlocal kernel, steps, pokes
        log.append(event)
        eff, kernel, n = _poke(kernel, event, fuel)
        steps += n
        pokes += 1
        queue.append(eff)

    apply(boot_event(world))
    while queue:
        p = _peel(queue[0], 2)
        if p is None or p[0] == 0 or len(p[1]) != 2:
            queue.popleft()             # nil, or not a list: no more cards here
            continue
        card, queue[0] = p[1]
        tagged = _pair(card)
        tag = read_nat(tagged[0], TAG_EXIT) if tagged else None
        data = tagged[1] if tagged else None
        done = None
        if tag == TAG_EXIT:
            code = read_nat(data, 255)
            if code is not None:
                return Run(bytes(out), bytes(err), code, kernel, log, steps,
                           pokes, passed)
        elif tag == TAG_WRITE:
            fb = _pair(data)
            fd = read_nat(fb[0], 2) if fb else None
            bs = _read_bytes(fb[1]) if fb and fd in (1, 2) else None
            if bs is not None:
                (out if fd == 1 else err).extend(bs)
                done = True
        elif tag in (TAG_ENTROPY, TAG_READ, TAG_ENV, TAG_STEPS):
            rid, args = (data, None) if tag in (TAG_ENTROPY, TAG_STEPS) else (
                _pair(data) or (None, None))
            rid = _normal(rid) if rid is not None else None
            answer = None
            if rid is None:
                pass
            elif tag == TAG_ENTROPY and world.entropy is not None:
                b = world.entropy[ENTROPY_BYTES * draws:ENTROPY_BYTES * (draws + 1)]
                if len(b) != ENTROPY_BYTES:
                    raise DriverError("the world's entropy has run out")
                draws += 1
                answer = bits_list(b)
            elif tag == TAG_READ:
                fm = _pair(args)
                fd = read_nat(fm[0], 0) if fm else None
                mx = read_nat(fm[1]) if fm and fd == 0 else None
                if mx:
                    answer, stdin = byte_list(stdin[:mx]), stdin[mx:]
            elif tag == TAG_ENV:
                name = _read_bytes(args)
                if name is not None:
                    v = world.env.get(name)
                    answer = term_list([] if v is None else [byte_list(v)])
            elif tag == TAG_STEPS:
                answer = nat(steps)
            if answer is not None:
                apply(_reply(rid, answer))
                done = True
        if not done:
            passed.append(card)
    return Run(bytes(out), bytes(err), 0, kernel, log, steps, pokes, passed)


def replay(kernel: Term, log: Sequence[Term], *, fuel: int = 10 ** 7) -> Term:
    """Apply a run's logged events and perform none of their cards: the
    kernel the run left."""
    for event in log:
        _, kernel, _ = _poke(kernel, event, fuel)
    return kernel
