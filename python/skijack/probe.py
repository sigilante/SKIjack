"""Behavioral decoding: read a compiled term by running it, never by
reading combinator syntax.

This is the verification discipline of the paper's artifact
(``SURFACE-LANGUAGE-DESIGN.md`` §1, last bullet): a value is observed by
applying the term to fresh uninterpreted marker atoms and seeing which
one comes back.  The markers are host-level constants admitted in the
harness and nowhere in the language (``SYNTAX.md`` §8).

:func:`fast_reduce` is the artifact's reducer wrapper (``tower_harness.py``
and ``scry_harness.py`` build the same one on top of
``aviary_kernel.reduce``): ``reduce()`` with the size guard sampled every
``SIZE_CHECK_EVERY`` contractions instead of on every one.  Nothing here
reimplements contraction or bracket abstraction.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Tuple

from aviary_kernel.environment import Environment
from aviary_kernel.reduce import (ReduceResult, Status, _decompose, _Frame,
                                  _try_contract)
from aviary_kernel.terms import Atom, App, apply as _apply, pretty

from .expand import Expansion
from . import avon as _avon

__all__ = ["fast_reduce", "dag_size", "Prober", "SIZE_CHECK_EVERY",
           "ProbeError"]

SIZE_CHECK_EVERY = 512


from .errors import SkijackError

class ProbeError(SkijackError):
    pass


def dag_size(term):
    """DAG-aware node count: reduction shares subterms, so the stock
    tree-walking size() can explode on reducer output."""
    seen, stack, n = set(), [term], 0
    while stack:
        x = stack.pop()
        if id(x) in seen:
            continue
        seen.add(id(x))
        n += 1
        if isinstance(x, App):
            stack.append(x.fn)
            stack.append(x.arg)
    return n


def fast_reduce(term, env, *, whnf_only=True, max_steps=10 ** 6,
                max_size=10 ** 9) -> ReduceResult:
    """``aviary_kernel.reduce.reduce`` with the size check sampled.

    ``max_size=None`` turns the guard off entirely.  Measuring rebuilds
    the whole term, which is O(nodes) per sample; at tower scale that
    costs more than the reduction it protects, and ``max_steps`` already
    bounds the run.

    With ``SKIJACK_REDUCER=avon`` the run goes to Avon instead, in copy
    mode or, with ``SKIJACK_AVON_STRATEGY=share``, share mode; with
    ``check`` to both, compared (:mod:`skijack.avon`).
    """
    mode, avon = _avon.reducer()
    if avon is not None:
        r = avon.reduce(term, env, whnf_only=whnf_only, max_steps=max_steps,
                        max_size=max_size)
        if r is not None:
            if mode == "check":
                ref = _aviary_reduce(term, env, whnf_only=whnf_only,
                                     max_steps=max_steps, max_size=max_size)
                if (ref.status is not r.status or ref.steps != r.steps
                        or not _avon.same_term(ref.term, r.term)):
                    raise _avon.AvonMismatch(
                        f"aviary {ref.status.name} {ref.steps}, avon "
                        f"{r.status.name} {r.steps}"
                        f"{'' if _avon.same_term(ref.term, r.term) else ', terms differ'}")
            return r
    return _aviary_reduce(term, env, whnf_only=whnf_only, max_steps=max_steps,
                          max_size=max_size)


def _aviary_reduce(term, env, *, whnf_only, max_steps, max_size) -> ReduceResult:
    """The reduction in Python: aviary's algorithm, the size guard sampled."""
    steps = 0
    stack: List[_Frame] = []

    def full_term(head, args):
        result = _apply(head, *args)
        for fr in reversed(stack):
            remaining = fr.todo[len(fr.done) + 1:]
            result = _apply(fr.head, *(fr.done + [result] + remaining))
        return result

    head, args = _decompose(term)
    while True:
        while True:
            if steps >= max_steps:
                return ReduceResult(full_term(head, args), steps, Status.FUEL, [])
            contraction = _try_contract(head, args, env)
            if contraction is None:
                break
            head, args, _ = contraction
            steps += 1
            if max_size is not None and steps % SIZE_CHECK_EVERY == 0:
                if dag_size(full_term(head, args)) > max_size:
                    return ReduceResult(full_term(head, args), steps,
                                        Status.SIZE, [])
        if whnf_only and not stack:
            return ReduceResult(_apply(head, *args), steps, Status.WHNF, [])
        if args:
            stack.append(_Frame(head=head, done=[], todo=list(args)))
            head, args = _decompose(args[0])
            continue
        result = head
        while stack:
            fr = stack[-1]
            fr.done.append(result)
            remaining = fr.todo[len(fr.done):]
            if remaining:
                head, args = _decompose(remaining[0])
                break
            built = _apply(fr.head, *fr.done)
            stack.pop()
            result = built
        else:
            return ReduceResult(result, steps, Status.NORMAL, [])


#: marker atoms for the Scott-numeral reader
ZERO_MARK = "Z"
SUCC_MARK = "S_"


class Prober:
    """Behavioral decoding over one :class:`~skijack.expand.Expansion`.

    Terms handed here are already closed ``{S,K,I}``; reduction runs in a
    fresh environment with no definitions, so the only atoms that can
    appear in a result are ``S``, ``K``, ``I`` and the markers.
    """

    def __init__(self, exp: Expansion,
                 zero: str = "Zero", suc: str = "Suc"):
        self.exp = exp
        self.env = Environment()
        self._zero_name = zero
        self._suc_name = suc
        #: id(node) -> (the node itself, its value).  The node is kept in
        #: the value on purpose: CPython recycles ids as soon as an object
        #: is collected, so a cache that held only the id would hand back
        #: another term's answer.  Holding the node pins the id, and the
        #: identity check below is belt and braces.
        self._nat_cache: Dict[int, Tuple[object, int]] = {}

    # --- markers ---------------------------------------------------------

    @staticmethod
    def markers(n: int) -> Sequence[Atom]:
        """``X1 .. Xn``, fresh uninterpreted constants."""
        return [Atom(f"X{i}") for i in range(1, n + 1)]

    def apply_markers(self, term, n: int, *, max_steps: int = 100_000) -> str:
        """Apply ``term`` to ``X1..Xn``, reduce to normal form, and return
        the pretty form of the result -- which is read only to see *which
        marker* came back."""
        return self.reduce_text(term, *self.markers(n), max_steps=max_steps)

    def reduce_text(self, term, *args, max_steps: int = 100_000,
                    whnf_only: bool = False) -> str:
        r = self.reduce(term, *args, max_steps=max_steps, whnf_only=whnf_only)
        return pretty(r.term)

    def reduce(self, term, *args, max_steps: int = 100_000,
               whnf_only: bool = False) -> ReduceResult:
        t = term
        for x in args:
            t = App(t, x)
        r = fast_reduce(t, self.env, whnf_only=whnf_only, max_steps=max_steps)
        if r.status is Status.FUEL:
            raise ProbeError(f"ran out of host fuel after {r.steps} contractions")
        if r.status is Status.SIZE:
            raise ProbeError(f"term grew past the size guard after {r.steps}")
        return r

    # --- Scott numerals --------------------------------------------------

    def nat(self, k: int):
        """The program's own Scott numeral for ``k``, built from its
        ``Zero`` and ``Suc``."""
        t = self.exp.terms[self._zero_name]
        suc = self.exp.terms[self._suc_name]
        for _ in range(k):
            t = App(suc, t)
        return t

    def read_nat(self, term, *, max_steps: int = 200_000,
                 max_depth: int = 1000) -> int:
        """Read a Scott numeral behaviorally.

        ``zero z s = z`` and ``suc n z s = s n``, so applying the numeral
        to the markers ``Z`` and ``S_`` either returns ``Z`` or returns
        ``S_`` applied to the predecessor.  Walking that chain is the
        whole reader; results are memoized by node identity, which is
        where the sharing the reducer creates pays off.
        """
        n = 0
        cur = term
        seen: List[object] = []
        for _ in range(max_depth):
            key = id(cur)
            hit = self._nat_cache.get(key)
            if hit is not None and hit[0] is cur:
                for i, node in enumerate(seen):
                    self._nat_cache[id(node)] = (node, hit[1] + len(seen) - i)
                return n + hit[1]
            seen.append(cur)
            r = self.reduce(cur, Atom(ZERO_MARK), Atom(SUCC_MARK),
                            max_steps=max_steps, whnf_only=True)
            x = r.term
            if isinstance(x, Atom) and x.name == ZERO_MARK:
                for i, node in enumerate(seen):
                    self._nat_cache[id(node)] = (node, len(seen) - 1 - i)
                return n
            if (isinstance(x, App) and isinstance(x.fn, Atom)
                    and x.fn.name == SUCC_MARK):
                n += 1
                cur = x.arg
                continue
            raise ProbeError(
                f"not a Scott numeral: applying it to the markers gave "
                f"{pretty(x)[:80]}")
        raise ProbeError(f"numeral deeper than {max_depth}")

    def pair(self, *items):
        """Build the program's cell ``[a b ...]`` from host terms."""
        p = self.exp.terms["pair"]
        out = items[-1]
        for x in reversed(items[:-1]):
            out = App(App(p, x), out)
        return out
