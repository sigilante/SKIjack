"""Avon as skijack's reducer.

:func:`skijack.probe.fast_reduce` is the one place skijack reduces a term,
and by default it runs ``aviary_kernel.reduce``'s algorithm in Python.
Set ``SKIJACK_REDUCER=avon`` and ``AVON`` to an ``avon`` binary, and the
same runs go to Avon instead (https://github.com/sigilante/avon), in its
copy mode: the reference host's algorithm in C, whose contraction counts,
statuses and terms are aviary's.  ``SKIJACK_REDUCER=check`` runs every
reduction both ways and raises :class:`AvonMismatch` on any difference.

``SKIJACK_AVON_STRATEGY=share`` runs Avon in its share mode instead:
graph reduction, each argument reduced once however often it is used,
so a program that uses a value twice computes it once.  A normal form is
the same term, but a weak head normal form may hold arguments already
reduced, and the contraction counts and the fuel's stopping point are
Avon's own, not aviary's; ``check`` compares counts, so it takes copy
mode alone.

Avon reduces S, K and I and nothing else, so a term goes to Avon only
when each of its leaves means there what it means in the environment
given: S, K and I as the default environment defines them, and every
other name an inert atom.  Any other term (one with a live aviary bird
in it, say) is reduced by aviary as before.

Each reduction is one line to a long-running ``avon batch`` in the DAG
form, sharing kept both ways, and one line back.  Atom names travel under
aliases, ``v0``, ``v1``, ..., since skijack's marker names hold characters
Avon does not take in a name, and come back as the caller's own atoms.

Avon's size guard counts the live nodes of its arena, where aviary's
samples the result's DAG every 512 steps; ``max_size`` is passed through
as Avon's ``--max-nodes`` and the two can stop a growing run at
different steps.  No reduction skijack makes comes near either bound.
"""

from __future__ import annotations

import os
import subprocess
import tempfile
from typing import IO, Dict, List, Optional, Tuple

from aviary_kernel.environment import Environment
from aviary_kernel.reduce import ReduceResult, Status
from aviary_kernel.terms import App, Atom

from .errors import SkijackError

__all__ = ["AvonError", "AvonMismatch", "AvonReducer", "reducer",
           "same_term"]

#: the most nodes Avon's arena addresses (its ``AV_MAX_NODES``)
_MAX_NODES = 1 << 30

#: the most batch processes kept open at once, one per mode and bound
_POOL = 8

#: Avon's strategies: ``copy``, aviary's algorithm, and ``share``
STRATEGIES = ("copy", "share")

_PRIMITIVES = ("S", "K", "I")
_DEFAULT = Environment()


class AvonError(SkijackError):
    """Avon could not run a term it was given, or its answer did not read."""


class AvonMismatch(SkijackError):
    """Under ``SKIJACK_REDUCER=check``, Avon and aviary disagreed."""


def _encode(term) -> Tuple[str, Dict[str, Atom]]:
    """``term`` in the DAG form, sharing kept, its atoms aliased; the
    aliases, mapped back to the caller's atoms.  Built without recursion:
    a compiled program is hundreds of thousands of nodes deep."""
    ids: Dict[int, int] = {}
    alias: Dict[str, str] = {}
    back: Dict[str, Atom] = {}
    parts: List[str] = ["dag"]
    stack = [(term, False)]
    keep = []                       # pins every node, so no id() is reused
    while stack:
        node, done = stack.pop()
        if id(node) in ids:
            continue
        if isinstance(node, App):
            if not done:
                stack.append((node, True))
                stack.append((node.arg, False))
                stack.append((node.fn, False))
                continue
            rhs = f"{ids[id(node.fn)]}.{ids[id(node.arg)]}"
        else:
            name = node.name
            if name in _PRIMITIVES:
                rhs = name
            elif name in alias:
                rhs = alias[name]
            else:
                rhs = alias[name] = f"v{len(alias)}"
                back[rhs] = node
        n = len(ids)
        ids[id(node)] = n
        keep.append(node)
        parts.append(f"{n}={rhs}")
    parts.append(f"@{ids[id(term)]}")
    return " ".join(parts), back


def _leaves_avon_can_run(term, env) -> bool:
    """Whether every leaf of ``term`` means in ``env`` what it means in
    Avon: S, K and I as the default environment has them, any other name
    inert."""
    seen = set()
    stack = [term]
    names = set()
    while stack:
        x = stack.pop()
        if id(x) in seen:
            continue
        seen.add(id(x))
        if isinstance(x, App):
            stack.append(x.fn)
            stack.append(x.arg)
        else:
            names.add(x.name)
    for name in names:
        comb = env.lookup(name)
        if name in _PRIMITIVES:
            if comb is None or comb != _DEFAULT.lookup(name):
                return False
        elif comb is not None:
            return False
    return True


def _decode(text: str, back: Dict[str, Atom]):
    """The DAG form Avon printed, as aviary terms sharing as Avon's do."""
    toks = text.split()
    if not toks or toks[0] != "dag" or not toks[-1].startswith("@"):
        raise AvonError(f"not a DAG term: {text[:200]!r}")
    nodes: Dict[str, object] = {}
    prim = {name: Atom(name) for name in _PRIMITIVES}
    for tok in toks[1:-1]:
        i, _, rhs = tok.partition("=")
        if rhs[:1].isdigit():
            l, _, r = rhs.partition(".")
            nodes[i] = App(nodes[l], nodes[r])
        elif rhs in prim:
            nodes[i] = prim[rhs]
        elif rhs in back:
            nodes[i] = back[rhs]
        else:
            raise AvonError(f"Avon answered with a leaf it was not given: {rhs!r}")
    return nodes[toks[-1][1:]]


class AvonReducer:
    """Reductions run by an ``avon`` binary, in copy mode or share mode."""

    def __init__(self, avon: str, strategy: str = "copy"):
        if strategy not in STRATEGIES:
            raise AvonError(f"strategy {strategy!r}: copy or share")
        self.avon = avon
        self.strategy = strategy
        self._procs: Dict[Tuple[bool, Optional[int], Optional[int]],
                          Tuple["subprocess.Popen[str]", IO[str]]] = {}
        self.runs = 0

    def close(self) -> None:
        for proc, err in self._procs.values():
            try:
                if proc.stdin is not None:
                    proc.stdin.close()
                proc.wait(timeout=10)
            except Exception:
                proc.kill()
            err.close()
        self._procs.clear()

    def __del__(self):  # pragma: no cover - interpreter shutdown
        try:
            self.close()
        except Exception:
            pass

    def _proc(self, whnf_only: bool, max_steps: Optional[int],
              max_size: Optional[int]) -> Tuple["subprocess.Popen[str]", IO[str]]:
        key = (whnf_only, max_steps, max_size)
        hit = self._procs.get(key)
        if hit is not None and hit[0].poll() is None:
            return hit
        if hit is not None:
            hit[1].close()
            del self._procs[key]
        if len(self._procs) >= _POOL:                 # drop the oldest
            old = next(iter(self._procs))
            proc, err = self._procs.pop(old)
            if proc.stdin is not None:
                proc.stdin.close()
            proc.wait()
            err.close()
        args = [self.avon, "batch", f"--strategy={self.strategy}", "--dag",
                f"--budget={_MAX_NODES}"]
        if whnf_only:
            args.append("--whnf")
        if max_steps is not None:
            args.append(f"--fuel={max_steps}")
        if max_size is not None:
            args.append(f"--max-nodes={max(1, min(max_size, _MAX_NODES))}")
        err = tempfile.TemporaryFile(mode="w+")
        try:
            proc = subprocess.Popen(args, stdin=subprocess.PIPE,
                                    stdout=subprocess.PIPE, stderr=err,
                                    text=True, bufsize=1)
        except OSError as ex:
            err.close()
            raise AvonError(f"cannot run {self.avon}: {ex}") from ex
        self._procs[key] = (proc, err)
        return proc, err

    def reduce(self, term, env, *, whnf_only: bool = True,
               max_steps: Optional[int] = 10 ** 6,
               max_size: Optional[int] = 10 ** 9) -> Optional[ReduceResult]:
        """``fast_reduce``'s result, from Avon; None when the term holds a
        leaf Avon would not read as ``env`` does."""
        if not _leaves_avon_can_run(term, env):
            return None
        line, back = _encode(term)
        proc, err = self._proc(whnf_only, max_steps, max_size)
        assert proc.stdin is not None and proc.stdout is not None
        try:
            proc.stdin.write(line + "\n")
            proc.stdin.flush()
            answer = proc.stdout.readline()
        except (BrokenPipeError, OSError) as ex:
            raise AvonError(f"avon batch died: {ex}; {self._stderr(err)}") from ex
        self.runs += 1
        if not answer:
            raise AvonError(f"avon batch ended without an answer; {self._stderr(err)}")
        answer = answer.rstrip("\n")
        if answer == "!":
            raise AvonError(f"avon could not run the term: {self._stderr(err)}")
        status, steps, rest = answer.split(" ", 2)
        if rest == "...":
            raise AvonError(f"the result passed {_MAX_NODES} nodes")
        return ReduceResult(_decode(rest, back), int(steps), Status[status], [])

    @staticmethod
    def _stderr(err: IO[str]) -> str:
        err.flush()
        err.seek(0)
        text = err.read().strip()
        if text.startswith("usage:"):
            return ("this avon takes no `batch --dag`; build Avon from "
                    "https://github.com/sigilante/avon at master")
        lines = text.splitlines()
        return lines[-1].strip() if lines else "(nothing on stderr)"


def same_term(x, y) -> bool:
    """Whether two aviary terms are the same tree, without recursion, each
    shared pair compared once."""
    seen = set()
    stack = [(x, y)]
    while stack:
        a, b = stack.pop()
        if a is b or (id(a), id(b)) in seen:
            continue
        seen.add((id(a), id(b)))
        if isinstance(a, App) and isinstance(b, App):
            stack.append((a.fn, b.fn))
            stack.append((a.arg, b.arg))
        elif isinstance(a, Atom) and isinstance(b, Atom):
            if a.name != b.name:
                return False
        else:
            return False
    return True


_reducer: Optional[AvonReducer] = None
_mode: Optional[str] = None


def reducer() -> Tuple[Optional[str], Optional[AvonReducer]]:
    """The mode ``SKIJACK_REDUCER`` names (``aviary``, ``avon`` or
    ``check``) and, unless it is ``aviary``, the Avon reducer ``AVON``
    names, in the strategy ``SKIJACK_AVON_STRATEGY`` names (``copy``, the
    default, or ``share``).  Read once."""
    global _reducer, _mode
    if _mode is None:
        mode = os.environ.get("SKIJACK_REDUCER", "aviary").strip() or "aviary"
        if mode not in ("aviary", "avon", "check"):
            raise AvonError(f"SKIJACK_REDUCER={mode!r}: aviary, avon or check")
        if mode != "aviary":
            avon = os.environ.get("AVON")
            if not avon:
                raise AvonError(f"SKIJACK_REDUCER={mode} needs AVON, the path of an avon binary")
            strategy = os.environ.get("SKIJACK_AVON_STRATEGY", "copy").strip() or "copy"
            if strategy not in STRATEGIES:
                raise AvonError(f"SKIJACK_AVON_STRATEGY={strategy!r}: copy or share")
            if mode == "check" and strategy != "copy":
                raise AvonError("SKIJACK_REDUCER=check compares aviary's counts, "
                                "so it takes SKIJACK_AVON_STRATEGY=copy")
            _reducer = AvonReducer(avon, strategy)
        _mode = mode
    return _mode, _reducer
