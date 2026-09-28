"""Export the conformance corpus for Avon (``avon/DESIGN.md`` §10.1).

    python3 -m skijack.export OUTDIR

Writes one SKIT container per target and ``OUTDIR/manifest.tsv``, one line
per target.  A target is a closed level-1 executable -- ``interp fuel
<datum>`` with the interpreter's parameters applied -- together with what
the reference host does with it: the status and contraction count of
reducing it to weak head normal form under a host cap, and, when it gets
there, the result constructor it peels to and the rendered payload it
decodes to.  The targets are

- every level-1 declaration the compilable corpus makes, a policy
  declaration at the budget ``run_policy`` settles on;
- ``EXAMPLES.md`` §4's fuel boundary: ``wf5Abs |- <K I Err>`` at fuel 0, 1,
  2 and 5;
- the paper's T3 table: five objects under ``wf5Abs`` and ``wf5Omg`` at
  fuel 20 and host cap 400,000, where ``CAP`` is a FUEL status.

Nothing here changes how anything else in the package behaves.

The manifest's columns, tab-separated:

    id  file  max_steps  status  copy_steps  result_ctors  object_ctors
    ctor  payload

``result_ctors`` is the result type's constructors in declaration order as
``Name/arity``; ``object_ctors`` the object type's, with ``*`` before the
application constructor.  ``ctor`` and ``payload`` are ``-`` when absent.
The container format is Avon's (``include/avon.h``): ``SKIT``, version 1,
an empty atom table, and the bitstring ``00`` S, ``01`` K, ``10`` I,
``11`` application.
"""

from __future__ import annotations

import pathlib
import sys
from typing import List, Tuple

from aviary_kernel.terms import App, Atom, pretty

from . import corpus
from .expand import expand_program
from .parser import parse
from .render import render_ascii
from .run import decode, peel, run_level1, run_policy

__all__ = ["jam", "targets", "export"]

CAP = 5_000_000
T3_CAP = 400_000

T3_OBJECTS = [("err", "Err"), ("err_k", "Err K"), ("k_i_err", "K I Err"),
              ("i_k", "I K"), ("omega", "S I I (S I I)")]


def jam(term) -> bytes:
    """Avon's SKIT container for a closed {S,K,I} term."""
    bits: List[int] = []
    stack = [term]
    while stack:
        t = stack.pop()
        if isinstance(t, App):
            bits += (1, 1)
            stack.append(t.arg)
            stack.append(t.fn)
        elif isinstance(t, Atom) and t.name in ("S", "K", "I"):
            bits += {"S": (0, 0), "K": (0, 1), "I": (1, 0)}[t.name]
        else:
            raise ValueError(f"not a closed {{S,K,I}} term: {pretty(t)[:40]}")
    body = bytearray((len(bits) + 7) // 8)
    for i, b in enumerate(bits):
        body[i // 8] |= b << (i % 8)
    return (b"SKIT\x01\x00\x00\x00" + (0).to_bytes(4, "little")
            + len(bits).to_bytes(8, "little") + bytes(body))


def _ctors(decl, app=None) -> str:
    out = []
    for c in decl.ctors:
        mark = "*" if app is not None and c.name == app.name else ""
        out.append(f"{mark}{c.name}/{len(c.fields)}")
    return " ".join(out)


def _row(ident, term, prog, max_steps):
    """Run one executable the way the tests read it: level 1, then peel,
    then decode."""
    out = run_level1(term, max_steps)
    ctor = payload = "-"
    if out.whnf:
        ctor, fields = peel(out.term, prog.result_type, max_steps=max_steps)
        if fields:
            payload = render_ascii(decode(fields[0], prog.object_type,
                                          max_steps=max_steps))
    return (ident, term, max_steps, out.status.name, out.steps,
            _ctors(prog.result_type),
            _ctors(prog.object_type.decl, prog.object_type.app),
            ctor, payload)


def targets() -> List[Tuple]:
    rows = []
    stems = sorted({p.name.split(".")[0] for p in corpus.DIR.glob("*.ascii.ski")})
    for stem in stems:
        try:
            exp = expand_program(parse(corpus.read(stem, "ascii"), "ascii"))
        except Exception:                       # Stage A refusals: not targets
            continue
        for name, prog in sorted(exp.level1.items()):
            if prog.fuel == "policy" or not isinstance(prog.fuel, int):
                pol = run_policy(prog, max_steps=CAP)
                budget = pol.budgets[-1]
                rows.append(_row(f"{stem}.{name}.policy{budget}",
                                 prog.with_fuel(budget), prog, CAP))
            else:
                rows.append(_row(f"{stem}.{name}", prog.term, prog, CAP))

    # EXAMPLES.md section 4, and the paper's T3 table, as declarations
    # appended to the interp-t3 source, the way test_level1.py writes them
    src = corpus.read("interp-t3", "ascii") + "answer := wf5Abs |- <K I Err>@5\n"
    for label, obj in T3_OBJECTS:
        for interp in ("wf5Abs", "wf5Omg"):
            src += f"t3_{label}_{interp} := {interp} |- <{obj}>@20\n"
    exp = expand_program(parse(src, "ascii"))
    ans = exp.level1["answer"]
    for fuel in (0, 1, 2, 5):
        rows.append(_row(f"examples4.answer.fuel{fuel}", ans.with_fuel(fuel),
                         ans, CAP))
    for label, _obj in T3_OBJECTS:
        for interp in ("wf5Abs", "wf5Omg"):
            prog = exp.level1[f"t3_{label}_{interp}"]
            rows.append(_row(f"t3.{label}.{interp}", prog.term, prog, T3_CAP))
    return rows


def export(outdir: pathlib.Path) -> int:
    outdir.mkdir(parents=True, exist_ok=True)
    lines = []
    for (ident, term, max_steps, status, steps, rctors, octors, ctor,
         payload) in targets():
        fname = f"{ident}.skit"
        (outdir / fname).write_bytes(jam(term))
        lines.append("\t".join([ident, fname, str(max_steps), status,
                                str(steps), rctors, octors, ctor, payload]))
    (outdir / "manifest.tsv").write_text("\n".join(lines) + "\n")
    return len(lines)


def main(argv=None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 1:
        print("usage: python3 -m skijack.export OUTDIR", file=sys.stderr)
        return 2
    n = export(pathlib.Path(argv[0]))
    print(f"{n} targets written to {argv[0]}")
    return 0


if __name__ == "__main__":
    sys.setrecursionlimit(1_000_000)
    sys.exit(main())
