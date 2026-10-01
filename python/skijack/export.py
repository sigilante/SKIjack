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

It writes ``interpreters.tsv`` for Avon's interpreter jet (``avon/DESIGN.md``
§7): one line per generated interpreter core whose arms it can classify,
``hash  name  params  object  result  answer``.  The hash is the core's
loop term's.  ``object`` lists the object type's constructors in
declaration order as ``role/hash`` -- ``S``, ``K``, ``I``, ``App``, or for
another leaf what its step arm does: ``errN`` (an outcome that maps to
result constructor ``N``), ``diverge``, or ``scry``.  ``result`` lists the
result type's constructors as ``role/hash``, ``value``, ``timeout`` or
``other``.  ``answer`` lists the resolver's answer constructors' roles for
a ``scry`` leaf -- ``hit``, ``missN``, ``notyetN`` -- or is ``-``.  Lines
``nat  ZERO  SUC`` name the Scott numerals the corpus's level-1 programs
use for fuel, by their constructors' hashes, so Avon can read a fuel
numeral built from them without probing.  Every arm
is classified by running it on marker atoms, never by its name: a core
with an arm that fits none of these shapes, or with a user-written walker,
step, loop or S/K/I arm, is left out and runs unjetted.

It writes ``namespaces.tsv`` for Avon's scry stage (``avon/DESIGN.md`` §8):
one line per resume-loop run that ``tests/test_scry.py`` pins, ``id  interp
params  datum  fuel  max_rounds  eq  hit  notyet  zero  suc  result_ctors
object_ctors  resolution  events  attempts``.  The terms are SKIT files
(``params`` a comma list, the resolver's slot excluded; ``-`` for none);
``fuel`` is a number or ``policy:START:CAP``; ``resolution`` is a file of
``rendered path <TAB> answer file`` lines, or ``-``; ``events`` is
``run_with_namespace``'s trace joined by ``|``; ``attempts`` lists every
level-1 run it made, in order, as ``fuel:STATUS:steps``.

It also writes the corpus's dictionary (``skijack.dictionary``), the table
Avon's jets key on (``avon/DESIGN.md`` §5, §6): ``dictionary.tsv``, one
line per distinct term, ``hash  atoms  printed-term``, and
``dictionary_names.tsv``, one line per name, ``program  name  hash``.
And the corpus's supercombinator templates (``skijack.templates``):
``templates.tsv``, each rule's formals and open body keyed by its term's
hash, and ``template_terms.tsv``, the closed terms the bodies reference,
in ``dictionary.tsv``'s format.  Both are hints beside the terms, which
they leave unchanged.

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
from . import ast as A
from .dictionary import from_expansion, structural_hash
from .generate import (find_answer_type, find_loop_types, find_object_type,
                       generated_names, is_interpreter_core,
                       names_generation_adds)
from .probe import fast_reduce
from .run import decode, peel, run_level1, run_policy

__all__ = ["jam", "targets", "dictionary", "interpreters", "namespaces",
           "export"]

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


def dictionary():
    """(distinct rows: hash -> (atoms, printed term), names: [(program,
    name, hash)]) over every compilable corpus program."""
    rows, names = {}, []
    stems = sorted({p.name.split(".")[0] for p in corpus.DIR.glob("*.ascii.ski")})
    for stem in stems:
        try:
            exp = expand_program(parse(corpus.read(stem, "ascii"), "ascii"))
        except Exception:                       # Stage A refusals
            continue
        d = from_expansion(exp)
        for name in d.names():
            e = d[name]
            rows.setdefault(e.hash, (e.size, pretty(e.term)))
            names.append((stem, name, e.hash))
    return rows, names


def corpus_templates():
    """Every compilable corpus program's templates (skijack.templates), the
    first of each key kept, in corpus order."""
    from .templates import templates
    out, seen = [], set()
    stems = sorted({p.name.split(".")[0] for p in corpus.DIR.glob("*.ascii.ski")})
    for stem in stems:
        try:
            exp = expand_program(parse(corpus.read(stem, "ascii"), "ascii"))
        except Exception:                       # Stage A refusals
            continue
        for t in templates(exp):
            if t.key_hash not in seen:
                seen.add(t.key_hash)
                out.append(t)
    return out


def _whnf(term, steps=20000):
    from aviary_kernel.environment import Environment
    return fast_reduce(term, Environment(), whnf_only=True, max_steps=steps)


def _ap(*ts):
    t = ts[0]
    for x in ts[1:]:
        t = App(t, x)
    return t


def _spine(t):
    args = []
    while isinstance(t, App):
        args.append(t.arg)
        t = t.fn
    return t, args[::-1]


def _outcome(t, lt):
    """Peel t as the outcome type: (ctor, fields), or None."""
    try:
        return peel(t, lt.outcome, max_steps=20000)
    except Exception:
        return None


def _is_atom(t, name):
    r = _whnf(t)
    return r.status.name == "WHNF" and isinstance(r.term, Atom) and r.term.name == name


def _classify_leaf(exp, core, leaf, lt, ans, obj):
    """What the core's step arm for `leaf` does, by running it: `errN`,
    `diverge`, or `scry` with the answer roles; None if none of these."""
    arm = exp.terms.get(f"{core.name}.step{leaf.name}")
    if arm is None:
        return None, None
    params = [Atom(f"\x00P{i}") for i in range(len(core.params))]
    rd = list(lt.result.ctors)
    # an arm that ignores its arguments: an outcome, or divergence
    r = _whnf(_ap(arm, *params, Atom("\x00ACC")))
    if r.status.name == "FUEL":
        return "diverge", None
    got = _outcome(r.term, lt) if r.status.name == "WHNF" else None
    if got is not None:
        c, fields = got
        if c not in (lt.stepped.name, lt.done.name) and not fields:
            return f"err{[x.name for x in rd].index(lt.r_of(c))}", None
        return None, None
    # the scry arm: no argument is done; one asks the resolver
    if ans is None or not params:
        return None, None
    nil, cons = exp.terms["nil"], exp.terms["cons"]
    got = _outcome(_ap(arm, *params, nil), lt)
    if got is None or got[0] != lt.done.name:
        return None, None
    P, R = Atom("\x00PATH"), Atom("\x00REST")
    r = _whnf(_ap(arm, *params, _ap(cons, P, R)))
    if r.status.name != "WHNF":
        return None, None
    head, args = _spine(r.term)
    if head != params[0] or len(args) != 1 + len(ans.decl.ctors) \
            or not _is_atom(args[0], P.name):
        return None, None
    roles = []
    for c, k in zip(ans.decl.ctors, args[1:]):
        if c.fields:                        # the hit: the answer spliced in
            V, A_ = Atom("\x00V"), Atom("\x00A")
            ok = False
            for rest, want in ((nil, None), (_ap(cons, A_, nil), A_)):
                arm2 = _ap(arm, *params, _ap(cons, P, rest))
                h2, a2 = _spine(_whnf(arm2).term)
                o = _outcome(_ap(a2[1 + list(ans.decl.ctors).index(c)], V), lt)
                if o is None or o[0] != lt.stepped.name:
                    break
                if want is None:
                    ok = _is_atom(o[1][0], V.name)
                else:
                    try:
                        ctor, fs = peel(o[1][0], obj.decl, max_steps=20000)
                    except Exception:
                        break
                    ok = ok and ctor == obj.app.name and _is_atom(fs[0], V.name) \
                        and _is_atom(fs[1], A_.name)
            if not ok:
                return None, None
            roles.append("hit")
        else:
            o = _outcome(k, lt)
            if o is None:
                return None, None
            idx = [x.name for x in rd].index(lt.r_of(o[0])) \
                if o[0] != lt.done.name else None
            if idx is None:
                return None, None
            if o[1]:                        # the path that blocked
                if not _is_atom(o[1][0], P.name):
                    return None, None
                roles.append(f"notyet{idx}")
            else:
                roles.append(f"miss{idx}")
    if roles.count("hit") != 1:
        return None, None
    return "scry", roles


def interpreters():
    """One line per classifiable generated interpreter core, deduplicated
    by the loop term's hash."""
    out = {}
    stems = sorted({p.name.split(".")[0] for p in corpus.DIR.glob("*.ascii.ski")})
    for stem in stems:
        prog = parse(corpus.read(stem, "ascii"), "ascii")
        try:
            exp = expand_program(prog)
        except Exception:
            continue
        obj = find_object_type(prog)
        if obj is None:
            continue
        lt = find_loop_types(prog, obj)
        try:
            ans = find_answer_type(prog, obj, lt)
        except Exception:
            ans = None
        top, per_core = names_generation_adds(prog)
        if not set(generated_names(obj)) <= top:
            continue                        # a user-written walker or arm
        for d in prog.decls:
            if not (isinstance(d, A.Core) and is_interpreter_core(d, obj)):
                continue
            if not {"loop", "loop1"} <= per_core.get(d.name, set()):
                continue                    # a user-written loop
            if {e.name for e in d.equations} & {"stepS", "stepK", "stepI"}:
                continue
            h = structural_hash(exp.terms[d.name])
            if "step" not in per_core[d.name]:
                # a user-written step counts only if it is the generated
                # one: with the generator's in its place, the loop must
                # compile to the same term
                from .generate import _core_step_equation
                rest = tuple(e for e in d.equations if e.name != "step")
                gen = _core_step_equation(obj, A.Core(d.name, rest, d.params))
                bare = A.Core(d.name, rest + (gen,), d.params)
                prog2 = A.Program(tuple(bare if x is d else x for x in prog.decls))
                try:
                    if structural_hash(expand_program(prog2).terms[d.name]) != h:
                        continue
                except Exception:
                    continue
            if h in out:
                continue
            objs, answer, ok = [], "-", True
            for c in obj.decl.ctors:
                ch = structural_hash(exp.terms[c.name])
                if c.name == obj.app.name:
                    objs.append(f"App/{ch}")
                elif c.name in ("S", "K", "I"):
                    objs.append(f"{c.name}/{ch}")
                else:
                    role, roles = _classify_leaf(exp, d, c, lt, ans, obj)
                    if role is None:
                        ok = False
                        break
                    objs.append(f"{role}/{ch}")
                    if roles:
                        answer = " ".join(roles)
            if not ok:
                continue
            res = []
            for c in lt.result.ctors:
                role = ("value" if c.name == lt.value.name else
                        "timeout" if c.name == lt.timeout.name else "other")
                res.append(f"{role}/{structural_hash(exp.terms[c.name])}")
            out[h] = "\t".join([h, f"{stem}.{d.name}", str(len(d.params)),
                                " ".join(objs), " ".join(res), answer])
    nats = set()
    for stem in stems:
        try:
            exp = expand_program(parse(corpus.read(stem, "ascii"), "ascii"))
        except Exception:
            continue
        for prog in exp.level1.values():
            nats.add((structural_hash(prog.zero), structural_hash(prog.suc)))
    return [out[h] for h in sorted(out)] + [f"nat\t{z}\t{s}" for z, s in sorted(nats)]


#: the resume-loop runs tests/test_scry.py pins: (id, program, resolution
#: as {rendered path: answer name}, fuel or None, max_rounds, start, cap)
NAMESPACE_RUNS = [
    ("no-scry", "pIK", {}, 10, 10, 8, 4096),
    ("one-block", "pIScryK", {"K": "ansI"}, 10, 10, 8, 4096),
    ("chain", "pScryS", {"S": "ansScryK", "K": "ansI"}, 10, 10, 8, 4096),
    ("stuck", "pIScryK", {}, 10, 10, 8, 4096),
    ("timeout", "pOmega", {}, 5, 10, 8, 4096),
    ("compound", "pScrySK", {"S K": "ansI"}, 10, 10, 8, 4096),
    ("prefix-long", "pScrySKK", {"S K": "ansI", "S K K": "ansK"}, 10, 10, 8, 4096),
    ("prefix-short", "pScrySK", {"S K": "ansI", "S K K": "ansK"}, 10, 10, 8, 4096),
    ("wrong-fact", "pScrySK", {"K S": "ansI"}, 10, 10, 8, 4096),
    ("policy", "pPolicy", {"K": "ansI"}, None, 10, 8, 4096),
    ("policy-cap", "pOmega", {}, None, 10, 2, 8),
    ("one-round-max", "pScryS", {"S": "ansScryK", "K": "ansI"}, 10, 1, 8, 4096),
]


def namespaces(outdir: pathlib.Path) -> List[str]:
    """Run each pinned resume loop, recording every level-1 attempt, and
    write its terms; the lines of ``namespaces.tsv``."""
    from . import run as R
    exp = expand_program(parse(corpus.read("scry-block", "ascii"), "ascii"))
    at = exp.answer_type
    assert at is not None               # scry-block declares its answer type
    shared = {"eq": exp.terms["EQ5"], "hit": exp.terms[at.hit.name],
              "notyet": exp.terms[at.notyet.name]}
    for key, term in shared.items():
        (outdir / f"ns.{key}.skit").write_bytes(jam(term))
    lines = []
    for ident, pname, res_names, fuel, rounds, start, cap in NAMESPACE_RUNS:
        prog = exp.level1[pname]
        parts = {"interp": prog.interp_term, "datum": prog.datum,
                 "zero": prog.zero, "suc": prog.suc}
        for key, term in parts.items():
            (outdir / f"ns.{pname}.{key}.skit").write_bytes(jam(term))
        pfiles = []
        for i, p in enumerate(prog.params[1:], 1):
            (outdir / f"ns.{pname}.param{i}.skit").write_bytes(jam(p))
            pfiles.append(f"ns.{pname}.param{i}.skit")
        resolution = {k: exp.terms[v] for k, v in res_names.items()}
        rfile = "-"
        if res_names:
            rfile = f"ns.{ident}.resolution.tsv"
            rows = []
            for k, v in res_names.items():
                (outdir / f"ns.{v}.skit").write_bytes(jam(exp.terms[v]))
                rows.append(f"{k}\tns.{v}.skit\n")
            (outdir / rfile).write_text("".join(rows))
        attempts = []
        real = R.run_level1

        def recording(packaged, max_steps=1_000_000, *, fuel=None, env=None):
            out = real(packaged, max_steps, fuel=fuel, env=env)
            attempts.append(f"{fuel}:{out.status.name}:{out.steps}")
            return out
        R.run_level1 = recording
        try:
            r = R.run_with_namespace(exp, prog, resolution, fuel, rounds,
                                     max_steps=CAP, start=start, cap=cap)
        finally:
            R.run_level1 = real
        lines.append("\t".join([
            f"scry-block.{ident}", f"ns.{pname}.interp.skit",
            ",".join(pfiles) or "-", f"ns.{pname}.datum.skit",
            str(fuel) if fuel is not None else f"policy:{start}:{cap}",
            str(rounds), "ns.eq.skit", "ns.hit.skit", "ns.notyet.skit",
            f"ns.{pname}.zero.skit", f"ns.{pname}.suc.skit",
            _ctors(prog.result_type),
            _ctors(prog.object_type.decl, prog.object_type.app),
            rfile, "|".join(r.events), ",".join(attempts)]))
    return lines


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
    (outdir / "namespaces.tsv").write_text(
        "".join(line + "\n" for line in namespaces(outdir)))
    (outdir / "interpreters.tsv").write_text(
        "".join(line + "\n" for line in interpreters()))
    rows, names = dictionary()
    (outdir / "dictionary.tsv").write_text("".join(
        f"{h}\t{size}\t{text}\n" for h, (size, text) in sorted(rows.items())))
    (outdir / "dictionary_names.tsv").write_text("".join(
        f"{stem}\t{name}\t{h}\n" for stem, name, h in names))
    from .templates import write as write_templates
    write_templates(corpus_templates(), outdir / "templates.tsv",
                    outdir / "template_terms.tsv")
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
