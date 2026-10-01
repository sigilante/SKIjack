"""``python3 -m skijack`` -- the whole pipeline from the command line.

In the spirit of nockasm's CLI: one file in, and each flag prints one
view of it.  With no flag it prints a summary.
"""

from __future__ import annotations

import argparse
import sys

from aviary_kernel.terms import pretty

from .check import check_program
from .typecheck import typecheck_program
from .errors import SkijackError
from .dictionary import from_expansion, lift, structural_hash
from .expand import PRELUDE_NAMES, expand_program
from .parser import parse
from .render import render
from .run import decode, peel, run_level1, run_policy


def _lexicon_of(path: str, given: str) -> str:
    if given != "auto":
        return given
    return "unicode" if ".unicode." in path else "ascii"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        prog="skijack",
        description="compile, check, render, lift and run a .ski program")
    ap.add_argument("file")
    ap.add_argument("--lexicon", default="auto",
                    choices=["auto", "ascii", "unicode"],
                    help="the source's lexicon (default: from the filename)")
    ap.add_argument("--check", action="store_true",
                    help="run Stage A and report every problem")
    ap.add_argument("--expand", action="store_true",
                    help="print every compiled term with its atom count")
    ap.add_argument("--lift", metavar="NAME",
                    help="lift NAME against the program's dictionary")
    ap.add_argument("--dictionary", action="store_true",
                    help="print the Tier 1 table: name, atoms, hash")
    ap.add_argument("--render", metavar="LEXICON",
                    choices=["ascii", "unicode"],
                    help="re-render the program in LEXICON")
    ap.add_argument("--run", metavar="NAME",
                    help="run NAME (a level-1 declaration) and decode it")
    ap.add_argument("--fuel", type=int, default=None,
                    help="override the fuel of --run")
    ap.add_argument("--inline", action="store_true",
                    help="unfold small functions at their calls (skijack.inline): "
                         "other terms, the same values")
    ap.add_argument("--max-steps", type=int, default=5_000_000,
                    help="host contraction cap (default 5,000,000)")
    args = ap.parse_args(argv)
    try:
        return _run(args)
    except (SkijackError, OSError, UnicodeDecodeError, RecursionError) as ex:
        print(f"{args.file}: {_message(ex)}", file=sys.stderr)
        return 1


def _message(ex: BaseException) -> str:
    """A line a user can act on, for the four families that reach here."""
    if isinstance(ex, RecursionError):
        return ("expression nests too deeply for this compiler; see the "
                "depth limit in skijack.expand")
    if isinstance(ex, UnicodeDecodeError):
        return "not valid UTF-8"
    if isinstance(ex, OSError):
        return ex.strerror or str(ex)
    return str(ex)


def _run(args) -> int:
    lx = _lexicon_of(args.file, args.lexicon)
    with open(args.file, encoding="utf-8") as fh:
        text = fh.read()
    program = parse(text, lx)

    if args.render:
        print(render(program, args.render), end="")
        return 0

    problems = check_program(program, PRELUDE_NAMES)
    if args.check:
        if problems:
            for p in problems:
                print(f"{args.file}: {p}", file=sys.stderr)
            return 1
        print(f"{args.file}: Stage A clean")
        problems = typecheck_program(program, PRELUDE_NAMES)
        if problems:
            for p in problems:
                print(f"{args.file}: {p}", file=sys.stderr)
            return 1
        print(f"{args.file}: Stage B clean")
        return 0
    if problems:
        for p in problems:
            print(f"{args.file}: {p}", file=sys.stderr)
        return 1

    exp = expand_program(program, inline=args.inline)

    if args.expand:
        for name in sorted(exp.terms):
            print(f"{exp.sizes[name]:8d}  {name:24s} {pretty(exp.terms[name])}")
        return 0

    if args.dictionary:
        d = from_expansion(exp)
        print(f"# {d.version}: {len(d)} entries")
        for name, atoms, h in d.rows():
            print(f"{atoms:8d}  {name:24s} {h}")
        return 0

    if args.lift:
        if args.lift not in exp.terms:
            print(f"{args.file}: no term named {args.lift!r}", file=sys.stderr)
            return 1
        d = from_expansion(exp)
        target = exp.terms[args.lift]
        whole = [n for n in d.names()
                 if d[n].hash == structural_hash(target)]
        print(render(lift(target, d, exclude=whole), lx))
        return 0

    if args.run:
        name = args.run
        if name not in exp.level1:
            if name in exp.terms:
                print(f"{exp.sizes[name]:8d}  {pretty(exp.terms[name])}")
                return 0
            print(f"{args.file}: no declaration named {name!r}",
                  file=sys.stderr)
            return 1
        prog = exp.level1[name]
        if prog.fuel == "policy" and args.fuel is None:
            r = run_policy(prog, max_steps=args.max_steps)
            budget = r.budget if r.budget is not None else "cap"
            payload = ("" if r.payload is None else
                       " " + render(decode(r.payload, prog.object_type), lx))
            print(f"{r.constructor}{payload}   (budget {budget}, "
                  f"{r.steps} contractions)")
            return 0
        out = run_level1(prog, args.max_steps, fuel=args.fuel)
        if not out.whnf:
            print(f"{out.status.value} after {out.steps} contractions",
                  file=sys.stderr)
            return 1
        ctor, fields = peel(out.term, prog.result_type,
                            max_steps=args.max_steps)
        payload = ("" if not fields else
                   " " + render(decode(fields[0], prog.object_type,
                                       max_steps=args.max_steps), lx))
        print(f"{ctor}{payload}   ({out.steps} contractions)")
        return 0

    # no flag: a summary
    print(f"{args.file}: {lx}, {len(program.decls)} declarations, "
          f"Stage A clean")
    print(f"  {len(exp.terms)} compiled terms, "
          f"{len(exp.level1)} level-1 declaration(s)")
    for name in sorted(exp.level1):
        lp = exp.level1[name]
        print(f"    {name} = {lp.interp} @ {lp.fuel}")
    return 0


if __name__ == "__main__":       # pragma: no cover
    sys.exit(main())
