"""CLI wall-clock comparison: the same commands through both binaries.

    python3 bench/compare.py [--reps N] [--python PY] [--rust BIN]

Prints a Markdown table of best-of-N wall times and the speed-up.
"""
import argparse
import os
import statistics
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
PYDIR = os.path.normpath(os.path.join(HERE, "..", "..", "python"))
CORPUS = "skijack/corpus"

COMMANDS = [
    ("summary, interp-whnff", f"{CORPUS}/interp-whnff.ascii.ski"),
    ("--check, scry-ns", f"{CORPUS}/scry-ns.ascii.ski --check"),
    ("--expand, tower", f"{CORPUS}/tower.ascii.ski --expand"),
    ("--dictionary, scry-block", f"{CORPUS}/scry-block.ascii.ski --dictionary"),
    ("--lift step, interp-whnff", f"{CORPUS}/interp-whnff.ascii.ski --lift step"),
    ("--run answer, scry-ns (28,661 contractions)", f"{CORPUS}/scry-ns.ascii.ski --run answer"),
    ("--run t1, tower (91,556 contractions)", f"{CORPUS}/tower.ascii.ski --run t1"),
    ("--run t2, tower (504,930 contractions)", f"{CORPUS}/tower.ascii.ski --run t2"),
]


def run(cmd, reps):
    times = []
    out = None
    for _ in range(reps):
        t0 = time.perf_counter()
        p = subprocess.run(cmd, cwd=PYDIR, capture_output=True, text=True)
        times.append(time.perf_counter() - t0)
        out = (p.returncode, p.stdout, p.stderr)
    return min(times), statistics.median(times), out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--python", default=sys.executable)
    ap.add_argument("--rust", default=os.path.join(HERE, "..", "target", "release", "skijack"))
    args = ap.parse_args()
    py = [args.python, "-m", "skijack"]
    rs = [os.path.abspath(args.rust)]
    print(f"| command | Python best (s) | Rust best (s) | speed-up |")
    print(f"|---|---:|---:|---:|")
    for label, argstr in COMMANDS:
        a = argstr.split()
        pmin, _, pout = run(py + a, args.reps)
        rmin, _, rout = run(rs + a, args.reps)
        same = "" if pout == rout else "  **OUTPUT DIFFERS**"
        print(f"| {label} | {pmin:.3f} | {rmin:.3f} | {pmin / rmin:.0f}x{same} |")


if __name__ == "__main__":
    main()
