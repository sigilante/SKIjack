"""The Python twin of examples/bench_inproc.rs: same stages, same labels."""
import sys
import time

import skijack
from skijack import corpus
from skijack.dictionary import from_expansion
from skijack.run import decode, peel, run_level1


def timeit(reps, f):
    times = []
    last = None
    for _ in range(reps):
        t0 = time.perf_counter()
        last = f()
        times.append((time.perf_counter() - t0) * 1000)
    times.sort()
    return times[0], times[len(times) // 2], last


def main():
    reps = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    files = [(s, lx) for s in corpus.names() for lx in ("ascii", "unicode")]

    def compile_all():
        n = 0
        for stem, lx in files:
            try:
                n += len(skijack.compile(corpus.read(stem, lx), lx).terms)
            except skijack.SkijackError:
                pass
        return n
    mn, md, n = timeit(reps, compile_all)
    print(f"compile-corpus\t{mn:.2f}\t{md:.2f}\t{n} terms over {len(files)} files")
    src = corpus.read("tower", "ascii")
    mn, md, _ = timeit(reps, lambda: skijack.compile(src))
    print(f"compile-tower\t{mn:.2f}\t{md:.2f}\t")
    mn, md, _ = timeit(reps, lambda: len(from_expansion(skijack.compile(src))))
    print(f"dictionary-tower\t{mn:.2f}\t{md:.2f}\t")
    exp = skijack.compile(src)
    for name in ("t0", "t1", "t2"):
        prog = exp.level1[name]
        mn, md, o = timeit(reps, lambda: run_level1(prog, 5_000_000))
        rate = o.steps / (mn / 1000)
        print(f"run-{name}\t{mn:.2f}\t{md:.2f}\t{o.steps} contractions, {rate/1e6:.1f} M/s at best")

        def dec():
            _, fields = peel(o.term, prog.result_type, max_steps=5_000_000)
            return decode(fields[0], prog.object_type, max_steps=5_000_000)
        mn, md, _ = timeit(reps, dec)
        print(f"decode-{name}\t{mn:.2f}\t{md:.2f}\t")
    src = corpus.read("scry-ns", "ascii")
    exp = skijack.compile(src)
    prog = exp.level1["answer"]
    mn, md, o = timeit(reps, lambda: run_level1(prog, 5_000_000))
    print(f"run-answer\t{mn:.2f}\t{md:.2f}\t{o.steps} contractions")


if __name__ == "__main__":
    main()
