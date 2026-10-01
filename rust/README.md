# skijack, in Rust

A port of the reference `python/skijack` compiler and runtime, including
the parts it takes from `aviary-kernel` (the term model, the bird registry,
Curry bracket abstraction and the normal-order reducer).  It has no Python
dependency.

    cargo build --release
    target/release/skijack ../python/skijack/corpus/tower.ascii.ski --run t2

The CLI takes the same flags as `python3 -m skijack` and prints the same
bytes: `--check`, `--expand`, `--dictionary`, `--lift NAME`,
`--render LEXICON`, `--run NAME [--fuel N] [--max-steps N]`, and the
summary with no flag.

## Conformance

The reference implementation is the specification.  `tests/golden.manifest`
pins the sha256 of stdout, exit code and stderr of the Python CLI for 2,200
invocations over the shipped corpus: every program in both spellings, every
flag, `--lift` of every compiled name, and `--run` of every level-1
declaration at its declared fuel and at fuel 1.  `cargo test` replays them
all through the Rust binary; `bench/golden.sh` regenerates the set.
`tests/api.rs` states the laws the Python suite checks (one tree from both
spellings, render round trips, `lower ∘ lift`, the 618-atom `whnfF`, the
tower's contraction counts, iterative deepening).

Two deliberate departures, neither visible on the corpus:

- A program nested deeper than CPython's recursion limit (four hundred
  parentheses around an atom) fails in Python with *expression nests too
  deeply*; this port parses it.  Its own limit is a nesting count of 20,000,
  and the CLI runs on a 1 GiB stack.
- The reducer's sampled DAG-size guard is off by default (`max_size: None`).
  The reference samples it every 512 contractions against a limit of one
  billion nodes, which never fires but costs an O(term) walk per sample;
  the step budget already bounds every run.  The figures below say what
  that guard costs Python.

## Speed

Ryzen 9 9950X, Linux, CPython 3.14, `cargo build --release`.  Best of
several runs; the reference numbers include its size guard because that is
what `python3 -m skijack` does.

CLI, wall clock, process start included:

| command | Python (s) | Rust (s) | speed-up |
|---|---:|---:|---:|
| summary, interp-whnff | 0.047 | 0.002 | 30x |
| `--check`, scry-ns | 0.046 | 0.001 | 37x |
| `--expand`, tower | 0.063 | 0.002 | 26x |
| `--dictionary`, scry-block | 0.079 | 0.005 | 15x |
| `--lift step`, interp-whnff | 0.063 | 0.002 | 28x |
| `--run answer`, scry-ns (28,661 contractions) | 0.185 | 0.004 | 46x |
| `--run t1`, tower (91,556 contractions) | 0.510 | 0.003 | 168x |
| `--run t2`, tower (504,930 contractions) | 9.930 | 0.016 | 624x |
| the whole 2,200-invocation conformance sweep, 32 jobs | 24.3 | 2.7 | 9x |

In process, so without interpreter start-up (`bench/bench_inproc.py` and
`examples/bench_inproc.rs`, same stages, same labels):

| stage | Python (ms) | Rust (ms) | speed-up |
|---|---:|---:|---:|
| compile the whole corpus (42 files, 1,698 terms) | 612 | 49 | 12x |
| compile tower | 8.3 | 0.94 | 9x |
| dictionary of tower (Merkle sha256 of every term) | 17.2 | 2.0 | 8x |
| run t1 (91,556 contractions) | 462 | 0.77 | 600x |
| run t2 (504,930 contractions) | 9,501 | 4.3 | 2,200x |
| decode t2's result (behavioral probing) | 573 | 5.8 | 99x |

Reducer throughput, contractions per second:

| | Python, guard on | Python, guard off | Rust |
|---|---:|---:|---:|
| t1 | 0.20 M/s | 0.50 M/s | 119 M/s |
| t2 | 0.05 M/s | 0.52 M/s | 117 M/s |

So the honest reducer figure is about 230x over a Python reducer with the
guard switched off, and the rest of the 2,200x on T2 is the guard.  The
dictionary is where the gap is smallest: Python's sha256 is C, and the work
there is hashing rather than interpretation.

## Layout

| module | reference |
|---|---|
| `term.rs` | `aviary_kernel.terms`: `Rc` DAG, iterative size, pretty, substitute, drop |
| `env.rs` | `aviary_kernel.birds`, `environment`, `abstraction` |
| `reduce.rs` | `aviary_kernel.reduce` and `skijack.probe.fast_reduce` |
| `lexicon.rs`, `parser.rs`, `render.rs`, `ast.rs` | the same names |
| `generate.rs`, `check.rs`, `typecheck.rs` | the same names; Stage B's cyclic types live in an arena |
| `expand.rs`, `quote.rs` | the same names |
| `dictionary.rs`, `run.rs` | the same names |
| `corpus.rs` | the `.ski` files under `python/skijack/corpus`, embedded |
| `main.rs` | `skijack.__main__` |

Names, passes, limits and messages follow the reference file for file, so
a reader of one can read the other; where the reference relies on `id()`
memoization the port keys on node pointers and holds the node, for the same
reason the reference holds it.
