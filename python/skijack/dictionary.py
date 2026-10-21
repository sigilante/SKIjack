"""The dictionary: Tier 1's table, and lift.

``DESIDERATA.md`` §5 -- "the dictionary is the ABI's public face. Tier
1's table, with expansions, sizes, and hashes, is a versioned artifact,
published with the language, and it is the same table the runtime's jets
key on."  ``RUNTIME-DESIGN.md`` §2 says how the runtime uses it: it
"matches expanded subterms against a table of known combinators by
structural hash".

And item 8 -- "a term produced by the expander can be lifted back to
named source by exact structural matching against the dictionary of
known expansions, and only that; unknown subterms stay raw."  That is
:func:`lift`, and :func:`lower` takes it back.

**The hash** is a Merkle hash over the tree, prefixed with the table's
version: ``skijack-2:8f3c…``.  A leaf hashes its name; an application
hashes ``"(" + hash(fn) + " " + hash(arg) + ")"``; both are ``sha256``
truncated to 32 hex digits, 128 bits: past the reach of the birthday
search that 64 bits left to anyone choosing both terms (``skijack-1``).

Two reasons for Merkle rather than hashing a printed form.  It is
computable in one bottom-up pass and *incrementally*: a runtime that
hash-conses its nodes already has every child's hash when it builds a
parent, which is exactly how ``RUNTIME-DESIGN.md`` §2's jet table is
meant to match ("matches expanded subterms against a table of known
combinators by structural hash").  And it is over the *tree*, not the
DAG, so two structurally equal terms hash alike however they were
shared -- the runtime meets a term without knowing how it was built.
:func:`canonical` gives the fully parenthesized printed form, which
determines the same tree and is what the tests read.

Changing an entry changes its hash, and ``DESIDERATA.md`` §5 makes that
a version change.

**Lift is not reduction.** It renames exact structural matches, largest
first, and nothing else; ``lower(lift(t)) == t`` holds by construction
and is tested on every corpus term.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple, Union

from aviary_kernel.abstraction import expand as _ski_expand
from aviary_kernel.terms import App, Atom, Term, size

from . import ast as A
from .expand import Expansion

__all__ = [
    "VERSION", "MIN_LIFT_SIZE", "DictionaryError", "Entry", "Dictionary",
    "canonical", "structural_hash", "hash_all", "from_expansion", "lift",
    "lower",
]


from .errors import SkijackError

class DictionaryError(SkijackError):
    """A name registered twice with two different terms."""

#: the table's version; a change to any entry is a change to this
VERSION = "skijack-2"

#: the hex digits a digest keeps: 128 bits
DIGITS = 32

#: entries smaller than this are tabled but never *lifted*: naming every
#: ``K`` in a term (``zero``, ``nil``, ``Zero``, ``PTrue`` all expand to
#: ``K``) is not a recognition, and DESIDERATA.md §3 makes Tier 1 "a name
#: for a shape the reader would otherwise have to recognize".
MIN_LIFT_SIZE = 3

#: the three primitives.  A program whose object type declares
#: constructors called ``S``, ``K`` and ``I`` puts real rows under those
#: names in the table, but lift and lower **reserve the names for the
#: ISA**: at level 0 they are the combinators (SURFACE-LANGUAGE-DESIGN.md
#: §6b), so a lifted ``S`` must lower back to the atom, not to ``encS``.
from .abi import ISA as _ISA


def canonical(term: Term) -> str:
    """The fully parenthesized printed form.  Iterative: a level-2 datum
    is deeper than the Python stack."""
    out: List[str] = []
    work: List[Union[str, Term]] = [term]
    while work:
        x = work.pop()
        if isinstance(x, str):
            out.append(x)
            continue
        if isinstance(x, Atom):
            out.append(x.name)
            continue
        work.append(")")
        work.append(x.arg)
        work.append(" ")
        work.append(x.fn)
        work.append("(")
    return "".join(out)


def _digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:DIGITS]


def hash_all(term: Term) -> Dict[int, Tuple[Term, str]]:
    """Every node's Merkle digest, bottom up, in one pass.  The node is
    held in the value so its ``id`` cannot be recycled under the map."""
    memo: Dict[int, Tuple[Term, str]] = {}
    work: List[Tuple[Term, bool]] = [(term, False)]
    while work:
        x, done = work.pop()
        hit = memo.get(id(x))
        if hit is not None and hit[0] is x:
            continue
        if isinstance(x, Atom):
            memo[id(x)] = (x, _digest(x.name))
            continue
        if not done:
            work.append((x, True))
            work.append((x.fn, False))
            work.append((x.arg, False))
        else:
            memo[id(x)] = (x, _digest(
                f"({memo[id(x.fn)][1]} {memo[id(x.arg)][1]})"))
    return memo


def structural_hash(term: Term) -> str:
    """The published hash of a term."""
    memo = hash_all(term)
    return f"{VERSION}:{memo[id(term)][1]}"


@dataclass(frozen=True)
class Entry:
    """One row of the published table."""
    name: str
    term: Term
    size: int
    hash: str
    tier: int = 1
    note: str = ""


class Dictionary:
    """A versioned table of named expansions."""

    def __init__(self, entries: Iterable[Entry] = (),
                 version: str = VERSION):
        self.version = version
        self.entries: Dict[str, Entry] = {}
        for e in entries:
            self.add(e)

    # --- building ---------------------------------------------------

    def add(self, entry: Entry, replace: bool = False) -> None:
        """Add a row.  A second row under the same name with a *different*
        term is refused: the table is per-ABI, and two programs over
        different object types do not share an ``sp``.  Re-registering
        the same term is a no-op, which is what makes merging programs
        that share the prelude work."""
        old = self.entries.get(entry.name)
        if old is not None and old.hash != entry.hash and not replace:
            raise DictionaryError(
                f"{entry.name!r} is already in the table as "
                f"{old.hash} ({old.size} atoms) and would become "
                f"{entry.hash} ({entry.size} atoms); one name is one "
                f"expansion, and a change is a version change "
                f"(DESIDERATA.md §5)")
        self.entries[entry.name] = entry

    def register(self, name: str, term: Term, tier: int = 1,
                 note: str = "", replace: bool = False) -> Entry:
        e = Entry(name, term, size(term), structural_hash(term), tier, note)
        self.add(e, replace)
        return e

    def __len__(self) -> int:
        return len(self.entries)

    def __contains__(self, name: str) -> bool:
        return name in self.entries

    def __getitem__(self, name: str) -> Entry:
        return self.entries[name]

    def names(self) -> List[str]:
        return sorted(self.entries)

    def rows(self) -> List[Tuple[str, int, str]]:
        """The published table: (name, atoms, hash), sorted by name."""
        return [(n, self.entries[n].size, self.entries[n].hash)
                for n in self.names()]

    # --- the lift index ---------------------------------------------

    def lift_index(self, min_size: int = MIN_LIFT_SIZE,
                   exclude: Sequence[str] = ()) -> Dict[str, str]:
        """hash -> name, for the entries lift may name.

        Two names for one term (``zero`` and ``nil`` are both ``K``;
        ``dec`` and ``arith.dec`` are one equation reached two ways) resolve
        by preferring the unqualified name, then the shorter, then
        alphabetically -- so the table is deterministic and the name it
        picks is the one a reader would write.  ``exclude`` drops names,
        which is how one lifts a term the table already holds whole:
        without it the largest match is the term itself.
        """
        index: Dict[str, str] = {}
        drop = set(exclude) | set(_ISA)
        for name in sorted(self.entries,
                           key=lambda n: (n.count("."), len(n), n)):
            if name in drop:
                continue
            e = self.entries[name]
            if e.size < min_size:
                continue
            index.setdefault(e.hash, name)
        return index


def from_expansion(exp: Expansion, *, include: Optional[Sequence[str]] = None,
                   dictionary: Optional[Dictionary] = None,
                   prefix: str = "") -> Dictionary:
    """Register a compiled program's names.

    Every name the expander produced -- the prelude, the Scott
    constructors of every declared type, every equation and every core's loop
    -- plus ``Y``, which the environment supplies and every recursive equation
    is tied with.
    """
    d = dictionary if dictionary is not None else Dictionary()
    if "Y" not in d:
        d.register("Y", _ski_expand(Atom("Y"), exp.env), tier=1,
                   note="the fixpoint every recursive equation is tied with")
    names = exp.terms if include is None else include
    for name in names:
        if name in exp.terms:
            d.register(prefix + name, exp.terms[name])
    return d


# ------------------------------------------------------------------ lift

def lift(term: Term, dictionary: Dictionary,
         min_size: int = MIN_LIFT_SIZE,
         exclude: Sequence[str] = ()) -> A.Expr:
    """Name every subterm that is an **exact structural match** of a
    dictionary entry, largest match first; leave everything else raw.

    The result is ordinary surface syntax -- ``ast.Name`` for a named
    entry or a bare ``S``/``K``/``I``, ``ast.App`` for an application --
    so it renders in either lexicon.
    """
    index = dictionary.lift_index(min_size, exclude)
    memo = hash_all(term)

    def h(x: Term) -> str:
        hit = memo.get(id(x))
        if hit is not None and hit[0] is x:
            return f"{VERSION}:{hit[1]}"
        return structural_hash(x)       # a node built after the memo pass

    # top down, so the largest match wins
    out: List[A.Expr] = []
    work: List[Tuple[Term, bool]] = [(term, False)]
    while work:
        x, done = work.pop()
        if done:
            r = out.pop()
            l = out.pop()
            out.append(A.App(l, r))
            continue
        name = index.get(h(x))
        if name is not None and same_term(x, dictionary[name].term):
            out.append(A.Name(name))
            continue
        if isinstance(x, Atom):
            out.append(A.Name(x.name))
            continue
        work.append((x, True))
        work.append((x.arg, False))
        work.append((x.fn, False))
    return out.pop()


def same_term(a: Term, b: Term) -> bool:
    """Whether two terms are one tree.  A §5 hash is 64 bits, so a match
    by hash is only a candidate: two terms built to collide share one.
    Iterative, and a pair compared once is not compared again, so a
    shared graph costs its size."""
    seen: Set[Tuple[int, int]] = set()
    work = [(a, b)]
    while work:
        x, y = work.pop()
        if x is y or (id(x), id(y)) in seen:
            continue
        seen.add((id(x), id(y)))
        if isinstance(x, Atom) or isinstance(y, Atom):
            if not (isinstance(x, Atom) and isinstance(y, Atom) and x.name == y.name):
                return False
            continue
        work.append((x.fn, y.fn))
        work.append((x.arg, y.arg))
    return True


def lower(named: A.Expr, dictionary: Dictionary) -> Term:
    """Take a lifted tree back to the closed term."""
    out: List[Term] = []
    work: List[Tuple[A.Expr, bool]] = [(named, False)]
    while work:
        x, done = work.pop()
        if done:
            r = out.pop()
            l = out.pop()
            out.append(App(l, r))
            continue
        if isinstance(x, A.Name):
            if x.name in _ISA:
                out.append(Atom(x.name))      # reserved: always the ISA
            elif x.name in dictionary:
                out.append(dictionary[x.name].term)
            else:
                raise KeyError(
                    f"{x.name!r} is neither a dictionary entry nor a "
                    f"primitive, so it cannot be lowered")
            continue
        if isinstance(x, A.App):
            work.append((x, True))
            work.append((x.arg, False))
            work.append((x.fn, False))
            continue
        raise TypeError(f"cannot lower {x!r}")
    return out.pop()
