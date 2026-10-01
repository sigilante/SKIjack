"""Inlining: an optional pass that unfolds small functions at their calls.

``skijack.compile(..., inline=True)`` runs it between macro expansion and
case lowering, on the program's top-level equations and definitions.  Its
output is still one closed SKI term per name, and each term denotes what
it denoted without the pass: every rewrite is an equation of the lambda
calculus (beta, and the two case laws below).  It changes the term, so it
is off by default, and a program compiled without it is byte for byte what
it was.

Three rewrites, to a fixpoint within a budget:

- **Unfolding.** A call ``f a1 .. ak``, ``f`` a top-level equation of k >= 1
  binders that is not recursive (no path back to itself through other
  equations) and whose body is at most :data:`SMALL` nodes, becomes the
  body with the arguments substituted.  A constant (no binders) is never
  unfolded: that would copy work it shares.
- **Case of a known constructor.** ``C a1 .. an |> { .. ; C x1 .. xn e ; .. }``
  becomes ``e`` with the arguments substituted.
- **Case of case.** ``(s |> { Ci ys ei }) |> alts`` becomes
  ``s |> { Ci ys (ei |> alts) }``, when the alternatives are small enough to
  copy into every branch (:data:`SMALL_ALTS`).

No rewrite makes a program do more work.  An argument is substituted for a
binder only if it is a bare name, or the binder is used at most once and
not under a lambda -- the branches of one case counting as one use, since
only one runs.  Otherwise the call, or the case, is left as it was.  A
rewrite that would put a name where a local binder captures it is left
out too, and so is anything touching a quotation, a scry or a namespace
literal, and the equations of cores.
"""

from __future__ import annotations

from typing import Dict, Iterable, List, Set, Tuple

from . import ast as A

__all__ = ["inline_bodies", "SMALL", "SMALL_ALTS"]

#: the largest body unfolded at a call, in nodes (:func:`size`)
SMALL = 12
#: the largest alternatives copied into each branch by case of case
SMALL_ALTS = 16
#: rewrites in one body before the pass stops rewriting it
BUDGET = 10_000
#: the deepest a rewritten body may nest: the passes after this one recurse
MAX_DEPTH = 200

MANY = 2        # "used more than once, or under a lambda"


def size(e: A.Expr) -> int:
    if isinstance(e, A.Name):
        return 1
    if isinstance(e, A.App):
        return size(e.fn) + size(e.arg)
    if isinstance(e, A.Lambda):
        return 1 + size(e.body)
    if isinstance(e, A.Case):
        return 1 + size(e.scrutinee) + sum(size(b) for _, _, b in e.branches)
    if isinstance(e, A.Cell):
        return 1 + sum(size(x) for x in e.items)
    if isinstance(e, A.Pick):
        return 1 + size(e.expr)
    return 1_000_000                            # quotation and the rest: never small


def depth(e: A.Expr) -> int:
    if isinstance(e, A.App):
        return 1 + max(depth(e.fn), depth(e.arg))
    if isinstance(e, A.Lambda):
        return 1 + depth(e.body)
    if isinstance(e, A.Case):
        return 1 + max([depth(e.scrutinee)] + [depth(b) for _, _, b in e.branches])
    if isinstance(e, A.Cell):
        return 1 + max(depth(x) for x in e.items)
    if isinstance(e, A.Pick):
        return 1 + depth(e.expr)
    return 1


def opaque(e: A.Expr) -> bool:
    """Whether e holds a form this pass does not rewrite through."""
    if isinstance(e, (A.Quote, A.Scry, A.NsLit)):
        return True
    if isinstance(e, A.App):
        return opaque(e.fn) or opaque(e.arg)
    if isinstance(e, A.Lambda):
        return opaque(e.body)
    if isinstance(e, A.Case):
        return opaque(e.scrutinee) or any(opaque(b) for _, _, b in e.branches)
    if isinstance(e, A.Cell):
        return any(opaque(x) for x in e.items)
    if isinstance(e, A.Pick):
        return opaque(e.expr)
    return False


def uses(e: A.Expr, x: str) -> int:
    """How often x is used in e: 0, 1, or MANY (more, or any use under a
    lambda).  Of a case's branches the most used counts, one running."""
    if isinstance(e, A.Name):
        return 1 if e.name == x else 0
    if isinstance(e, A.App):
        return min(MANY, uses(e.fn, x) + uses(e.arg, x))
    if isinstance(e, A.Lambda):
        if e.param == x:
            return 0
        return MANY if uses(e.body, x) else 0
    if isinstance(e, A.Case):
        n = uses(e.scrutinee, x)
        branch = 0
        for _, binders, body in e.branches:
            if x not in binders:
                branch = max(branch, uses(body, x))
        return min(MANY, n + branch)
    if isinstance(e, A.Cell):
        return min(MANY, sum(uses(i, x) for i in e.items))
    if isinstance(e, A.Pick):
        return uses(e.expr, x)
    return MANY


def spine(e: A.Expr) -> Tuple[A.Expr, List[A.Expr]]:
    args: List[A.Expr] = []
    while isinstance(e, A.App):
        args.append(e.arg)
        e = e.fn
    args.reverse()
    return e, args


def apply(f: A.Expr, args: Iterable[A.Expr]) -> A.Expr:
    for x in args:
        f = A.App(f, x)
    return f


class _Pass:
    def __init__(self, callees: Dict[str, Tuple[Tuple[str, ...], A.Expr]],
                 ctors: Dict[str, Tuple[str, int, int]], substitute, free_names, fresh):
        self.callees = callees
        self.ctors = ctors
        self.substitute = substitute
        self.free_names = free_names
        self.fresh = fresh
        self.left = BUDGET

    @staticmethod
    def bind(binders, args) -> Dict[str, A.Expr]:
        """args for binders; a binder repeated binds its last occurrence."""
        return {b: a for b, a in zip(binders, args)}

    def safe(self, body: A.Expr, binders, args) -> bool:
        """Whether substituting args copies no work: each argument a name,
        or its binder used at most once and not under a lambda."""
        return all(isinstance(a, A.Name) or uses(body, b) <= 1
                   for b, a in self.bind(binders, args).items())

    def rewrite(self, e: A.Expr, bound: Set[str]) -> A.Expr:
        """e with its calls unfolded and its cases simplified, children
        first; bound, the names local binders hold here."""
        if self.left <= 0 or opaque(e):
            return e
        if isinstance(e, A.Name):
            return self.unfold(e, [], bound)
        if isinstance(e, A.App):
            head, args = spine(e)
            args = [self.rewrite(x, bound) for x in args]
            head = self.rewrite(head, bound) if not isinstance(head, A.Name) else head
            return self.unfold(head, args, bound)
        if isinstance(e, A.Lambda):
            return A.Lambda(e.param, self.rewrite(e.body, bound | {e.param}))
        if isinstance(e, A.Case):
            scrut = self.rewrite(e.scrutinee, bound)
            branches = tuple((c, bs, self.rewrite(b, bound | set(bs)))
                             for c, bs, b in e.branches)
            return self.case(A.Case(scrut, branches), bound)
        if isinstance(e, A.Cell):
            return A.Cell(tuple(self.rewrite(x, bound) for x in e.items))
        if isinstance(e, A.Pick):
            return A.Pick(e.axis, self.rewrite(e.expr, bound))
        return e

    def unfold(self, head: A.Expr, args: List[A.Expr], bound: Set[str]) -> A.Expr:
        """head applied to args, with head's body in place of the call if it
        is a small function's, called with all its arguments."""
        e = apply(head, args)
        if not isinstance(head, A.Name) or head.name in bound:
            return e
        callee = self.callees.get(head.name)
        if callee is None:
            return e
        binders, body = callee
        k = len(binders)
        if len(args) < k or not self.safe(body, binders, args[:k]):
            return e
        if (self.free_names(body) - set(binders)) & bound:
            return e                        # a global of the callee's, bound here
        out = apply(self.substitute(body, self.bind(binders, args[:k])), args[k:])
        self.left -= 1
        out = self.rewrite(out, bound)
        return e if depth(out) > MAX_DEPTH else out

    def case(self, e: A.Case, bound: Set[str]) -> A.Expr:
        scrut = e.scrutinee
        head, args = spine(scrut)
        # a known constructor: its branch, the fields substituted
        if isinstance(head, A.Name) and head.name in self.ctors and head.name not in bound:
            for c, bs, body in e.branches:
                if c == head.name and len(args) == len(bs) and self.safe(body, bs, args):
                    self.left -= 1
                    return self.rewrite(self.substitute(body, self.bind(bs, args)), bound)
            return e
        # a case of a case: the outer alternatives into each inner branch
        if isinstance(scrut, A.Case) and sum(size(b) for _, _, b in e.branches) <= SMALL_ALTS:
            alts_free = set()
            for c, bs, body in e.branches:
                alts_free |= self.free_names(body) - set(bs)
            inner = []
            for c, cbs, body in scrut.branches:
                names = list(cbs)
                for i, b in enumerate(names):       # an inner binder the alts use: renamed
                    if b in alts_free:
                        taken = alts_free | self.free_names(body) | set(names) | bound
                        nb = self.fresh(b + "_", taken)
                        body = self.substitute(body, {b: A.Name(nb)})
                        names[i] = nb
                inner.append((c, tuple(names), A.Case(body, e.branches)))
            self.left -= 1
            out = self.rewrite(A.Case(scrut.scrutinee, tuple(inner)), bound)
            return e if depth(out) > MAX_DEPTH else out
        return e


def _recursive(bodies: Dict[str, Tuple[Tuple[str, ...], A.Expr]], free_names) -> Set[str]:
    """The equations that reach themselves through calls among the given."""
    calls = {n: free_names(b) & set(bodies) for n, (_, b) in bodies.items()}
    rec: Set[str] = set()
    for start in bodies:
        seen, todo = set(), list(calls[start])
        while todo:
            n = todo.pop()
            if n == start:
                rec.add(start)
                break
            if n not in seen:
                seen.add(n)
                todo.extend(calls[n])
    return rec


def inline_bodies(equations: Dict[str, Tuple[Tuple[str, ...], A.Expr]],
                  defs: Dict[str, A.Expr], ctors: Dict[str, Tuple[str, int, int]],
                  substitute, free_names, fresh
                  ) -> Tuple[Dict[str, A.Expr], Dict[str, A.Expr]]:
    """The top-level equations' bodies (name -> (binders, body), after macro
    expansion, before case lowering) and the definitions' (name -> body),
    rewritten.  The expander's own substitution, free names and fresh names
    are passed in, so the pass renames as it does."""
    rec = _recursive(equations, free_names)
    callees = {n: (bs, b) for n, (bs, b) in equations.items()
               if bs and n not in rec and size(b) <= SMALL and not opaque(b)}
    out_eq, out_def = {}, {}
    for n, (bs, b) in equations.items():
        p = _Pass(callees, ctors, substitute, free_names, fresh)
        out_eq[n] = p.rewrite(b, set(bs))
    for n, b in defs.items():
        p = _Pass(callees, ctors, substitute, free_names, fresh)
        out_def[n] = p.rewrite(b, set())
    return out_eq, out_def
