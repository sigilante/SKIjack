"""SKIjack-0: the self-hosted front end's language, and its expansion
specified term for term (``docs/SKIJACK-0.md``).

This is a second implementation of the expander for the subset, written
from the specification rather than from ``expand.py``, so that agreement
between the two -- term for term, on every program the subset admits --
is evidence that the specification says what the expander does.  The
front end written in SKIjack implements the same specification; this
module is what its output is first checked against, and ``expand.py``
is checked against both.

It shares only the parser (``skijack.parser``) and aviary's bracket
abstraction with the expander.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

from aviary_kernel.abstraction import bracket_abstract
from aviary_kernel.birds import BY_NAME
from aviary_kernel.terms import App as KApp, Atom, Term

from . import ast as A

__all__ = ["Subset0Error", "compile0", "in_subset"]


class Subset0Error(Exception):
    """The program is outside SKIjack-0, or is ill-formed within it."""


ISA = ("S", "K", "I")
PRELUDE = ("pair", "hd", "tl", "nil", "cons", "zero", "suc")

#: aviary's Y, the fixpoint combinator every recursion is tied with
_Y = KApp(KApp(Atom("S"), KApp(Atom("K"), KApp(KApp(Atom("S"), Atom("I")), Atom("I")))),
          KApp(KApp(Atom("S"), KApp(KApp(Atom("S"), KApp(Atom("K"), Atom("S"))), Atom("K"))),
               KApp(Atom("K"), KApp(KApp(Atom("S"), Atom("I")), Atom("I")))))


# ------------------------------------------------------------ rule terms
# A rule's body before inlining: variables, references to other rules,
# the three combinators, applications.  Keeping variables and references
# apart is what lets a binder share a name with a rule.

@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class Ref:
    rule: str


@dataclass(frozen=True)
class Comb:
    name: str


@dataclass(frozen=True)
class Ap:
    fn: object
    arg: object


def ap(*ts):
    r = ts[0]
    for t in ts[1:]:
        r = Ap(r, t)
    return r


@dataclass
class Rule:
    formals: Tuple[str, ...]        #: () for an alias
    body: object


# --------------------------------------------------------------- subset

def _expr_in(e) -> Optional[str]:
    if isinstance(e, A.Name):
        return None
    if isinstance(e, A.App):
        return _expr_in(e.fn) or _expr_in(e.arg)
    if isinstance(e, A.Lambda):
        return ("binder " + e.param) if e.param in ISA else _expr_in(e.body)
    if isinstance(e, A.Cell):
        for x in e.items:
            r = _expr_in(x)
            if r:
                return r
        return None
    if isinstance(e, A.Pick):
        return _expr_in(e.expr)
    if isinstance(e, A.Case):
        r = _expr_in(e.scrutinee)
        for _c, bs, body in e.branches:
            for b in bs:
                if b in ISA:
                    return "binder " + b
            r = r or _expr_in(body)
        return r
    return type(e).__name__


def in_subset(program: A.Program) -> Optional[str]:
    """None if the program is SKIjack-0, else what puts it outside."""
    for d in program.decls:
        if isinstance(d, A.TypeDecl):
            continue
        if isinstance(d, A.Equation):
            for b in d.binders:
                if b in ISA:
                    return "binder " + b
            r = _expr_in(d.body)
        elif isinstance(d, A.Def):
            r = _expr_in(d.expr)
        else:
            return type(d).__name__
        if r:
            return r
    return None


# ------------------------------------------------------------- the passes

def _free(e, bound=frozenset()) -> List[str]:
    """Free names of e, in first-occurrence order."""
    out: List[str] = []

    def go(x, b):
        if isinstance(x, A.Name):
            if x.name not in b and x.name not in out:
                out.append(x.name)
        elif isinstance(x, A.App):
            go(x.fn, b)
            go(x.arg, b)
        elif isinstance(x, A.Lambda):
            go(x.body, b | {x.param})
        elif isinstance(x, A.Cell):
            for y in x.items:
                go(y, b)
        elif isinstance(x, A.Pick):
            go(x.expr, b)
        elif isinstance(x, A.Case):
            go(x.scrutinee, b)
            for _c, bs, body in x.branches:
                go(body, b | set(bs))
    go(e, set(bound))
    return out


def _desugar(e, ctors, types):
    """Cells, picks and cases become applications and lambdas."""
    if isinstance(e, A.Name):
        return e
    if isinstance(e, A.App):
        return A.App(_desugar(e.fn, ctors, types), _desugar(e.arg, ctors, types))
    if isinstance(e, A.Lambda):
        return A.Lambda(e.param, _desugar(e.body, ctors, types))
    if isinstance(e, A.Cell):
        items = [_desugar(x, ctors, types) for x in e.items]
        out = items[-1]
        for x in reversed(items[:-1]):
            out = A.App(A.App(A.Name("pair"), x), out)
        return out
    if isinstance(e, A.Pick):
        if e.axis < 1:
            raise Subset0Error(f"axis {e.axis}")
        out = _desugar(e.expr, ctors, types)
        for bit in bin(e.axis)[3:]:
            out = A.App(A.Name("tl" if bit == "1" else "hd"), out)
        return out
    if isinstance(e, A.Case):
        branches = {c: (bs, body) for c, bs, body in e.branches}
        if not e.branches or e.branches[0][0] not in ctors:
            raise Subset0Error("a case's first branch is no constructor")
        decl = types[ctors[e.branches[0][0]][0]]
        if sorted(branches) != sorted(c.name for c in decl.ctors) or len(branches) != len(e.branches):
            raise Subset0Error("a case must name each constructor once")
        out = _desugar(e.scrutinee, ctors, types)
        for c in decl.ctors:                            # declaration order
            bs, body = branches[c.name]
            k = _desugar(body, ctors, types)
            for b in reversed(bs):
                k = A.Lambda(b, k)
            out = A.App(out, k)
        return out
    raise Subset0Error(type(e).__name__)


def _vars(t) -> set:
    if isinstance(t, Var):
        return {t.name}
    if isinstance(t, Ap):
        return _vars(t.fn) | _vars(t.arg)
    return set()


class _Gen:
    """Code generation: names resolved, lambdas lifted into rules."""

    def __init__(self, rules: Dict[str, Rule], names: Sequence[str]):
        self.rules = rules
        self.names = set(names)
        self.n = 0

    def gen(self, e, scope: Sequence[str], sub: Dict[str, object]):
        if isinstance(e, A.Name):
            if e.name in sub:                           # a recursion's stand-in
                return sub[e.name]
            if e.name in scope:
                return Var(e.name)
            if e.name in ISA:
                return Comb(e.name)
            if e.name in self.names:
                return Ref(e.name)
            raise Subset0Error(f"unresolved name {e.name!r}")
        if isinstance(e, A.App):
            return Ap(self.gen(e.fn, scope, sub), self.gen(e.arg, scope, sub))
        if isinstance(e, A.Lambda):
            params: List[str] = []
            body = e
            while isinstance(body, A.Lambda):
                params.append(body.param)
                body = body.body
            fv = set(_free(body)) - set(params)
            # a name a stand-in replaces is free through the variables the
            # stand-in mentions: the group, or a recursion's own self
            for k, t in sub.items():
                if k in fv:
                    fv |= _vars(t)
            captured = [s for s in scope if s in fv]
            self.n += 1
            name = f"\x00lift{self.n}"
            inner = [s for s in sub if s not in params]
            term = self.gen(body, captured + params,
                            {k: sub[k] for k in inner})
            self.rules[name] = Rule(tuple(captured + params), term)
            out = Ref(name)
            for c in captured:
                out = Ap(out, Var(c))
            return out
        raise Subset0Error(type(e).__name__)


def compile0(program: A.Program) -> Dict[str, Term]:
    """Every name's closed term: constructors, equations, definitions and
    the prelude, as ``expand_program`` names them."""
    why = in_subset(program)
    if why:
        raise Subset0Error(f"outside SKIjack-0: {why}")
    types: Dict[str, A.TypeDecl] = {}
    ctors: Dict[str, Tuple[str, int, int]] = {}
    eqs: List[A.Equation] = []
    defs: List[A.Def] = []
    order: List[str] = []
    for d in program.decls:
        if isinstance(d, A.TypeDecl):
            types[d.name] = d
            for i, c in enumerate(d.ctors):
                ctors[c.name] = (d.name, i, len(c.fields))
                order.append(c.name)
        elif isinstance(d, A.Equation):
            eqs.append(d)
            order.append(d.name)
        else:
            defs.append(d)
            order.append(d.name)
    rules: Dict[str, Rule] = {}

    # the prelude: the Scott pair, list and numeral
    rules["pair"] = Rule(("x", "y", "c"), ap(Var("c"), Var("x"), Var("y")))
    rules["hd"] = Rule(("p",), ap(Var("p"), Comb("K")))
    rules["tl"] = Rule(("p",), ap(Var("p"), ap(Comb("K"), Comb("I"))))
    rules["nil"] = Rule(("n", "c"), Var("n"))
    rules["cons"] = Rule(("h", "t", "n", "c"), ap(Var("c"), Var("h"), Var("t")))
    rules["zero"] = Rule(("z", "s"), Var("z"))
    rules["suc"] = Rule(("n", "z", "s"), ap(Var("s"), Var("n")))

    # constructors: C f0 .. fk-1 c0 .. cn-1 = c_i f0 .. fk-1
    for tdecl in types.values():
        conts = [f"c{i}" for i in range(len(tdecl.ctors))]
        for i, c in enumerate(tdecl.ctors):
            fields = [f"f{j}" for j in range(len(c.fields))]
            rules[c.name] = Rule(tuple(fields + conts),
                                 ap(Var(conts[i]), *[Var(f) for f in fields]))

    names = list(dict.fromkeys(order + list(PRELUDE)))
    g = _Gen(rules, names)
    bodies = {q.name: _desugar(q.body, ctors, types) for q in eqs}
    eqnames = [q.name for q in eqs]

    # recursion: which equations each equation calls, and the groups
    deps = {q.name: [n for n in _free(bodies[q.name], frozenset(q.binders)) if n in bodies]
            for q in eqs}
    reach: Dict[str, set] = {}
    for n in eqnames:                                   # everything n reaches
        seen, todo = set(), list(deps[n])
        while todo:
            m = todo.pop()
            if m not in seen:
                seen.add(m)
                todo.extend(deps[m])
        reach[n] = seen
    grouped = set()
    for q in eqs:
        if q.name in grouped:
            continue
        group = [m for m in eqnames
                 if m == q.name or (m in reach[q.name] and q.name in reach[m])]
        grouped.update(group)
        if len(group) == 1:
            if q.name not in reach[q.name]:
                rules[q.name] = Rule(tuple(q.binders), g.gen(bodies[q.name], q.binders, {}))
            else:                                       # Y gen, gen taking itself
                selfv = "\x00self"
                scope = [selfv] + list(q.binders)
                term = g.gen(bodies[q.name], scope, {q.name: Var(selfv)})
                rules[q.name + "\x00gen"] = Rule(tuple(scope), term)
                rules[q.name] = Rule((), Ap(Ref("\x00Y"), Ref(q.name + "\x00gen")))
            continue
        # a group: gen t = tuple (code_0 t) .. (code_n-1 t); member_i = sel_i (Y gen)
        n = len(group)
        key = "\x00group:" + group[0]
        xs = [f"x{i}" for i in range(n)]
        rules[key + "tuple"] = Rule(tuple(xs) + ("c",), ap(Var("c"), *[Var(x) for x in xs]))
        for j in range(n):
            rules[f"{key}pick{j}"] = Rule(tuple(xs), Var(xs[j]))
            rules[f"{key}sel{j}"] = Rule(("t",), Ap(Var("t"), Ref(f"{key}pick{j}")))
        tv = "\x00grp"
        for j, m in enumerate(group):
            binders = next(q2.binders for q2 in eqs if q2.name == m)
            sub = {o: Ap(Ref(f"{key}sel{i}"), Var(tv)) for i, o in enumerate(group)}
            scope = [tv] + list(binders)
            rules[f"{key}code{j}"] = Rule(tuple(scope), g.gen(bodies[m], scope, sub))
        rules[key + "gen"] = Rule(("t",), ap(Ref(key + "tuple"),
                                              *[Ap(Ref(f"{key}code{j}"), Var("t")) for j in range(n)]))
        rules[key] = Rule((), Ap(Ref("\x00Y"), Ref(key + "gen")))
        for j, m in enumerate(group):
            rules[m] = Rule((), Ap(Ref(f"{key}sel{j}"), Ref(key)))

    for d in defs:
        rules[d.name] = Rule((), g.gen(_desugar(d.expr, ctors, types), [], {}))

    # expansion: inline every reference, then abstract the formals
    memo: Dict[str, Term] = {}

    def term_of(rule: str) -> Term:
        if rule == "\x00Y":
            return _Y
        if rule not in memo:
            r = rules[rule]
            t = inline(r.body)
            for f in reversed(r.formals):
                t = bracket_abstract("\x00v:" + f, t)
            memo[rule] = t
        return memo[rule]

    def inline(t) -> Term:
        if isinstance(t, Var):
            return Atom("\x00v:" + t.name)
        if isinstance(t, Comb):
            return Atom(t.name)
        if isinstance(t, Ref):
            return term_of(t.rule)
        return KApp(inline(t.fn), inline(t.arg))

    return {nm: term_of(nm) for nm in names}
