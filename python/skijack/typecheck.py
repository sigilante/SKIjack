"""Stage B: the type discipline (``DESIDERATA.md`` item 11).

A pass that rejects and never rewrites, run after generation and before
codegen, over macro-expanded bodies.  Hindley--Milner over the declared
sum types and function types, with the rule that is the whole
discipline:

**A datum may be applied; a function is never a datum.**  Every declared
type is Scott-encoded, so a value of type ``T`` *is* its own case
analysis and may be applied to one continuation per constructor.  The
unifier is therefore oriented, ``unify(expected, given)``: a *given* sum
type meeting an *expected* arrow expands to its Scott scheme, and an
*expected* sum type meeting a *given* arrow is the error.  ``Zero``
compiles to ``K``, so a symmetric rule would accept ``Suc K``; the
orientation is what makes it an error.

A case form ``e |> { C b... body }`` is typed nominally: the scrutinee
has the branches' declared type, the binders have the declared field
types, and the branches agree on one result.  A datum applied by hand
to its continuations, as the interpreters do (``args h (rb1 rb h)``), is
typed by those continuations instead, and recursion over it yields a
cyclic type; unification is equirecursive, so those are admitted, as is
``omega = S I I (S I I)``.  The nominal form is the stronger check, and
the one to write when the check is wanted.

The operands of ``EQ`` carry a *data* constraint: a type variable so
marked may be bound to a sum type and never to an arrow, which is how
``f x = EQ x PTrue`` followed by ``g := f K`` is refused although ``x``
is a bare binder.

Erased at codegen: nothing here changes a term.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Set, Tuple, Union

from . import ast as A
from .abi import ISA
from .check import CheckError, Problem, Site
from .generate import (GenerateError, find_answer_type, find_loop_types,
                       find_object_type, is_interpreter_core)

__all__ = ["TypeMismatchError", "typecheck", "typecheck_program",
           "Type", "TVar", "TCon", "TArrow", "Scheme", "render_type"]


class TypeMismatchError(CheckError):
    """Stage B: the program is not well typed."""


# ------------------------------------------------------------------ types

@dataclass(eq=False)
class TVar:
    id: int
    data: bool = False          #: an operand of EQ: may never be a function
    ref: Optional["Type"] = None


@dataclass(frozen=True, eq=False)
class TCon:
    name: str
    args: Tuple["Type", ...] = ()


@dataclass(eq=False)
class TArrow:
    """A function type, with its provenance.

    ``elim`` marks an arrow a *variable* acquired by being applied -- the
    shape of some unknown datum eliminated against continuations -- as
    opposed to one a value was built with (a lambda, a combinator, a
    partially applied constructor).  Only the latter is a function that
    can never be a datum.  When an elimination arrow is checked against a
    declared type it records it in ``nominal``; ``datum`` records that an
    operand of ``EQ`` went through it.  Both then refuse a built arrow.
    """
    param: "Type"
    result: "Type"
    elim: bool = False
    nominal: Optional[str] = None
    datum: bool = False
    checked: Optional[str] = None    #: validated against this type's Scott spine


Type = Union[TVar, TCon, TArrow]

FUEL = TCon("fuel")


def _list(a: Type) -> Type:
    return TCon("list", (a,))


def _cell(a: Type, b: Type) -> Type:
    return TCon("cell", (a, b))


def _arrows(params: Sequence[Type], result: Type) -> Type:
    t = result
    for p in reversed(params):
        t = TArrow(p, t)
    return t


def _scott(conts: Sequence[Type], result: Type, name: str) -> Type:
    """The spine of a datum applied to its continuations: every arrow on
    it is an elimination arrow committed to ``name``; the continuation
    types inside it are ordinary functions the program supplies."""
    t = result
    for c in reversed(conts):
        t = TArrow(c, t, elim=True, nominal=name)
    return t


@dataclass(frozen=True)
class Scheme:
    vars: Tuple[int, ...]       #: quantified TVar ids
    data: Tuple[int, ...]       #: those of them that carry the data constraint
    type: Type


def resolve(t: Type) -> Type:
    while isinstance(t, TVar) and t.ref is not None:
        t = t.ref
    return t


def render_type(t: Type, names: Optional[Dict[int, str]] = None) -> str:
    names = {} if names is None else names
    seen: Set[int] = set()

    def go(t: Type, left: bool) -> str:
        t = resolve(t)
        if isinstance(t, TVar):
            if t.id not in names:
                n = len(names)
                names[t.id] = chr(ord("a") + n) if n < 26 else f"t{n}"
            return names[t.id]
        if id(t) in seen:
            return "..."
        seen.add(id(t))
        try:
            if isinstance(t, TCon):
                if not t.args:
                    return t.name
                return "(" + " ".join([t.name] + [go(a, True) for a in t.args]) + ")"
            s = f"{go(t.param, True)} -> {go(t.result, False)}"
            if t.nominal:
                s = f"{s} as {t.nominal}"
            return f"({s})" if left else s
        finally:
            seen.discard(id(t))
    return go(t, False)


class _Fail(Exception):
    """A type error inside one declaration; reported and the pass continues."""


# ------------------------------------------------------------ the checker

class _Types:
    def __init__(self, program: A.Program, prelude: Sequence[str]):
        self.program = program
        self.prelude = tuple(prelude)
        self.problems: List[Problem] = []
        self.next_id = 0
        self.types: Dict[str, A.TypeDecl] = {}
        self.ctor_of: Dict[str, A.TypeDecl] = {}
        self.env: Dict[str, Scheme] = {}         # program-level names
        self.core_env: Dict[str, Dict[str, Scheme]] = {}
        self.mono: Dict[str, Type] = {}          # names in the group being inferred

    # ---- variables and schemes (every walker is cycle-safe)

    def fresh(self, data: bool = False) -> TVar:
        self.next_id += 1
        return TVar(self.next_id, data)

    def instantiate(self, s: Scheme) -> Type:
        if not s.vars:
            return s.type
        sub = {v: self.fresh(v in s.data) for v in s.vars}
        memo: Dict[int, TVar] = {}

        def go(t: Type) -> Type:
            t = resolve(t)
            if isinstance(t, TVar):
                return sub.get(t.id, t)
            if id(t) in memo:
                return memo[id(t)]
            if isinstance(t, TCon) and not t.args:
                return t
            hole = self.fresh()
            memo[id(t)] = hole
            new: Type
            if isinstance(t, TCon):
                new = TCon(t.name, tuple(go(a) for a in t.args))
            else:
                new = TArrow(go(t.param), go(t.result), t.elim, t.nominal, t.datum, t.checked)
            hole.ref = new
            return new
        return go(s.type)

    def free(self, t: Type, out: Dict[int, TVar], seen: Optional[Set[int]] = None) -> None:
        seen = set() if seen is None else seen
        t = resolve(t)
        if isinstance(t, TVar):
            out[t.id] = t
            return
        if id(t) in seen:
            return
        seen.add(id(t))
        if isinstance(t, TCon):
            for a in t.args:
                self.free(a, out, seen)
        else:
            self.free(t.param, out, seen)
            self.free(t.result, out, seen)

    def env_free(self) -> Set[int]:
        out: Dict[int, TVar] = {}
        for s in self.env.values():
            fv: Dict[int, TVar] = {}
            self.free(s.type, fv)
            for k in fv:
                if k not in s.vars:
                    out[k] = fv[k]
        for t in self.mono.values():
            self.free(t, out)
        return set(out)

    def generalize(self, t: Type) -> Scheme:
        fv: Dict[int, TVar] = {}
        self.free(t, fv)
        env_fv = self.env_free()
        qs = tuple(sorted(k for k in fv if k not in env_fv))
        return Scheme(qs, tuple(k for k in qs if fv[k].data), t)

    def close(self, t: Type) -> Scheme:
        fv: Dict[int, TVar] = {}
        self.free(t, fv)
        return Scheme(tuple(sorted(fv)), (), t)

    # ---- the Scott scheme of a datum: what it is when applied

    def scott(self, t: TCon) -> Optional[Type]:
        r = self.fresh()
        if t.name in self.types:
            conts = [_arrows([self.field(f) for f in c.fields], r)
                     for c in self.types[t.name].ctors]
            return _scott(conts, r, t.name)
        if t.name == "fuel":
            return _scott([r, TArrow(FUEL, r)], r, "fuel")
        if t.name == "list":
            (a,) = t.args
            return _scott([r, _arrows([a, _list(a)], r)], r, "list")
        if t.name == "cell":
            a, b = t.args
            return _scott([_arrows([a, b], r)], r, "cell")
        return None

    def field(self, name: str) -> Type:
        if name in self.types:
            return TCon(name)
        raise _Fail(f"{name!r} is not a declared type")

    # ---- unification, oriented: expected against given; equirecursive

    def bind(self, v: TVar, t: Type) -> None:
        t = resolve(t)
        if t is v:
            return
        if v.data:
            if isinstance(t, TArrow):
                if not t.elim:
                    raise _Fail("an operand of 'EQ' is a function "
                                f"({render_type(t)}); a value of function type "
                                "cannot be compared")
                t.datum = True
            if isinstance(t, TVar):
                t.data = True
        v.ref = t

    def unify(self, expected: Type, given: Type,
              seen: Optional[Set[Tuple[int, int]]] = None) -> None:
        seen = set() if seen is None else seen
        e, g = resolve(expected), resolve(given)
        if e is g:
            return
        if isinstance(e, TVar):
            self.bind(e, g)
            return
        if isinstance(g, TVar):
            self.bind(g, e)
            return
        key = (id(e), id(g))
        if key in seen:                          # a cycle: assumed to hold
            return
        seen.add(key)
        if isinstance(e, TArrow) and isinstance(g, TArrow):
            if g.elim and not e.elim:
                # a datum-shaped unknown used where a function is wanted:
                # fine, a datum is its own case function
                pass
            elif e.elim and not g.elim:
                if e.nominal is not None or e.datum:
                    what = f"a value of type {e.nominal}" if e.nominal else "a datum"
                    raise _Fail(f"a function ({render_type(g)}) where {what} "
                                f"is expected; a function is not a datum")
                e.elim = False                   # it was a function all along
            elif e.elim and g.elim:
                if e.nominal and g.nominal and e.nominal != g.nominal:
                    raise _Fail(f"expected {e.nominal}, found {g.nominal}")
                nm = e.nominal or g.nominal
                e.nominal = g.nominal = nm
                e.datum = g.datum = e.datum or g.datum
            self.unify(g.param, e.param, seen)   # parameters flip
            self.unify(e.result, g.result, seen)
            return
        if isinstance(e, TArrow) and isinstance(g, TCon):
            if e.checked == g.name:              # already validated as this datum
                return
            if e.elim and e.nominal is not None and e.nominal != g.name:
                raise _Fail(f"expected {e.nominal}, found {g.name}")
            sc = self.scott(g)                   # a datum, applied
            if sc is None:
                raise _Fail(f"expected {render_type(e)}, found {g.name}")
            if e.elim:
                e.nominal = g.name
            e.checked = g.name                   # coinductively: a cycle meeting T again holds
            try:
                self.unify(e, sc, seen)
            except _Fail:
                e.checked = None
                raise
            return
        if isinstance(e, TCon) and isinstance(g, TArrow):
            if not g.elim:
                raise _Fail(f"a function ({render_type(g)}) where a value of "
                            f"type {render_type(e)} is expected; a function "
                            f"is not a datum")
            if g.nominal is not None and g.nominal != e.name:
                raise _Fail(f"expected {render_type(e)}, found {g.nominal}")
            if g.checked == e.name:
                return
            sc = self.scott(e)
            if sc is None:
                raise _Fail(f"expected {render_type(e)}, found a function")
            g.nominal = e.name
            g.checked = e.name
            try:
                self.unify(g, sc, seen)          # what was asked of it, against what it provides
            except _Fail:
                g.checked = None
                raise
            return
        assert isinstance(e, TCon) and isinstance(g, TCon)
        if e.name != g.name or len(e.args) != len(g.args):
            raise _Fail(f"expected {render_type(e)}, found {render_type(g)}")
        for ea, ga in zip(e.args, g.args):
            self.unify(ea, ga, seen)

    # ---- the environment

    def builtin(self, name: str) -> Optional[Scheme]:
        v = self.fresh
        if name == "S":
            a, b, c = v(), v(), v()
            return self.close(_arrows([_arrows([a, b], c), TArrow(a, b), a], c))
        if name == "K":
            a, b = v(), v()
            return self.close(_arrows([a, b], a))
        if name == "I":
            a = v()
            return self.close(TArrow(a, a))
        if name == "B":
            a, b, c = v(), v(), v()
            return self.close(_arrows([TArrow(b, c), TArrow(a, b), a], c))
        if name == "C":
            a, b, c = v(), v(), v()
            return self.close(_arrows([_arrows([a, b], c), b, a], c))
        if name == "W":
            a, b = v(), v()
            return self.close(_arrows([_arrows([a, a], b), a], b))
        if name == "Y":
            a = v()
            return self.close(TArrow(TArrow(a, a), a))
        if name == "pair":
            a, b = v(), v()
            return self.close(_arrows([a, b], _cell(a, b)))
        if name == "hd":
            a, b = v(), v()
            return self.close(TArrow(_cell(a, b), a))
        if name == "tl":
            a, b = v(), v()
            return self.close(TArrow(_cell(a, b), b))
        if name == "nil":
            a = v()
            return self.close(_list(a))
        if name == "cons":
            a = v()
            return self.close(_arrows([a, _list(a)], _list(a)))
        if name == "zero":
            return Scheme((), (), FUEL)
        if name == "suc":
            return Scheme((), (), TArrow(FUEL, FUEL))
        # the numeral operations (expand.NAT_NAMES) serve any type declared
        # as `Zero | Suc t`, whatever its name, so here they only tie their
        # operands, and a test's two outcomes, to one type each
        if name in ("natAdd", "natSub", "natMul"):
            a = v()
            return self.close(_arrows([a, a], a))
        if name in ("natIfEq", "natIfLe"):
            a, b = v(), v()
            return self.close(_arrows([a, a, b, b], b))
        return None

    # ---- inference over macro-expanded bodies

    def lookup(self, name: str, bound: Dict[str, Type], core: Optional[str]) -> Type:
        if name in bound:
            return bound[name]
        if name in ISA:
            s = self.builtin(name)
            assert s is not None
            return self.instantiate(s)
        if core is not None:
            key = f"{core}.{name}"
            if key in self.mono:
                return self.mono[key]
            if name in self.core_env.get(core, {}):
                return self.instantiate(self.core_env[core][name])
        if name in self.mono:
            return self.mono[name]
        if name in self.env:
            return self.instantiate(self.env[name])
        s = self.builtin(name)
        if s is not None:
            return self.instantiate(s)
        raise _Fail(f"unresolved name {name!r}")

    def infer(self, e: A.Expr, bound: Dict[str, Type], core: Optional[str]) -> Type:
        if isinstance(e, A.Name):
            return self.lookup(e.name, bound, core)
        if isinstance(e, A.Lambda):
            p = self.fresh()
            body = self.infer(e.body, {**bound, e.param: p}, core)
            return TArrow(p, body)
        if isinstance(e, A.App):
            args: List[A.Expr] = []
            head: A.Expr = e
            while isinstance(head, A.App):
                args.append(head.arg)
                head = head.fn
            args.reverse()
            tf = self.infer(head, bound, core)
            is_eq = isinstance(head, A.Name) and head.name == "EQ"
            for i, x in enumerate(args):
                tx = self.infer(x, bound, core)
                if is_eq and i < 2:
                    d = self.fresh(data=True)
                    self.unify(d, tx)
                    tx = d
                r = self.fresh()
                self.unify(TArrow(tx, r, elim=True), tf)
                tf = r
            return tf
        if isinstance(e, A.Cell):
            items = [self.infer(item, bound, core) for item in e.items]
            cell_t = items[-1]
            for item_t in reversed(items[:-1]):
                cell_t = _cell(item_t, cell_t)
            return cell_t
        if isinstance(e, A.Pick):
            pick_t = self.infer(e.expr, bound, core)
            for bit in bin(e.axis)[3:]:          # after the leading 1: 0 head, 1 tail
                a, b = self.fresh(), self.fresh()
                self.unify(_cell(a, b), pick_t)
                pick_t = a if bit == "0" else b
            return pick_t
        if isinstance(e, A.Case):
            first = e.branches[0][0]
            if first not in self.ctor_of:
                raise _Fail(f"undeclared constructor {first!r} in a case branch")
            decl = self.ctor_of[first]
            self.unify(TCon(decl.name), self.infer(e.scrutinee, bound, core))
            result = self.fresh()
            fields = {c.name: c.fields for c in decl.ctors}
            for cname, cbinders, cbody in e.branches:
                if cname not in fields or len(cbinders) != len(fields[cname]):
                    raise _Fail(f"branch {cname!r} does not fit type {decl.name!r}")
                inner: Dict[str, Type] = {**bound, **{b: self.field(f) for b, f in zip(cbinders, fields[cname])}}
                self.unify(result, self.infer(cbody, inner, core))
            return result
        return self.fresh()                  # a Quote/Scry/NsLit here: the expander refuses it

    # ---- declarations

    def run(self) -> List[Problem]:
        from .expand import expand_macros           # the same pass codegen runs
        prog = self.program
        macros: Dict[str, A.Macro] = {}
        for d in prog.decls:
            if isinstance(d, A.TypeDecl):
                self.types[d.name] = d
                for c in d.ctors:
                    self.ctor_of[c.name] = d
            elif isinstance(d, A.Macro):
                macros[d.name] = d

        for d in self.types.values():
            for c in d.ctors:
                try:
                    self.env[c.name] = Scheme((), (), _arrows(
                        [self.field(f) for f in c.fields], TCon(d.name)))
                except _Fail as ex:
                    self.add(Site("type", d.name), f"constructor {c.name!r}: {ex}")
                    self.env[c.name] = Scheme((), (), TCon(d.name))

        obj = lt = answer = None
        try:
            obj = find_object_type(prog)
            if obj is not None:
                lt = find_loop_types(prog, obj)
                answer = find_answer_type(prog, obj, lt)
        except GenerateError:
            pass                                  # the generator reports these

        object_t = TCon(obj.name) if obj is not None else None
        runs: List[A.Def] = []
        for d in prog.decls:
            if isinstance(d, A.Def) and isinstance(d.expr, A.Quote):
                if d.expr.fuel is None and d.expr.interp is None:
                    if object_t is not None:
                        self.env[d.name] = Scheme((), (), object_t)
                else:
                    runs.append(d)
            elif isinstance(d, A.Def) and isinstance(d.expr, A.NsLit):
                if object_t is not None and answer is not None:
                    self.env[d.name] = Scheme((), (), TArrow(object_t, TCon(answer.decl.name)))

        Item = Tuple[str, Optional[str], Tuple[str, ...], A.Expr, Site]
        items: List[Item] = []
        for d in prog.decls:
            if isinstance(d, A.Equation):
                items.append((d.name, None, d.binders, d.body, Site("equation", d.name)))
            elif isinstance(d, A.Def) and not isinstance(d.expr, (A.Quote, A.NsLit)):
                items.append((d.name, None, (), d.expr, Site("definition", d.name)))
            elif isinstance(d, A.Core):
                for eq in d.equations:
                    items.append((eq.name, d.name, tuple(d.params) + tuple(eq.binders),
                                  eq.body, Site("equation", eq.name, d.name)))
        keys = {(f"{core}.{name}" if core else name) for name, core, *_ in items}
        expanded: Dict[str, A.Expr] = {}
        item_of: Dict[str, Item] = {}
        deps: Dict[str, Set[str]] = {}
        for it in items:
            name, core, binders, body, site = it
            key = f"{core}.{name}" if core else name
            item_of[key] = it
            expanded[key] = expand_macros(body, macros)   # its errors are its own
            deps[key] = set()
            for nm in _names(expanded[key]):
                if nm in binders:
                    continue
                if core is not None and f"{core}.{nm}" in keys:
                    deps[key].add(f"{core}.{nm}")
                elif nm in keys:
                    deps[key].add(nm)
        for group in _sccs(keys, deps):
            self.infer_group(group, item_of, expanded)

        for d in prog.decls:                      # a core's name denotes its loop
            if isinstance(d, A.Core) and obj is not None and is_interpreter_core(d, obj):
                loop = self.core_env.get(d.name, {}).get("loop")
                if loop is not None:
                    self.env[d.name] = loop

        for d in prog.decls:
            if isinstance(d, A.Sig) and d.name in self.env:
                try:
                    sig = _arrows([self.field(t) for t in d.types[:-1]],
                                  self.field(d.types[-1]))
                    self.unify(sig, self.instantiate(self.env[d.name]))
                except _Fail as ex:
                    self.add(Site("signature", d.name),
                             f"declared {' -> '.join(d.types)}, inferred "
                             f"{render_type(self.instantiate(self.env[d.name]))}: {ex}")

        for d in runs:
            assert isinstance(d.expr, A.Quote)
            if object_t is None or lt is None:
                continue
            try:
                self.run_decl(d, d.expr, macros, object_t, lt.result.name)
            except _Fail as ex:
                self.add(Site("definition", d.name), str(ex))
        return self.problems

    def run_decl(self, d: A.Def, q: A.Quote, macros, object_t: Type,
                 result_name: str) -> None:
        from .expand import expand_macros
        head: A.Expr = q.interp if q.interp is not None else A.Name("whnfF")
        args: List[A.Expr] = []
        while isinstance(head, A.App):
            args.append(head.arg)
            head = head.fn
        args.reverse()
        if not isinstance(head, A.Name) or head.name not in self.env:
            return                                # the expander reports it
        t = self.instantiate(self.env[head.name])
        for x in args:
            tx = self.infer(expand_macros(x, macros), {}, None)
            r = self.fresh()
            self.unify(TArrow(tx, r, elim=True), t)
            t = r
        r = self.fresh()
        self.unify(_arrows([FUEL, object_t], r), t)
        self.unify(TCon(result_name), r)
        self.env[d.name] = Scheme((), (), TCon(result_name))

    def infer_group(self, group: List[str], item_of, expanded) -> None:
        for key in group:
            self.mono[key] = self.fresh()
        results: Dict[str, Type] = {}
        for key in group:
            name, core, binders, body, site = item_of[key]
            try:
                bound: Dict[str, Type] = {b: self.fresh() for b in binders}
                t = _arrows([bound[b] for b in binders],
                            self.infer(expanded[key], bound, core))
                self.unify(self.mono[key], t)
                results[key] = t
            except _Fail as ex:
                self.add(site, str(ex))
                results[key] = self.fresh()
        for key in group:
            del self.mono[key]
        for key in group:
            name, core, *_ = item_of[key]
            s = self.generalize(results[key])
            if core is None:
                self.env[name] = s
            else:
                self.core_env.setdefault(core, {})[name] = s

    def add(self, site: Site, message: str) -> None:
        self.problems.append(Problem(TypeMismatchError, site, message))


def _names(e: A.Expr, out: Optional[Set[str]] = None) -> Set[str]:
    out = set() if out is None else out
    if isinstance(e, A.Name):
        out.add(e.name)
    elif isinstance(e, A.App):
        _names(e.fn, out)
        _names(e.arg, out)
    elif isinstance(e, A.Lambda):
        _names(e.body, out)
    elif isinstance(e, A.Cell):
        for x in e.items:
            _names(x, out)
    elif isinstance(e, A.Pick):
        _names(e.expr, out)
    elif isinstance(e, A.Case):
        _names(e.scrutinee, out)
        for _, _, body in e.branches:
            _names(body, out)
    return out


def _sccs(keys: Set[str], deps: Dict[str, Set[str]]) -> List[List[str]]:
    """Tarjan's algorithm; groups in dependency order, callees first."""
    index: Dict[str, int] = {}
    low: Dict[str, int] = {}
    stack: List[str] = []
    on: Set[str] = set()
    out: List[List[str]] = []
    counter = [0]

    def visit(v: str) -> None:
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        for w in sorted(deps.get(v, ())):
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            group: List[str] = []
            while True:
                w = stack.pop()
                on.discard(w)
                group.append(w)
                if w == v:
                    break
            out.append(group)

    for v in sorted(keys):
        if v not in index:
            visit(v)
    return out


def typecheck_program(program: A.Program, prelude: Sequence[str] = (), *,
                      generated: bool = False) -> List[Problem]:
    """Every Stage B problem in ``program``.  Never raises for a program
    problem, and never rewrites anything.  Stage B types the generated
    interface forms too, so unless ``generated`` says the program already
    carries them, they are generated first (into a copy)."""
    if not generated:
        from .expand import _generate
        program = _generate(program)
    return _Types(program, prelude).run()


def typecheck(program: A.Program, prelude: Sequence[str] = (), *,
              generated: bool = False) -> None:
    """Run Stage B and raise :class:`TypeMismatchError` if anything is wrong,
    with every problem in the message and on ``.problems``."""
    problems = typecheck_program(program, prelude, generated=generated)
    if problems:
        n = len(problems)
        msg = f"{n} Stage B problem{'s' if n > 1 else ''}:\n" + "\n".join(
            f"  {p}" for p in problems)
        err = TypeMismatchError(msg)
        err.problems = tuple(problems)
        raise err
