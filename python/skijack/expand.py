"""The code generator: syntax tree -> closed ``{S,K,I}`` terms.

Scope of this step: no types (Stage B, ``DESIDERATA.md`` item 11) and no
quotation / level-1 packaging (``SURFACE-LANGUAGE-DESIGN.md`` §6a).  A
``Quote``, ``Scry`` or ``NsLit`` reaching the code generator is a clear
:class:`ExpandError`.

The passes, in order:

1. **macro expansion** -- ``:=*`` macros are rewritten at each use site
   with all parameters supplied; substitution is capture avoiding.
   ``:=!`` is refused.
2. **case forms** -- ``x |> { C1 bs1 b1 ; ... }`` becomes ``x`` applied
   to one continuation per constructor *in declaration order*, each
   continuation the body abstracted over its binders.
3. **cells and picks** -- ``[a b]`` is ``pair a b``; ``2@p`` is ``hd p``
   and ``3@p`` is ``tl p``, and axis ``n`` in general is the chain of
   heads and tails Nock's numbering gives.
4. **cores** -- per-equation fixpoints: a self-recursive equation becomes
   ``Y gen`` where ``gen`` takes the equation itself as its first parameter,
   the way ``tower_harness.py`` writes ``wfGen``/``whnfF``.  A
   non-recursive equation is a plain ``D``.  Every lambda (a case branch with
   binders, or a ``\\x.e``) is lambda-lifted into its own supercombinator
   over the enclosing binders that occur free in it.
5. **bracket abstraction** -- ``aviary_kernel.abstraction.expand`` by way
   of the artifact's ``D`` / ``AL`` idiom.  Nothing here reimplements it.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Set, Tuple

from aviary_kernel.abstraction import (bracket_abstract as _bracket_abstract,
                                       expand as _ski_expand)
from aviary_kernel.birds import BY_NAME
from .abi import TIER1_NAMES
from aviary_kernel.environment import Environment
from aviary_kernel.terms import Atom, App as KApp, Term, pretty, size

from . import ast as A
from .generate import (AnswerType, ObjectType, PathType, find_answer_type,
                       find_loop_types, find_object_type, find_path_type,
                       generate as _generate)
from .check import check as _check
from .quote import Encoder, level1_names

__all__ = ["ExpandError", "Expansion", "expand_program", "PRELUDE_NAMES",
           "ISA_NAMES", "Level1Program", "FUEL_PLACEHOLDER"]

#: the free atom that stands in for elided fuel, ``<t>@[]`` -- the
#: runtime's policy supplies the real numeral (``RUNTIME-DESIGN.md`` §3c)
FUEL_PLACEHOLDER = Atom("\x00fuel")


from .errors import SkijackError

class ExpandError(SkijackError):
    pass


def a(name: str) -> Atom:
    return Atom(name)


v = a


def K_(*terms: Term) -> Term:
    r = terms[0]
    for t in terms[1:]:
        r = KApp(r, t)
    return r


#: names the expander installs before the program is seen.  ``pair`` /
#: ``hd`` / ``tl`` are the Scott pair and its projections
#: (``SURFACE-LANGUAGE-DESIGN.md`` §2); the rest are the aviary kernel's
#: own built-ins, reached by name.
PRELUDE_NAMES = ("pair", "hd", "tl", "nil", "cons", "zero", "suc")

#: the three primitives.  ``SURFACE-LANGUAGE-DESIGN.md`` §6b keeps two
#: symbol tables: outside quotation these names are the ISA, inside it
#: they are the object type's constructors.  Quotation is a later step,
#: so here they are always the ISA -- which is what ``EXAMPLES.md`` §4
#: means by "outside it they would be the level-0 combinators" even
#: though ``term5 === S | K | I | ...`` declares constructors of those
#: names.
ISA_NAMES = ("S", "K", "I")

#: aviary kernel built-ins a program may name directly
_BUILTIN_OK = set(TIER1_NAMES)


# ---------------------------------------------------------------- utilities

def free_names(e: A.Expr) -> Set[str]:
    """Names occurring free in an expression (binders of ``Lambda`` and of
    case branches bind)."""
    if isinstance(e, A.Name):
        return {e.name}
    if isinstance(e, A.App):
        return free_names(e.fn) | free_names(e.arg)
    if isinstance(e, A.Cell):
        out: Set[str] = set()
        for x in e.items:
            out |= free_names(x)
        return out
    if isinstance(e, A.Pick):
        return free_names(e.expr)
    if isinstance(e, A.Lambda):
        return free_names(e.body) - {e.param}
    if isinstance(e, A.Case):
        out = free_names(e.scrutinee)
        for cname, binders, body in e.branches:
            out |= {cname}
            out |= (free_names(body) - set(binders))
        return out
    if isinstance(e, A.Quote):
        out = free_names(e.expr)
        if e.interp is not None:
            out |= free_names(e.interp)
        return out
    if isinstance(e, A.Scry):
        return _path_names(e.path)
    if isinstance(e, A.NsLit):
        out = set()
        for p, val in e.facts:
            out |= _path_names(p) | free_names(val)
        return out
    raise TypeError(f"free_names: {e!r}")


def _path_names(p: A.Path) -> Set[str]:
    out: Set[str] = set()
    for seg in p.segments:
        if seg.payload is not None:
            out |= free_names(seg.payload)
    return out


def _fresh(base: str, taken: Set[str]) -> str:
    if base not in taken:
        return base
    i = 0
    while f"{base}{i}" in taken:
        i += 1
    return f"{base}{i}"


def substitute(e: A.Expr, sub: Dict[str, A.Expr]) -> A.Expr:
    """Capture-avoiding substitution of names by expressions."""
    if not sub:
        return e
    if isinstance(e, A.Name):
        return sub.get(e.name, e)
    if isinstance(e, A.App):
        return A.App(substitute(e.fn, sub), substitute(e.arg, sub))
    if isinstance(e, A.Cell):
        return A.Cell(tuple(substitute(x, sub) for x in e.items))
    if isinstance(e, A.Pick):
        return A.Pick(e.axis, substitute(e.expr, sub))
    if isinstance(e, A.Lambda):
        param, body = _rename_binders(e.param, e.body, sub)
        inner = {k: t for k, t in sub.items() if k != param}
        return A.Lambda(param, substitute(body, inner))
    if isinstance(e, A.Case):
        branches = []
        for cname, binders, body in e.branches:
            nb = list(binders)
            for i, b in enumerate(binders):
                nb[i], body = _rename_binders(b, body, sub)
            inner = {k: t for k, t in sub.items() if k not in nb}
            branches.append((cname, tuple(nb), substitute(body, inner)))
        return A.Case(substitute(e.scrutinee, sub), tuple(branches))
    if isinstance(e, A.Quote):
        return A.Quote(substitute(e.expr, sub), e.fuel,
                       None if e.interp is None else substitute(e.interp, sub))
    if isinstance(e, (A.Scry, A.NsLit)):
        raise ExpandError(
            "quotation, scry and namespace literals are not handled by this "
            "step of the expander")
    raise TypeError(f"substitute: {e!r}")


def _rename_binders(binder: str, body: A.Expr, sub: Dict[str, A.Expr]):
    """Alpha-rename ``binder`` if it would capture a name free in one of
    the substituted expressions."""
    danger: Set[str] = set()
    for k, t in sub.items():
        if k == binder:
            continue
        if k in free_names(body):
            danger |= free_names(t)
    if binder not in danger:
        return binder, body
    taken = danger | free_names(body) | set(sub)
    fresh = _fresh(binder + "_", taken)
    return fresh, substitute(body, {binder: A.Name(fresh)})


# ------------------------------------------------------------- pass 1: macros

#: nested macro unfoldings on one path before we call it a non-fixpoint
_MACRO_FUEL = 100

#: structural nesting of one expression.  Deep corpus expressions reach
#: 11, so this is generous; it exists because the passes below this one
#: (``lower``, ``_Codegen.gen``, ``free_names``, ``substitute``) recurse,
#: and without it a deep enough expression is a ``RecursionError`` from
#: somewhere internal rather than a located error.
_MAX_DEPTH = 256

#: total macro substitutions in one declaration.  ``_MACRO_FUEL`` bounds
#: the *depth* of unfolding and not the *work*: a chain of macros each
#: using its predecessor twice costs 2^n substitutions at depth n, so a
#: forty-line file can run for hours and yield a one-atom term.  This
#: bounds the work.
_MACRO_WORK = 200_000


def _spine(e: A.Expr) -> Tuple[A.Expr, List[A.Expr]]:
    args: List[A.Expr] = []
    while isinstance(e, A.App):
        args.append(e.arg)
        e = e.fn
    args.reverse()
    return e, args


def expand_macros(e: A.Expr, macros: Dict[str, A.Macro], depth: int = 0,
                  unfold: int = 0, budget: Optional[Dict[str, int]] = None
                  ) -> A.Expr:
    """Expand macros to a fixpoint.

    Three separate limits, because they fail in three different ways.
    ``depth`` is structural nesting of the expression; ``unfold`` counts
    macro substitutions along one path; ``budget`` counts substitutions
    in total.  Conflating the first two is what once reported a
    102-application expression in a macro-free program as ``macro
    expansion did not reach a fixpoint``.
    """
    if budget is None:
        budget = {"work": _MACRO_WORK}
    if depth > _MAX_DEPTH:
        raise ExpandError(
            f"expression nests more than {_MAX_DEPTH} levels deep")
    if unfold > _MACRO_FUEL:
        raise ExpandError(
            f"macro expansion did not reach a fixpoint after {_MACRO_FUEL} "
            f"nested unfoldings")
    if budget["work"] <= 0:
        raise ExpandError(
            f"macro expansion exceeded {_MACRO_WORK:,} substitutions; a "
            f"macro that uses another twice costs exponentially in its "
            f"nesting depth")
    if isinstance(e, A.Name):
        if e.name in macros:
            m = macros[e.name]
            if m.params:
                raise ExpandError(
                    f"macro {m.name!r} takes {len(m.params)} parameter(s); "
                    f"partial application of a macro is an error")
            budget['work'] -= 1
            return expand_macros(m.body, macros, depth, unfold + 1, budget)
        return e
    if isinstance(e, A.App):
        head, args = _spine(e)
        if isinstance(head, A.Name) and head.name in macros:
            m = macros[head.name]
            if m.capturing:
                raise ExpandError(
                    f"macro {m.name!r} is declared capturing (':=!'); the "
                    f"capturing form is not implemented")
            n = len(m.params)
            if len(args) < n:
                raise ExpandError(
                    f"macro {m.name!r} takes {n} parameter(s) but got "
                    f"{len(args)}; partial application of a macro is an error")
            args = [expand_macros(x, macros, depth + 1, unfold, budget)
                    for x in args]
            body = substitute(m.body, dict(zip(m.params, args[:n])))
            budget['work'] -= 1
            out = expand_macros(body, macros, depth, unfold + 1, budget)
            for extra in args[n:]:
                out = A.App(out, extra)
            return out
        return A.App(expand_macros(e.fn, macros, depth + 1, unfold, budget),
                     expand_macros(e.arg, macros, depth + 1, unfold, budget))
    if isinstance(e, A.Cell):
        return A.Cell(tuple(expand_macros(x, macros, depth + 1, unfold, budget)
                            for x in e.items))
    if isinstance(e, A.Pick):
        return A.Pick(e.axis, expand_macros(e.expr, macros, depth + 1, unfold, budget))
    if isinstance(e, A.Lambda):
        inner = {k: m for k, m in macros.items() if k != e.param}
        return A.Lambda(e.param, expand_macros(e.body, inner, depth + 1, unfold, budget))
    if isinstance(e, A.Case):
        branches = []
        for cname, binders, body in e.branches:
            inner = {k: m for k, m in macros.items() if k not in binders}
            branches.append((cname, binders,
                             expand_macros(body, inner, depth + 1, unfold, budget)))
        return A.Case(expand_macros(e.scrutinee, macros, depth + 1, unfold, budget),
                      tuple(branches))
    if isinstance(e, (A.Quote, A.Scry, A.NsLit)):
        raise ExpandError(
            "quotation, scry and namespace literals are out of scope for "
            "this step of the expander")
    raise TypeError(f"expand_macros: {e!r}")


# ------------------------------------------ pass 2 and 3: cases, cells, picks

def axis_chain(n: int) -> List[str]:
    """The head/tail chain for Nock axis ``n``, outermost last.

    Axis 1 is the whole; axis ``2n`` is the head of axis ``n`` and
    ``2n+1`` its tail, so the bits of ``n`` below the leading one spell
    the walk from the root: 0 for ``hd``, 1 for ``tl``.
    """
    if n < 1:
        raise ExpandError(f"axis {n} does not exist; axes start at 1")
    bits = bin(n)[3:]          # drop '0b1'
    return ["hd" if b == "0" else "tl" for b in bits]


def desugar(e: A.Expr, ctors: Dict[str, Tuple[str, int, int]],
            types: Dict[str, A.TypeDecl]) -> A.Expr:
    """Passes 2 and 3: case forms, cells and picks become applications.

    Named ``desugar`` and not ``lower`` because ``lower`` is the name of
    a law: ``lower`` takes a syntax tree to its closed term
    (``DESIDERATA.md`` item 4, and :func:`skijack.dictionary.lower`).
    This pass is tree to tree.
    """
    if isinstance(e, A.Name):
        return e
    if isinstance(e, A.App):
        return A.App(desugar(e.fn, ctors, types), desugar(e.arg, ctors, types))
    if isinstance(e, A.Lambda):
        return A.Lambda(e.param, desugar(e.body, ctors, types))
    if isinstance(e, A.Cell):
        items = [desugar(x, ctors, types) for x in e.items]
        out = items[-1]
        for x in reversed(items[:-1]):
            out = A.App(A.App(A.Name("pair"), x), out)
        return out
    if isinstance(e, A.Pick):
        out = desugar(e.expr, ctors, types)
        for step in axis_chain(e.axis):
            out = A.App(A.Name(step), out)
        return out
    if isinstance(e, A.Case):
        return _lower_case(e, ctors, types)
    raise ExpandError(f"cannot compile {type(e).__name__} in this step")


def _lower_case(e: A.Case, ctors, types) -> A.Expr:
    if not e.branches:
        raise ExpandError("a case form needs at least one branch")
    first = e.branches[0][0]
    if first not in ctors:
        raise ExpandError(f"undeclared constructor {first!r} in a case branch")
    tname = ctors[first][0]
    decl = types[tname]
    seen: Dict[str, Tuple[Tuple[str, ...], A.Expr]] = {}
    for cname, binders, body in e.branches:
        if cname not in ctors or ctors[cname][0] != tname:
            raise ExpandError(
                f"case branch {cname!r} is not a constructor of {tname!r}")
        if cname in seen:
            raise ExpandError(f"case branch {cname!r} appears twice")
        seen[cname] = (binders, body)
    missing = [c.name for c in decl.ctors if c.name not in seen]
    if missing:
        raise ExpandError(
            f"case over {tname!r} is missing branch(es) for "
            f"{', '.join(missing)}; case must be complete "
            f"(DESIDERATA.md item 11, Stage A)")
    out = desugar(e.scrutinee, ctors, types)
    for c in decl.ctors:                     # declaration order is the ABI
        binders, body = seen[c.name]
        k = desugar(body, ctors, types)
        for b in reversed(binders):
            k = A.Lambda(b, k)
        out = A.App(out, k)
    return out


# --------------------------------------------------- passes 4 and 5: codegen

@dataclass
class Level1Program:
    """A ``name := I |- <t>@n`` declaration, packaged
    (``SURFACE-LANGUAGE-DESIGN.md`` §6, "Level 1, virtualized").

    The executable the host reduces is ``interp fuel datum``.  When the
    fuel was elided (``@[]``) there is no closed term until the runtime's
    policy supplies a numeral (``RUNTIME-DESIGN.md`` §3c); :attr:`term`
    then raises and :meth:`with_fuel` builds it.
    """
    name: str
    interp: str                      #: the interpreter core's name
    interp_term: Term
    datum: Term
    fuel: object                     #: an ``int``, or :data:`ast.POLICY`
    object_type: ObjectType
    result_type: A.TypeDecl
    zero: Term
    suc: Term
    params: Tuple[Term, ...] = ()   #: the interpreter core's arguments

    def numeral(self, k: int) -> Term:
        t = self.zero
        for _ in range(k):
            t = KApp(self.suc, t)
        return t

    def _apply(self, fuel: Term) -> Term:
        t = self.interp_term
        for p in self.params:          # the interpreter's own parameters
            t = KApp(t, p)             # come before its fuel
        return KApp(KApp(t, fuel), self.datum)

    def with_fuel(self, k: int) -> Term:
        """The closed executable at fuel ``k``."""
        return self._apply(self.numeral(k))

    @property
    def placeholder(self) -> Term:
        """The executable with :data:`FUEL_PLACEHOLDER` where the numeral
        goes -- an open term, for inspection only."""
        return self._apply(FUEL_PLACEHOLDER)

    @property
    def term(self) -> Term:
        if not isinstance(self.fuel, int):
            raise ExpandError(
                f"{self.name!r} has elided fuel ('@[]'); it has no closed "
                f"term until the runtime policy picks a budget -- use "
                f"with_fuel(k), or run.run_policy()")
        return self.with_fuel(self.fuel)


@dataclass
class Expansion:
    """The result of :func:`expand_program`."""
    terms: Dict[str, Term] = field(default_factory=dict)
    sizes: Dict[str, int] = field(default_factory=dict)
    helpers: Dict[str, Term] = field(default_factory=dict)
    backend: Dict[str, str] = field(default_factory=dict)
    env: Optional[Environment] = None
    types: Dict[str, A.TypeDecl] = field(default_factory=dict)
    ctors: Dict[str, Tuple[str, int, int]] = field(default_factory=dict)
    level1: Dict[str, Level1Program] = field(default_factory=dict)
    object_type: Optional[ObjectType] = None
    answer_type: Optional[AnswerType] = None
    path_type: Optional[PathType] = None
    #: name -> the (key datum, answer datum) pairs of a namespace literal
    namespaces: Dict[str, Tuple[Tuple[Term, Term], ...]] = field(
        default_factory=dict)
    #: backend rule name -> (kind, label), for every rule the expander
    #: defined with formals: kind is prelude, ctor, eq, rec (a recursion's
    #: body), code (a group member's body), group (a group's tuple, pick,
    #: sel or gen) or lift; the label is the source name it serves.
    #: Bookkeeping only: no term depends on it (skijack.templates).
    rule_kinds: Dict[str, Tuple[str, str]] = field(default_factory=dict)

    def term(self, name: str) -> Term:
        return self.terms[name]

    def size(self, name: str) -> int:
        return self.sizes[name]

    def text(self, name: str) -> str:
        return pretty(self.terms[name])


class _Codegen:
    def __init__(self, env: Environment, resolve, helper_names=None, kinds=None):
        self.env = env
        self.resolve = resolve          # source name -> backend Atom, or None
        self.helper_names: List[str] = ([] if helper_names is None
                                        else helper_names)
        #: shared with Expansion.rule_kinds: each lift's kind and label
        self.kinds: Dict[str, Tuple[str, str]] = {} if kinds is None else kinds

    def with_resolver(self, resolve) -> "_Codegen":
        """The same code generator under a different name environment --
        one per core, so a core's equations see their siblings first."""
        return _Codegen(self.env, resolve, self.helper_names, self.kinds)

    def gen(self, e: A.Expr, scope: Sequence[str], owner: str) -> Term:
        """Compile ``e``; ``scope`` is the enclosing binder list in order."""
        if isinstance(e, A.Name):
            if e.name in scope:
                return v(e.name)
            t = self.resolve(e.name)
            if t is None:
                raise ExpandError(
                    f"unresolved name {e.name!r} in {owner!r}; free variables "
                    f"do not exist at runtime (SYNTAX.md §8)")
            return t
        if isinstance(e, A.App):
            return KApp(self.gen(e.fn, scope, owner),
                        self.gen(e.arg, scope, owner))
        if isinstance(e, A.Lambda):
            return self.lift(e, scope, owner)
        raise ExpandError(f"cannot compile {type(e).__name__} in {owner!r}")

    def lift(self, lam: A.Lambda, scope: Sequence[str], owner: str) -> Term:
        """Lambda-lift a lambda chain into its own supercombinator."""
        params: List[str] = []
        body: A.Expr = lam
        while isinstance(body, A.Lambda):
            params.append(body.param)
            body = body.body
        fv = free_names(body) - set(params)
        captured = [s for s in scope if s in fv]
        name = _fresh_name(f"{owner}_b", self.env, len(self.helper_names))
        inner_scope = list(captured) + params
        term = self.gen(body, inner_scope, owner)
        self.env.define_rule(name, tuple(inner_scope), term)
        self.helper_names.append(name)
        self.kinds[name] = ("lift", owner)
        out: Term = a(name)
        for c in captured:
            out = KApp(out, v(c))
        return out


_counter = {"n": 0}


def _fresh_name(base: str, env: Environment, _i: int) -> str:
    _counter["n"] += 1
    name = f"{base}{_counter['n']}"
    while env.lookup(name) is not None:
        _counter["n"] += 1
        name = f"{base}{_counter['n']}"
    return name


def _mangle(name: str, used: Set[str]) -> str:
    """A backend name for a source name.

    The aviary kernel refuses to shadow a built-in bird, so an equation called
    ``C`` is defined as ``Cc`` (the form recorded in ``EXAMPLES.md``'s
    codegen notes).  The mangling never changes the compiled term.
    """
    cand = name
    while cand in BY_NAME or cand in used:
        cand = cand + name[0].lower()
    return cand


# -------------------------------------------------------------- the driver

def expand_program(program: A.Program, env: Optional[Environment] = None,
                   generate_forms: bool = True, check: bool = True
                   ) -> Expansion:
    """Compile a program to closed ``{S,K,I}`` terms, one per name.

    With ``check`` (the default), Stage A runs first, over the *parsed*
    program and before generation; it can only reject
    (``DESIDERATA.md`` item 11), so the output is the same whether
    checking is on or off.  With ``generate_forms`` (the default),
    :func:`skijack.generate.generate` then adds the type-generated forms
    -- the walker, the rebuilder, the default ISA step equations and each
    interpreter core's ``step`` and fuel loop -- as surface declarations.
    """
    if env is None:
        env = Environment()
    _counter["n"] = 0
    if check:
        _check(program, PRELUDE_NAMES)
    if generate_forms:
        program = _generate(program)
    if check:
        from .typecheck import typecheck   # Stage B, over the generated program
        typecheck(program, PRELUDE_NAMES, generated=generate_forms)

    # --- collect declarations
    types: Dict[str, A.TypeDecl] = {}
    ctors: Dict[str, Tuple[str, int, int]] = {}
    macros: Dict[str, A.Macro] = {}
    equations: List[Tuple[str, A.Equation, Optional[str]]] = []   # (name, equation, core)
    cores: Dict[str, A.Core] = {}
    defs: List[A.Def] = []
    qdefs: List[A.Def] = []            # level-1: name := [I |-] <t>[@n]
    for d in program.decls:
        if isinstance(d, A.TypeDecl):
            if d.name in types:
                raise ExpandError(f"type {d.name!r} declared twice")
            types[d.name] = d
            for idx, c in enumerate(d.ctors):
                if c.name in ctors:
                    raise ExpandError(f"constructor {c.name!r} declared twice")
                ctors[c.name] = (d.name, idx, len(c.fields))
        elif isinstance(d, A.Macro):
            macros[d.name] = d
        elif isinstance(d, A.Sig):
            pass                       # Stage B; parsed, kept, ignored
        elif isinstance(d, A.Equation):
            equations.append((d.name, d, None))
        elif isinstance(d, A.Core):
            if d.name in cores:
                raise ExpandError(f"core {d.name!r} declared twice")
            cores[d.name] = d
            seen_equation: Set[str] = set()
            for equation in d.equations:
                if equation.name in seen_equation:
                    raise ExpandError(
                        f"core {d.name!r} defines equation {equation.name!r} twice")
                seen_equation.add(equation.name)
                # a core's parameters are prepended to every equation's binder
                # list and are in scope in every equation body; references
                # between equations stay raw, so the parameters are passed
                # explicitly, which is the artifact's `stepScQ e` shape
                equations.append((equation.name,
                             A.Equation(equation.name, d.params + equation.binders, equation.body),
                             d.name))
        elif isinstance(d, A.Def):
            if isinstance(d.expr, (A.Quote, A.NsLit)):
                qdefs.append(d)      # needs quotation: compiled in pass 6
            else:
                defs.append(d)
        else:
            raise ExpandError(f"unknown declaration {d!r}")

    # --- the prelude: the Scott pair and its projections
    backend: Dict[str, str] = {}
    used: Set[str] = set()
    for nm in PRELUDE_NAMES:
        backend[nm] = nm
        used.add(nm)
    # The binders are \x00-prefixed sentinels, which no source program can
    # spell: a program that named a combinator `x` or `p` collided with the
    # rule's own binder inside the host's expansion of a cell or a pick.
    # Abstraction removes binders, so the emitted terms are unchanged.
    _x, _y, _c, _p = "\x00x", "\x00y", "\x00c", "\x00p"
    _h, _t, _n, _z, _sc = "\x00h", "\x00t", "\x00n", "\x00z", "\x00sc"
    env.define_rule("pair", (_x, _y, _c), K_(v(_c), v(_x), v(_y)))
    env.define_rule("hd", (_p,), K_(v(_p), a("K")))
    env.define_rule("tl", (_p,), K_(v(_p), K_(a("K"), a("I"))))
    env.define_rule("nil", (_n, _c), v(_n))
    env.define_rule("cons", (_h, _t, _n, _c), K_(v(_c), v(_h), v(_t)))
    # Scott numerals, the fuel convention (SURFACE-LANGUAGE-DESIGN.md §2
    # and §4): a fuel numeral is what a generated loop peels.
    env.define_rule("zero", (_z, _sc), v(_z))
    env.define_rule("suc", (_n, _z, _sc), K_(v(_sc), v(_n)))
    kinds: Dict[str, Tuple[str, str]] = {
        nm: ("prelude", nm) for nm in ("pair", "hd", "tl", "nil", "cons", "zero", "suc")}

    # --- backend names.  Program-level names (constructors, top-level
    # equations, definitions, the prelude) share one namespace; a core's equations
    # get their own, so two interpreter cores can each have a `step`.
    source_names: List[str] = []
    for tdecl in types.values():
        for c in tdecl.ctors:
            source_names.append(c.name)
    for name, _arm, core in equations:
        if core is None:
            source_names.append(name)
    for d in defs + qdefs:
        source_names.append(d.name)
    seen_source: Set[str] = set()
    for nm in source_names:
        if nm in seen_source:
            raise ExpandError(f"{nm!r} is defined twice")
        seen_source.add(nm)
        if nm in PRELUDE_NAMES:
            # the program supplies its own pair / hd / tl / nil / cons; keep
            # the name so cells, picks and the walker still reach it, and let
            # the definition below replace the prelude's.
            continue
        backend[nm] = _mangle(nm, used)
        used.add(backend[nm])

    #: (core, equation) -> backend name, and core -> {equation name}
    equation_backend: Dict[Tuple[str, str], str] = {}
    core_equations: Dict[str, Set[str]] = {c: set() for c in cores}
    for name, _arm, core in equations:
        if core is None:
            continue
        core_equations[core].add(name)
        equation_backend[(core, name)] = _mangle(f"{core}_{name}", used)
        used.add(equation_backend[(core, name)])

    # an interpreter core's own name denotes its fuel loop
    for cname in cores:
        if (cname, "loop") in equation_backend and cname not in backend:
            backend[cname] = equation_backend[(cname, "loop")]

    def resolver(core: Optional[str]):
        """Name resolution inside ``core`` (``None`` at top level):
        binders, then this core's sibling equations, then program-level names,
        then the aviary built-ins.  ``S``, ``K`` and ``I`` are always the
        ISA at level 0 (``SURFACE-LANGUAGE-DESIGN.md`` §6b)."""
        def resolve(nm: str) -> Optional[Term]:
            if nm in ISA_NAMES:
                return a(nm)
            if core is not None and nm in core_equations[core]:
                return a(equation_backend[(core, nm)])
            if nm in backend:
                return a(backend[nm])
            if nm in _BUILTIN_OK:
                return a(nm)
            return None
        return resolve

    resolve = resolver(None)

    # --- the constructors, from the type declarations
    for tdecl in types.values():
        n = len(tdecl.ctors)
        conts = [f"c{i}" for i in range(n)]
        for idx, c in enumerate(tdecl.ctors):
            fields = [f"f{i}" for i in range(len(c.fields))]
            body: Term = v(conts[idx])
            for f in fields:
                body = KApp(body, v(f))
            env.define_rule(backend[c.name], tuple(fields + conts), body)
            kinds[backend[c.name]] = ("ctor", c.name)

    cg = _Codegen(env, resolve, kinds=kinds)

    # --- passes 1..3 on every equation body, then codegen
    lowered: Dict[Tuple[Optional[str], str], A.Equation] = {}
    for name, equation, core in equations:
        body = expand_macros(equation.body, macros)
        body = desugar(body, ctors, types)
        lowered[(core, name)] = A.Equation(name, equation.binders, body)

    def _key_of(core: Optional[str], nm: str):
        """Which equation a name refers to from inside ``core``: a sibling
        first, then a top-level equation."""
        if core is not None and nm in core_equations[core] and (core, nm) in lowered:
            return (core, nm)
        if (None, nm) in lowered:
            return (None, nm)
        return None

    def _dep_keys(key):
        core, _name = key
        equation = lowered[key]
        free = free_names(equation.body) - set(equation.binders)
        out_ = set()
        for nm in free:
            if nm in ISA_NAMES:
                continue
            k = _key_of(core, nm)
            if k is not None:
                out_.add(k)
        return out_

    # --- pass 4: recursion.  An equation that calls only itself ties its
    # own fixpoint, `name := Y nameGen`, nameGen taking itself first.  A
    # group of mutually recursive equations ties one fixpoint for all of
    # them: its generator takes the group -- a Scott tuple of the members --
    # and returns the tuple of their codes, each applied to it; a member is
    # its projection from `Y` of the generator, and inside the group a call
    # to a member is its projection from the tuple.
    def _groups():
        """Tarjan over the equations, in their order; each group's members
        in declaration order."""
        order = list(lowered)
        at = {k: i for i, k in enumerate(order)}
        index: Dict = {}
        low: Dict = {}
        stack: List = []
        on: Set = set()
        out_: List[List] = []
        counter = [0]

        def visit(v_):
            index[v_] = low[v_] = counter[0]
            counter[0] += 1
            stack.append(v_)
            on.add(v_)
            for w in sorted(_dep_keys(v_), key=lambda k: at[k]):
                if w not in index:
                    visit(w)
                    low[v_] = min(low[v_], low[w])
                elif w in on:
                    low[v_] = min(low[v_], index[w])
            if low[v_] == index[v_]:
                grp = []
                while True:
                    w = stack.pop()
                    on.discard(w)
                    grp.append(w)
                    if w == v_:
                        break
                out_.append(sorted(grp, key=lambda k: at[k]))

        for k in order:
            if k not in index:
                visit(k)
        return out_

    def _bname(key):
        core, name = key
        return backend[name] if core is None else equation_backend[(core, name)]

    for group in _groups():
        if len(group) == 1:
            key = group[0]
            core, name = key
            equation = lowered[key]
            bname = _bname(key)
            gen = cg.with_resolver(resolver(core))
            recursive = key in _dep_keys(key)
            if recursive:
                selfp = _fresh("f", set(equation.binders) | free_names(equation.body))
                body = substitute(equation.body, {name: A.Name(selfp)})
                scope = [selfp] + list(equation.binders)
                gen_name = _mangle(bname + "Gen", used)
                used.add(gen_name)
                term = gen.gen(body, scope, bname)
                env.define_rule(gen_name, tuple(scope), term)
                kinds[gen_name] = ("rec", bname)
                env.define_alias(bname, K_(a("Y"), a(gen_name)))
            else:
                scope = list(equation.binders)
                term = gen.gen(equation.body, scope, bname)
                env.define_rule(bname, tuple(scope), term)
                kinds[bname] = ("eq", bname)
            continue
        n = len(group)
        gname = _mangle(_bname(group[0]) + "Group", used)
        used.add(gname)
        # the tuple, its projections: tuple x1 .. xn c = c x1 .. xn, and
        # sel_j t = t (pick_j), pick_j x1 .. xn = x_j
        xs = [f"\x00x{i}" for i in range(n)]
        tup = _mangle(gname + "Tuple", used)
        used.add(tup)
        env.define_rule(tup, tuple(xs) + ("\x00c",), K_(v("\x00c"), *[v(x) for x in xs]))
        kinds[tup] = ("group", gname)
        sels = []
        for j in range(n):
            pick = _mangle(f"{gname}Pick{j}", used)
            used.add(pick)
            env.define_rule(pick, tuple(xs), v(xs[j]))
            kinds[pick] = ("group", gname)
            sel = _mangle(f"{gname}Sel{j}", used)
            used.add(sel)
            env.define_rule(sel, ("\x00t",), K_(v("\x00t"), a(pick)))
            kinds[sel] = ("group", gname)
            sels.append(sel)
        # each member's code takes the group first; its calls to members
        # (itself too) project from it
        codes = []
        for j, key in enumerate(group):
            core, name = key
            equation = lowered[key]
            taken = set(equation.binders) | free_names(equation.body)
            grp = _fresh("g", taken)
            sub: Dict[str, A.Expr] = {}
            for i, okey in enumerate(group):
                ocore, oname = okey
                # a member is reached by its source name from this body when
                # the name resolves to it from here
                if _key_of(core, oname) == okey:
                    sub[oname] = A.App(A.Name("\x00sel%d" % i), A.Name(grp))
            body = substitute(equation.body, sub)
            scope = [grp] + list(equation.binders)
            code = _mangle(_bname(key) + "Code", used)
            used.add(code)

            def resolve_in(nm, _core=core):
                if nm.startswith("\x00sel"):
                    return a(sels[int(nm[len("\x00sel"):])])
                return resolver(_core)(nm)
            term = cg.with_resolver(resolve_in).gen(body, scope, _bname(key))
            env.define_rule(code, tuple(scope), term)
            kinds[code] = ("code", _bname(key))
            codes.append(code)
        gen_name = _mangle(gname + "Gen", used)
        used.add(gen_name)
        env.define_rule(gen_name, ("\x00t",),
                        K_(a(tup), *[KApp(a(c), v("\x00t")) for c in codes]))
        kinds[gen_name] = ("group", gname)
        env.define_alias(gname, K_(a("Y"), a(gen_name)))
        for j, key in enumerate(group):
            env.define_alias(_bname(key), K_(a(sels[j]), a(gname)))

    # --- plain definitions (``name := expr``)
    for d in defs:
        body = expand_macros(d.expr, macros)
        body = desugar(body, ctors, types)
        term = cg.gen(body, [], backend[d.name])
        env.define_alias(backend[d.name], term)

    # --- pass 5: bracket abstraction
    out = Expansion(env=env, backend=dict(backend), types=dict(types),
                    ctors=dict(ctors), rule_kinds=kinds)
    quoted_names = {d.name for d in qdefs}
    names = [n for n in dict.fromkeys(list(source_names) + list(PRELUDE_NAMES))
             if n not in quoted_names]
    bare_count: Dict[str, int] = {}
    for (core, name) in lowered:
        if core is not None:
            bare_count[name] = bare_count.get(name, 0) + 1

    def expand_all() -> None:
        """Expand every level-0 name.  Run again after pass 6, because a
        level-0 equation may name a datum a quotation defines, and that alias
        only exists once pass 6 has built it."""
        for nm in names:
            t = _ski_expand(a(backend[nm]), env)
            out.terms[nm] = t
            out.sizes[nm] = size(t)
        # core equations are always reachable as "core.equation", and as the bare
        # name when that name is unambiguous across the whole program
        for (core_, name_) in lowered:
            if core_ is None:
                continue
            t = _ski_expand(a(equation_backend[(core_, name_)]), env)
            out.terms[f"{core_}.{name_}"] = t
            out.sizes[f"{core_}.{name_}"] = size(t)
            if bare_count[name_] == 1 and name_ not in quoted_names:
                out.terms[name_] = t
                out.sizes[name_] = size(t)
        # an interpreter core's name denotes its fuel loop
        for cname in cores:
            if (cname, "loop") in lowered:
                out.terms[cname] = out.terms[f"{cname}.loop"]
                out.sizes[cname] = out.sizes[f"{cname}.loop"]
        for h in cg.helper_names:
            out.helpers[h] = _ski_expand(a(h), env)

    expand_all()

    # --- pass 6: quotation and level-1 packaging (§6a step 2, §6)
    if qdefs:
        obj = find_object_type(program)
        if obj is None:
            raise ExpandError(
                "quotation needs an object type: declare the alphabet the "
                "quoted term is written in, e.g. "
                "'term === S | K | I | App term term'")
        out.object_type = obj
        lt = find_loop_types(program, obj)
        out.answer_type = find_answer_type(program, obj, lt)
        out.path_type = find_path_type(program)
        enc = Encoder(obj, lambda n: out.terms[n])
        leafmap = level1_names(obj)

        def path_expr(path: A.Path, owner: str) -> A.Expr:
            """``/nat/three`` is ``Cons Nat (Cons Three Nil)``: each
            segment word names the ``seg`` constructor spelled with its
            first letter capitalized (``SYNTAX.md`` §6, decision 33)."""
            pt = out.path_type
            if pt is None:
                raise ExpandError(
                    f"{owner!r}: a path literal needs the path type; declare "
                    f"'path === Nil | Cons seg path' (SYNTAX.md §6)")
            e: A.Expr = A.Name(pt.nil.name)
            for seg in reversed(path.segments):
                if seg.payload is not None:
                    raise ExpandError(
                        f"{owner!r}: a segment payload "
                        f"('/vane/care[<t>]/desk') is not compiled yet")
                cname = seg.tag[:1].upper() + seg.tag[1:]
                if cname not in ctors or ctors[cname][0] != pt.seg:
                    raise ExpandError(
                        f"{owner!r}: path segment {seg.tag!r} names no "
                        f"constructor {cname!r} of the segment type "
                        f"{pt.seg!r}")
                e = A.App(A.App(A.Name(pt.cons.name), A.Name(cname)), e)
            return e

        scry_leaf = next((c.name for c in obj.leaves if c.name == "Scry"), None)

        def quote_expr(expr: A.Expr, owner: str) -> Term:
            """Compile a quoted expression to its datum: level-0 codegen
            with the object type's leaves admitted as atoms, then a
            structural Scott encode (§6a, steps 1 and 2)."""
            subs: Dict[str, Term] = {}

            def strip(e: A.Expr) -> A.Expr:
                """Replace each nested quotation by a placeholder name,
                compiling it to its datum first."""
                if isinstance(e, A.Quote):
                    if e.fuel is not None or e.interp is not None:
                        raise ExpandError(
                            f"{owner!r}: a nested quotation is a datum and "
                            f"may not carry fuel or an interpreter")
                    nm = f"\x00quote:{len(subs)}"
                    subs[nm] = quote_expr(e.expr, owner)
                    return A.Name(nm)
                if isinstance(e, A.App):
                    return A.App(strip(e.fn), strip(e.arg))
                if isinstance(e, A.Cell):
                    return A.Cell(tuple(strip(x) for x in e.items))
                if isinstance(e, A.Pick):
                    return A.Pick(e.axis, strip(e.expr))
                if isinstance(e, A.Lambda):
                    return A.Lambda(e.param, strip(e.body))
                if isinstance(e, A.Case):
                    return A.Case(strip(e.scrutinee),
                                  tuple((c, b, strip(x))
                                        for c, b, x in e.branches))
                if isinstance(e, A.Scry):
                    # `?^/nat/three` is the object type's Scry leaf applied
                    # to the quotation of the path term (§6a: the alphabet
                    # inside < > is the interpreter's object type)
                    if scry_leaf is None:
                        raise ExpandError(
                            f"{owner!r}: the object type {obj.name!r} has no "
                            f"'Scry' leaf, so '?^' has nothing to build")
                    return A.App(A.Name(scry_leaf),
                                 strip(path_expr(e.path, owner)))
                if isinstance(e, A.NsLit):
                    raise ExpandError(
                        f"{owner!r}: a namespace literal is a resolver, not "
                        f"a quotable term")
                return e

            body = strip(expr)
            body = expand_macros(body, macros)
            body = desugar(body, ctors, types)

            def qresolve(nm: str) -> Optional[Term]:
                if nm in subs:
                    return a(nm)                  # a nested datum
                if nm in leafmap:
                    return a(leafmap[nm])         # the object type's leaf
                return resolve(nm)                # inlined level-0 term

            term = cg.with_resolver(qresolve).gen(body, [], owner)
            term = _ski_expand(term, env)
            if subs:
                term = _splice(term, subs)
            return enc.quote(term)

        # 6a: every datum and resolver, in declaration order, each
        # defined in the environment so later declarations can name it
        packaged: List[Tuple[A.Def, A.Quote, Term]] = []
        for d in qdefs:
            if isinstance(d.expr, A.NsLit):
                _compile_nslit(d, out, lt, quote_expr, path_expr, env,
                               backend[d.name])
                continue
            if not isinstance(d.expr, A.Quote):
                raise ExpandError(f"{d.name!r}: expected a quotation")
            q = d.expr
            datum = quote_expr(q.expr, d.name)
            if q.fuel is None and q.interp is None:
                out.terms[d.name] = datum           # a datum, not run
                out.sizes[d.name] = size(datum)
                env.define_alias(backend[d.name], datum)
                continue
            packaged.append((d, q, datum))

        # 6b: a level-0 equation may name one of those datums, so expand again
        expand_all()

        # 6c: package the level-1 executables
        for d, q, datum in packaged:
            iname, iargs = _interp_spine(q.interp, cores, d.name)
            if (iname, "loop") not in lowered:
                raise ExpandError(
                    f"{d.name!r}: {iname!r} is not an interpreter core (it "
                    f"has no fuel loop)")
            params: List[Term] = []
            for arg in iargs:
                body = desugar(expand_macros(arg, macros), ctors, types)
                params.append(cg.gen(body, [], d.name))
            prog = Level1Program(
                name=d.name, interp=iname, interp_term=out.terms[iname],
                datum=datum, fuel=q.fuel if q.fuel is not None else A.POLICY,
                object_type=obj, result_type=lt.result,
                zero=out.terms["zero"], suc=out.terms["suc"],
                params=tuple(_ski_expand(t, env) for t in params))
            out.level1[d.name] = prog
            if isinstance(prog.fuel, int):
                out.terms[d.name] = prog.term
                out.sizes[d.name] = size(prog.term)
    return out


def _compile_nslit(d: A.Def, out: "Expansion", lt, quote_expr, path_expr,
                   env: Environment, bname: str) -> None:
    """``ns{/nat/two => <I>, /nat/three => <K>}`` is a resolver.

    It compiles to ``scry_paths.py``'s ``make_path_oracle`` shape::

        \\p. EQ5 p <k1> (OJust <a1>) (EQ5 p <k2> (OJust <a2>) ONotYet)

    First structural match wins; no match answers "not yet".  A flat
    chain, not a mount table: prefix routing (``SYNTAX.md`` §6) is later.
    """
    at = out.answer_type
    if at is None:
        raise ExpandError(
            f"{d.name!r}: a namespace literal needs an oracle answer type; "
            f"declare one, e.g. 'oanswer === OJust t | ONothing | ONotYet'")
    if "EQ5" not in out.terms:
        raise ExpandError(
            f"{d.name!r}: a namespace literal compares paths with 'EQ5', "
            f"which this program does not define")
    facts: List[Tuple[Term, Term]] = []
    lit = d.expr
    if not isinstance(lit, A.NsLit):
        raise ExpandError(f"{d.name!r}: expected a namespace literal")
    for path, value in lit.facts:
        if not (isinstance(value, A.Quote) and value.fuel is None
                and value.interp is None):
            raise ExpandError(
                f"{d.name!r}: a fact's value must be a quotation, e.g. "
                f"'/nat/two => <I>'; it is stored as data")
        key = quote_expr(path_expr(path, d.name), d.name)
        facts.append((key, quote_expr(value.expr, d.name)))
    out.namespaces[d.name] = tuple(facts)
    term = resolver_term(out.terms["EQ5"], out.terms[at.hit.name],
                         out.terms[at.notyet.name], facts)
    out.terms[d.name] = term
    out.sizes[d.name] = size(term)
    env.define_alias(bname, term)     # so later declarations can name it


#: the binder a compiled resolver abstracts over
_RESOLVER_BINDER = "\x00p"


def resolver_term(eq: Term, hit: Term, notyet: Term, facts) -> Term:
    """The closed resolver for a list of (key datum, answer datum) pairs.

    Bracket abstraction is the kernel's, as everywhere else.
    """
    body: Term = notyet
    for key, ans in reversed(list(facts)):
        body = K_(eq, v(_RESOLVER_BINDER), key, KApp(hit, ans), body)
    return _bracket_abstract(_RESOLVER_BINDER, body)


def _interp_spine(interp: Optional[A.Expr], cores, owner: str):
    """Which interpreter core runs a level-1 declaration, and with what
    arguments.

    ``I |- <t>@n`` names it; ``wfQ E |- <t>@n`` supplies its parameters,
    which is how a resolver enters (``SURFACE-LANGUAGE-DESIGN.md`` §6:
    the executable's arity is the interpreter's).  A bare ``<t>@n`` uses
    the default, a core named ``whnfF``.
    """
    if interp is None:
        if "whnfF" in cores:
            return "whnfF", []
        raise ExpandError(
            f"{owner!r}: no interpreter given and no core named 'whnfF' to "
            f"default to; write 'I |- <t>@n'")
    head, args = _spine(interp)
    if not isinstance(head, A.Name):
        raise ExpandError(
            f"{owner!r}: the interpreter left of '|-' must be a core, "
            f"optionally applied to its parameters")
    if head.name not in cores:
        raise ExpandError(
            f"{owner!r}: {head.name!r} is not a core in this program")
    want = len(cores[head.name].params)
    if len(args) != want:
        raise ExpandError(
            f"{owner!r}: core {head.name!r} takes {want} parameter(s) but "
            f"got {len(args)}; an interpreter is applied to all of them "
            f"before its fuel")
    return head.name, args


def _splice(term: Term, subs: Dict[str, Term]) -> Term:
    """Replace placeholder atoms by their terms, iteratively (a level-2
    datum is far deeper than the Python stack)."""
    out: List[Term] = []
    work: List[Tuple[Term, bool]] = [(term, False)]
    while work:
        x, done = work.pop()
        if isinstance(x, Atom):
            out.append(subs.get(x.name, x))
            continue
        if not done:
            work.append((x, True))
            work.append((x.arg, False))
            work.append((x.fn, False))
        else:
            r = out.pop()
            l = out.pop()
            out.append(KApp(l, r))
    return out.pop()
