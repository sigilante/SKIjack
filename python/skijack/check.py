"""Stage A: the checker.

``DESIDERATA.md`` item 11 -- "the checker is a pass that can reject and
never rewrites, and the expander's output is the same whether checking
is on or off".  Nothing here builds a term or touches the tree; it walks
the parsed program and returns problems.

The Stage A list, and where each lives below:

======  ========================================  ====================
item    check                                     error class
======  ========================================  ====================
(a)     constructor arity where a constructor
        application denotes data                  :class:`ArityError`
(b)     case completeness and declaration order   :class:`CaseError`
(c)     data versus function at the positions
        of ``SURFACE-LANGUAGE-DESIGN.md`` §5      :class:`DataError`
(d)     the interpreter interface (§6c)           :class:`InterfaceError`
(e)     the two symbol tables (§6b): a name inside
        a quotation that names neither            :class:`SymbolTableError`
(f)     unresolved names, duplicate declarations  :class:`ScopeError`
======  ========================================  ====================

Every problem found is collected; :func:`check` reports them **together**
and raises the first one's class, so a caller may catch a specific check
(``pytest.raises(ArityError)``) and still see the whole list.

Two readings this pass takes, both stated in the README:

* **Arity is checked where a constructor application denotes data** --
  inside a quotation, a path literal and a namespace key.  At level 0 a
  Scott constructor *is* a function of its fields and then of its
  continuations, so ``Zero c0 c1`` is an ordinary case analysis and
  neither over- nor under-application means anything there.  In a case
  branch the parser already fixes the binder count at the arity.
* **§5's data/function line refuses what it can prove is a function**,
  not everything it cannot prove is data.  With no types, a binder's
  kind is unknown until Stage B; an equation name, a bare combinator, a
  lambda, a macro and a partially applied constructor are known
  functions, and those are refused.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Set, Tuple

from .abi import ISA as _ISA, TIER1_NAMES

from . import ast as A
from .generate import (GenerateError, ObjectType, PathType, find_object_type,
                       find_path_type, is_interpreter_core,
                       names_generation_adds)

__all__ = [
    "CheckError", "ArityError", "CaseError", "DataError", "InterfaceError",
    "SymbolTableError", "ScopeError", "Problem", "check", "check_program",
    "isa_binders",
]


from .errors import SkijackError

class CheckError(SkijackError):
    """Base of every Stage A rejection.  Carries ``.problems``."""
    problems: Tuple["Problem", ...] = ()


class ArityError(CheckError):
    """(a) a constructor applied to the wrong number of fields as data."""


class CaseError(CheckError):
    """(b) a case form that is incomplete, repeated, or mixed-type."""


class DataError(CheckError):
    """(c) a function where §5 requires data."""


class InterfaceError(CheckError):
    """(d) an interpreter core that does not match the §6c interface."""


class SymbolTableError(CheckError):
    """(e) a name looked up in the wrong one of §6b's two tables."""


class ScopeError(CheckError):
    """(f) an unresolved name, or a name declared twice."""


@dataclass(frozen=True)
class Site:
    """Where a problem is.

    A structured site rather than a pre-formatted string, because the
    words in it are vocabulary: an *equation* is the source form, a
    *core* is the group it is declared in.  Renaming what we call these
    is then one ``__str__`` and not a hundred f-strings.
    """
    kind: str                       # "equation", "core", "definition"
    name: str
    core: Optional[str] = None

    @property
    def dotted(self) -> str:
        """The qualified name, as the dictionary spells it."""
        return f"{self.core}.{self.name}" if self.core else self.name

    def __str__(self) -> str:
        if self.core is not None:
            return f"core {self.core}, equation {self.name}"
        return f"{self.kind} {self.name}" if self.name else self.kind


@dataclass
class Problem:
    kind: type
    where: Site
    message: str

    def __str__(self) -> str:
        return f"{self.kind.__name__} in {self.where}: {self.message}"




@dataclass
class _Env:
    types: Dict[str, A.TypeDecl] = field(default_factory=dict)
    ctors: Dict[str, Tuple[str, int, int]] = field(default_factory=dict)
    macros: Dict[str, A.Macro] = field(default_factory=dict)
    equations: Dict[str, A.Equation] = field(default_factory=dict)        # top level
    core_equations: Dict[str, Dict[str, A.Equation]] = field(default_factory=dict)
    cores: Dict[str, A.Core] = field(default_factory=dict)
    defs: Dict[str, A.Def] = field(default_factory=dict)
    generated: Set[str] = field(default_factory=set)
    core_generated: Dict[str, Set[str]] = field(default_factory=dict)
    obj: Optional[ObjectType] = None
    path: Optional[PathType] = None
    prelude: Tuple[str, ...] = ()

    def known(self, name: str, core: Optional[str]) -> bool:
        if name in _ISA or name in TIER1_NAMES or name in self.prelude:
            return True
        if core is not None:
            if name in self.core_equations.get(core, ()):
                return True
            if name in self.core_generated.get(core, ()):
                return True
            if name in self.cores[core].params:
                return True
        return (name in self.ctors or name in self.equations or name in self.defs
                or name in self.cores or name in self.generated
                or name in self.macros)


def isa_binders(program: A.Program) -> List[Tuple["Site", str]]:
    """Every binder named ``S``, ``K`` or ``I``, as (where, name).  Those
    names resolve to the ISA unconditionally (SPEC.md §5), so a binder of
    one could never be used; it is refused rather than left dead."""
    out: List[Tuple[Site, str]] = []

    def names(where: Site, ns) -> None:
        out.extend((where, n) for n in ns if n in _ISA)

    def walk(where: Site, x) -> None:
        stack = [x]
        while stack:
            y = stack.pop()
            if isinstance(y, A.Lambda):
                names(where, (y.param,))
            elif isinstance(y, A.Case):
                for _c, bs, _b in y.branches:
                    names(where, bs)
            if isinstance(y, (list, tuple)):
                stack.extend(y)
            elif hasattr(y, "__dataclass_fields__"):
                stack.extend(getattr(y, f) for f in y.__dataclass_fields__)

    for d in program.decls:
        if isinstance(d, A.Equation):
            names(Site("equation", d.name), d.binders)
            walk(Site("equation", d.name), d.body)
        elif isinstance(d, A.Macro):
            names(Site("macro", d.name), d.params)
            walk(Site("macro", d.name), d.body)
        elif isinstance(d, A.Core):
            # a core's parameters are each equation's first binders, so a
            # core with no equations binds nothing
            for eq in d.equations:
                site = Site("equation", eq.name, d.name)
                names(site, tuple(d.params) + tuple(eq.binders))
                walk(site, eq.body)
        elif isinstance(d, A.Def):
            walk(Site("definition", d.name), d.expr)
    return out


def _spine(e: A.Expr):
    args = []
    while isinstance(e, A.App):
        args.append(e.arg)
        e = e.fn
    args.reverse()
    return e, args


class _Checker:
    def __init__(self, program: A.Program, prelude: Sequence[str]):
        self.program = program
        self.problems: List[Problem] = []
        self.env = _Env(prelude=tuple(prelude))
        self._collect()

    # ------------------------------------------------------------ collect

    def add(self, kind: type, where: Site, message: str) -> None:
        self.problems.append(Problem(kind, where, message))

    def _collect(self) -> None:
        e = self.env
        seen: Dict[str, str] = {}

        def declare(name, what, where):
            if name in seen:
                self.add(ScopeError, where,
                         f"{name!r} is declared twice (already a "
                         f"{seen[name]})")
            seen[name] = what

        for d in self.program.decls:
            if isinstance(d, A.TypeDecl):
                declare(d.name, "type", f"type {d.name}")
                if d.name in e.types:
                    continue
                e.types[d.name] = d
                for i, c in enumerate(d.ctors):
                    declare(c.name, "constructor", f"type {d.name}")
                    e.ctors.setdefault(c.name, (d.name, i, len(c.fields)))
            elif isinstance(d, A.Macro):
                declare(d.name, "macro", f"macro {d.name}")
                e.macros[d.name] = d
            elif isinstance(d, A.Equation):
                declare(d.name, "equation", Site("equation", d.name))
                e.equations[d.name] = d
            elif isinstance(d, A.Core):
                declare(d.name, "core", Site("core", d.name))
                e.cores[d.name] = d
                inner: Dict[str, A.Equation] = {}
                for equation in d.equations:
                    if equation.name in inner:
                        self.add(ScopeError, Site("core", d.name),
                                 f"equation {equation.name!r} is defined twice")
                    inner[equation.name] = equation
                e.core_equations[d.name] = inner
            elif isinstance(d, A.Def):
                declare(d.name, "definition", f"definition {d.name}")
                e.defs[d.name] = d
        try:
            e.obj = find_object_type(self.program)
            e.path = find_path_type(self.program)
            top, per_core = names_generation_adds(self.program)
            e.generated = set(top)
            e.core_generated = {k: set(v) for k, v in per_core.items()}
        except GenerateError as ex:
            self.add(InterfaceError, Site("the program", ""), str(ex))

    # ------------------------------------------------------------- walk

    def run(self) -> List[Problem]:
        for where, nm in isa_binders(self.program):
            self.add(ScopeError, where,
                     f"a binder named {nm!r}: S, K and I always name the "
                     f"ISA (SPEC.md §5), so it could never be used")
        for d in self.program.decls:
            if isinstance(d, A.Equation):
                self.expr(d.body, Site("equation", d.name), None, set(d.binders))
            elif isinstance(d, A.Macro):
                self.expr(d.body, Site("macro", d.name), None, set(d.params),
                          macro=True)
            elif isinstance(d, A.Core):
                self.core(d)
            elif isinstance(d, A.Def):
                self.definition(d)
        return self.problems

    def core(self, d: A.Core) -> None:
        bound = set(d.params)
        for equation in d.equations:
            self.expr(equation.body, Site("equation", equation.name, d.name), d.name,
                      bound | set(equation.binders))
        if self.env.obj is not None and is_interpreter_core(d, self.env.obj):
            self.interface(d)

    def definition(self, d: A.Def) -> None:
        where = Site("definition", d.name)
        if isinstance(d.expr, A.NsLit):
            for path, value in d.expr.facts:
                self.path_literal(path, where)
                if not (isinstance(value, A.Quote) and value.fuel is None
                        and value.interp is None):
                    self.add(DataError, where,
                             "a namespace fact's value must be data (a "
                             "quotation); §5 rule 3: a function cannot be "
                             "stored as a fact")
                else:
                    self.quoted(value.expr, where)
            return
        if isinstance(d.expr, A.Quote):
            self.quote(d.expr, where)
            return
        self.expr(d.expr, where, None, set())

    # ---------------------------------------------------- expressions

    def expr(self, e: A.Expr, where: Site, core: Optional[str],
             bound: Set[str], macro: bool = False) -> None:
        if isinstance(e, A.Name):
            self.name(e.name, where, core, bound, macro)
            return
        if isinstance(e, A.Num):
            return                       # a numeral: closed, and names nothing
        if isinstance(e, A.App):
            head, args = _spine(e)
            self.eq_position(head, args, where, core, bound)
            self.expr(head, where, core, bound, macro)
            for x in args:
                self.expr(x, where, core, bound, macro)
            return
        if isinstance(e, A.Cell):
            for x in e.items:
                self.expr(x, where, core, bound, macro)
            return
        if isinstance(e, A.Pick):
            self.expr(e.expr, where, core, bound, macro)
            return
        if isinstance(e, A.Lambda):
            self.expr(e.body, where, core, bound | {e.param}, macro)
            return
        if isinstance(e, A.Case):
            self.case(e, where, core, bound, macro)
            return
        if isinstance(e, A.Quote):
            if e.interp is not None:
                self.expr(e.interp, where, core, bound, macro)
            self.quoted(e.expr, where)
            return
        if isinstance(e, A.Scry):
            self.add(DataError, where,
                     "'?^' is live only inside a quotation (§6: nothing at "
                     "level 0 may use a scry)")
            return
        if isinstance(e, A.NsLit):
            self.add(DataError, where,
                     "a namespace literal is a resolver; it belongs on the "
                     "right of a definition")
            return

    def name(self, nm: str, where: Site, core: Optional[str], bound: Set[str],
             macro: bool) -> None:
        if nm in bound or macro:
            return
        if not self.env.known(nm, core):
            self.add(ScopeError, where,
                     f"unresolved name {nm!r}; free variables do not exist "
                     f"at runtime (SYNTAX.md §8)")
        # (e) has nothing to say at level 0: a declared type's
        # constructors are ordinary Scott constructors there, whatever
        # type they belong to.  The rebuilder *must* apply the object
        # type's `App` to build encoded terms, exactly as `Suc` and
        # `Just` are applied at level 0 everywhere else.  Only `S`, `K`
        # and `I` are reserved, and they resolve to the ISA rather than
        # being refused (SURFACE-LANGUAGE-DESIGN.md §6b).  The level-1
        # half of the check is in `quoted` below.

    def case(self, e: A.Case, where: Site, core, bound, macro) -> None:
        self.expr(e.scrutinee, where, core, bound, macro)
        if not e.branches:
            self.add(CaseError, where, "a case form needs at least one branch")
            return
        first = e.branches[0][0]
        if first not in self.env.ctors:
            self.add(CaseError, where,
                     f"undeclared constructor {first!r} in a case branch")
            return
        tname = self.env.ctors[first][0]
        decl = self.env.types[tname]
        seen: Dict[str, Tuple[str, ...]] = {}
        for cname, binders, body in e.branches:
            if cname not in self.env.ctors:
                self.add(CaseError, where,
                         f"undeclared constructor {cname!r} in a case branch")
                continue
            if self.env.ctors[cname][0] != tname:
                self.add(CaseError, where,
                         f"branch {cname!r} is a constructor of "
                         f"{self.env.ctors[cname][0]!r}, but the case is over "
                         f"{tname!r}")
                continue
            if cname in seen:
                self.add(CaseError, where, f"branch {cname!r} appears twice")
            seen[cname] = binders
            self.expr(body, where, core, bound | set(binders), macro)
        missing = [c.name for c in decl.ctors if c.name not in seen]
        if missing:
            self.add(CaseError, where,
                     f"case over {tname!r} is missing branch(es) for "
                     f"{', '.join(missing)}; a case must be complete, and "
                     f"the continuations are emitted in declaration order "
                     f"(DESIDERATA.md item 11)")

    # --------------------------------------------------- §5, position by position

    def eq_position(self, head, args, where: Site, core, bound) -> None:
        """(c) the arguments of ``EQ`` must not be provably functions."""
        if not (isinstance(head, A.Name) and head.name == "EQ"):
            return
        for i, x in enumerate(args[:2]):
            why = self.provably_function(x, core, bound)
            if why is not None:
                self.add(DataError, where,
                         f"argument {i + 1} of 'EQ' is {why}; §5 rule 3: a "
                         f"value of function type cannot be compared")

    def provably_function(self, e: A.Expr, core: Optional[str],
                          bound: Set[str]) -> Optional[str]:
        """What makes ``e`` a function, or ``None`` when Stage A cannot
        tell.  Conservative on purpose: with no types a binder's kind is
        unknown until Stage B."""
        if isinstance(e, (A.Quote, A.Scry, A.Cell)):
            return None
        if isinstance(e, A.Lambda):
            return "a lambda"
        if isinstance(e, A.NsLit):
            return "a resolver"
        head, args = _spine(e)
        if not isinstance(head, A.Name):
            return None
        nm = head.name
        if nm in bound:
            return None
        if nm in _ISA or nm in TIER1_NAMES:
            return f"the combinator {nm!r}"
        if nm in self.env.ctors:
            arity = self.env.ctors[nm][2]
            if len(args) < arity:
                return (f"the constructor {nm!r} applied to {len(args)} of "
                        f"its {arity} field(s), which is a function")
            return None
        if nm in self.env.macros:
            return f"the macro {nm!r}"
        if nm in self.env.equations and self.env.equations[nm].binders:
            return f"the equation {nm!r}"
        if core is not None and nm in self.env.core_equations.get(core, ()):
            if self.env.core_equations[core][nm].binders:
                return f"the equation {nm!r}"
        if nm in self.env.cores:
            return f"the core {nm!r}"
        return None

    # -------------------------------------------------------- quotation

    def quote(self, q: A.Quote, where: Site) -> None:
        if q.interp is not None:
            self.interp_application(q.interp, where)
        self.quoted(q.expr, where)

    def quoted(self, e: A.Expr, where: Site) -> None:
        """Inside ``< >``: §6b's level-1 table.  A name is a constructor
        of the object type, or a level-0 name that is inlined and
        quoted; anything else names neither table."""
        obj = self.env.obj
        if isinstance(e, A.Num):
            self.add(DataError, where,
                     f"the literal {e.value} inside a quotation: a numeral is "
                     f"a level-0 value, and a quotation holds object terms")
            return
        if isinstance(e, A.Scry):
            self.path_literal(e.path, where)
            if obj is not None and not any(c.name == "Scry"
                                           for c in obj.leaves):
                self.add(SymbolTableError, where,
                         f"'?^' needs a 'Scry' leaf in the object type "
                         f"{obj.name!r}")
            return
        if isinstance(e, A.Quote):
            if e.fuel is not None or e.interp is not None:
                self.add(DataError, where,
                         "a nested quotation is a datum and may not carry "
                         "fuel or an interpreter")
            self.quoted(e.expr, where)
            return
        if isinstance(e, A.NsLit):
            self.add(DataError, where,
                     "a namespace literal is a resolver, not a quotable term")
            return
        if isinstance(e, A.Lambda):
            self.quoted(e.body, where)
            return
        if isinstance(e, A.Cell):
            for x in e.items:
                self.quoted(x, where)
            return
        if isinstance(e, A.Pick):
            self.quoted(e.expr, where)
            return
        if isinstance(e, A.Case):
            self.quoted(e.scrutinee, where)
            for _c, _b, body in e.branches:
                self.quoted(body, where)
            return
        head, args = _spine(e)
        for x in args:
            self.quoted(x, where)
        if not isinstance(head, A.Name):
            self.quoted(head, where)
            return
        nm = head.name
        obj_names = set() if obj is None else {c.name for c in obj.decl.ctors}
        if nm in obj_names:
            return                       # the level-1 table
        if self.env.known(nm, None):
            # a level-0 name, inlined and quoted; if it is a constructor
            # of some *other* declared type it must be saturated, because
            # a partial application is a function (§5 rule 3)
            if nm in self.env.ctors:
                arity = self.env.ctors[nm][2]
                if len(args) != arity:
                    self.add(ArityError, where,
                             f"constructor {nm!r} takes {arity} field(s) but "
                             f"is given {len(args)} inside a quotation, where "
                             f"it denotes data")
            return
        self.add(SymbolTableError, where,
                 f"{nm!r} names neither table (§6b): it is not a constructor "
                 f"of the object type"
                 + (f" {obj.name!r}" if obj is not None else "")
                 + " and not a level-0 name")

    def path_literal(self, path: A.Path, where: Site) -> None:
        pt = self.env.path
        if pt is None:
            self.add(ScopeError, where,
                     "a path literal needs the path type; declare "
                     "'path === Nil | Cons seg path' (SYNTAX.md §6)")
            return
        for seg in path.segments:
            if seg.payload is not None:
                self.add(DataError, where,
                         "a segment payload ('/vane/care[<t>]/desk') is not "
                         "compiled yet; only path literals are accepted "
                         "until Stage B (SYNTAX.md §6)")
                continue
            cname = seg.tag[:1].upper() + seg.tag[1:]
            got = self.env.ctors.get(cname)
            if got is None or got[0] != pt.seg:
                self.add(ScopeError, where,
                         f"path segment {seg.tag!r} names no constructor "
                         f"{cname!r} of the segment type {pt.seg!r}")
            elif got[2] != 0:
                self.add(ArityError, where,
                         f"path segment constructor {cname!r} carries "
                         f"{got[2]} field(s); a segment tag is nullary")

    # ----------------------------------------------- the §6c interface

    def interp_application(self, interp: A.Expr, where: Site) -> None:
        head, args = _spine(interp)
        if not isinstance(head, A.Name):
            self.add(InterfaceError, where,
                     "the interpreter left of '|-' must be a core, "
                     "optionally applied to its parameters")
            return
        core = self.env.cores.get(head.name)
        if core is None:
            self.add(InterfaceError, where,
                     f"{head.name!r} is not a core in this program")
            return
        if len(args) != len(core.params):
            self.add(InterfaceError, where,
                     f"core {head.name!r} takes {len(core.params)} "
                     f"parameter(s) but is applied to {len(args)}; an "
                     f"interpreter is applied to all of them before its fuel")

    def interface(self, d: A.Core) -> None:
        obj = self.env.obj
        if obj is None:                  # only called when an object type exists
            return
        where = Site("core", d.name)
        leaves = [c.name for c in obj.leaves]
        for equation in d.equations:
            if not equation.name.startswith("step") or equation.name == "step":
                continue
            rest = equation.name[4:]
            if rest == obj.app.name:
                self.add(InterfaceError, where,
                         f"{equation.name!r}: the application constructor "
                         f"{obj.app.name!r} has no step equation -- it is the "
                         f"spine the walker descends, not a head that fires "
                         f"(§6c)")
        written = {equation.name: equation for equation in d.equations}
        if "step" in written:
            self.step_arm(written["step"], d, leaves, where)
        if "loop" in written:
            n = len(written["loop"].binders)
            if n != 2:
                self.add(InterfaceError, where,
                         f"a written 'loop' takes the fuel and the term, two "
                         f"binders after the core's parameters; this one has "
                         f"{n}")
        if "loop1" in written and "loop" not in written:
            self.add(InterfaceError, where,
                     "'loop1' is written but 'loop' is not; write both or "
                     "neither")
        if "loop1" in written and len(written["loop1"].binders) != 3:
            self.add(InterfaceError, where,
                     f"a written 'loop1' takes the loop, the term and the "
                     f"remaining fuel, three binders after the core's "
                     f"parameters; this one has "
                     f"{len(written['loop1'].binders)}")

    def step_arm(self, equation: A.Equation, d: A.Core, leaves, where: Site) -> None:
        if len(equation.binders) != 1:
            self.add(InterfaceError, where,
                     f"a written 'step' takes the term, one binder after the "
                     f"core's parameters; this one has {len(equation.binders)}")
            return
        head, args = _spine(equation.body)
        if not (isinstance(head, A.Name) and head.name == "sp"):
            return                      # not the generated shape; leave it
        if len(args) != 2 + len(leaves):
            self.add(InterfaceError, where,
                     f"'step' hands the walker {len(args) - 2} step equation(s) "
                     f"but the object type has {len(leaves)} leaves "
                     f"({', '.join(leaves)})")
            return
        got: List[Optional[str]] = []
        for x in args[2:]:
            h, _ = _spine(x)
            got.append(h.name if isinstance(h, A.Name) else None)
        want = ["step" + c for c in leaves]
        named = [g for g in got if g is not None]
        if len(named) == len(got) \
                and all(g.startswith("step") for g in named) \
                and sorted(named) == sorted(want) and named != want:
            self.add(InterfaceError, where,
                     f"'step' installs the leaf equations in the order "
                     f"{', '.join(named)}, but the object type declares "
                     f"{', '.join(leaves)}; declaration order is the ABI and "
                     f"a wrong order is silent wrong semantics "
                     f"(DESIDERATA.md item 11)")


def check_program(program: A.Program, prelude: Sequence[str] = ()
                  ) -> List[Problem]:
    """Every Stage A problem in ``program``, in source order.  Never
    raises for a program problem, and never rewrites anything."""
    return _Checker(program, prelude).run()


def check(program: A.Program, prelude: Sequence[str] = ()) -> None:
    """Run Stage A and raise if anything is wrong.

    The raised exception is the *first* problem's class, so a caller may
    catch one check; its message lists every problem found, and
    ``.problems`` carries them all.
    """
    problems = check_program(program, prelude)
    if not problems:
        return
    lines = "\n".join("  " + str(p) for p in problems)
    n = len(problems)
    exc = problems[0].kind(
        f"{n} Stage A problem{'s' if n > 1 else ''}:\n{lines}")
    exc.problems = tuple(problems)
    raise exc
