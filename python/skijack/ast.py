"""The lexicon-free syntax tree.

A program's identity is its tree (``SYNTAX.md`` §5): there is no lexicon
field anywhere below, so a tree parsed from the ASCII spelling and a tree
parsed from the Unicode spelling of the same program are equal objects.

Every node is a frozen dataclass over tuples, so trees are hashable and
compare structurally.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple, Union

__all__ = [
    "Expr", "Name", "Num", "App", "Cell", "Quote", "Scry", "Pick", "Lambda",
    "Case", "NsLit", "Path", "Seg",
    "Decl", "TypeDecl", "Ctor", "Sig", "Equation", "Core", "Macro", "Def",
    "Program", "POLICY",
]


# --------------------------------------------------------------- expressions

@dataclass(frozen=True)
class Name:
    """A name.  A qualified name ``a.b`` is carried as the dotted text
    ``"a.b"``; it is looked up in the name table like any other name, and
    resolving it to an axis chain is not planned -- there is no runtime
    environment for an axis to index (``DESIDERATA.md`` item 2)."""
    name: str


@dataclass(frozen=True)
class Num:
    """``5``: a numeral literal.  It denotes the Scott numeral
    ``suc (suc (suc (suc (suc zero))))`` of any type declared
    ``Zero | Suc t``, built from the prelude's terms whatever a program
    calls its own ``zero`` and ``suc``.  Kept as a node, not desugared
    here, so a rendered program spells it as it was written."""
    value: int


@dataclass(frozen=True)
class App:
    """Binary application.  The parser left-associates juxtaposition, so
    ``f x y`` is ``App(App(f, x), y)``."""
    fn: "Expr"
    arg: "Expr"


@dataclass(frozen=True)
class Cell:
    """``[a b c]``.  Items are kept flat here; the expander right-nests
    them into Scott pairs (``SURFACE-LANGUAGE-DESIGN.md`` §2)."""
    items: Tuple["Expr", ...]


#: fuel elided, to be supplied by the runtime's policy: ASCII ``@[]``,
#: Unicode ``₍₎`` (``EXAMPLES.md`` §5).
POLICY = "policy"


@dataclass(frozen=True)
class Quote:
    """``<t>`` / ``<t>``: compile-time quotation.

    ``fuel`` is ``None`` for a bare datum, an ``int`` for ``<t>@n``, or
    :data:`POLICY` for ``<t>@[]``.  ``interp`` is the expression left of
    ``|-`` / ``⊢`` when an interpreter was selected."""
    expr: "Expr"
    fuel: Optional[Union[int, str]] = None
    interp: Optional["Expr"] = None


@dataclass(frozen=True)
class Seg:
    """One path segment: a tag with an optional bracketed payload."""
    tag: str
    payload: Optional["Expr"] = None


@dataclass(frozen=True)
class Path:
    segments: Tuple[Seg, ...]


@dataclass(frozen=True)
class Scry:
    """``?^/a/b`` / ``∵/a/b``."""
    path: Path


@dataclass(frozen=True)
class Pick:
    """``2@p`` / ``2⊑p``: projection by Nock axis."""
    axis: int
    expr: "Expr"


@dataclass(frozen=True)
class Lambda:
    """``\\x.e`` / ``λx.e``."""
    param: str
    body: "Expr"


@dataclass(frozen=True)
class Case:
    """``e |> { C1 bs1 b1 ; C2 bs2 b2 }``.

    ``branches`` is a tuple of ``(cname, binders, body)``; the number of
    binders is the constructor's declared arity."""
    scrutinee: "Expr"
    branches: Tuple[Tuple[str, Tuple[str, ...], "Expr"], ...]


@dataclass(frozen=True)
class NsLit:
    """``ns{/a/b -> v, ...}`` / ``ns{/a/b ↦ v, …}``."""
    facts: Tuple[Tuple[Path, "Expr"], ...]


Expr = Union[Name, Num, App, Cell, Quote, Scry, Pick, Lambda, Case, NsLit]


# -------------------------------------------------------------- declarations

@dataclass(frozen=True)
class Ctor:
    """One constructor of a sum type: a capitalized name followed by the
    *types* of its fields (``Suc nat``).  ``len(fields)`` is the arity."""
    name: str
    fields: Tuple[str, ...] = ()


@dataclass(frozen=True)
class TypeDecl:
    """``nat === Zero | Suc nat``.  Constructor order is the ABI."""
    name: str
    ctors: Tuple[Ctor, ...]


@dataclass(frozen=True)
class Sig:
    """``f : s -> t``.  Parsed, kept, and ignored (DESIDERATA item 11)."""
    name: str
    types: Tuple[str, ...]


@dataclass(frozen=True)
class Equation:
    """``name b1 b2 = body``.  An equation of a core, or (see the README) a
    top-level declaration."""
    name: str
    binders: Tuple[str, ...]
    body: Expr


@dataclass(frozen=True)
class Core:
    """``name := { equations }``, or ``name p1 p2 := { equations }``.

    A core's parameters are prepended to every equation's binder list and are
    in scope in every equation body; the core's name denotes its loop applied
    to nothing, so ``wfQ E |- <t>@n`` supplies them
    (``SURFACE-LANGUAGE-DESIGN.md`` §6, the interpreter's own arity)."""
    name: str
    equations: Tuple[Equation, ...]
    params: Tuple[str, ...] = ()


@dataclass(frozen=True)
class Macro:
    """``name p* :=* body`` (hygienic) or ``name p* :=! body`` (capturing)."""
    name: str
    params: Tuple[str, ...]
    body: Expr
    capturing: bool = False


@dataclass(frozen=True)
class Def:
    """``name := expr`` where the right side is not a core."""
    name: str
    expr: Expr


Decl = Union[TypeDecl, Sig, Equation, Core, Macro, Def]


@dataclass(frozen=True)
class Program:
    decls: Tuple[Decl, ...]
