"""Supercombinator templates: each rule's formals and open body, beside the
pure SKI term it compiles to (avon/docs/DESIGN.md §18.1, §6.9).

The expander compiles every equation, recursion body, group part, lifted
lambda, constructor and prelude rule to a closed SKI term by bracket
abstraction.  Before abstraction each is a rule: formals and a body.  A
runtime that instantiates the body with the arguments, instead of running
the abstraction's S/K plumbing, reaches the same value; that is lean-ski's
``absN_beta_close`` (``Ski/Inst.lean``), and the runtime checks each
template by abstracting its body again and comparing with the term.

This module reads the templates off an :class:`~skijack.expand.Expansion`.
It changes no term: the SKI the expander emits stays the program, and a
template is an optional hint keyed by that term's §5 hash.

A template's body is an open term over its formals: S, K, I, variables,
and references -- closed terms, the SKI of other rules or of built-in
birds.  An atom is a reference exactly when aviary's expansion expands it
(``aviary_kernel.abstraction._expand``: a name the environment knows), so
the body abstracts to the term the expander emitted, which
:func:`check` verifies.

Left out, as lean-ski's ``jetTable`` leaves them out: rules of no formals
(aliases), open bodies (a variable outside the formals), and η-templates,
``λ xs. G xs`` with ``G`` closed, which compile to ``G`` itself, so that
instantiating one rewrites ``G xs`` to ``G xs`` forever.

The files, beside ``dictionary.tsv``:

``templates.tsv``
    ``key kind label k formals body`` per template: the key, the §5 hash of
    the rule's SKI term; its kind (see ``Expansion.rule_kinds``) and label;
    the arity; the formals, a comma-separated list of variable numbers --
    the format lets a formal repeat, the last occurrence binding it, as
    lean-ski's ``overrideN``, though aviary refuses a repeated formal so
    the expander never writes one; and the body in prefix form, `` ` `` before an
    application, ``S`` ``K`` ``I``, ``vN`` a variable, ``#hash`` a
    reference.
``template_terms.tsv``
    ``hash atoms printed-term`` for every reference, in
    ``dictionary.tsv``'s format.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Tuple, Union

from aviary_kernel.abstraction import bracket_abstract, expand as ski_expand
from aviary_kernel.terms import App, Atom, Term, pretty

from .dictionary import structural_hash

__all__ = ["Var", "Ref", "Template", "templates", "check", "write",
           "body_text", "is_eta"]

_SKI = ("S", "K", "I")


@dataclass(frozen=True)
class Var:
    """Formal number ``n``."""
    n: int


@dataclass(frozen=True)
class Ref:
    """A closed term: another rule's SKI, or a bird's."""
    term: Term


Body = Union[Var, Ref, Atom, "BApp"]


@dataclass(frozen=True)
class BApp:
    fn: "Body"
    arg: "Body"


@dataclass(frozen=True)
class Template:
    name: str                   #: the backend rule
    kind: str
    label: str
    key: Term                   #: the rule's SKI term
    formals: Tuple[int, ...]    #: variable numbers, a repeat binding last
    body: Body

    @property
    def arity(self) -> int:
        return len(self.formals)

    @property
    def key_hash(self) -> str:
        return structural_hash(self.key)


def _body(t: Term, formals: Dict[str, int], env) -> Optional[Body]:
    """The rule body as an open term, classifying atoms as aviary's
    expansion does; None if a variable is not a formal (an open body)."""
    out: List[Body] = []
    stack: list = [t]
    while stack:
        x = stack.pop()
        if x is None:
            arg = out.pop()
            out.append(BApp(out.pop(), arg))
        elif isinstance(x, App):
            stack.extend([None, x.arg, x.fn])
        elif x.name in _SKI:
            out.append(x)
        elif x.name in env.expansion_cache or env.lookup(x.name) is not None:
            out.append(Ref(ski_expand(x, env)))
        elif x.name in formals:
            out.append(Var(formals[x.name]))
        else:
            return None
    return out[0]


def _app_formals(body: Body, formals: Tuple[int, ...]) -> Optional[Body]:
    """If body is H v_1 .. v_k over the formals in order, H; else None."""
    h = body
    for n in reversed(formals):
        if not (isinstance(h, BApp) and h.arg == Var(n)):
            return None
        h = h.fn
    return h


def _closed(b: Body) -> bool:
    stack = [b]
    while stack:
        x = stack.pop()
        if isinstance(x, Var):
            return False
        if isinstance(x, BApp):
            stack += [x.fn, x.arg]
    return True


def _to_term(b: Body, var_name) -> Term:
    out: List[Term] = []
    stack: list = [b]
    while stack:
        x = stack.pop()
        if x is None:
            arg = out.pop()
            out.append(App(out.pop(), arg))
        elif isinstance(x, BApp):
            stack.extend([None, x.arg, x.fn])
        elif isinstance(x, Var):
            out.append(Atom(var_name(x.n)))
        elif isinstance(x, Ref):
            out.append(x.term)
        else:
            out.append(x)
    return out[0]


def is_eta(t: Template) -> bool:
    """λ xs. G xs with G closed: its key is G, and instantiating it loops."""
    head = _app_formals(t.body, t.formals)
    return head is not None and _closed(head)


def check(t: Template) -> bool:
    """The body, abstracted over its formals the last first, is the key."""
    term = _to_term(t.body, lambda n: f"\x00v{n}")
    for n in reversed(t.formals):
        term = bracket_abstract(f"\x00v{n}", term)
    return structural_hash(term) == t.key_hash


def templates(exp) -> List[Template]:
    """Every rule of the expansion with formals, closed over them, and not
    an η-template, in the order the expander defined them."""
    env = exp.env
    out: List[Template] = []
    for name, d in env.definitions.items():
        if d.builtin or d.is_alias or not d.formals:
            continue
        ids: Dict[str, int] = {}
        for f in d.formals:
            ids.setdefault(f, len(ids))
        formals = tuple(ids[f] for f in d.formals)
        body = _body(d.body, ids, env)
        if body is None:
            continue                            # open: not a template
        kind, label = exp.rule_kinds.get(name, ("other", name))
        t = Template(name, kind, label, ski_expand(Atom(name), env), formals, body)
        if is_eta(t):
            continue
        out.append(t)
    return out


def body_text(b: Body) -> str:
    """The body in prefix form: `` ` `` before an application."""
    out: List[str] = []
    stack: list = [b]
    while stack:
        x = stack.pop()
        if isinstance(x, BApp):
            out.append("`")
            stack.extend([x.arg, x.fn])
        elif isinstance(x, Var):
            out.append(f"v{x.n} ")
        elif isinstance(x, Ref):
            out.append(f"#{structural_hash(x.term)[len('skijack-1:'):]} ")
        else:
            out.append(f"{x.name} ")
    return "".join(out).rstrip()


def refs(b: Body) -> Iterable[Term]:
    stack = [b]
    while stack:
        x = stack.pop()
        if isinstance(x, BApp):
            stack += [x.fn, x.arg]
        elif isinstance(x, Ref):
            yield x.term


def write(ts: List[Template], templates_path, terms_path) -> Tuple[int, int]:
    """Write templates.tsv and template_terms.tsv; their line counts."""
    lines = []
    terms: Dict[str, Term] = {}
    for t in ts:
        for r in refs(t.body):
            terms.setdefault(structural_hash(r), r)
        formals = ",".join(str(n) for n in t.formals)
        lines.append("\t".join([t.key_hash, t.kind, t.label.replace("\t", " "),
                                str(t.arity), formals, body_text(t.body)]))
    templates_path.write_text("".join(line + "\n" for line in lines))
    rows = []
    for h in sorted(terms):
        term = terms[h]
        rows.append(f"{h}\t{_atoms(term)}\t{pretty(term)}\n")
    terms_path.write_text("".join(rows))
    return len(lines), len(rows)


def _atoms(t: Term) -> int:
    n, stack = 0, [t]
    while stack:
        x = stack.pop()
        if isinstance(x, App):
            stack += [x.fn, x.arg]
        else:
            n += 1
    return n
