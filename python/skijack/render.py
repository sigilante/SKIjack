"""Tree -> text, in either lexicon.

The law tested in ``tests/test_roundtrip.py`` is the one of
``DESIDERATA.md`` item 4 restricted to the surface: for a corpus source
``S`` in lexicon ``L``, ``parse_L(render_L(parse_L(S))) == parse_L(S)``,
and across lexicons ``parse_A(render_A(parse_U(S))) == parse_U(S)``.
Whitespace is not reproduced, only an equal tree.

Every operator spelling is read out of the token table, which is a strict
bijection, so the renderer never has to decide between two spellings of
one token kind.  The two places the *construct* rather than the token
picks the text are the namespace literal's closer (``}`` against ``}``)
and a Tier 1 name's glyph (``⇄`` for ``C``), both stated in
``SYNTAX.md`` §2 and its lexing notes.
"""

from __future__ import annotations

from typing import Dict, List

from . import ast as A
from .lexicon import GLYPH_NAMES, TOKEN_TABLE

__all__ = ["render", "render_ascii", "render_unicode"]

_SUB = {str(i): chr(0x2080 + i) for i in range(10)}


def _spellings(lexicon: str):
    out: Dict[str, str] = {}
    for r in TOKEN_TABLE:
        if not r.structural:
            continue
        out.setdefault(r.kind, getattr(r, lexicon))
    return out


_ASCII = _spellings("ascii")
_UNICODE = _spellings("unicode")


class _Renderer:
    def __init__(self, lexicon: str):
        if lexicon not in ("ascii", "unicode"):
            raise ValueError(lexicon)
        self.lx = lexicon
        self.t = _ASCII if lexicon == "ascii" else _UNICODE

    # both come straight from the table now that they are distinct kinds
    def mapsto(self) -> str:
        return self.t["MAPSTO"]

    def arrow(self) -> str:
        return self.t["ARROW"]

    def ns_close(self) -> str:
        """``SYNTAX.md`` §2: ``}`` is the same token kind as ``}``, so the
        closer is chosen by the construct, not by the token."""
        return "}" if self.lx == "ascii" else "}"

    def name(self, n: str) -> str:
        if self.lx == "unicode" and n in GLYPH_NAMES:
            return GLYPH_NAMES[n]
        return n

    def fuel(self, f) -> str:
        if f is None:
            return ""
        if self.lx == "ascii":
            return "@[]" if f == A.POLICY else f"@{f}"
        if f == A.POLICY:
            return "₍₎"
        return "".join(_SUB[c] for c in str(f))

    # --- expressions -----------------------------------------------------
    # prec 0: anywhere;  1: as the function of an application;
    # 2: as an argument / a cell item (must be an atom)

    def expr(self, e, prec: int = 0) -> str:
        if isinstance(e, A.Name):
            return self.name(e.name)
        if isinstance(e, A.Num):
            return str(e.value)
        if isinstance(e, A.App):
            s = f"{self.expr(e.fn, 1)} {self.expr(e.arg, 2)}"
            return f"({s})" if prec >= 2 else s
        if isinstance(e, A.Cell):
            return "[" + " ".join(self.expr(x, 2) for x in e.items) + "]"
        if isinstance(e, A.Pick):
            mark = "@" if self.lx == "ascii" else "⊑"
            return f"{e.axis}{mark}{self.expr(e.expr, 2)}"
        if isinstance(e, A.Scry):
            return self.t["SCRY"] + self.path(e.path)
        if isinstance(e, A.Quote):
            q = (f"{self.t['QOPEN']}{self.expr(e.expr, 0)}"
                 f"{self.t['QCLOSE']}{self.fuel(e.fuel)}")
            if e.interp is None:
                return q
            s = f"{self.expr(e.interp, 1)} {self.t['TURNSTILE']} {q}"
            return f"({s})" if prec >= 1 else s
        if isinstance(e, A.Lambda):
            s = f"{self.t['LAMBDA']}{e.param}.{self.expr(e.body, 0)}"
            return f"({s})" if prec >= 1 else s
        if isinstance(e, A.Case):
            branches = " ; ".join(
                " ".join([self.name(c)] + list(bs) + [self.expr(b, 0)])
                for c, bs, b in e.branches)
            s = f"{self.expr(e.scrutinee, 1)} {self.t['CASE']} {{ {branches} }}"
            return f"({s})" if prec >= 1 else s
        if isinstance(e, A.NsLit):
            facts = ", ".join(
                f"{self.path(p)} {self.mapsto()} {self.expr(v, 0)}"
                for p, v in e.facts)
            return f"{self.t['NSOPEN']}{facts}{self.ns_close()}"
        raise TypeError(f"cannot render {e!r}")

    def path(self, p: A.Path) -> str:
        out = []
        for seg in p.segments:
            s = "/" + seg.tag
            if seg.payload is not None:
                s += "[" + self.expr(seg.payload, 0) + "]"
            out.append(s)
        return "".join(out)

    # --- declarations ----------------------------------------------------

    def decl(self, d) -> str:
        if isinstance(d, A.TypeDecl):
            ctors = f" {self.t['ALT']} ".join(
                " ".join([self.name(c.name)] + list(c.fields)) for c in d.ctors)
            return f"{self.name(d.name)} {self.t['TYPEDECL']} {ctors}"
        if isinstance(d, A.Sig):
            return (f"{self.name(d.name)} {self.t['COLON']} "
                    + f" {self.arrow()} ".join(d.types))
        if isinstance(d, A.Equation):
            head = " ".join([self.name(d.name)] + list(d.binders))
            return f"{head} {self.t['EQUALS']} {self.expr(d.body, 0)}"
        if isinstance(d, A.Core):
            equations = "\n".join("  " + self.decl(x) for x in d.equations)
            head = " ".join([self.name(d.name)] + list(d.params))
            return f"{head} {self.t['ASSIGN']} {{\n{equations}\n}}"
        if isinstance(d, A.Macro):
            op = self.t["CMACRO"] if d.capturing else self.t["MACRO"]
            head = " ".join([self.name(d.name)] + list(d.params))
            return f"{head} {op} {self.expr(d.body, 0)}"
        if isinstance(d, A.Def):
            return (f"{self.name(d.name)} {self.t['ASSIGN']} "
                    f"{self.expr(d.expr, 0)}")
        raise TypeError(f"cannot render {d!r}")

    def program(self, p: A.Program) -> str:
        lines: List[str] = [self.decl(d) for d in p.decls]
        return "\n".join(lines) + "\n"


def render(node, lexicon: str) -> str:
    r = _Renderer(lexicon)
    if isinstance(node, A.Program):
        return r.program(node)
    if isinstance(node, (A.TypeDecl, A.Sig, A.Equation, A.Core, A.Macro, A.Def)):
        return r.decl(node)
    return r.expr(node, 0)


def render_ascii(node) -> str:
    return render(node, "ascii")


def render_unicode(node) -> str:
    return render(node, "unicode")
