"""One grammar over token kinds; both lexers feed it.

The grammar is the sketch of ``SYNTAX.md`` §4 with the token table's
substitutions applied by :mod:`skijack.lexicon`, so nothing below knows
which lexicon the source was written in.

Two decisions the sketch leaves open (both documented in the README):

(a) A case branch is ``CName binder* body`` and the number of binders is
    the constructor's *declared* arity, so the parser needs the type
    declarations before it can parse a body.  Parsing is therefore two
    pass: :func:`collect_ctors` scans the token stream for ``===``
    declarations, then the real parse runs with that table.  An
    undeclared constructor in a branch is a :class:`ParseError`.

(b) A core body ``{ equations }`` and a namespace literal ``ns{ ... }`` are
    told apart by the ``ns`` prefix, which the ASCII lexer munches as one
    NSOPEN token (Unicode spells it ``ns{``).

A namespace literal's facts use MAPSTO (``=>`` / ``↦``); a signature uses
ARROW (``->`` / ``→``).  They are different token kinds in both lexicons,
so no grammar position has to disambiguate them.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Tuple

from . import ast as A
from .lexicon import Token, lex

__all__ = ["ParseError", "parse", "parse_ascii", "parse_unicode",
           "collect_ctors", "parse_expr_text"]


from .errors import SkijackError

class ParseError(SkijackError):
    pass


#: token kinds that can begin an atom
_ATOM_START = {"IDENT", "LPAREN", "LBRACK", "QOPEN", "SCRY", "AXIS",
               "LAMBDA", "NSOPEN", "NUMBER"}

#: token kinds that terminate the leading name run of a declaration
_DECL_OPS = {"TYPEDECL", "COLON", "ASSIGN", "MACRO", "CMACRO", "EQUALS"}


def collect_ctors(tokens: List[Token]) -> Dict[str, Tuple[str, int, int]]:
    """Pass one: constructor name -> (type name, declaration index, arity).

    A ``===`` declaration runs to the end of its logical line, which is
    how the scan knows where the field types stop and the next
    declaration begins.
    """
    table: Dict[str, Tuple[str, int, int]] = {}
    for i, tok in enumerate(tokens):
        if tok.kind != "TYPEDECL":
            continue
        if i == 0 or tokens[i - 1].kind != "IDENT":
            raise ParseError(
                f"line {tok.line}: type declaration needs a name on its left")
        tname = tokens[i - 1].text
        j = i + 1
        groups: List[List[str]] = [[]]
        while tokens[j].kind not in ("NEWLINE", "EOF"):
            t = tokens[j]
            if t.kind == "ALT":
                groups.append([])
            elif t.kind == "IDENT":
                groups[-1].append(t.text)
            else:
                raise ParseError(
                    f"line {t.line}: unexpected {t.kind} in the declaration "
                    f"of type {tname!r}")
            j += 1
        for idx, g in enumerate(groups):
            if not g:
                raise ParseError(
                    f"line {tok.line}: empty constructor in type {tname!r}")
            cname = g[0]
            if cname in table:
                raise ParseError(f"constructor {cname!r} declared twice")
            table[cname] = (tname, idx, len(g) - 1)
    return table


class _Parser:
    def __init__(self, tokens: List[Token], ctors: Dict[str, Tuple[str, int, int]]):
        self.toks = tokens
        self.i = 0
        self.ctors = ctors
        self.depth = 0          # bracket nesting; > 0 makes NEWLINE invisible

    # --- token plumbing --------------------------------------------------

    def peek(self, ahead: int = 0) -> Token:
        j = self.i
        seen = 0
        while True:
            t = self.toks[j]
            if t.kind == "NEWLINE" and self.depth > 0:
                j += 1
                continue
            if seen == ahead:
                return t
            seen += 1
            j += 1

    def next(self) -> Token:
        while self.toks[self.i].kind == "NEWLINE" and self.depth > 0:
            self.i += 1
        t = self.toks[self.i]
        self.i += 1
        return t

    def expect(self, kind: str) -> Token:
        t = self.next()
        if t.kind != kind:
            raise ParseError(
                f"line {t.line}, column {t.col}: expected {kind}, got "
                f"{t.kind} {t.value!r}")
        return t

    def at(self, kind: str) -> bool:
        return self.peek().kind == kind

    def skip_newlines(self) -> None:
        while self.toks[self.i].kind == "NEWLINE":
            self.i += 1

    def end_of_decl(self, also: Tuple[str, ...] = ()) -> None:
        """A declaration ends at a newline or end of input; inside a core
        a closing ``}`` ends the last equation too, so a one-equation core fits on
        one line."""
        t = self.toks[self.i]
        if t.kind in ("NEWLINE", "EOF") or t.kind in also:
            return
        raise ParseError(
            f"line {t.line}, column {t.col}: unexpected {t.kind} {t.value!r} "
            f"at the end of a declaration")

    # --- program ---------------------------------------------------------

    def program(self) -> A.Program:
        decls: List[A.Decl] = []
        while True:
            self.skip_newlines()
            if self.toks[self.i].kind == "EOF":
                break
            decls.append(self.decl())
        return A.Program(tuple(decls))

    def decl(self) -> A.Decl:
        names, op = self._lookahead_head()
        if op == "TYPEDECL":
            return self.type_decl(names)
        if op == "COLON":
            return self.sig(names)
        if op == "ASSIGN":
            return self.core_or_def(names)
        if op in ("MACRO", "CMACRO"):
            return self.macro(names, capturing=(op == "CMACRO"))
        if op == "EQUALS":
            return self.equation(names)
        t = self.toks[self.i]
        raise ParseError(
            f"line {t.line}, column {t.col}: not a declaration "
            f"(expected one of :=, :=*, :=!, =, ===, :)")

    def _lookahead_head(self) -> Tuple[List[str], Optional[str]]:
        """The run of names that opens a declaration, and the operator
        that follows it."""
        j = self.i
        names: List[str] = []
        while self.toks[j].kind == "IDENT":
            names.append(self.toks[j].text)
            j += 1
        kind = self.toks[j].kind
        if not names or kind not in _DECL_OPS:
            return names, None
        return names, kind

    def _take_names(self, n: int) -> None:
        for _ in range(n):
            self.expect("IDENT")

    # --- declarations ----------------------------------------------------

    def type_decl(self, names: List[str]) -> A.TypeDecl:
        if len(names) != 1:
            raise ParseError(f"type declaration {names!r}: one name before ===")
        self._take_names(1)
        self.expect("TYPEDECL")
        ctors: List[A.Ctor] = []
        while True:
            cname = self.expect("IDENT").text
            fields: List[str] = []
            while self.toks[self.i].kind == "IDENT":
                fields.append(self.toks[self.i].text)
                self.i += 1
            ctors.append(A.Ctor(cname, tuple(fields)))
            if self.toks[self.i].kind == "ALT":
                self.i += 1
                continue
            break
        self.end_of_decl()
        return A.TypeDecl(names[0], tuple(ctors))

    def sig(self, names: List[str]) -> A.Sig:
        if len(names) != 1:
            raise ParseError(f"signature {names!r}: one name before ':'")
        self._take_names(1)
        self.expect("COLON")
        types = [self.expect("IDENT").text]
        while self.toks[self.i].kind == "ARROW":
            self.i += 1
            types.append(self.expect("IDENT").text)
        self.end_of_decl()
        return A.Sig(names[0], tuple(types))

    def core_or_def(self, names: List[str]) -> A.Decl:
        # a core may take parameters: `wfQ e := { ... }`
        if self.toks[self.i + len(names) + 1].kind == "LBRACE" or (
                len(names) == 1
                and self.toks[self.i + 1].kind == "ASSIGN"
                and self.toks[self.i + 2].kind == "LBRACE"):
            self._take_names(len(names))
            self.expect("ASSIGN")
            return self.core(names[0], tuple(names[1:]))
        if len(names) != 1:
            raise ParseError(
                f"{names[0]!r}: ':=' takes binders only for a core "
                f"('name p := {{ equations }}'); write an equation with '=' or a macro "
                f"with ':=*'")
        self._take_names(1)
        self.expect("ASSIGN")
        e = self.expr()
        self.end_of_decl()
        return A.Def(names[0], e)

    def core(self, name: str, params=()) -> A.Core:
        self.expect("LBRACE")
        equations: List[A.Equation] = []
        while True:
            self.skip_newlines()
            if self.toks[self.i].kind == "RBRACE":
                self.i += 1
                break
            if self.toks[self.i].kind == "EOF":
                raise ParseError(f"core {name!r}: unterminated block")
            anames, op = self._lookahead_head()
            if op != "EQUALS":
                t = self.toks[self.i]
                raise ParseError(
                    f"line {t.line}: a core body holds equations "
                    f"'name binder* = body'")
            equations.append(self.equation(anames, also=("RBRACE",)))
        self.end_of_decl()
        return A.Core(name, tuple(equations), tuple(params))

    def macro(self, names: List[str], capturing: bool) -> A.Macro:
        self._take_names(len(names))
        self.next()
        body = self.expr()
        self.end_of_decl()
        return A.Macro(names[0], tuple(names[1:]), body, capturing)

    def equation(self, names: List[str], also: Tuple[str, ...] = ()) -> A.Equation:
        self._take_names(len(names))
        self.expect("EQUALS")
        body = self.expr()
        self.end_of_decl(also)
        return A.Equation(names[0], tuple(names[1:]), body)

    # --- expressions -----------------------------------------------------

    def expr(self) -> A.Expr:
        e = self.app()
        while True:
            k = self.peek().kind
            if k == "CASE":
                self.next()
                e = A.Case(e, self.branches())
            elif k == "TURNSTILE":
                self.next()
                q = self.quote()
                e = A.Quote(q.expr, q.fuel, interp=e)
            else:
                return e

    def app(self) -> A.Expr:
        e = self.atom()
        while self.peek().kind in _ATOM_START:
            e = A.App(e, self.atom())
        return e

    def atom(self) -> A.Expr:
        t = self.peek()
        k = t.kind
        if k == "IDENT":
            self.next()
            name = t.text
            while (self.toks[self.i].kind == "DOT"
                   and self.toks[self.i + 1].kind == "IDENT"):
                self.i += 1
                name += "." + self.expect("IDENT").text
            return A.Name(name)
        if k == "LPAREN":
            self.next()
            self.depth += 1
            e = self.expr()
            self.depth -= 1
            self.expect("RPAREN")
            return e
        if k == "LBRACK":
            self.next()
            self.depth += 1
            items = []
            while self.peek().kind in _ATOM_START:
                items.append(self.atom())
            self.depth -= 1
            self.expect("RBRACK")
            if len(items) < 2:
                raise ParseError(
                    f"line {t.line}: a cell needs at least two items")
            return A.Cell(tuple(items))
        if k == "QOPEN":
            return self.quote()
        if k == "SCRY":
            self.next()
            return A.Scry(self.path())
        if k == "AXIS":
            self.next()
            return A.Pick(t.number, self.atom())
        if k == "LAMBDA":
            self.next()
            param = self.expect("IDENT").text
            self.expect("DOT")
            return A.Lambda(param, self.expr())
        if k == "NSOPEN":
            return self.nslit()
        if k == "NUMBER":
            self.next()
            return A.Num(t.number)
        raise ParseError(
            f"line {t.line}, column {t.col}: expected an expression, got "
            f"{t.kind} {t.value!r}")

    def quote(self) -> A.Quote:
        self.expect("QOPEN")
        self.depth += 1
        e = self.expr()
        self.depth -= 1
        self.expect("QCLOSE")
        fuel = None
        if self.toks[self.i].kind == "FUEL":
            fuel = self.toks[self.i].value
            self.i += 1
        return A.Quote(e, fuel, None)

    def path(self) -> A.Path:
        segs: List[A.Seg] = []
        while self.toks[self.i].kind == "SLASH":
            self.i += 1
            tag = self.expect("IDENT").text
            payload = None
            if self.toks[self.i].kind == "LBRACK":
                self.i += 1
                self.depth += 1
                payload = self.expr()
                self.depth -= 1
                self.expect("RBRACK")
            segs.append(A.Seg(tag, payload))
        if not segs:
            t = self.peek()
            raise ParseError(
                f"line {t.line}: a path is one or more '/tag' segments")
        return A.Path(tuple(segs))

    def nslit(self) -> A.NsLit:
        self.expect("NSOPEN")
        self.depth += 1
        facts = []
        if self.peek().kind == "RBRACE":     # the empty namespace
            self.next()
            self.depth -= 1
            return A.NsLit(())
        while True:
            p = self.path()
            self.expect("MAPSTO")
            facts.append((p, self.expr()))
            if self.peek().kind == "COMMA":
                self.next()
                continue
            break
        self.depth -= 1
        self.expect("RBRACE")
        return A.NsLit(tuple(facts))

    def branches(self):
        self.expect("LBRACE")
        self.depth += 1
        out = []
        while True:
            t = self.expect("IDENT")
            cname = t.text
            if cname not in self.ctors:            # decision (a)
                raise ParseError(
                    f"line {t.line}, column {t.col}: undeclared constructor "
                    f"{cname!r} in a case branch; declare it with "
                    f"'type === {cname} ...' before use")
            _tname, _idx, arity = self.ctors[cname]
            binders = tuple(self.expect("IDENT").text for _ in range(arity))
            out.append((cname, binders, self.expr()))
            if self.peek().kind == "SEMI":
                self.next()
                continue
            break
        self.depth -= 1
        self.expect("RBRACE")
        return tuple(out)


def parse(text: str, lexicon: str) -> A.Program:
    tokens = lex(text, lexicon)
    return _Parser(tokens, collect_ctors(tokens)).program()


def parse_ascii(text: str) -> A.Program:
    return parse(text, "ascii")


def parse_unicode(text: str) -> A.Program:
    return parse(text, "unicode")


def parse_expr_text(text: str, lexicon: str = "ascii") -> A.Expr:
    """Parse a bare expression; convenient for tests."""
    tokens = lex(text, lexicon)
    p = _Parser(tokens, collect_ctors(tokens))
    p.depth += 1
    e = p.expr()
    p.depth -= 1
    if p.toks[p.i].kind not in ("NEWLINE", "EOF"):
        t = p.toks[p.i]
        raise ParseError(f"trailing {t.kind} {t.value!r}")
    return e
