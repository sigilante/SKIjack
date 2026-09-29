"""The front end's generated declarations (docs/SKIJACK-0.md §5).

    python3 -m skijack.selfhost.tables

The front end reads characters as 7-bit codes and classifies each by a
case on its bits; that tree is long and regular, so this writes it, the
name constants the front end compares against, and one predicate
or table per question it asks of a token, into front0.ascii.ski
between the markers `-- BEGIN GENERATED` and `-- END GENERATED`.  The
file is the source; this only keeps its tables consistent.
"""

from __future__ import annotations

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
SOURCE = HERE / "front0.ascii.ski"


def code(n: int) -> str:
    bits = [(n >> (6 - i)) & 1 for i in range(7)]
    return "(Code " + " ".join("Hi" if b else "Lo" for b in bits) + ")"


def nat(n: int) -> str:
    out = "Zero"
    for _ in range(n):
        out = f"(Suc {out})"
    return out


def name(s: str) -> str:
    out = "NNil"
    for ch in reversed(s):
        out = f"(NCons {code(ord(ch))} {out})"
    return out


SYMBOLS = {"=": "SEq", "|": "SBar", ">": "SGt", ":": "SColon", "\\": "SBack",
           ".": "SDot", ";": "SSemi", "(": "SLP", ")": "SRP", "[": "SLB",
           "]": "SRB", "{": "SLC", "}": "SRC", "@": "SAt", "-": "SMinus"}


def classify(n: int) -> str:
    ch = chr(n)
    if ch in " \t\r":
        return "ChSpace"
    if ch == "\n":
        return "ChNl"
    if ch.isascii() and (ch.isalpha() or ch == "_"):
        return "ChLetter"
    if ch.isdigit():
        return f"(ChDigit {nat(n - 48)})"
    if ch == "'":
        return "ChPrime"
    if ch in SYMBOLS:
        return f"(ChSym {SYMBOLS[ch]})"
    return "ChOther"


#: the names the front end must recognize, interned first and in this
#: order: `@` is the name no identifier can be, for a recursion's own
#: variable and the cycle mark; the empty name is a formal never looked up
RESERVED = [("S", "S"), ("K", "K"), ("I", "I"), ("Pair", "pair"), ("Hd", "hd"),
            ("Tl", "tl"), ("Nil", "nil"), ("Cons", "cons"), ("Zero", "zero"),
            ("Suc", "suc"), ("At", "@"), ("None", "")]


def bits(n: int) -> str:
    """n as the front end's binary number, least significant bit first."""
    out = "Bn"
    for b in bin(n)[2:] if n else "":   # most significant first, nested deepest
        out = f"({'Bo' if b == '1' else 'Bz'} {out})"
    return out


#: the token type's constructors, as front0.ascii.ski declares them
TOKS = ["TName", "TAxis", "TTypeDecl", "TCase", "TAssign", "TEq", "TAlt", "TLam", "TDot",
        "TSemi", "TLP", "TRP", "TLB", "TRB", "TLC", "TRC", "TNl", "TBad"]

#: the tokens a predicate `isX` is written for
TESTED = ["TTypeDecl", "TCase", "TAlt", "TDot", "TSemi", "TRP", "TRB", "TLC", "TRC", "TNl"]


def over_tokens(fn: str, each) -> str:
    """`fn t = t |> { ... }`, a branch per token constructor."""
    arms = []
    for k in TOKS:
        binder = {"TName": " n", "TAxis": " n"}.get(k, "")
        arms.append(f"{k}{binder} {each(k)}")
    return f"{fn} t = t |> {{ {' ; '.join(arms)} }}"


def token_tables() -> list:
    lines = [over_tokens("is" + k[1:], lambda x, k=k: "Yes" if x == k else "No") for k in TESTED]
    lines.append(over_tokens("atomStart", lambda x: "Yes" if x in
                             ("TName", "TAxis", "TLP", "TLB", "TLam") else "No"))
    lines.append(over_tokens("nameOf", lambda x: "(MName n)" if x == "TName" else "MNone"))
    lines.append(over_tokens("depthKind", lambda x: {"TLP": "DOpen", "TLB": "DOpen", "TLC": "DOpen",
                                                     "TRP": "DClose", "TRB": "DClose", "TRC": "DClose",
                                                     "TNl": "DNl"}.get(x, "DOther")))
    lines.append(over_tokens("declOp", lambda x: {"TTypeDecl": "OType", "TEq": "OEq",
                                                  "TAssign": "ODef"}.get(x, "ONone")))
    return lines


def classify_tree(prefix: int = 0, depth: int = 0) -> str:
    """`classify`'s body: a case on each bit, most significant first, with
    a subtree whose characters all classify alike cut to that class."""
    lo, hi = prefix << (7 - depth), (prefix + 1) << (7 - depth)
    classes = {classify(n) for n in range(lo, hi)}
    if len(classes) == 1:
        return classes.pop()
    b = f"b{6 - depth}"
    zero = classify_tree(prefix << 1, depth + 1)
    one = classify_tree((prefix << 1) | 1, depth + 1)
    return f"({b} |> {{ Lo {zero} ; Hi {one} }})"


def generated() -> str:
    lines = [f"classify c = c |> {{ Code b6 b5 b4 b3 b2 b1 b0 {classify_tree()} }}"]
    for k, v in RESERVED:
        lines.append(f"name{k} := {name(v)}")
    for i, (k, _v) in enumerate(RESERVED):
        lines.append(f"id{k} := Id {bits(i)}")
    seed = "NmNil"
    for k, _v in reversed(RESERVED):
        seed = f"(NmCons (IdRaw name{k}) {seed})"
    lines.append(f"seedNames := {seed}")
    for k, ch in [("codeGt", ">"), ("codeEqc", "="),
                  ("codeMinus", "-"), ("codeNl", "\n")]:
        lines.append(f"{k} := {code(ord(ch))}")
    lines.extend(token_tables())
    return "\n".join(lines) + "\n"


def main() -> int:
    text = SOURCE.read_text()
    begin, end = "-- BEGIN GENERATED\n", "-- END GENERATED\n"
    i, j = text.index(begin) + len(begin), text.index(end)
    SOURCE.write_text(text[:i] + generated() + text[j:])
    print(f"wrote the generated declarations into {SOURCE}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
