"""The front ends' generated declarations (docs/SKIJACK-0.md §5).

    python3 -m skijack.selfhost.tables [front0|front1]

A front end reads characters as 7-bit codes and classifies each by a
case on its bits; that tree is long and regular, so this writes it, the
name constants the front end compares against, and one predicate
or table per question it asks of a token, into the front end's source
between the markers `-- BEGIN GENERATED` and `-- END GENERATED`.  The
file is the source; this only keeps its tables consistent.  front0 is
SKIjack-0's front end; front1 the full language's, being built (avon
docs/WORKLIST.md, Stage 8), with more symbols, names and tokens.
"""

from __future__ import annotations

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent


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


SYMBOLS0 = {"=": "SEq", "|": "SBar", ">": "SGt", ":": "SColon", "\\": "SBack",
            ".": "SDot", ";": "SSemi", "(": "SLP", ")": "SRP", "[": "SLB",
            "]": "SRB", "{": "SLC", "}": "SRC", "@": "SAt", "-": "SMinus"}

#: front1 adds `*` and `!`, which follow `:=` in a macro's operator, and
#: `<`, which opens a quotation, and a scry's and a namespace literal's
#: `?`, `^`, `,` and `/`
SYMBOLS1 = dict(SYMBOLS0, **{"*": "SStar", "!": "SBang", "<": "SLt", "?": "SQuest",
                             "^": "SCaret", ",": "SComma", "/": "SSlash"})

#: the front end being generated: set by main
SYMBOLS = SYMBOLS0


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
RESERVED0 = [("S", "S"), ("K", "K"), ("I", "I"), ("Pair", "pair"), ("Hd", "hd"),
             ("Tl", "tl"), ("Nil", "nil"), ("Cons", "cons"), ("Zero", "zero"),
             ("Suc", "suc"), ("At", "@"), ("None", "")]

#: front1 adds the Tier 1 birds, which a program may name (skijack/abi.py);
#: `loop`, the equation an interpreter core's name denotes; and the numeral
#: operations, installed when a program names one (skijack/expand.py)
RESERVED1 = RESERVED0 + [("B", "B"), ("C", "C"), ("W", "W"), ("Y", "Y"),
                         ("Loop", "loop"), ("NatAdd", "natAdd"), ("NatSub", "natSub"),
                         ("NatMul", "natMul"), ("NatIfEq", "natIfEq"), ("NatIfLe", "natIfLe")]

#: and the names interpreter generation writes (skijack/generate.py): the
#: prefixes of the names it builds, `res`, `step` and `c`, and the rest
RESERVED1 += [("G" + k, v) for k, v in [
    ("Res", "res"), ("Step", "step"), ("LowC", "c"), ("SpApp", "spApp"), ("Sp", "sp"),
    ("Rb1", "rb1"), ("Rb", "rb"), ("Acc", "acc"), ("F", "f"), ("T", "t"), ("U", "u"),
    ("M", "m"), ("H", "h"), ("X", "x"), ("Xs", "xs"), ("Args", "args"), ("Y", "y"),
    ("Z", "z"), ("Rest", "rest"), ("R", "r"), ("R2", "r2"), ("N", "n"), ("N2", "n2"),
    ("Loop1", "loop1"), ("StepI", "stepI"), ("StepI1", "stepI1"), ("StepK", "stepK"),
    ("StepK2", "stepK2"), ("StepK1", "stepK1"), ("StepS", "stepS"), ("StepS3", "stepS3"),
    ("StepS2", "stepS2"), ("StepS1", "stepS1")]]

#: and quotation's: the default interpreter core, and the path type's name
RESERVED1 += [("WhnfF", "whnfF"), ("Path", "path")]

#: and scry's and namespace literals': the object type's scry leaf, the
#: path comparison a resolver calls, and `ns`, which before `{` opens one
RESERVED1 += [("Scry", "Scry"), ("EQ5", "EQ5"), ("Ns", "ns")]

RESERVED = RESERVED0


def bits(n: int) -> str:
    """n as the front end's binary number, least significant bit first."""
    out = "Bn"
    for b in bin(n)[2:] if n else "":   # most significant first, nested deepest
        out = f"({'Bo' if b == '1' else 'Bz'} {out})"
    return out


#: the token type's constructors, as front0.ascii.ski declares them
TOKS0 = ["TName", "TAxis", "TTypeDecl", "TCase", "TAssign", "TEq", "TAlt", "TLam", "TDot",
         "TSemi", "TLP", "TRP", "TLB", "TRB", "TLC", "TRC", "TNl", "TBad"]

#: front1's: a signature's `:` and `->`, a macro's `:=*` and `:=!`, a
#: quotation's `<` and `>`, `|-`, and fuel, `@n` or `@[]`
TOKS1 = TOKS0[:-1] + ["TColon", "TArrow", "TMacro", "TCMacro", "TQOpen", "TQClose",
                      "TTurn", "TFuel", "TFuelE", "TScry", "TNsOpen", "TMapsTo", "TComma",
                      "TSlash", "TGlue", "TBad"]

#: the tokens a predicate `isX` is written for
TESTED0 = ["TTypeDecl", "TCase", "TAlt", "TDot", "TSemi", "TRP", "TRB", "TLC", "TRC", "TNl"]
TESTED1 = TESTED0 + ["TAssign", "TArrow", "TQOpen", "TQClose", "TTurn", "TMapsTo", "TComma",
                     "TSlash", "TGlue", "TLB"]

#: each declaration operator's kind
DECLOPS0 = {"TTypeDecl": "OType", "TEq": "OEq", "TAssign": "ODef"}
DECLOPS1 = dict(DECLOPS0, TColon="OSig", TMacro="OMacro", TCMacro="OCMacro")

TOKS, TESTED, DECLOPS = TOKS0, TESTED0, DECLOPS0


def over_tokens(fn: str, each) -> str:
    """`fn t = t |> { ... }`, a branch per token constructor."""
    arms = []
    for k in TOKS:
        binder = {"TName": " n", "TAxis": " n", "TFuel": " n"}.get(k, "")
        arms.append(f"{k}{binder} {each(k)}")
    return f"{fn} t = t |> {{ {' ; '.join(arms)} }}"


def token_tables() -> list:
    lines = [over_tokens("is" + k[1:], lambda x, k=k: "Yes" if x == k else "No") for k in TESTED]
    lines.append(over_tokens("atomStart", lambda x: "Yes" if x in
                             ("TName", "TAxis", "TLP", "TLB", "TLam", "TQOpen", "TScry",
                              "TNsOpen") else "No"))
    lines.append(over_tokens("nameOf", lambda x: "(MName n)" if x == "TName" else "MNone"))
    lines.append(over_tokens("depthKind", lambda x: {"TLP": "DOpen", "TLB": "DOpen", "TLC": "DOpen",
                                                     "TQOpen": "DOpen", "TNsOpen": "DOpen",
                                                     "TRP": "DClose",
                                                     "TRB": "DClose", "TRC": "DClose",
                                                     "TQClose": "DClose", "TNl": "DNl"}.get(x, "DOther")))
    lines.append(over_tokens("declOp", lambda x: DECLOPS.get(x, "ONone")))
    if "TFuel" in TOKS:
        lines.append(over_tokens("fuelOf", lambda x: {"TFuel": "(FNum n)", "TFuelE": "FPol"}.get(x, "FNone")))
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
    codes = [("codeGt", ">"), ("codeEqc", "="), ("codeMinus", "-"), ("codeNl", "\n")]
    if SYMBOLS is SYMBOLS1:
        codes += [("codeStar", "*"), ("codeBang", "!"), ("codeDot", ".")]
        codes += [(f"codeD{d}", str(d)) for d in range(10)]
        codes += [("codeLB", "["), ("codeRB", "]"), ("codeCaret", "^"), ("codeLC", "{")]
    for k, ch in codes:
        lines.append(f"{k} := {code(ord(ch))}")
    lines.extend(token_tables())
    return "\n".join(lines) + "\n"


def select(front: str) -> pathlib.Path:
    """Generate for `front` (front0 or front1) from here on; its source."""
    global SYMBOLS, RESERVED, TOKS, TESTED, DECLOPS
    if front == "front1":
        SYMBOLS, RESERVED, TOKS, TESTED, DECLOPS = SYMBOLS1, RESERVED1, TOKS1, TESTED1, DECLOPS1
    elif front == "front0":
        SYMBOLS, RESERVED, TOKS, TESTED, DECLOPS = SYMBOLS0, RESERVED0, TOKS0, TESTED0, DECLOPS0
    else:
        raise ValueError(f"no front end {front!r}")
    return HERE / f"{front}.ascii.ski"


def main() -> int:
    front = sys.argv[1] if len(sys.argv) > 1 else "front0"
    if front not in ("front0", "front1"):
        print("usage: python3 -m skijack.selfhost.tables [front0|front1]", file=sys.stderr)
        return 2
    source = select(front)
    text = source.read_text()
    begin, end = "-- BEGIN GENERATED\n", "-- END GENERATED\n"
    i, j = text.index(begin) + len(begin), text.index(end)
    source.write_text(text[:i] + generated() + text[j:])
    print(f"wrote the generated declarations into {source}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
