"""skijack -- a surface language over SKI.

The pipeline, end to end: :func:`compile` parses, checks (Stage A),
generates the type-generated forms, and expands to closed ``{S,K,I}``
terms; :func:`run_level1` runs a level-1 declaration; :func:`lift` names
what the dictionary knows.  ``python3 -m skijack FILE`` does all of it
from the command line.

See ``../README.md`` for what is implemented and what is not.
"""

from . import ast
from .errors import SkijackError
from .lexicon import lex_ascii, lex_unicode, LexError, TOKEN_TABLE
from .parser import parse, parse_ascii, parse_unicode, ParseError
from .render import render, render_ascii, render_unicode
from .expand import expand_program, Expansion, ExpandError
from .generate import generate, GenerateError
from .quote import quote, Encoder, QuoteError
from .run import (run_level0, run_level1, run_policy, run_with_namespace,
                  make_resolver, peel, decode, RunError)
from .check import (check, check_program, CheckError, ArityError, CaseError,
                    DataError, InterfaceError, SymbolTableError, ScopeError)
from .typecheck import typecheck, typecheck_program, TypeMismatchError
from .dictionary import (Dictionary, Entry, from_expansion, lift, lower,
                         structural_hash, VERSION as DICTIONARY_VERSION)


def compile(source: str, lexicon: str = "ascii", *, check: bool = True,
            generate_forms: bool = True, inline: bool = False) -> Expansion:
    """Source text -> a compiled program.

    Parse, then Stage A (``check``), then the type-generated forms
    (``generate_forms``), then expansion.  Checking can only reject, so
    the terms are the same either way (``DESIDERATA.md`` item 11).
    ``inline`` unfolds small functions at their calls (:mod:`skijack.inline`):
    other terms, the same values; off by default.
    """
    return expand_program(parse(source, lexicon), check=check,
                          generate_forms=generate_forms, inline=inline)


#: ``compile`` shadows the builtin inside this module's namespace only;
#: this alias is for callers who would rather not.
compile_source = compile
from .probe import Prober, fast_reduce

from ._version import __version__

__all__ = [
    "ast", "SkijackError", "lex_ascii", "lex_unicode", "LexError",
    "TOKEN_TABLE",
    "parse", "parse_ascii", "parse_unicode", "ParseError",
    "render", "render_ascii", "render_unicode",
    "expand_program", "Expansion", "ExpandError",
    "generate", "GenerateError",
    "quote", "Encoder", "QuoteError",
    "compile", "compile_source",
    "run_level0", "run_level1", "run_policy", "run_with_namespace",
    "make_resolver", "peel", "decode", "RunError",
    "check", "check_program", "CheckError", "ArityError", "CaseError",
    "DataError", "InterfaceError", "SymbolTableError", "ScopeError",
    "typecheck", "typecheck_program", "TypeMismatchError",
    "Dictionary", "Entry", "from_expansion", "lift", "lower",
    "structural_hash", "DICTIONARY_VERSION",
    "Prober", "fast_reduce", "__version__",
]
