"""The package API and `python3 -m skijack`."""

import io
import contextlib

import pytest

import skijack
from skijack.__main__ import main
from skijack.parser import parse_ascii

from conftest import CORPUS, source

WHNFF = str(CORPUS / "interp-whnff.ascii.ski")
SCRYNS = str(CORPUS / "scry-ns.ascii.ski")
BAD = str(CORPUS / "sec4-interp.ascii.ski")


def run(*argv):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = main(list(argv))
    return code, out.getvalue(), err.getvalue()


# ------------------------------------------------------------- the API

def test_compile_runs_the_whole_pipeline():
    e = skijack.compile(source("interp-whnff", "ascii"))
    assert e.sizes["whnfF"] == 618


def test_compile_takes_either_lexicon():
    a = skijack.compile(source("interp-whnff", "ascii"), "ascii")
    u = skijack.compile(source("interp-whnff", "unicode"), "unicode")
    assert a.sizes["whnfF"] == u.sizes["whnfF"] == 618


def test_compile_checks_by_default():
    """With checking on, Stage A rejects first, with its own class; with
    it off the expander's own backstop still refuses -- the output is
    never wrong, only the message is coarser."""
    with pytest.raises(skijack.ScopeError):
        skijack.compile("f x = x nowhere\n")
    with pytest.raises(skijack.ExpandError):
        skijack.compile("f x = x nowhere\n", check=False)


def test_the_package_exposes_the_pipeline():
    for name in ("compile", "check", "lift", "lower", "run_level1",
                 "run_policy", "run_with_namespace", "from_expansion",
                 "structural_hash", "render_ascii", "parse_ascii"):
        assert hasattr(skijack, name), name


# ------------------------------------------------------------- the CLI

def test_summary_is_the_default():
    code, out, _ = run(WHNFF)
    assert code == 0
    assert "Stage A clean" in out and "compiled terms" in out


def test_check_reports_clean():
    code, out, _ = run(WHNFF, "--check")
    assert code == 0 and "Stage A clean" in out


def test_check_reports_problems_and_fails():
    code, _out, err = run(BAD, "--check")
    assert code == 1 and "ScopeError" in err and "errd" in err


def test_expand_prints_terms_with_sizes():
    code, out, _ = run(WHNFF, "--expand")
    assert code == 0
    assert any(line.split()[:2] == ["618", "whnfF"] for line in out.splitlines())


def test_dictionary_prints_the_versioned_table():
    code, out, _ = run(WHNFF, "--dictionary")
    assert code == 0
    assert out.startswith(f"# {skijack.DICTIONARY_VERSION}:")
    assert any(" Y " in line and "14" in line for line in out.splitlines())


def test_lift_prints_named_source():
    code, out, _ = run(WHNFF, "--lift", "step")
    assert code == 0
    assert out.strip() == "S (S (S (S sp (K K)) (K stepS)) (K stepK)) (K stepI)"


def test_render_round_trips_through_the_cli():
    code, out, _ = run(WHNFF, "--render", "unicode")
    assert code == 0
    from skijack.parser import parse, parse_ascii as pa
    assert parse(out, "unicode") == pa(source("interp-whnff", "ascii"))


def test_run_a_level_1_declaration():
    code, out, _ = run(SCRYNS, "--run", "answer")
    assert code == 0 and out.startswith("RValN K")


def test_run_overrides_the_fuel():
    code, out, _ = run(SCRYNS, "--run", "answer", "--fuel", "1")
    assert code == 0 and out.startswith("RTimeN")


def test_run_a_level_0_name_prints_its_term():
    code, out, _ = run(WHNFF, "--run", "sp")
    assert code == 0 and out.split()[0] == "126"


def test_an_unknown_name_fails():
    code, _out, err = run(WHNFF, "--run", "nope")
    assert code == 1 and "no declaration named" in err


# ------------------------------------------- failure paths reach the user
#
# Every one of these used to print a Python traceback: the CLI caught
# CheckError alone, which is not a base of ExpandError, LexError,
# ParseError or OSError.  The contract now is that a bad program or a bad
# file exits 1 with one line on stderr naming the file and the problem,
# and that no input produces a traceback.

def _write(tmp_path, name, text, mode="w"):
    p = tmp_path / name
    p.write_bytes(text) if mode == "wb" else p.write_text(text, encoding="utf-8")
    return str(p)


def test_a_missing_file_is_an_error_not_a_traceback(tmp_path):
    code, _, err = run(str(tmp_path / "absent.ski"))
    assert code == 1 and "No such file" in err and "Traceback" not in err


def test_a_directory_is_an_error_not_a_traceback(tmp_path):
    code, _, err = run(str(tmp_path))
    assert code == 1 and "directory" in err and "Traceback" not in err


def test_non_utf8_input_is_reported(tmp_path):
    f = _write(tmp_path, "bad.ascii.ski", b"\xff\xfe\x00bad", mode="wb")
    code, _, err = run(f)
    assert code == 1 and "UTF-8" in err and "Traceback" not in err


def test_a_parse_error_is_reported_with_its_location(tmp_path):
    f = _write(tmp_path, "unterm.ascii.ski", "x := <I K\n")
    code, _, err = run(f)
    assert code == 1 and "line 1" in err and "QCLOSE" in err


def test_an_expander_rejection_is_reported(tmp_path):
    """ExpandError is not a CheckError; this is the case the old handler
    missed for every mutually recursive program, which now compiles: a
    quotation without an object type is the expander's to refuse."""
    f = _write(tmp_path, "noobject.ascii.ski",
               "nat === Zero | Suc nat\n"
               "q := <Zero>\n")
    code, _, err = run(f)
    assert code == 1 and "Traceback" not in err and err.strip()


def test_a_deep_expression_is_located_not_a_recursion_error(tmp_path):
    f = _write(tmp_path, "deep.ascii.ski",
               "nat === Zero | Suc nat\nf := " + "(" * 400 + "I" + ")" * 400 + "\n")
    code, _, err = run(f)
    assert code == 1 and "Traceback" not in err and "nests too deeply" in err


# ------------------------------------------------- the three macro limits

def test_a_long_application_chain_is_not_a_macro_error():
    """102 applications in a macro-free program once failed as 'macro
    expansion did not reach a fixpoint'.  Structural depth and macro
    unfolding are separate limits now."""
    src = "nat === Zero | Suc nat\nf := " + "I " * 200 + "\n"
    e = skijack.compile(src)
    assert "f" in e.terms


def test_macro_work_is_bounded_not_just_macro_depth():
    """A macro chain where each uses its predecessor twice costs 2^n
    substitutions at depth n: bounded by depth alone it hangs."""
    lines = ["nat === Zero | Suc nat", "m0 x :=* x"]
    lines += [f"m{i} x :=* m{i-1} (m{i-1} x)" for i in range(1, 25)]
    lines.append("f := m24 I")
    with pytest.raises(skijack.SkijackError, match="substitutions"):
        skijack.compile("\n".join(lines) + "\n")


def test_every_error_class_shares_one_base():
    from skijack.lexicon import LexError
    from skijack.parser import ParseError
    from skijack.check import CheckError
    from skijack.expand import ExpandError
    from skijack.generate import GenerateError
    from skijack.quote import QuoteError
    from skijack.run import RunError
    for cls in (LexError, ParseError, CheckError, ExpandError,
                GenerateError, QuoteError, RunError):
        assert issubclass(cls, skijack.SkijackError), cls.__name__
