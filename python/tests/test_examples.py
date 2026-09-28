"""The three worked examples added after the paper: words to numbers two
ways, full ASCII as a type with a digit parser, and an event type with a
kernel the runtime pokes.  Every number here was measured on this
expander; values are read behaviourally, never by inspecting syntax.
"""

import pytest
from aviary_kernel.terms import App, Atom

import skijack
from skijack import corpus
from skijack.parser import parse
from skijack.probe import Prober
from skijack.render import render_ascii
from skijack.run import decode, peel, run_level0, run_level1

LEXICONS = ["ascii", "unicode"]


def build(stem, lx):
    return skijack.compile(corpus.read(stem, lx), lexicon=lx)


def yes_or_no(term):
    r = run_level0(App(App(term, Atom("yes")), Atom("no")), 100_000)
    assert isinstance(r.term, Atom)
    return r.term.name


# ------------------------------------------------ words to numbers, two ways

@pytest.mark.parametrize("lx", LEXICONS)
def test_words_to_numbers_case_at_level_0(lx):
    e = build("words-to-numbers", lx)
    assert (e.sizes["toNum"], e.sizes["three"]) == (58, 61)
    assert Prober(e).read_nat(e.terms["three"]) == 3
    assert run_level0(e.terms["three"], 100_000).steps == 10


@pytest.mark.parametrize("lx", LEXICONS)
def test_words_to_numbers_namespace_at_level_1(lx):
    """The same three facts as a namespace: two orders of magnitude more
    atoms, tens of thousands of contractions, and an encoded term back."""
    e = build("words-to-numbers", lx)
    assert (e.sizes["nums"], e.sizes["n3"]) == (6_691, 9_081)
    p = e.level1["n3"]
    out = run_level1(p, 5_000_000)
    ctor, fields = peel(out.term, p.result_type, max_steps=5_000_000)
    assert (ctor, out.steps) == ("RValN", 22_280)
    # what comes back is the *encoding* of Suc (Suc (Suc Zero)), not a numeral
    assert render_ascii(decode(fields[0], p.object_type, max_steps=5_000_000)).startswith("K (S (K (S I)) K")


# ---------------------------------------------- full ASCII as a type; digits

@pytest.mark.parametrize("lx", LEXICONS)
def test_full_ascii_is_a_type_and_a_character_is_a_datum(lx):
    e = build("ascii-digits", lx)
    assert (e.sizes["C0"], e.sizes["C48"], e.sizes["C127"]) == (379, 283, 128)
    # a 128-way case is a few hundred atoms, not a few hundred thousand
    assert (e.sizes["isDigit"], e.sizes["digitValue"]) == (503, 745)
    assert yes_or_no(e.terms["yes"]) == "yes"      # isDigit C55 ('7')
    assert yes_or_no(e.terms["no"]) == "no"        # isDigit C65 ('A')


@pytest.mark.parametrize("lx", LEXICONS)
def test_digits_fold_to_a_numeral(lx):
    e = build("ascii-digits", lx)
    assert (e.sizes["add"], e.sizes["mul"], e.sizes["parseDigits"]) == (42, 77, 1_000)
    pr = Prober(e)
    assert pr.read_nat(e.terms["twelve"]) == 12        # "12"
    assert pr.read_nat(e.terms["fortyTwo"]) == 42      # "42"
    assert run_level0(e.terms["twelve"], 2_000_000).steps == 592


# ------------------------------------------- an event type and a kernel

def axis(n, t, hd, tl):
    """Nock's numbering over Scott cells, as `n@t` compiles it: the bits of
    n after the leading 1, most significant first, 0 for head, 1 for tail."""
    for bit in bin(n)[3:]:
        t = App(tl if bit == "1" else hd, t)
    return t


@pytest.mark.parametrize("lx", LEXICONS)
def test_a_runtime_can_poke_the_kernel_with_events_it_builds(lx):
    """RUNTIME-DESIGN.md section 3b's loop over an Arvo-shaped kernel
    (SPEC.md section 4.1): pull an arm by axis, apply it to the whole
    kernel and the event, install the kernel it returns, read the effects.
    The runtime never names an arm; it selects by axis, as Nock 9 does."""
    e = build("kernel-events", lx)
    assert (e.sizes["poke"], e.sizes["peek"], e.sizes["load"], e.sizes["kernel"]) == (217, 8, 23, 300)
    assert (e.sizes["Tick"], e.sizes["Poke"], e.sizes["Log"]) == (1, 8, 5)
    pr = Prober(e)
    src = (corpus.DIR / f"kernel-events.{lx}.ski").read_text()
    decl = {d.name: d for d in parse(src, lx).decls if hasattr(d, "ctors")}
    hd, tl = e.terms["hd"], e.terms["tl"]
    POKE, PEEK, LOAD, STATE = 4, 10, 11, 3

    def pull(arm, k, arg):
        return App(App(axis(arm, k, hd, tl), k), arg)

    def inject(k, event):
        out = run_level0(pull(POKE, k, event), 200_000)
        k2 = App(tl, out.term)
        ctor, fields = peel(App(hd, out.term), decl["effects"])
        effect = None
        if fields:
            name, payload = peel(fields[0], decl["effect"])
            effect = (name, pr.read_nat(payload[0]))
        return out.steps, k2, pr.read_nat(axis(STATE, k2, hd, tl)), ctor, effect

    k0 = e.terms["kernel"]
    s1, k1, n1, c1, f1 = inject(k0, e.terms["Tick"])
    s2, k2, n2, c2, f2 = inject(k1, App(e.terms["Poke"], pr.nat(5)))
    s3, k3, n3, c3, f3 = inject(k2, e.terms["Tick"])
    assert (n1, c1, f1) == (1, "Nil", None)
    assert (n2, c2, f2) == (6, "Cons", ("Log", 1))
    assert (n3, c3, f3) == (7, "Nil", None)
    # The kernel is installed as reduced, not normalized: its state is the
    # application the last poke built, so under the reference host, which
    # shares no work, each poke re-reduces the history (a Tick costs 34
    # more steps per earlier event).  A sharing runtime computes each
    # state once (avon/DESIGN.md section 9).
    assert (s1, s2, s3) == (61, 108, 135)

    # peek reads the state through the same pull; load puts this battery
    # over an old kernel's state, which is how a new battery takes over
    assert pr.read_nat(pull(PEEK, k3, e.terms["Zero"])) == 7
    k4 = pull(LOAD, k0, axis(STATE, k2, hd, tl))
    assert pr.read_nat(axis(STATE, k4, hd, tl)) == 6
    assert inject(k4, e.terms["Tick"])[2] == 7
