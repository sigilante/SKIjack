"""Step 5a: resolver-taking interpreters, typed paths, the namespace
literal, and the blocking driver.

Checked against `scry_harness.py`, `scry_namespace.py` and
`scry_paths.py`, loaded read-only by the `scry_oracle` fixture.
"""

import pytest
from aviary_kernel.terms import App, Atom, pretty

from skijack import ast as A
from skijack.check import DataError, InterfaceError, ScopeError
from skijack.expand import ExpandError, expand_program
from skijack.generate import (GenerateError, find_answer_type,
                              find_loop_types, find_object_type,
                              find_path_type)
from skijack.parser import parse, parse_ascii
from skijack.render import render_ascii
from skijack.run import (block_constructor, decode, make_resolver, peel,
                         run_level1, run_with_namespace)

from conftest import source

LEXICONS = ["ascii", "unicode"]
CAP = 5_000_000


@pytest.fixture(scope="module")
def built():
    out = {}
    for stem in ("scry-wfq", "scry-wfn", "scry-ns"):
        for lx in LEXICONS:
            out[(stem, lx)] = expand_program(parse(source(stem, lx), lx))
    out[("scry-block", "ascii")] = expand_program(
        parse(source("scry-block", "ascii"), "ascii"))
    return out


def read(exp, name, max_steps=CAP, fuel=None):
    """(constructor, decoded payload or None, contractions)."""
    p = exp.level1[name]
    out = run_level1(p, max_steps, fuel=fuel)
    assert out.whnf, f"{name}: {out.status.value} after {out.steps}"
    ctor, fields = peel(out.term, p.result_type, max_steps=max_steps)
    payload = None
    if fields:
        payload = render_ascii(decode(fields[0], p.object_type,
                                      max_steps=max_steps))
    return ctor, payload, out.steps


# ------------------------------------------------ wfQ, atom for atom

WFQ_PAIRS = [("wfQ", "wfQ"), ("wfQ.loop1", "wfQ1"), ("wfQ.step", "stepQE"),
             ("wfQ.stepScry", "stepScQ"), ("wfQ.stepScry1", "stepScQ1"),
             ("scHit", "scHit"), ("sp", "spQ"), ("rb", "rbQ"),
             ("stepS", "stepSQ"), ("stepK", "stepKQ"), ("stepI", "stepIQ"),
             ("S", "encSQ"), ("K", "encKQ"), ("I", "encIQ"),
             ("App", "encAQ"), ("Scry", "encCQ"),
             ("oracleAlways", "oracleAlways"), ("oracleNever", "oracleNever"),
             ("oracleIfKk", "oracleIfKk"), ("oracleIfK", "oracleIfK")]


@pytest.mark.parametrize("lx", LEXICONS)
@pytest.mark.parametrize("mine,theirs", WFQ_PAIRS, ids=[p[0] for p in WFQ_PAIRS])
def test_wfQ_definitions_match_the_artifact(built, scry_oracle, lx, mine, theirs):
    e = built[("scry-wfq", lx)]
    assert pretty(e.term(mine)) == pretty(scry_oracle.term(theirs))


@pytest.mark.parametrize("lx", LEXICONS)
def test_wfQ_is_950_atoms(built, scry_oracle, lx):
    e = built[("scry-wfq", lx)]
    assert e.size("wfQ") == 950
    assert pretty(e.term("wfQ")) == pretty(scry_oracle.WQ)


# ------------------------------------------------ wfN, atom for atom

WFN_PAIRS = [("wfN", "wfN"), ("wfN.loop1", "wfN1"), ("wfN.step", "stepNE"),
             ("wfN.stepScry", "stepScN"), ("wfN.stepScry1", "stepScN1"),
             ("scHitN", "scHitN"), ("stepS", "stepSN"), ("stepK", "stepKN"),
             ("stepI", "stepIN"), ("SteppedN", "steppedN"),
             ("DoneN", "doneN"), ("ErrdN", "errdN"), ("PendingN", "pendingN"),
             ("RValN", "rValN"), ("RErrN", "rErrN"), ("RTimeN", "rTimeN"),
             ("RBlockN", "rBlockN"), ("OJust", "oJust"),
             ("ONothing", "oNothing"), ("ONotYet", "oNotYet")]


@pytest.mark.parametrize("lx", LEXICONS)
@pytest.mark.parametrize("mine,theirs", WFN_PAIRS, ids=[p[0] for p in WFN_PAIRS])
def test_wfN_definitions_match_the_artifact(built, scry_oracle, lx, mine, theirs):
    e = built[("scry-wfn", lx)]
    assert pretty(e.term(mine)) == pretty(scry_oracle.term(theirs))


@pytest.mark.parametrize("lx", LEXICONS)
def test_wfN_is_1066_atoms(built, scry_oracle, lx):
    e = built[("scry-wfn", lx)]
    assert e.size("wfN") == 1066
    assert pretty(e.term("wfN")) == pretty(scry_oracle.WN)


# -------------------------------------------------------------- EQ5

EQ5_PAIRS = [("EQ5", "EQ5"), ("eqNP", "eqNP"), ("eqApp1P", "eqApp1P"),
             ("eqApp2P", "eqApp2P"), ("pAnd", "pAnd"), ("pKKF", "pKKF"),
             ("PTrue", "pTrue"), ("PFalse", "pFalse")]


@pytest.mark.parametrize("lx", LEXICONS)
@pytest.mark.parametrize("mine,theirs", EQ5_PAIRS, ids=[p[0] for p in EQ5_PAIRS])
def test_EQ5_matches_the_artifact(built, scry_oracle, lx, mine, theirs):
    e = built[("scry-ns", lx)]
    assert pretty(e.term(mine)) == pretty(scry_oracle.term(theirs))


@pytest.mark.parametrize("lx", LEXICONS)
def test_EQ5_is_240_atoms(built, scry_oracle, lx):
    e = built[("scry-ns", lx)]
    assert e.size("EQ5") == 240
    assert pretty(e.term("EQ5")) == pretty(scry_oracle.EQ5)


# ------------------------------------------ the paper's scry table

#: scry_harness.py's whole table: (declaration, result, decoded value)
SCRY_TABLE = [
    ("qBase", "RVal", "K"),       # no Scry present: matches whnfF
    ("qBaseN", "RVal", "K"),      # the oracle is never consulted
    ("qHit", "RVal", "K"),        # I fires, exposing Scry K; the oracle hits
    ("qMiss", "RErr", None),      # ... and misses
    ("qBareN", "RErr", None),     # bare, saturated, miss
    ("qBareA", "RVal", "K"),      # bare, saturated, hit
    ("qUnsat", "RVal", "Scry"),   # bare, unsaturated: stuck, not a miss
    ("qLazy", "RVal", "K"),       # a scry inside a discarded K-argument
    ("qIfKhit", "RVal", "I"),     # path-dependent oracle: head K
    ("qIfKmiss", "RErr", None),   # ... head S
    ("qOmega", "RTime", None),    # fuel exhaustion, still separate
]


@pytest.mark.parametrize("lx", LEXICONS)
@pytest.mark.parametrize("name,ctor,value", SCRY_TABLE,
                         ids=[r[0] for r in SCRY_TABLE])
def test_the_scry_table(built, lx, name, ctor, value):
    got_ctor, got_value, _steps = read(built[("scry-wfq", lx)], name)
    assert (got_ctor, got_value) == (ctor, value)


def test_a_miss_a_stuck_term_and_a_timeout_are_three_outcomes(built):
    """The point of the three-way outcome: a 2-way Maybe would conflate
    them."""
    e = built[("scry-wfq", "ascii")]
    assert {read(e, n)[0] for n in ("qMiss", "qUnsat", "qOmega")} == \
        {"RErr", "RVal", "RTime"}


# ------------------------------------------ blocking, and the driver

def _facts(e, **kw):
    return {k.replace("_", " "): e.terms[v] for k, v in kw.items()}


def test_no_scry_resolves_in_one_round(built):
    e = built[("scry-block", "ascii")]
    r = run_with_namespace(e, e.level1["pIK"], {}, 10)
    assert r.events == ("RValN",)
    assert render_ascii(decode(r.payload, e.object_type)) == "K"


def test_one_block_then_a_value(built):
    """scry_namespace.py: `I (Scry K)` with the fact K = I."""
    e = built[("scry-block", "ascii")]
    r = run_with_namespace(e, e.level1["pIScryK"], {"K": e.terms["ansI"]}, 10)
    assert r.events == ("BLOCK on K", "RValN")
    assert render_ascii(decode(r.payload, e.object_type)) == "I"


def test_a_learned_answer_may_itself_block(built):
    """The chain: `Scry S` resolves to `Scry K`, which resolves to `I`."""
    e = built[("scry-block", "ascii")]
    r = run_with_namespace(e, e.level1["pScryS"],
                           {"S": e.terms["ansScryK"], "K": e.terms["ansI"]}, 10)
    assert r.events == ("BLOCK on S", "BLOCK on K", "RValN")
    assert render_ascii(decode(r.payload, e.object_type)) == "I"
    assert r.rounds == 3


def test_an_unresolvable_block_is_stuck_not_silently_wrong(built):
    e = built[("scry-block", "ascii")]
    r = run_with_namespace(e, e.level1["pIScryK"], {}, 10)
    assert r.events == ("BLOCK on K", "STUCK")
    assert r.payload is None


def test_fuel_exhaustion_is_still_its_own_outcome(built):
    e = built[("scry-block", "ascii")]
    r = run_with_namespace(e, e.level1["pOmega"], {}, 5)
    assert r.events == ("RTimeN",)


# ----------------------------------- compound paths, prefix discrimination

def test_a_compound_path_resolves(built):
    e = built[("scry-block", "ascii")]
    r = run_with_namespace(e, e.level1["pScrySK"], {"S K": e.terms["ansI"]}, 10)
    assert r.events == ("BLOCK on S K", "RValN")
    assert render_ascii(decode(r.payload, e.object_type)) == "I"


def test_a_path_is_told_from_its_own_prefix(built):
    """scry_paths.py's prefix row: `S K K` must not match the fact for
    its prefix `S K`."""
    e = built[("scry-block", "ascii")]
    facts = {"S K": e.terms["ansI"], "S K K": e.terms["ansK"]}
    r = run_with_namespace(e, e.level1["pScrySKK"], facts, 10)
    assert render_ascii(decode(r.payload, e.object_type)) == "K"
    r = run_with_namespace(e, e.level1["pScrySK"], facts, 10)
    assert render_ascii(decode(r.payload, e.object_type)) == "I"


def test_a_wrong_fact_is_not_a_false_hit(built):
    e = built[("scry-block", "ascii")]
    r = run_with_namespace(e, e.level1["pScrySK"], {"K S": e.terms["ansI"]}, 10)
    assert r.events == ("BLOCK on S K", "STUCK")


# ------------------------------------------------ EXAMPLES.md section 5

@pytest.mark.parametrize("lx", LEXICONS)
@pytest.mark.parametrize("name,want", [("answer", "K"), ("answer2", "I")])
def test_examples_section_5(built, lx, name, want):
    """`answer := wfN resolve |- <?^/nat/three>@10` decodes to `K`."""
    ctor, value, _ = read(built[("scry-ns", lx)], name)
    assert (ctor, value) == ("RValN", want)


@pytest.mark.parametrize("lx", LEXICONS)
def test_the_quoted_scry_program_and_the_resolver(built, lx):
    e = built[("scry-ns", lx)]
    assert e.sizes["prog"] == 2485          # <?^/nat/three>
    assert e.sizes["resolve"] == 5375       # the two-fact resolver
    assert len(e.namespaces["resolve"]) == 2


def test_the_two_spellings_produce_the_same_data(built):
    for stem in ("scry-wfq", "scry-wfn", "scry-ns"):
        a, u = built[(stem, "ascii")], built[(stem, "unicode")]
        for name, prog in a.level1.items():
            assert pretty(prog.datum) == pretty(u.level1[name].datum), name
        for name in a.namespaces:
            assert [(pretty(k), pretty(v)) for k, v in a.namespaces[name]] == \
                [(pretty(k), pretty(v)) for k, v in u.namespaces[name]]


# --------------------------------------------------- shapes and errors

def test_a_core_may_take_parameters():
    d = parse_ascii("wfQ e := {\n  f x = e x\n}\n").decls[0]
    assert isinstance(d, A.Core) and d.params == ("e",)


def test_the_interpreter_is_applied_to_its_parameters_before_its_fuel(built):
    """`wfQ E |- <t>@n` is `loop E n <t>` -- the artifact's argument
    order for `wfQ e n m`."""
    e = built[("scry-wfq", "ascii")]
    p = e.level1["qBase"]
    assert len(p.params) == 1
    assert pretty(p.params[0]) == pretty(e.term("oracleAlways"))
    t = p.term                        # loop E fuel datum
    assert pretty(t.fn.fn.fn) == pretty(e.term("wfQ"))
    assert pretty(t.fn.fn.arg) == pretty(e.term("oracleAlways"))


def test_a_missing_interpreter_parameter_is_refused(built):
    with pytest.raises(InterfaceError, match="takes 1 parameter"):
        expand_program(parse_ascii(
            source("scry-wfq", "ascii") + "bad := wfQ |- <I K>@3\n"))


def test_the_pending_constructor_maps_to_the_block_constructor(built):
    """Decision 3: an outcome constructor carrying a payload maps to the
    result constructor at the same position, handed the same payload."""
    p = parse(source("scry-wfn", "ascii"), "ascii")
    lt = find_loop_types(p, find_object_type(p))
    assert dict(lt.mapping) == {"DoneN": "RValN", "ErrdN": "RErrN",
                                "PendingN": "RBlockN"}
    assert lt.timeout.name == "RTimeN"
    e = built[("scry-wfn", "ascii")]
    assert block_constructor(
        find_loop_types(p, find_object_type(p)).result, "term5") == "RBlockN"


def test_the_answer_type_is_the_remaining_outcome_shaped_declaration():
    p = parse(source("scry-wfn", "ascii"), "ascii")
    obj = find_object_type(p)
    at = find_answer_type(p, obj, find_loop_types(p, obj))
    assert at.decl.name == "oanswer"
    assert (at.hit.name, at.notyet.name) == ("OJust", "ONotYet")


def test_the_path_type_is_found_by_name_and_shape():
    p = parse(source("scry-wfn", "ascii"), "ascii")
    pt = find_path_type(p)
    assert (pt.nil.name, pt.cons.name, pt.seg) == ("Nil", "Cons", "seg")


def test_a_path_literal_is_a_cons_list_of_segments(built, scry_oracle):
    """`/nat/three` is `Cons Nat (Cons Three Nil)`, quoted."""
    e = expand_program(parse_ascii(
        source("scry-ns", "ascii")
        + "lit = Cons Nat (Cons Three Nil)\nlitq := <Cons Nat (Cons Three Nil)>\n"))
    assert pretty(e.term("litq")) == pretty(e.terms["prog"].arg)


def test_an_unknown_path_segment_is_refused():
    with pytest.raises(ScopeError, match="names no constructor 'Nope'"):
        expand_program(parse_ascii(
            source("scry-ns", "ascii") + "bad := <?^/nope>\n"))


def test_a_namespace_literal_needs_EQ5():
    src = source("scry-wfn", "ascii") + "r := ns{/nat/two => <I>}\n"
    with pytest.raises(ExpandError, match="compares paths with 'EQ5'"):
        expand_program(parse_ascii(src))


def test_a_fact_value_must_be_a_quotation():
    with pytest.raises(DataError, match="must be data"):
        expand_program(parse_ascii(
            source("scry-ns", "ascii") + "r := ns{/nat/two => I}\n"))


def test_the_empty_namespace_always_answers_not_yet(built):
    e = built[("scry-block", "ascii")]
    assert e.namespaces["empty"] == ()
    assert pretty(e.term("empty")) == pretty(
        App(Atom("K"), e.term("ONotYet")))


def test_make_resolver_rebuilds_the_literal(built):
    """The driver builds the same term the literal compiles to."""
    e = built[("scry-ns", "ascii")]
    facts = e.namespaces["resolve"]
    assert pretty(make_resolver(e, facts)) == pretty(e.term("resolve"))


def test_the_fuel_policy_composes_with_the_blocking_driver(built):
    """`@[]` inside a blocking run: each round deepens iteratively, and
    the outer loop still learns one fact per round."""
    e = built[("scry-block", "ascii")]
    r = run_with_namespace(e, e.level1["pPolicy"], {"K": e.terms["ansI"]},
                           None, 10)
    assert r.events == ("budget 8", "BLOCK on K", "budget 8", "RValN")
    assert render_ascii(decode(r.payload, e.object_type)) == "I"


def test_the_policy_still_reports_a_cap(built):
    e = built[("scry-block", "ascii")]
    r = run_with_namespace(e, e.level1["pOmega"], {}, None, 10,
                           start=2, cap=8)
    assert r.constructor == "RTimeN"


# ------------------------------------------- the paper's character table

@pytest.fixture(scope="module")
def chars():
    return {lx: expand_program(parse(source("parse-chars", lx), lx))
            for lx in LEXICONS}


@pytest.mark.parametrize("lx", LEXICONS)
def test_the_character_table_compiles_to_the_papers_sizes(chars, lx):
    e = chars[lx]
    assert e.sizes["chars"] == 8_707        # the three-fact literal
    assert len(e.namespaces["chars"]) == 3
    assert [e.sizes[n] for n in ("one", "apply", "disc", "held")] == \
        [12_580, 15_374, 18_203, 18_283]


@pytest.mark.parametrize("lx", LEXICONS)
@pytest.mark.parametrize("name,steps", [("one", 16_150), ("apply", 62_199),
                                        ("disc", 47_257), ("held", 16_739)])
def test_the_character_table_runs_to_the_papers_counts(chars, lx, name, steps):
    ctor, value, n = read(chars[lx], name)
    assert (ctor, n) == ("RValN", steps)
    # `held` stops with S unsaturated, so its two unread lookups come back
    # in the term; the other three reduce to the looked-up combinator.
    assert value.startswith("S (Scry") if name == "held" else value == "S"


def test_a_discarded_lookup_is_never_performed(chars):
    """`K S I` keeps S, so /src/eye is discarded rather than read.

    Lookup cost is linear in a fact's position in the literal, so a
    performed third probe would cost about fifteen thousand more.
    """
    _, _, disc = read(chars["ascii"], "disc")
    _, _, apply_ = read(chars["ascii"], "apply")
    assert disc < apply_          # three paths written, but one fewer read


def test_a_lookup_left_unforced_under_a_whnf_term_comes_back_unread():
    """`K ?^/src/eye` is already in weak head normal form, so the scry is
    never forced: the answer holds the Scry leaf, unread, at the cost of
    `K I`, where forcing the same path costs a lookup."""
    import skijack
    from skijack import corpus
    e = skijack.compile(corpus.read("parse-chars")
                        + "lazy := wfN chars |- <K ?^/src/eye>@20\n"
                          "plain := wfN chars |- <K I>@20\n"
                          "forced := wfN chars |- <?^/src/eye>@20\n")
    (lc, lp, ls), (pc, pp, ps), (fc, fp, fs) = (read(e, n) for n in ("lazy", "plain", "forced"))
    assert lc == pc == fc == "RValN"
    assert lp.startswith("K (Scry ") and pp == "K I" and fp == "I"
    assert ls == ps and fs > 100 * ps


@pytest.mark.parametrize("cut,match", [
    ("EQ5 m = eqNP EQ5 m\n", "compares paths with 'EQ5', which this program does not define"),
    ("oanswer === OJust term5 | ONothing | ONotYet\n", "needs an oracle answer type"),
])
def test_a_namespace_literal_needs_EQ5_and_an_answer_type(cut, match):
    import skijack
    from skijack import corpus
    from skijack.expand import ExpandError
    base = corpus.read("scry-ns").split("resolve := ")[0].replace(cut, "")
    with pytest.raises(ExpandError, match=match):
        skijack.compile(base + "rz := ns{/nat => <I>}\n")
