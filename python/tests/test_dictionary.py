"""The dictionary and lift.

`DESIDERATA.md` item 8: "a term produced by the expander can be lifted
back to named source by exact structural matching against the dictionary
of known expansions, and only that; unknown subterms stay raw."
"""

import pytest
from aviary_kernel.terms import App, Atom, pretty, size

from skijack import ast as A
from skijack.dictionary import (VERSION, Dictionary, canonical, from_expansion,
                                hash_all, lift, lower, structural_hash)
from skijack.expand import expand_program
from skijack.parser import parse_ascii
from skijack.render import render_ascii

from conftest import source
from test_check import COMPILABLE

PROGRAMS = ("sec1-nat", "sec2-c", "sec3-swap", "interp-whnff", "scry-wfq",
            "scry-wfn", "scry-ns")

#: One table is one ABI.  These four share the prelude and disagree about
#: nothing, so they merge; the scry programs walk a *different* object
#: type, so their `sp`, `rb` and step equations are different terms under the
#: same names and the table refuses to hold both (see the conflict test).
ONE_ABI = ("sec1-nat", "sec2-c", "sec3-swap", "interp-whnff")


@pytest.fixture(scope="module")
def built():
    return {s: expand_program(parse_ascii(source(s, "ascii")))
            for s in PROGRAMS}


@pytest.fixture(scope="module")
def standard(built):
    """One table over every program: the prelude, `Y`, the Scott
    constructors of every declared type, every equation, every core's loop."""
    d = None
    for stem in ONE_ABI:
        d = from_expansion(built[stem], dictionary=d)
    # EQ5 and its parts come from the five-constructor programs, but
    # under names nothing else claims
    d = from_expansion(built["scry-ns"], dictionary=d,
                       include=["EQ5", "eqNP", "eqApp1P", "eqApp2P", "pAnd",
                                "pKKF", "PTrue", "PFalse"])
    return d


def names_in(x, acc=None):
    acc = set() if acc is None else acc
    if isinstance(x, A.Name):
        acc.add(x.name)
    else:
        names_in(x.fn, acc)
        names_in(x.arg, acc)
    return acc


def whole_names(d, term):
    h = structural_hash(term)
    return [n for n in d.names() if d[n].hash == h]


# ------------------------------------------------------------- the hash

def test_the_hash_is_merkle_and_versioned():
    t = App(App(Atom("S"), Atom("K")), Atom("I"))
    h = structural_hash(t)
    assert VERSION == "skijack-2"
    assert h.startswith(VERSION + ":") and len(h.split(":")[1]) == 32
    # a leaf hashes its name; a node hashes "(fn arg)" of its children
    import hashlib
    d = {n: hashlib.sha256(n.encode()).hexdigest()[:32] for n in "SKI"}
    inner = hashlib.sha256(f"({d['S']} {d['K']})".encode()).hexdigest()[:32]
    outer = hashlib.sha256(f"({inner} {d['I']})".encode()).hexdigest()[:32]
    assert h == f"{VERSION}:{outer}"


def test_equal_trees_hash_alike_however_they_were_shared():
    shared = App(Atom("S"), Atom("K"))
    a = App(shared, shared)
    b = App(App(Atom("S"), Atom("K")), App(Atom("S"), Atom("K")))
    assert structural_hash(a) == structural_hash(b)


def test_different_trees_hash_differently(standard):
    seen = {}
    for name in standard.names():
        e = standard[name]
        if e.hash in seen:
            assert canonical(e.term) == canonical(standard[seen[e.hash]].term)
        seen.setdefault(e.hash, name)


def test_canonical_determines_the_tree():
    t = App(App(Atom("S"), Atom("K")), Atom("I"))
    assert canonical(t) == "((S K) I)"
    assert canonical(App(Atom("S"), App(Atom("K"), Atom("I")))) == "(S (K I))"


def test_hash_all_holds_its_nodes(standard):
    t = standard["whnfF"].term
    memo = hash_all(t)
    for key, (node, _h) in memo.items():
        assert id(node) == key


# -------------------------------------------------------- the table

def test_the_table_registers_the_prelude_Y_and_every_arm(standard):
    for name in ("pair", "hd", "tl", "nil", "cons", "zero", "suc", "Y"):
        assert name in standard, name
    for name in ("whnfF", "sp", "rb", "stepS", "stepK", "stepI", "EQ5",
                 "dec", "add", "sub", "C", "flipA"):
        assert name in standard, name


def test_Y_is_the_fourteen_atom_fixpoint(standard):
    assert standard["Y"].size == 14
    assert pretty(standard["Y"].term) == \
        "S (K (S I I)) (S (S (K S) K) (K (S I I)))"


def test_the_published_rows_are_name_atoms_hash(standard):
    rows = standard.rows()
    assert rows == sorted(rows)
    for name, atoms, h in rows:
        assert atoms == size(standard[name].term)
        assert h == structural_hash(standard[name].term)


def test_the_interpreters_are_in_the_table_at_their_paper_sizes(standard, built):
    assert standard["whnfF"].size == 618
    assert standard["EQ5"].size == 240
    assert from_expansion(built["scry-wfq"])["wfQ"].size == 950
    assert from_expansion(built["scry-wfn"])["wfN"].size == 1066


# ------------------------------------------------------------ the laws

@pytest.mark.parametrize("stem", PROGRAMS)
def test_lower_lift_is_the_identity(built, standard, stem):
    """The law of DESIDERATA.md item 8, on every term of every program --
    against the shared table, and against the program's own."""
    e = built[stem]
    own = from_expansion(e)
    for d in (standard, own):
        for name, term in e.terms.items():
            back = lower(lift(term, d), d)
            assert pretty(back) == pretty(term), f"{stem}:{name}"


def test_one_name_is_one_expansion(built):
    """Merging two programs over different object types is refused: their
    `sp` are different terms."""
    from skijack.dictionary import DictionaryError
    d = from_expansion(built["interp-whnff"])
    with pytest.raises(DictionaryError, match="one name is one expansion"):
        from_expansion(built["scry-wfq"], dictionary=d)


def test_merging_programs_that_agree_is_a_no_op(built):
    """They share the prelude and `Y`, registered with the same terms."""
    d = from_expansion(built["sec1-nat"])
    before = dict(d.entries)
    from_expansion(built["sec2-c"], dictionary=d)
    for name in ("pair", "hd", "tl", "nil", "cons", "zero", "suc", "Y"):
        assert d[name].hash == before[name].hash


def test_lift_never_names_a_near_miss(standard, built):
    """One atom different from `dec` and it stays raw: lift matches
    exactly, and only exactly."""
    e = built["sec1-nat"]
    dec = e.term("dec")
    assert pretty(dec) == "S (S I (K K)) (K I)"
    assert "dec" in names_in(lift(dec, standard))
    near = App(App(Atom("S"), App(App(Atom("S"), Atom("I")),
                                  App(Atom("K"), Atom("K")))),
               App(Atom("K"), Atom("K")))          # (K I) -> (K K)
    assert size(near) == size(dec)
    assert "dec" not in names_in(lift(near, standard))


def test_lift_leaves_an_unknown_term_entirely_raw(standard):
    odd = App(App(Atom("S"), Atom("S")), App(Atom("S"), Atom("S")))
    assert names_in(lift(odd, standard)) == {"S"}
    assert pretty(lower(lift(odd, standard), standard)) == pretty(odd)


def test_the_tie_break_prefers_the_name_a_reader_would_write(built):
    """One equation is reachable as `dec` and as `arith.dec`; lift picks the
    unqualified one."""
    e = built["sec1-nat"]
    d = from_expansion(e)
    assert "arith.dec" in d and "dec" in d
    assert render_ascii(lift(e.term("dec"), d)) == "dec"


def test_S_K_and_I_are_reserved_for_the_ISA(standard, built):
    """A program whose object type declares constructors called S, K and
    I puts real rows under those names, but lift and lower keep the names
    for the combinators (SURFACE-LANGUAGE-DESIGN.md section 6b)."""
    assert "S" in standard and standard["S"].size > 1
    assert "S" not in standard.lift_index().values()
    assert pretty(lower(A.Name("S"), standard)) == "S"


def test_single_atom_entries_are_tabled_but_not_lifted(standard):
    assert standard["zero"].size == 1 and standard["nil"].size == 1
    assert "zero" not in standard.lift_index().values()
    assert "nil" not in standard.lift_index().values()


# -------------------------------- the paper's appendix, made mechanical

def test_lifting_step_names_the_walker_and_the_three_arms(built):
    standard = from_expansion(built["interp-whnff"])
    """`step` is `sp m nil stepS stepK stepI`, and lift finds exactly
    that back in the 569-atom term."""
    e = built["interp-whnff"]
    lifted = lift(e.term("step"), standard,
                  exclude=whole_names(standard, e.term("step")))
    assert render_ascii(lifted) == \
        "S (S (S (S sp (K K)) (K stepS)) (K stepK)) (K stepI)"
    assert {"sp", "stepS", "stepK", "stepI"} <= names_in(lifted)


def test_lifting_whnfF_names_Y_at_its_head(built):
    standard = from_expansion(built["interp-whnff"])
    """The paper's appendix observation: the first fourteen atoms of a
    Y-tied equation are `Y`."""
    e = built["interp-whnff"]
    t = e.term("whnfF")
    lifted = lift(t, standard, exclude=whole_names(standard, t))
    assert isinstance(lifted, A.App)
    head = lifted
    while isinstance(head, A.App):
        head = head.fn
    assert head == A.Name("Y")
    assert "Y" in names_in(lifted)
    assert pretty(lower(lifted, standard)) == pretty(t)


def test_lifting_whnfF_through_its_wrappers_names_the_whole_interface(
        built):
    standard = from_expansion(built["interp-whnff"])
    """Largest match first, so `loop1` hides what is inside it; exclude
    the wrappers and the walker, the rebuilder's equations and `Y` come out."""
    e = built["interp-whnff"]
    t = e.term("whnfF")
    lifted = lift(t, standard,
                  exclude=whole_names(standard, t)
                  + ["loop1", "whnfF.loop1", "step", "whnfF.step"])
    got = names_in(lifted)
    assert {"Y", "sp", "stepS", "stepK", "stepI"} <= got
    assert pretty(lower(lifted, standard)) == pretty(t)


def test_lifting_a_step_arm_names_the_rebuilder(built):
    standard = from_expansion(built["interp-whnff"])
    """`rb` is nested inside `stepS`/`stepK`/`stepI`, so it surfaces once
    those are not matched whole."""
    e = built["interp-whnff"]
    t = e.term("stepI")
    lifted = lift(t, standard,
                  exclude=whole_names(standard, t) + ["stepI1"])
    assert "rb" in names_in(lifted)
    assert pretty(lower(lifted, standard)) == pretty(t)


def test_lifting_is_the_jet_tables_operation(built):
    standard = from_expansion(built["interp-whnff"])
    """RUNTIME-DESIGN.md section 2: the runtime "matches expanded subterms
    against a table of known combinators by structural hash".  That is
    lift with the same index."""
    index = standard.lift_index()
    e = built["interp-whnff"]
    memo = hash_all(e.term("whnfF"))
    hits = {index[f"{VERSION}:{h}"] for _node, h in memo.values()
            if f"{VERSION}:{h}" in index}
    assert {"Y", "sp", "rb", "stepS", "stepK", "stepI", "step"} <= hits
    # the whole term is in the table too, under the name the tie-break
    # prefers among `whnfF`, `loop` and `whnfF.loop`
    assert structural_hash(e.term("whnfF")) in index
    assert index[structural_hash(e.term("whnfF"))] == "loop"


# ------------------------- the paper's supercombinator-vs-macro example

def test_a_supercombinator_lifts_back_to_its_name_and_a_macro_does_not():
    """S5.4's claim, on sec2-c.  flipK1 is literally C applied to K, so
    against a dictionary that names C it lifts to `C K`; flipK2 went
    through the macro, which rewrote the use site before abstraction, so
    nothing of `flip` survives and the term names nothing."""
    import skijack
    from skijack import corpus
    from skijack.render import render_ascii
    e = skijack.compile(corpus.read("sec2-c"))
    d = from_expansion(e, include=["C"])
    assert render_ascii(lift(e.terms["flipK1"], d)) == "C K"
    assert render_ascii(lift(e.terms["flipK2"], d)) == "S (K (S K)) K"
    assert (e.sizes["flipK1"], e.sizes["flipK2"]) == (11, 5)


def test_lift_names_a_subterm_only_when_the_entry_is_it(monkeypatch):
    """A §5 hash is 64 bits, so lift takes a hash match as a candidate and
    names the subterm only when the entry's term is the subterm: an entry
    indexed under another term's hash, as a collision would index it,
    names nothing, and lower ∘ lift stays the identity.  No collision is
    searched for: the index is given the colliding hash."""
    from skijack import dictionary as D
    e = expand_program(parse_ascii("nat === Zero | Suc nat\n"
                                   "add m n = n |> { Zero m ; Suc k (Suc (add m k)) }\n"))
    d = from_expansion(e)
    t = e.terms["Suc"]
    monkeypatch.setattr(D.Dictionary, "lift_index",
                        lambda self, *a, **k: {structural_hash(t): "add"})
    named = lift(t, d, min_size=1)
    assert lower(named, d) == t
    assert "add" not in render_ascii(named)


def _program_level_names(prog, e):
    """The names a program's own top level can spell: its equations and
    definitions, its constructors and the prelude.  A core's equation is
    reached by a qualified name, which resolves to nothing (SPEC.md §2),
    and a quotation's or a namespace literal's name is not a level-0 term."""
    from skijack.expand import PRELUDE_NAMES
    top = {d.name for d in prog.decls if isinstance(d, (A.Equation, A.Def))
           and not isinstance(getattr(d, "expr", None), (A.Quote, A.NsLit))}
    top |= {c.name for d in prog.decls if isinstance(d, A.TypeDecl) for c in d.ctors}
    return [n for n in e.terms if n in top | set(PRELUDE_NAMES)]


@pytest.mark.parametrize("stem", COMPILABLE)
def test_expand_of_render_is_lower(stem):
    """SPEC.md §12: a lifted term, rendered and compiled again, is the term
    `lower` gives back -- for every program-level term of every compiling
    corpus program, lifted against the program-level names and compiled
    with checking off, as lift names a subterm by its term, not its type."""
    import skijack
    from skijack import corpus
    src = corpus.read(stem)
    prog = parse_ascii(src)
    e = expand_program(prog)
    names = _program_level_names(prog, e)
    d = from_expansion(e, include=names)
    for name in names:
        named = lift(e.terms[name], d, exclude=[name])
        again = skijack.compile(src + f"\nzzLaw := {render_ascii(named)}\n", check=False)
        assert again.terms["zzLaw"] == lower(named, d), name
