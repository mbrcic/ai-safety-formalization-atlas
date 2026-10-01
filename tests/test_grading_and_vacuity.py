"""Regression tests for the two dispositions added on 2026-09-16.

Both scripts under test answer a question of the form "is this silence
legitimate?", and both had a first version that answered it with a word match.

`check_module_graded` accepted a module's final component occurring anywhere in
ledger prose, so `AISafetyAtlas.Decision.Expect` and
`AISafetyAtlas.Sovereignty.Boundary` passed on the English words "Expect" and
"Boundary". The tests below pin the replacement: a mention is resolved against
`docs/status/declaration-index.json`, it must come from a declaration-carrying
field or a backticked span rather than bare prose, and a dotted suffix shared by
two declarations resolves to neither.

`check_witness_debt` had no way to say that a leaf's antecedent is provably
empty, so the two `O24Solution` rows were counted as work nobody can do. The
tests below pin that a disposition is checked rather than believed: every name in
it has to exist, and the theorem has to still be an unwitnessed leaf.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"


def _load(name: str):
    # `scripts/` modules import each other by bare name
    if str(SCRIPTS) not in sys.path:
        sys.path.insert(0, str(SCRIPTS))
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / f"{name}.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


graded = _load("check_module_graded")
debt = _load("check_witness_debt")


# --- what counts as naming a module -------------------------------------------

HOMES = {
    "AISafetyAtlas.Decision.Expect": {"AISafetyAtlas.Decision.expect"},
    "AISafetyAtlas.Sovereignty.Boundary": {"AISafetyAtlas.Sovereignty.Boundary.reach"},
    "AISafetyAtlas.Wireheading.ProgramPrior": {
        "AISafetyAtlas.Wireheading.ProgramPrior.expectation_eq_programSum"
    },
    "AISafetyAtlas.Left.Shared": {"AISafetyAtlas.Left.Thing.collide"},
    "AISafetyAtlas.Right.Shared": {"AISafetyAtlas.Right.Other.collide"},
}


def test_a_declaration_name_names_its_module():
    found = graded.named_modules(HOMES, "", {"ProgramPrior.expectation_eq_programSum"})
    assert "AISafetyAtlas.Wireheading.ProgramPrior" in found


def test_the_dotted_module_path_names_it_too():
    found = graded.named_modules(HOMES, "see AISafetyAtlas.Decision.Expect", set())
    assert "AISafetyAtlas.Decision.Expect" in found


def test_a_suffix_two_declarations_share_names_neither():
    # `collide` is the leaf of a declaration in each of two modules, so the
    # mention is evidence for both and therefore for neither.
    found = graded.named_modules(HOMES, "", {"collide"})
    assert "AISafetyAtlas.Left.Shared" not in found
    assert "AISafetyAtlas.Right.Shared" not in found


def test_an_exact_full_name_resolves_despite_a_shared_leaf():
    found = graded.named_modules(HOMES, "", {"AISafetyAtlas.Left.Thing.collide"})
    assert found == {"AISafetyAtlas.Left.Shared"}


def test_bare_prose_is_not_a_mention():
    """The regression this check was rewritten for.

    A sentence using the words "expect" and "reach" is not a reference to
    `AISafetyAtlas.Decision.expect` or `Sovereignty.Boundary.reach`, and
    `ledger_runs` is what keeps those words out of the candidate set.
    """
    prose = "We expect the reader to reach the same conclusion."
    found = graded.named_modules(HOMES, prose, set())
    assert found == set()


def test_a_backticked_name_in_prose_is_a_mention():
    found = graded.named_modules(HOMES, "", {"expect"})
    assert "AISafetyAtlas.Decision.Expect" in found


def test_a_module_defining_nothing_still_appears():
    """A facade cannot be graded by declaration, so it must reach the exclusions.

    Dropping it from the list would be the silence this check exists to make
    unreachable, arriving by a different route.
    """
    homes = {"AISafetyAtlas.Facade": set(), "AISafetyAtlas.Real": {"AISafetyAtlas.Real.thm"}}
    assert "AISafetyAtlas.Facade" in graded.library_modules(homes)


def test_the_repository_passes_its_own_module_check():
    assert graded.main.__module__  # loaded
    homes = graded.declarations_by_module()
    modules = graded.library_modules(homes)
    mentioned = graded.named_modules(homes, graded.ledger_text(), graded.ledger_runs())
    exclusions = graded.load_exclusions()
    for module in modules:
        assert module in mentioned or exclusions.get(module, "").strip(), module


# --- what counts as a checked vacuity disposition -----------------------------

KNOWN = {"A.thm", "A.Empty", "A.isEmpty_proof"}
GOOD = {"empty_type": "A.Empty", "emptiness_proof": "A.isEmpty_proof"}


def test_a_well_formed_disposition_is_accepted():
    assert debt.check_vacuity({"A.thm": GOOD}, ["A.thm"], KNOWN) == []


def test_a_disposition_for_a_theorem_that_is_no_longer_a_leaf_fails():
    problems = debt.check_vacuity({"A.thm": GOOD}, [], KNOWN)
    assert any("no longer an unwitnessed leaf" in problem for problem in problems)


def test_a_disposition_whose_emptiness_proof_vanished_fails():
    """The day somebody inhabits the type, this is how the reader finds out."""
    record = dict(GOOD, emptiness_proof="A.gone")
    problems = debt.check_vacuity({"A.thm": record}, ["A.thm"], KNOWN)
    assert any("not a declaration in this tree" in problem for problem in problems)


def test_a_disposition_must_name_both_the_type_and_the_proof():
    problems = debt.check_vacuity(
        {"A.thm": {"emptiness_proof": "A.isEmpty_proof"}}, ["A.thm"], KNOWN
    )
    assert any("empty_type" in problem for problem in problems)


def test_a_disposition_for_a_declaration_that_does_not_exist_fails():
    problems = debt.check_vacuity({"A.gone": GOOD}, ["A.gone"], KNOWN)
    assert any("not a declaration here" in problem for problem in problems)


def test_the_repositorys_own_dispositions_check_out():
    entries = debt.load_vacuity(ROOT)
    assert entries, "the O24 rows are the reason this file exists"
    _, leaves, _, _, _ = debt.analyse(ROOT)
    kinds, _ = debt.load_index(ROOT)
    assert debt.check_vacuity(entries, leaves, set(kinds)) == []
