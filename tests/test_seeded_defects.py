"""Deliberate defects, and the assertion that the gates reject each one.

Every other suite here asserts the checkers accept a *correct* tree. That
establishes they do not fire spuriously; it establishes nothing about whether
they fire at all. "The gate is green" is only evidence if a red tree would have
turned it red, and until this file existed nothing in the repository tested
that direction.

The gap is not hypothetical. ``check_print_axioms.py`` scanned for public
theorems with a pattern that rejected any leading attribute, so
``@[simp] public theorem`` was collected by nothing and fifty-one declarations
were dropped from the kernel axiom audit in silence. Its own test file,
``test_public_theorem_regex.py``, pinned the *name* grammar case by case --
primes, subscripts, Greek letters, every delimiter -- and never varied what
preceded ``public``. The audit then reported a count, the v4.33.0 migration
compared that count against the pre-migration one, found it identical, and was
right: both sides were computed by the same pattern and inherited the same hole.

So each test below states a defect a reviewer would care about, applies it, and
asserts the responsible checker says no. A test here that starts passing for the
wrong reason -- because the checker stopped looking rather than because the
defect stopped existing -- is caught by the suites that assert the clean tree
stays green; the two directions are only meaningful together.

Scope: the source-text checkers, which is where the heuristics live and where
the bug above came from. The kernel-level gates (``lake build``, the axiom
harness, ``leanchecker``) are not seeded here -- each needs a full elaboration
per mutation, and a defect that survives *those* is a defect in Lean.

Run: `python3 -m pytest tests/ -q`
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / f"{name}.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


drift = _load("check_statement_drift")


def _drifts(before: str, after: str) -> bool:
    """Whether the statement checker reports the pair as a statement change."""
    return drift.units(before) != drift.units(after)


# --- Seeded weakenings: the checker must call each one drift -----------------
#
# A migration is faithful when proofs may change and statements may not, so each
# of these is a statement change dressed as a plausible edit. The existing suite
# covers a changed hypothesis, a changed definition body and a dropped `deriving`
# clause; these are the shapes it did not.


def test_dropping_a_hypothesis_is_drift() -> None:
    """The classic weakening: prove the same conclusion from less."""
    before = "public theorem foo (n : ℕ) (h : 0 < n) (k : n ≠ 1) : n ≠ 0 := by omega\n"
    after = "public theorem foo (n : ℕ) (h : 0 < n) : n ≠ 0 := by omega\n"
    assert _drifts(before, after)


def test_weakening_a_strict_inequality_is_drift() -> None:
    before = "public theorem bound (x : ℝ) : f x < 1 := by simp\n"
    after = "public theorem bound (x : ℝ) : f x ≤ 1 := by simp\n"
    assert _drifts(before, after)


def test_weakening_a_typeclass_hypothesis_is_drift() -> None:
    """`[Fintype α]` is strictly stronger than `[Finite α]`."""
    before = "public theorem card_pos [Fintype α] : 0 < n := by simp\n"
    after = "public theorem card_pos [Finite α] : 0 < n := by simp\n"
    assert _drifts(before, after)


def test_changing_a_binder_from_implicit_to_explicit_is_drift() -> None:
    """Not a weakening but an API change, which a version bump may not make."""
    before = "public theorem foo {n : ℕ} : n = n := rfl\n"
    after = "public theorem foo (n : ℕ) : n = n := rfl\n"
    assert _drifts(before, after)


def test_replacing_a_universal_with_an_existential_is_drift() -> None:
    before = "public theorem all_good : ∀ x : S, P x := by simp\n"
    after = "public theorem all_good : ∃ x : S, P x := by simp\n"
    assert _drifts(before, after)


def test_changing_the_conclusion_is_drift() -> None:
    before = "public theorem foo (n : ℕ) : n + 0 = n := by simp\n"
    after = "public theorem foo (n : ℕ) : 0 + n = n := by simp\n"
    assert _drifts(before, after)


def test_loosening_a_numeric_bound_is_drift() -> None:
    before = "public theorem three_le (h : 3 ≤ Fintype.card A) : P := by simp\n"
    after = "public theorem three_le (h : 2 ≤ Fintype.card A) : P := by simp\n"
    assert _drifts(before, after)


def test_changing_a_structure_field_type_is_drift() -> None:
    before = "public structure M where\n  cost : ℝ\n  ok : 0 ≤ cost\n"
    after = "public structure M where\n  cost : ℚ\n  ok : 0 ≤ cost\n"
    assert _drifts(before, after)


def test_dropping_a_structure_field_is_drift() -> None:
    """A dropped `Prop` field is an obligation nobody has to discharge again."""
    before = "public structure M where\n  cost : ℝ\n  ok : 0 ≤ cost\n"
    after = "public structure M where\n  cost : ℝ\n"
    assert _drifts(before, after)


def test_introducing_an_axiom_is_drift() -> None:
    """The cheapest way to make a migration pass, and it must not be quiet."""
    before = "public theorem foo : P := by simp\n"
    after = "axiom cheat : P\npublic theorem foo : P := cheat\n"
    assert _drifts(before, after)


def test_removing_a_set_option_is_drift() -> None:
    """The mirror of the existing `adding` test: it changes meaning either way."""
    before = "set_option linter.checkUnivs false in\npublic theorem foo : True := trivial\n"
    after = "public theorem foo : True := trivial\n"
    assert _drifts(before, after)


def test_changing_an_import_is_drift() -> None:
    before = "import AISafetyAtlas.Causal.Model\npublic theorem foo : True := trivial\n"
    after = "import AISafetyAtlas.Causal.Decision\npublic theorem foo : True := trivial\n"
    assert _drifts(before, after)


def test_renaming_a_declaration_is_drift() -> None:
    """A rename is a removal and an addition, and both halves must be reported."""
    before = "public theorem old_name : True := trivial\n"
    after = "public theorem new_name : True := trivial\n"
    assert _drifts(before, after)


# --- The other direction, so the tests above cannot pass vacuously ----------


def test_a_pure_proof_rewrite_is_still_not_drift() -> None:
    """If this ever fails, every assertion above is passing for the wrong reason."""
    before = "public theorem foo (n : ℕ) (h : 0 < n) : n ≠ 0 := by omega\n"
    after = "public theorem foo (n : ℕ) (h : 0 < n) : n ≠ 0 := by\n  intro k\n  simp_all\n"
    assert not _drifts(before, after)


def test_reformatting_a_statement_is_not_drift() -> None:
    """Whitespace and line breaks are not meaning; the units are normalised."""
    before = "public theorem foo (n : ℕ) (h : 0 < n) : n ≠ 0 := by omega\n"
    after = "public theorem foo\n    (n : ℕ)\n    (h : 0 < n) :\n    n ≠ 0 := by omega\n"
    assert not _drifts(before, after)


def test_a_comment_is_not_a_statement() -> None:
    before = "public theorem foo : True := trivial\n"
    after = "/-- Doc comment added. -/\n-- and a line comment\npublic theorem foo : True := trivial\n"
    assert not _drifts(before, after)


# --- Audit coverage: what counts as compiler-generated ----------------------
#
# `check_audit_coverage.py` excuses a declaration from the regex audit only when
# the environment says the compiler produced it. Two of those rules are judgement
# calls encoded as code, so they are seeded here: getting either wrong hides real
# declarations, which is the failure this whole file is about.

coverage = _load("check_audit_coverage")


def _row(name: str, kind: str, rng: str, module: str = "M", instance: bool = False) -> dict:
    return {
        "name": name,
        "kind": kind,
        "module": module,
        "generated": False,
        "range": rng,
        "instance": instance,
        "axioms": set(),
    }


def test_a_declaration_sharing_a_types_range_is_generated() -> None:
    """`deriving` and `@[ext]` emit declarations that point at the type's syntax."""
    rows = [
        _row("M.Coord", "inductive", "52:0"),
        _row("M.instFintypeCoord", "def", "52:0"),
    ]
    coverage.mark_derived(rows)
    assert rows[0]["generated"] is False, "the type itself is hand-written"
    assert rows[1]["generated"] is True, "the derived instance is not"


def test_an_anonymous_instance_owning_its_range_is_not_generated() -> None:
    """The case that must not be swallowed: it is hand-written and can hide a `sorry`.

    `public instance : Fintype X := …` has no name for a text pattern to
    capture, but it is source code someone wrote, so the range rule must leave
    it alone and let the axiom check reach it.
    """
    rows = [
        _row("M.Coord", "inductive", "52:0"),
        _row("M.instFintypeX", "def", "97:0", instance=True),
    ]
    coverage.mark_derived(rows)
    assert rows[1]["generated"] is False


def test_range_sharing_without_a_type_does_not_generate() -> None:
    """Two declarations on one line are both hand-written; neither derives the other."""
    rows = [_row("M.f", "def", "10:0"), _row("M.g", "def", "10:0")]
    coverage.mark_derived(rows)
    assert [r["generated"] for r in rows] == [False, False]


def test_every_exclusion_carries_a_reason() -> None:
    """The exclusions file is a record of a known gap, so a bare name is not enough."""
    exclusions = coverage.load_exclusions()
    assert exclusions, "the file should not be silently empty"
    for name, reason in exclusions.items():
        assert reason.strip(), f"{name} is excluded with no reason"
