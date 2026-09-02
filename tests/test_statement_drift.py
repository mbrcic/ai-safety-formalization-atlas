"""What `check_statement_drift.py` must and must not call a statement change.

The check exists because 54 files changed across the v4.33.0 migration while
`check_public_api.py` (names only) and `check_statement_freeze.py` (graded
statements only) both stayed green. Its whole value is the distinction between a
proof, which the kernel checks and which may be rewritten freely, and a
statement, which may not — so that distinction is what is pinned here.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent


def _git_ok(*args: str) -> bool:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True).returncode == 0


_BASELINE = json.loads(
    (ROOT / "docs/status/migration-baseline.json").read_text(encoding="utf-8")
)["migration"]["baseline_commit"]
_HAS_BASELINE = _git_ok("cat-file", "-e", f"{_BASELINE}^{{commit}}")
_TREE_MATCHES_HEAD = _git_ok("diff", "--quiet", "HEAD", "--", "AISafetyAtlas")


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / f"{name}.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


drift = _load("check_statement_drift")


def units(source: str):
    return drift.units(source)


def test_rewriting_a_proof_is_not_drift():
    before = "public theorem foo (n : ℕ) : n + 0 = n := by simp\n"
    after = "public theorem foo (n : ℕ) : n + 0 = n := by\n  induction n <;> simp\n"
    assert units(before) == units(after)


def test_changing_a_hypothesis_is_drift():
    before = "public theorem foo (n : ℕ) (h : 0 < n) : n ≠ 0 := by omega\n"
    after = "public theorem foo (n : ℕ) (h : 1 ≤ n) : n ≠ 0 := by omega\n"
    assert units(before) != units(after)


def test_changing_a_definition_body_is_drift():
    before = "public def f (n : ℕ) : ℕ := n + 1\n"
    after = "public def f (n : ℕ) : ℕ := n + 2\n"
    assert units(before) != units(after)


def test_a_by_block_inside_a_definition_is_a_proof():
    """`Finset` membership arguments are proofs even buried in a term."""
    before = "public def q : T where\n  joint := fun x => x ⟨.c, by simp⟩\n"
    after = (
        "public def q : T where\n"
        "  joint := fun x => x ⟨.c, (by simp only [arch]; exact Finset.mem_insert_self _ _)⟩\n"
    )
    assert units(before) == units(after)


def test_dropping_a_deriving_clause_is_drift():
    """The `Fintype` workaround has to show up; it is real, documented debt."""
    before = "public inductive P\n  | a | b\n  deriving DecidableEq, Fintype\n"
    after = "public inductive P\n  | a | b\n  deriving DecidableEq\n"
    assert units(before) != units(after)


def test_attributes_do_not_confuse_the_kind():
    """An attribute prefix must not become the kind: `@[simp] public theorem`
    read as kind `@` sends a theorem down the definition path, where its proof
    reads as a statement change."""
    kind, name = drift.kind_and_name("@[simp] public theorem factor_id (p : ℝ) : f p = g p")
    assert (kind, name) == ("theorem", "factor_id")


def test_pattern_alternatives_do_not_split_a_declaration():
    """`| 0 => …` sits at column zero and continues the declaration above it."""
    source = (
        "public def steps : (n : ℕ) → T\n"
        "| 0 => pure 1\n"
        "| n+1 => steps n\n"
    )
    assert len(units(source)) == 1


def test_adding_a_set_option_is_drift():
    """A file-level option changes what the declarations under it mean."""
    before = "public theorem foo : True := trivial\n"
    after = "set_option linter.checkUnivs false in\npublic theorem foo : True := trivial\n"
    assert units(before) != units(after)


def test_a_tactic_block_that_builds_data_is_not_silently_equal():
    """`by` is masked as a proof, and that assumption is not sound.

    `def f : Nat := by exact 0` and `by exact 1` mask to the same text and denote
    different numbers. The masked comparison cannot tell them apart, so the pair
    must surface for adjudication instead of being dropped.
    """
    before = "public def f : Nat := by exact 0\n"
    after = "public def f : Nat := by exact 1\n"
    assert units(before) == units(after), "masking makes these look equal"
    reported = drift.adjudications(before, after)
    assert [name for name, _ in reported] == ["def f"], reported


def test_a_proof_only_change_in_a_definition_still_adjudicates():
    """A Prop field rewritten in a `def` is reported, then judged by a human.

    This is what the v4.33.0 migration produced four of: `Set.mem_setOf_eq` ->
    `Set.mem_ofPred_eq` inside a structure's proof obligations.
    """
    before = "public def w : T where\n  sel := s\n  ok := by simp [mem_setOf_eq]\n"
    after = "public def w : T where\n  sel := s\n  ok := by simp [mem_ofPred_eq]\n"
    assert [name for name, _ in drift.adjudications(before, after)] == ["def w"]


def test_an_unchanged_definition_is_not_adjudicated():
    source = "public def f : Nat := by exact 0\n"
    assert drift.adjudications(source, source) == []


def test_same_leaf_name_in_two_namespaces_does_not_collide():
    """`A.f` and `B.f` shared one slot, so a change to the first was masked.

    Found by review after the adjudication pass was added: keying on the leaf
    name meant an unchanged sibling could hide a changed declaration entirely,
    which is the same silent-drop the pass exists to prevent.
    """
    before = (
        "namespace A\npublic def f : Nat := by exact 0\nend A\n"
        "namespace B\npublic def f : Nat := by exact 0\nend B\n"
    )
    after = (
        "namespace A\npublic def f : Nat := by exact 1\nend A\n"
        "namespace B\npublic def f : Nat := by exact 0\nend B\n"
    )
    assert [name for name, _ in drift.adjudications(before, after)] == ["def A.f"]


def test_two_anonymous_instances_do_not_collide():
    """`Portfolio.lean` carries four `instance :` with no name of their own."""
    before = (
        "public instance : Fintype X where elems := {x} complete := by simp\n"
        "public instance : Fintype Y where elems := {y} complete := by simp\n"
    )
    after = (
        "public instance : Fintype X where elems := {x} complete := by decide\n"
        "public instance : Fintype Y where elems := {y} complete := by simp\n"
    )
    assert len(drift.adjudications(before, after)) == 1


def test_namespaces_qualify_reported_names():
    source = "namespace A.B\npublic def f : Nat := 0\nend A.B\n"
    assert any(name == "A.B.f" for _, name, _ in drift.units(source))


@pytest.mark.skipif(not _HAS_BASELINE, reason="migration baseline commit not in this checkout")
def test_fail_on_drift_exits_nonzero_on_an_unresolved_adjudication():
    """The CLI, not the library: an adjudication must make `--fail-on-drift` fail.

    The first version of this test asserted `adjudications()` was non-empty and
    was named for the exit status it never checked. Review caught it. The exit
    status is the contract a migration relies on, so it is exercised through
    `subprocess`.
    """
    baseline = _BASELINE
    result = subprocess.run(
        [sys.executable, "scripts/check_statement_drift.py", "--ref", baseline,
         "--fail-on-drift"],
        cwd=ROOT, capture_output=True, text=True,
    )
    assert result.returncode == 1, result.stdout[-2000:]
    assert "adjudicate:" in result.stdout
    assert "statement drift ok" not in result.stdout, "must not report ok over an adjudication"


@pytest.mark.skipif(not _TREE_MATCHES_HEAD, reason="Lean sources differ from HEAD")
def test_no_drift_against_head_exits_zero():
    """The other half of the contract: a clean tree reports ok and exits zero."""
    result = subprocess.run(
        [sys.executable, "scripts/check_statement_drift.py", "--ref", "HEAD",
         "--fail-on-drift"],
        cwd=ROOT, capture_output=True, text=True,
    )
    assert result.returncode == 0, result.stdout[-2000:]
    assert "statement drift ok" in result.stdout


@pytest.mark.skipif(not _HAS_BASELINE, reason="migration baseline commit not in this checkout")
def test_recorded_adjudications_match_what_the_checker_reports():
    """The migration note's table is only worth having if it still holds."""
    baseline = json.loads(
        (ROOT / "docs/status/migration-baseline.json").read_text(encoding="utf-8")
    )
    commit = _BASELINE
    result = subprocess.run(
        [sys.executable, "scripts/check_statement_drift.py", "--ref", commit],
        cwd=ROOT, capture_output=True, text=True,
    )
    reported = sorted(
        line.split("[", 1)[1].rsplit("]", 1)[0]
        for line in result.stdout.splitlines()
        if line.startswith("  ? ")
    )
    recorded = sorted(a["declaration"] for a in baseline["adjudications"])
    assert reported == recorded, f"reported={reported}\nrecorded={recorded}"
