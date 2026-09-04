"""The frontier-evidence check must reject what it claims to reject.

`check_frontier_evidence.py` exists because a false frontier proposition passed
every other gate in this repository. A check written for that failure mode and
never shown to fail is worth as much as the gates it was added to. Each case
below builds a small Lean tree in a temporary directory, removes exactly one
piece of the evidence package, and asserts the check notices.

`evaluate` takes its root, its frozen surfaces, its lock contents and its
manifest text as parameters, so none of this touches the repository.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from typing import Any

import pytest


ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "check_frontier_evidence", ROOT / "scripts" / "check_frontier_evidence.py")
assert SPEC is not None and SPEC.loader is not None
EVIDENCE: Any = importlib.util.module_from_spec(SPEC)
# Registered before execution: the module defines dataclasses, and
# `dataclasses` resolves a field's type through `sys.modules[cls.__module__]`.
sys.modules["check_frontier_evidence"] = EVIDENCE
SPEC.loader.exec_module(EVIDENCE)

FREEZE_SPEC = importlib.util.spec_from_file_location(
    "check_statement_freeze", ROOT / "scripts" / "check_statement_freeze.py")
assert FREEZE_SPEC is not None and FREEZE_SPEC.loader is not None
FREEZE: Any = importlib.util.module_from_spec(FREEZE_SPEC)
FREEZE_SPEC.loader.exec_module(FREEZE)

FRONTIER_FILE = "AISafetyAtlas/Fake/Frontier.lean"
SURFACE = "AISafetyAtlas.Fake.fakeFrontier_iff"
PROPOSITION = "AISafetyAtlas.Fake.FakeFrontier"

# One module carrying all four roles: the frontier, its frozen surface, a
# consumer that takes it as a hypothesis, and an unconditional theorem that does
# not.  The docstring names the frontier too, and must not count as a consumer.
LEAN = """\
namespace AISafetyAtlas.Fake

@[expose] public def FakeFrontier : Prop :=
  ∀ n : Nat, 0 < n → n ≠ 0

public theorem fakeFrontier_iff :
    FakeFrontier ↔ ∀ n : Nat, 0 < n → n ≠ 0 := Iff.rfl

/-- A consumer: `FakeFrontier` in the docstring must not count, the binder must. -/
public theorem consumer_of_frontier (h : FakeFrontier) (n : Nat) (hn : 0 < n) :
    n ≠ 0 := h n hn

public theorem unconditional_witness (n : Nat) (hn : 0 < n) : n ≠ 0 :=
  Nat.pos_iff_ne_zero.mp hn

end AISafetyAtlas.Fake
"""

MANIFEST = """\
# Fake manifest

## FAKE-FRONTIER

**Lean.** `AISafetyAtlas.Fake.FakeFrontier`.
"""


def probe(unconditional: bool = True) -> Any:
    return EVIDENCE.Artifact(
        kind="script",
        name="scripts/fake_probe.py",
        file="scripts/fake_probe.py",
        unconditional=unconditional,
        note="numerical falsification attempt",
    )


def witness(name: str, unconditional: bool = True) -> Any:
    return EVIDENCE.Artifact(
        kind="lean",
        name=f"AISafetyAtlas.Fake.{name}",
        file=FRONTIER_FILE,
        unconditional=unconditional,
        note="stress witness",
    )


def frontier(*artifacts: Any, identifier: str = "FAKE-FRONTIER") -> Any:
    return EVIDENCE.Frontier(
        identifier=identifier,
        proposition=PROPOSITION,
        file=FRONTIER_FILE,
        surface=SURFACE,
        artifacts=artifacts,
        # The debt fields carry a maintainer's judgement and no script checks
        # them, so the evaluation cases fix them once here rather than varying
        # them per case.
        owed_to="candidate",
        decision="hold",
        reason="fixture",
    )


@pytest.fixture
def tree(tmp_path: Path) -> Path:
    (tmp_path / "AISafetyAtlas" / "Fake").mkdir(parents=True)
    (tmp_path / FRONTIER_FILE).write_text(LEAN, encoding="utf-8")
    (tmp_path / "scripts").mkdir()
    (tmp_path / "scripts" / "fake_probe.py").write_text("# probe\n", encoding="utf-8")
    return tmp_path


def run(
    tree: Path,
    subject: Any,
    *,
    surfaces: dict[str, str] | None = None,
    locked: set[str] | None = None,
    manifest: str | None = MANIFEST,
) -> Any:
    return EVIDENCE.evaluate(
        subject,
        tree,
        {SURFACE: FRONTIER_FILE} if surfaces is None else surfaces,
        {SURFACE} if locked is None else locked,
        manifest,
    )


def test_full_evidence_passes(tree: Path) -> None:
    report = run(tree, frontier(probe(), witness("unconditional_witness")))

    assert report.failures == []
    assert [name for name, _, _ in report.consumers] == ["consumer_of_frontier"]
    assert len(report.counted) == 2
    assert EVIDENCE.describe(report).startswith("ok")


def test_missing_stress_artifact_fails(tree: Path) -> None:
    report = run(tree, frontier())

    assert any("no unconditional stress artifact" in failure
               for failure in report.failures)
    assert "FAIL" in EVIDENCE.describe(report)


def test_conditional_consequence_is_not_independent_stress_evidence(
        tree: Path) -> None:
    """The ZetaVolumeBridge failure mode: `frontier -> X` proves nothing."""
    report = run(tree, frontier(witness("consumer_of_frontier",
                                        unconditional=False)))

    assert report.conditional and not report.counted
    assert any("no unconditional stress artifact" in failure
               for failure in report.failures)


def test_artifact_that_assumes_the_frontier_may_not_claim_otherwise(
        tree: Path) -> None:
    report = run(tree, frontier(witness("consumer_of_frontier")))

    assert any("recorded as unconditional" in failure
               for failure in report.failures)
    assert not report.counted


def test_unconditional_artifact_may_not_be_recorded_as_conditional(
        tree: Path) -> None:
    report = run(tree, frontier(probe(), witness("unconditional_witness",
                                                 unconditional=False)))

    assert any("recorded as conditional" in failure
               for failure in report.failures)


def test_script_artifact_must_exist(tree: Path) -> None:
    (tree / "scripts" / "fake_probe.py").unlink()
    report = run(tree, frontier(probe()))

    assert any("missing file" in failure for failure in report.failures)


def test_lean_artifact_must_resolve(tree: Path) -> None:
    report = run(tree, frontier(witness("no_such_theorem")))

    assert any("does not resolve" in failure for failure in report.failures)


def test_missing_manifest_entry_fails(tree: Path) -> None:
    report = run(tree, frontier(probe()), manifest="# Fake manifest\n")

    assert any("FAKE-FRONTIER" in failure and "section" in failure
               for failure in report.failures)
    assert any("never names" in failure for failure in report.failures)


def test_absent_manifest_fails(tree: Path) -> None:
    report = run(tree, frontier(probe()), manifest=None)

    assert any("missing frontier manifest" in failure
               for failure in report.failures)


def test_frontier_with_no_consumer_fails(tree: Path) -> None:
    (tree / FRONTIER_FILE).write_text(
        LEAN.replace("public theorem consumer_of_frontier (h : FakeFrontier) "
                     "(n : Nat) (hn : 0 < n) :\n    n ≠ 0 := h n hn",
                     ""),
        encoding="utf-8")
    report = run(tree, frontier(probe()))

    assert report.consumers == []
    assert any("takes it as a hypothesis" in failure
               for failure in report.failures)


def test_examples_do_not_count_as_consumers(tree: Path) -> None:
    """An `example` is a use of a frontier, not something standing on it."""
    (tree / "AISafetyAtlas" / "Examples").mkdir()
    (tree / "AISafetyAtlas" / "Examples" / "Fake.lean").write_text(
        "example (h : AISafetyAtlas.Fake.FakeFrontier) : True := trivial\n",
        encoding="utf-8")
    report = run(tree, frontier(probe()))

    assert [path for _, path, _ in report.consumers] == [FRONTIER_FILE]


def test_unwatched_surface_fails(tree: Path) -> None:
    report = run(tree, frontier(probe()), surfaces={})

    assert any("check_statement_freeze" in failure
               for failure in report.failures)


def test_unlocked_surface_fails(tree: Path) -> None:
    report = run(tree, frontier(probe()), locked=set())

    assert any("statement-lock.json" in failure
               for failure in report.failures)


def test_missing_proposition_fails(tree: Path) -> None:
    report = run(tree, frontier(probe(),
                                witness("unconditional_witness")))
    assert report.failures == []

    (tree / FRONTIER_FILE).write_text(
        LEAN.replace("def FakeFrontier", "def RenamedFrontier"),
        encoding="utf-8")
    renamed = run(tree, frontier(probe()))

    assert any("does not resolve" in failure for failure in renamed.failures)


def test_registry_surfaces_are_the_frozen_ones() -> None:
    """Every frontier's specification surface is one the freeze check watches.

    The two scripts have to agree about which surfaces are load-bearing: the
    freeze notices a surface that changes, this notices a frontier with nothing
    behind it, and a surface named in one and not the other is a hole.
    """
    for subject in EVIDENCE.FRONTIERS:
        assert subject.surface in FREEZE.SPECIFICATION_SURFACES


def test_registry_entries_resolve_in_the_repository() -> None:
    """Names in the registry point at declarations and files that exist."""
    for subject in EVIDENCE.FRONTIERS:
        assert EVIDENCE.find_declaration(
            ROOT, subject.proposition, subject.file) is not None
        for artifact in subject.artifacts:
            assert (ROOT / artifact.file).is_file()
            if artifact.kind == "lean":
                assert EVIDENCE.find_declaration(
                    ROOT, artifact.name, artifact.file) is not None
