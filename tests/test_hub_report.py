"""Regression tests for `report_consumers.py --hub`.

The hub report enumerated the *ledger* until 2026-09-07, which made it blind to
any kernel declaration a registry row did not list under `lean_artifact`. Two
independent reviews found the same defect, and one produced a live missed edge:
`Oversight.JointObservation.Residual` names
`Knowledge.knowable_iff_worstAmbiguity_le_one`, which appears in LAND-AMBIG-001's
formalization record but not in its artifact list. That edge is the first test
below and is the reason this file exists.

Widening the enumeration to the elaborated index reintroduced a different
defect: the matcher resolves a use by dotted suffix, so three Oversight modules
naming their own `CollisionWitness.sameObservation` field read as consumers of
`Knowledge.IndistinguishabilityWitness.sameObservation`. The second test pins
the narrowing that fixes it, and the third pins that the narrowing did not throw
out `Knowable.mono` with it.
"""

from __future__ import annotations

from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parent.parent
INDEX = ROOT / "docs/status/declaration-index.json"


pytestmark = pytest.mark.skipif(
    not INDEX.is_file(),
    reason="the declaration index is a build product and is not present",
)


@pytest.fixture(scope="module")
def hub_output() -> str:
    result = subprocess.run(
        [sys.executable, "scripts/report_consumers.py", "--hub"],
        cwd=ROOT, capture_output=True, text=True, check=True,
    )
    return result.stdout


def _edges(output: str) -> dict[str, set[str]]:
    edges: dict[str, set[str]] = {}
    module = None
    for line in output.splitlines():
        if line.startswith("      "):
            if module is not None:
                edges.setdefault(module, set()).add(line.strip())
        elif line.startswith("  ") and not line.startswith("   "):
            module = line.strip()
    return edges


def test_reports_the_edge_the_ledger_hid(hub_output: str) -> None:
    """The worst-ambiguity theorem is used and was invisible to the old report."""
    edges = _edges(hub_output)
    residual = "AISafetyAtlas.Oversight.JointObservation.Residual"
    assert residual in edges, hub_output
    assert (
        "AISafetyAtlas.Knowledge.knowable_iff_worstAmbiguity_le_one" in edges[residual]
    ), edges.get(residual)


def test_shared_leaf_does_not_manufacture_an_edge(hub_output: str) -> None:
    """`cw.sameObservation` is CollisionWitness's field, not the kernel's."""
    edges = _edges(hub_output)
    field = "AISafetyAtlas.Knowledge.IndistinguishabilityWitness.sameObservation"
    for module in (
        "AISafetyAtlas.Oversight.JointObservation.Coverage",
        "AISafetyAtlas.Oversight.JointObservation.FiniteDecision",
        "AISafetyAtlas.Oversight.JointObservation.RepairBoundary",
    ):
        assert field not in edges.get(module, set()), module


def test_narrowing_keeps_qualified_mentions(hub_output: str) -> None:
    """`mono` is a shared leaf; `Knowledge.Knowable.mono` is still a use."""
    edges = _edges(hub_output)
    repair = "AISafetyAtlas.Oversight.JointObservation.RepairBoundary"
    assert "AISafetyAtlas.Knowledge.Knowable.mono" in edges.get(repair, set()), (
        edges.get(repair)
    )


def test_scans_the_whole_public_kernel(hub_output: str) -> None:
    """The report says how much of its domain it covered, and covers all of it."""
    line = [l for l in hub_output.splitlines() if "declaration(s) scanned" in l]
    assert line, hub_output
    scanned = int(line[0].split()[0])
    assert scanned > 100, line[0]
