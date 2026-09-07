"""The intake lane refuses what it is supposed to refuse.

The lane's whole reason to exist is an authority split: a proposer may deposit
a statement, and may not deposit a grade. That split is worth nothing as a
convention and something as a check, so these tests are written against the
refusals rather than against the happy path.

Each case is a defect somebody would plausibly commit -- a fidelity verdict
copied over from a conjecture row, a statement parked outside the containment
prefix, a promotion with nothing on the other end -- and the test asserts the
validator names it.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
VALIDATOR = ROOT / "scripts" / "validate_intake.py"
INTAKE = ROOT / "intake.yaml"

WELL_FORMED = {
    "id": "IN-001",
    "statement": "A precise prose statement of the deposited proposition.",
    "lean": "AISafetyAtlas.Conjectures.Intake.Example.someStatement",
    "lean_module": "AISafetyAtlas.Conjectures.Intake.Example",
    "proposed_by": "someone",
    "received": "2026-09-07",
    "status": "OPEN",
}


def run(tmp_path: Path, rows: list[dict], next_id: int = 2) -> subprocess.CompletedProcess:
    """Run the validator against a throwaway ledger.

    The validator reads `intake.yaml` from the repository root, so the file is
    swapped and restored rather than parameterised: keeping the production path
    under test is the point, and a validator that only ever runs against a
    fixture is a validator nobody has run.
    """
    original = INTAKE.read_text(encoding="utf-8")
    payload = json.loads(original)
    payload["intake"] = rows
    payload["next_id"] = next_id
    try:
        INTAKE.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        return subprocess.run(
            [sys.executable, str(VALIDATOR)], capture_output=True, text=True, cwd=ROOT
        )
    finally:
        INTAKE.write_text(original, encoding="utf-8")


def message(result: subprocess.CompletedProcess) -> str:
    return (result.stderr or "") + (result.stdout or "")


def test_shipped_lane_validates() -> None:
    result = subprocess.run(
        [sys.executable, str(VALIDATOR)], capture_output=True, text=True, cwd=ROOT
    )
    assert result.returncode == 0, message(result)


def test_empty_lane_says_so() -> None:
    result = run(tmp_path=ROOT, rows=[], next_id=1)
    assert result.returncode == 0
    assert "empty" in message(result)


@pytest.mark.parametrize(
    "field, value",
    [
        ("source_fidelity", "Literal"),
        ("source_scope", "Same"),
        ("relationship", "EXACT"),
        ("ai_bridge_status", "REVIEWED"),
        ("source_ref", ["survey-ref-005"]),
        ("resolution", "settled"),
    ],
)
def test_a_grade_cannot_ride_in_on_an_intake_row(field: str, value: object) -> None:
    """The authority split, enforced by rejection rather than by convention."""
    result = run(ROOT, [{**WELL_FORMED, field: value}])
    assert result.returncode == 1
    assert field in message(result)
    assert "not grades" in message(result)


def test_statement_must_live_inside_the_containment_prefix() -> None:
    """Containment is structural: nothing deposited can reach the public API."""
    row = {**WELL_FORMED, "lean": "AISafetyAtlas.Knowledge.knowable_iff_no_collision"}
    result = run(ROOT, [row])
    assert result.returncode == 1
    assert "AISafetyAtlas.Conjectures.Intake" in message(result)


def test_promotion_must_name_the_row_it_became() -> None:
    row = {**WELL_FORMED, "status": "PROMOTED", "outcome": "graded and promoted"}
    result = run(ROOT, [row])
    assert result.returncode == 1
    assert "must name the conjecture row" in message(result) or "declaration index" in message(result)


def test_promotion_cannot_point_at_a_conjecture_that_does_not_exist() -> None:
    row = {
        **WELL_FORMED,
        "status": "PROMOTED",
        "outcome": "graded and promoted",
        "promoted_to": "CONJ-999",
    }
    result = run(ROOT, [row])
    assert result.returncode == 1
    assert "CONJ-999" in message(result) or "declaration index" in message(result)


def test_leaving_the_lane_is_never_undocumented() -> None:
    row = {**WELL_FORMED, "status": "DECLINED"}
    result = run(ROOT, [row])
    assert result.returncode == 1
    assert "outcome" in message(result)


def test_ids_are_never_reused() -> None:
    result = run(ROOT, [WELL_FORMED, dict(WELL_FORMED)])
    assert result.returncode == 1
    assert "twice" in message(result)


def test_next_id_must_stay_ahead_of_the_ledger() -> None:
    result = run(ROOT, [WELL_FORMED], next_id=1)
    assert result.returncode == 1
    assert "next_id" in message(result)
