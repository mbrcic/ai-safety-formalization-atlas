"""End-to-end tests for `scripts/check_intake_statements.py`.

The intake lane is empty, so a passing run in the gate proves only that the
script starts. These tests are the only evidence the check *works*, which makes
them load-bearing rather than decorative: an adversarial review found that the
lane admitted a `Nat`-valued definition, and this file is what stops that
regressing.

The fixtures point at real declarations in the kernel rather than adding a
throwaway Lean module, because the harness has to elaborate through a module
that is actually built. `Knowable` is the positive: a parameterised definition
whose type telescopes to `Prop`, which is exactly the shape a deposited
statement has. `ambiguity` is the negative: same namespace, `ℕ`-valued, and reached through its
own module `AISafetyAtlas.Knowledge.Ambiguity`, because the kernel facade
withholds its specializations and pointing the row at `AISafetyAtlas.Knowledge`
would fail for the wrong reason. The wrong-module case uses
`AISafetyAtlas.Fairness.RiskAssignment`, one of the two domains with no
cross-domain import, since a module that transitively imports the kernel reaches
`Knowable` perfectly well — the harness establishes *reachability from the
advertised module*, and `validate_intake.py`'s index comparison is what pins the
defining module. Containment (`AISafetyAtlas.Conjectures.Intake.*`) is also
`validate_intake.py`'s check and is deliberately not re-tested here.

Each case shells out to `lake env lean`, so they are skipped where `lake` is
absent.
"""

from __future__ import annotations

import json
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts/check_intake_statements.py"

pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(
        shutil.which("lake") is None, reason="lake is not on PATH"
    ),
]


def _run(rows: list[dict[str, str]], tmp_path: Path) -> subprocess.CompletedProcess[str]:
    """Run the checker against a temporary intake ledger."""
    ledger = tmp_path / "intake.yaml"
    ledger.write_text(
        json.dumps({"schema_version": 1, "next_id": 1, "description": "fixture",
                    "intake": rows}),
        encoding="utf-8",
    )
    probe = tmp_path / "probe.py"
    probe.write_text(
        "import sys\n"
        f"sys.path.insert(0, {str(ROOT / 'scripts')!r})\n"
        "import check_intake_statements as c\n"
        "from pathlib import Path\n"
        f"c.INTAKE = Path({str(ledger)!r})\n"
        "raise SystemExit(c.main())\n",
        encoding="utf-8",
    )
    return subprocess.run(
        [sys.executable, str(probe)], cwd=ROOT, capture_output=True, text=True
    )


def _row(lean: str, module: str) -> dict[str, str]:
    return {
        "id": "IN-001", "statement": "fixture", "lean": lean, "lean_module": module,
        "proposed_by": "fixture", "received": "2026-09-07", "status": "OPEN",
    }


def test_prop_valued_definition_is_admitted(tmp_path: Path) -> None:
    result = _run(
        [_row("AISafetyAtlas.Knowledge.Knowable", "AISafetyAtlas.Knowledge")], tmp_path
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert "elaborate to Prop" in result.stdout


def test_value_valued_definition_is_refused(tmp_path: Path) -> None:
    """A `Nat` is not a statement. This is the case the review demonstrated."""
    result = _run(
        [_row("AISafetyAtlas.Knowledge.ambiguity", "AISafetyAtlas.Knowledge.Ambiguity")],
        tmp_path,
    )
    assert result.returncode != 0, result.stdout
    assert "does not land in Prop" in result.stdout + result.stderr


def test_wrong_module_is_refused(tmp_path: Path) -> None:
    """The advertised module is an import instruction; a wrong one is broken."""
    result = _run(
        [_row("AISafetyAtlas.Knowledge.Knowable",
              "AISafetyAtlas.Fairness.RiskAssignment")],
        tmp_path,
    )
    assert result.returncode != 0, result.stdout
    assert "does not exist in the environment" in result.stdout + result.stderr


def test_several_rows_are_all_checked(tmp_path: Path) -> None:
    """More than one row, all good. The lane will not stay a single row."""
    rows = [
        _row("AISafetyAtlas.Knowledge.Knowable", "AISafetyAtlas.Knowledge"),
        _row("AISafetyAtlas.Knowledge.Determines", "AISafetyAtlas.Knowledge"),
        _row("AISafetyAtlas.Compositional.Networks.SameView",
             "AISafetyAtlas.Compositional.Networks"),
    ]
    for index, row in enumerate(rows, start=1):
        row["id"] = f"IN-{index:03d}"
    result = _run(rows, tmp_path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "3 deposited statement(s)" in result.stdout


def test_a_bad_row_is_caught_behind_a_good_one(tmp_path: Path) -> None:
    """The check is over every row, not over the first one.

    Two modules and two rows, with the offending one second, so a harness that
    stopped at the first success would pass this and should not.
    """
    rows = [
        _row("AISafetyAtlas.Knowledge.Knowable", "AISafetyAtlas.Knowledge"),
        _row("AISafetyAtlas.Knowledge.ambiguity", "AISafetyAtlas.Knowledge.Ambiguity"),
    ]
    rows[0]["id"], rows[1]["id"] = "IN-001", "IN-002"
    result = _run(rows, tmp_path)
    assert result.returncode != 0, result.stdout
    assert "does not land in Prop" in result.stdout + result.stderr


def test_one_row_cannot_supply_another_rows_import(tmp_path: Path) -> None:
    """A wrong module must not be masked by a second row that imports the truth.

    Reproduced before the fix: `IN-001` advertised `Fairness.RiskAssignment` for
    `Knowledge.Knowable`, `IN-002` advertised `Knowledge`, both went into one
    environment, and the run exited 0 while reporting success "through the
    module each row advertises". Each advertised module gets its own harness
    now, so the union cannot satisfy a row that its own module does not reach.
    """
    rows = [
        _row("AISafetyAtlas.Knowledge.Knowable",
             "AISafetyAtlas.Fairness.RiskAssignment"),
        _row("AISafetyAtlas.Knowledge.Determines", "AISafetyAtlas.Knowledge"),
    ]
    rows[0]["id"], rows[1]["id"] = "IN-001", "IN-002"
    result = _run(rows, tmp_path)
    assert result.returncode != 0, result.stdout
    combined = result.stdout + result.stderr
    assert "IN-001" in combined, combined
    assert "AISafetyAtlas.Fairness.RiskAssignment" in combined, combined


def test_a_module_that_does_not_supply_lean_still_works(tmp_path: Path) -> None:
    """The harness needs `MetaM`, and a minimal deposit will not provide it.

    Every module used elsewhere in these tests reaches `Lean` through Mathlib,
    so the missing `import Lean` in the harness was invisible: a real minimal
    submission — `module` plus `public def s : Prop := True`, importing nothing
    — failed with `identifier MetaM is unknown` on a valid statement. `Init` is
    the same shape: it is a real module, `True` is a real `Prop` in it, and it
    does not provide `MetaM`. Passing here means the harness brings its own.
    """
    result = _run([_row("True", "Init")], tmp_path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "elaborate to Prop" in result.stdout


def test_empty_lane_passes_and_says_so(tmp_path: Path) -> None:
    result = _run([], tmp_path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "the lane is empty" in result.stdout
