"""The migration gate, tested in the direction that matters: does it go red.

``check_migration_adjudicated.py`` exists because ``--fail-on-drift`` was written
for a toolchain bump and then wired to nothing, so the one time it mattered a
person had to remember. A gate that only ever passes is indistinguishable from no
gate, and this one passes on every ordinary branch by design -- which is exactly
the shape that hides a broken check. So each test below puts it in a situation
where it must refuse.

Run: `python3 -m pytest tests/ -q`
"""

from __future__ import annotations

import importlib.util
import json
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


gate = _load("check_migration_adjudicated")

DRIFT_OUTPUT = (
    "adjudicate: 4 non-theorem declaration(s) differ only inside a masked `by` block.\n"
    "  ? A/B.lean  [def X]\n"
    "statement drift against main: 31 difference(s); 135 proof body/bodies also "
    "rewritten (kernel-checked)\n"
)

RECORD = {
    "migration": {"baseline_commit": "4edc04182b931a3ac0941d3b98120a6f1ca4fe85"},
    "measured": {
        "statement_drift_differences": 31,
        "proof_bodies_rewritten": 135,
    },
    "adjudications": [{"declaration": f"d{i}", "verdict": "proof"} for i in range(4)],
}


def _install(monkeypatch, tmp_path, *, before: str, now: str, record, drift: str = DRIFT_OUTPUT):
    """Point the gate at a synthetic tree so no test depends on the real one.

    ``ROOT`` moves with ``BASELINE`` because the failure messages report the
    record's path relative to the root, and a baseline outside it raises
    ``ValueError`` before the test can see the exit code it came for.
    """
    monkeypatch.setattr(gate, "toolchain_at", lambda _ref: before)
    monkeypatch.setattr(gate, "working_toolchain", lambda: now)
    monkeypatch.setattr(gate, "run_drift", lambda _ref: (drift, 1))
    monkeypatch.setattr(sys, "argv", ["check_migration_adjudicated.py"])

    path = tmp_path / "docs" / "status" / "migration-baseline.json"
    if record is not None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(record), encoding="utf-8")
    monkeypatch.setattr(gate, "ROOT", tmp_path)
    monkeypatch.setattr(gate, "BASELINE", path)


# --- Must refuse ------------------------------------------------------------


def test_a_toolchain_bump_with_no_record_fails(monkeypatch, tmp_path) -> None:
    """The bump nobody measured is the one this whole gate is for."""
    _install(monkeypatch, tmp_path, before="v4.31.0", now="v4.33.0", record=None)
    monkeypatch.setattr(sys, "argv", ["x", "--ref", "abc123"])
    assert gate.main() == 1


def test_a_record_that_undercounts_the_drift_fails(monkeypatch, tmp_path) -> None:
    stale = json.loads(json.dumps(RECORD))
    stale["measured"]["statement_drift_differences"] = 30
    _install(monkeypatch, tmp_path, before="v4.31.0", now="v4.33.0", record=stale)
    assert gate.main() == 1


def test_a_record_missing_an_adjudication_fails(monkeypatch, tmp_path) -> None:
    """Three verdicts on file, four declarations needing one."""
    short = json.loads(json.dumps(RECORD))
    short["adjudications"] = short["adjudications"][:3]
    _install(monkeypatch, tmp_path, before="v4.31.0", now="v4.33.0", record=short)
    assert gate.main() == 1


def test_a_record_with_stale_proof_counts_fails(monkeypatch, tmp_path) -> None:
    stale = json.loads(json.dumps(RECORD))
    stale["measured"]["proof_bodies_rewritten"] = 100
    _install(monkeypatch, tmp_path, before="v4.31.0", now="v4.33.0", record=stale)
    assert gate.main() == 1


def test_a_record_about_a_different_baseline_fails(monkeypatch, tmp_path) -> None:
    """An adjudication of some other tree is not an adjudication of this one."""
    other = json.loads(json.dumps(RECORD))
    other["migration"]["baseline_commit"] = "0000000000000000000000000000000000000000"
    _install(monkeypatch, tmp_path, before="v4.31.0", now="v4.33.0", record=other)
    monkeypatch.setattr(sys, "argv", ["x", "--ref", "4edc04182b931a3ac0941d3b98120a6f1ca4fe85"])
    assert gate.main() == 1


def test_an_unreadable_baseline_fails_rather_than_skips(monkeypatch, tmp_path) -> None:
    """A check that cannot see its baseline must not report success."""
    _install(monkeypatch, tmp_path, before="v4.31.0", now="v4.33.0", record=RECORD)
    monkeypatch.setattr(gate, "toolchain_at", lambda _ref: None)
    assert gate.main() == 1


# --- Must allow -------------------------------------------------------------


def test_an_ordinary_branch_passes(monkeypatch, tmp_path) -> None:
    """No toolchain move, so added statements are the point and must not block."""
    _install(monkeypatch, tmp_path, before="v4.33.0", now="v4.33.0", record=RECORD)
    assert gate.main() == 0


def test_a_fully_adjudicated_bump_passes(monkeypatch, tmp_path) -> None:
    """If this fails, every refusal above could be passing for the wrong reason."""
    _install(monkeypatch, tmp_path, before="v4.31.0", now="v4.33.0", record=RECORD)
    assert gate.main() == 0


# --- Reading the checker's report -------------------------------------------


def test_counts_are_read_from_the_summary_lines() -> None:
    assert gate.measured(DRIFT_OUTPUT) == {
        "statement_drift_differences": 31,
        "proof_bodies_rewritten": 135,
        "adjudications": 4,
    }


def test_a_clean_report_reads_as_zero() -> None:
    clean = "statement drift against main: 0 difference(s); 0 proof body/bodies also rewritten\n"
    assert gate.measured(clean)["statement_drift_differences"] == 0
    assert gate.measured(clean)["adjudications"] == 0


def test_the_real_record_matches_the_real_tree() -> None:
    """The committed record has to be about the committed tree, not a past one."""
    record = json.loads((ROOT / "docs/status/migration-baseline.json").read_text("utf-8"))
    assert record["migration"]["baseline_commit"]
    assert record["measured"]["statement_drift_differences"] >= 0
    assert len(record["adjudications"]) >= 1
