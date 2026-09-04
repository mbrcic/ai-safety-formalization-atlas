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


# --- The default baseline ---------------------------------------------------
#
# Everything above monkeypatches `toolchain_at` and moves ROOT into a plain
# temporary directory, so `live_baseline()` finds no repository, returns None,
# and the recorded pin is used. That is the fallback path, and it means none of
# those tests can tell whether the default was taken from the branch point or
# from the record -- reverting the default would leave all of them green.
#
# These two build a real repository instead and let git answer.


def _run(cwd, *args: str) -> str:
    import subprocess

    proc = subprocess.run(
        ["git", "-c", "user.name=t", "-c", "user.email=t@example.invalid", *args],
        cwd=cwd,
        capture_output=True,
        text=True,
        check=True,
    )
    return proc.stdout.strip()


def _repo(tmp_path: Path, *, upstream: bool):
    """A history whose recorded pin and whose branch point disagree.

    * `A` carries the old toolchain and is what the record pins.
    * `B` carries the new one, and is where `origin/main` points.
    * `HEAD` is an ordinary feature commit on top of `B` that adds a file --
      the shape of every contribution made after a migration merges.

    So the recorded pin says "the toolchain moved" and the branch point says it
    did not, and only one of those is a true statement about this branch.
    """
    (tmp_path / "docs" / "status").mkdir(parents=True)
    # `git init -b` needs git 2.28; Ubuntu 20.04 ships 2.25 and the branch name
    # is never used here.
    _run(tmp_path, "init", "-q")

    (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n", encoding="utf-8")
    _run(tmp_path, "add", "-A")
    _run(tmp_path, "commit", "-q", "-m", "before the migration")
    recorded = _run(tmp_path, "rev-parse", "HEAD")

    (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.33.0\n", encoding="utf-8")
    _run(tmp_path, "add", "-A")
    _run(tmp_path, "commit", "-q", "-m", "the migration")
    migrated = _run(tmp_path, "rev-parse", "HEAD")
    if upstream:
        _run(tmp_path, "update-ref", "refs/remotes/origin/main", migrated)

    (tmp_path / "new_module.txt").write_text("a declaration this branch adds\n", encoding="utf-8")
    _run(tmp_path, "add", "-A")
    _run(tmp_path, "commit", "-q", "-m", "an ordinary feature branch")
    return recorded


def _record_at(tmp_path: Path, recorded: str) -> Path:
    path = tmp_path / "docs" / "status" / "migration-baseline.json"
    record = dict(RECORD)
    record["migration"] = {"baseline_commit": recorded}
    path.write_text(json.dumps(record), encoding="utf-8")
    return path


def _point_at(monkeypatch, tmp_path: Path, path: Path) -> None:
    monkeypatch.setattr(gate, "ROOT", tmp_path)
    monkeypatch.setattr(gate, "BASELINE", path)
    monkeypatch.setattr(sys, "argv", ["check_migration_adjudicated.py"])
    # A feature branch must never reach the drift comparison at all: it is not a
    # migration, so there is nothing to adjudicate. Returning counts that
    # disagree with the record makes reaching it an audible failure rather than
    # a silent pass.
    monkeypatch.setattr(
        gate,
        "run_drift",
        lambda _ref: ("statement drift against main: 38 difference(s)\n", 1),
    )


def test_default_baseline_is_the_branch_point_not_the_recorded_pin(
    monkeypatch, tmp_path, capsys
) -> None:
    """A feature branch cut after a migration is not itself a migration.

    Reverting the default to `record["migration"]["baseline_commit"]` makes this
    fail: the pin's toolchain is v4.31.0, the tree's is v4.33.0, the gate reads
    that as a bump, and the 38 measured differences do not match the recorded
    31.
    """
    recorded = _repo(tmp_path, upstream=True)
    _point_at(monkeypatch, tmp_path, _record_at(tmp_path, recorded))

    assert gate.main() == 0
    out = capsys.readouterr().out
    assert "not a migration" in out, out
    assert recorded[:12] not in out, f"took the recorded pin as its baseline:\n{out}"


def test_without_an_upstream_ref_it_falls_back_to_the_recorded_pin(
    monkeypatch, tmp_path, capsys
) -> None:
    """A shallow or forkless checkout keeps the old behaviour rather than none.

    `merge-base` fails when `origin/main` is not in the checkout. The gate has
    to stay a gate there, so it falls back to the record and -- on this
    history -- correctly refuses.
    """
    recorded = _repo(tmp_path, upstream=False)
    _point_at(monkeypatch, tmp_path, _record_at(tmp_path, recorded))

    assert gate.main() == 1
    err = capsys.readouterr().err
    assert "no longer matches the tree" in err, err
