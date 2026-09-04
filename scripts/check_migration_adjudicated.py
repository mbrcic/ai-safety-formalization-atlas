#!/usr/bin/env python3
"""When the toolchain moves, require the statement drift to have been adjudicated.

``check_statement_drift.py`` grows a ``--fail-on-drift`` flag for exactly one
situation -- a toolchain bump, where the honest answer is "no statement changed"
-- and its own docstring says so. Nothing ran it that way. ``agent_gate.sh``
piped the advisory form through ``grep … || true``, which discards the exit
status twice over, so the v4.31.0 -> v4.33.0 adjudication happened because a
person chose to do it, not because anything required it. The thirty-one
differences it found were all benign; that was luck plus care, and neither is a
control.

So this decides whether the branch is a migration by looking at the toolchain
rather than at anybody's intent, and if it is, insists that the drift has been
written down and that the record still matches what the checker reports now:

* the recorded completed migration is an ancestor and its toolchain is still
  current -> not a migration, pass. An ordinary feature branch is *supposed* to
  add statements, and failing it on drift would train everyone to ignore this;
* without a completed-migration anchor, ``lean-toolchain`` unchanged against the
  baseline -> not a migration, pass;
* Changed, with no ``migration-baseline.json`` naming that baseline -> fail. The
  bump has not been measured.
* Changed, with a record that disagrees with the live numbers -> fail, and print
  both. Either the tree moved after the record was written, or the record was
  wrong.

The record is a countersignature, not a proof: it says a human looked at each
difference and judged it. What is enforced here is that the looking happened and
that its subject is still the tree in front of us.

Usage:
    python3 scripts/check_migration_adjudicated.py
    python3 scripts/check_migration_adjudicated.py --ref <commit>
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "docs" / "status" / "migration-baseline.json"
TOOLCHAIN = "lean-toolchain"

DRIFT_RE = re.compile(r"^statement drift against .*?: (\d+) difference")
PROOFS_RE = re.compile(r"(\d+) proof body/bodies also rewritten")
ADJUDICATE_RE = re.compile(r"^adjudicate: (\d+) non-theorem declaration")


def git(*args: str) -> str | None:
    proc = subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, check=False
    )
    return proc.stdout if proc.returncode == 0 else None


def toolchain_at(ref: str) -> str | None:
    blob = git("show", f"{ref}:{TOOLCHAIN}")
    return blob.strip() if blob is not None else None


def is_ancestor(ref: str) -> bool:
    """Whether the current branch descends from the recorded completed bump."""
    proc = subprocess.run(
        ["git", "merge-base", "--is-ancestor", ref, "HEAD"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    return proc.returncode == 0


def working_toolchain() -> str:
    return (ROOT / TOOLCHAIN).read_text(encoding="utf-8").strip()


def run_drift(ref: str) -> tuple[str, int]:
    proc = subprocess.run(
        [sys.executable, "scripts/check_statement_drift.py", "--ref", ref, "--fail-on-drift"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    return (proc.stdout or "") + (proc.stderr or ""), proc.returncode


def measured(blob: str) -> dict[str, int]:
    found = {"statement_drift_differences": 0, "proof_bodies_rewritten": 0, "adjudications": 0}
    for line in blob.splitlines():
        match = DRIFT_RE.match(line)
        if match:
            found["statement_drift_differences"] = int(match.group(1))
            proofs = PROOFS_RE.search(line)
            if proofs:
                found["proof_bodies_rewritten"] = int(proofs.group(1))
        match = ADJUDICATE_RE.match(line)
        if match:
            found["adjudications"] = int(match.group(1))
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--ref",
        default=None,
        help="baseline to compare against; defaults to the recorded baseline_commit",
    )
    arguments = parser.parse_args()

    record = None
    if BASELINE.is_file():
        record = json.loads(BASELINE.read_text(encoding="utf-8"))

    ref = arguments.ref
    if ref is None:
        if record is None:
            print(
                "check_migration_adjudicated: no --ref and no "
                f"{BASELINE.relative_to(ROOT)} to take a baseline from",
                file=sys.stderr,
            )
            return 1
        ref = record["migration"]["baseline_commit"]

    now = working_toolchain()

    # Once the adjudicated migration has merged, feature branches must be
    # compared with that completed tree, not forever with the pre-migration
    # baseline. The old comparison remains reproducible from the record and its
    # two committed elaboration dumps; this shortcut only decides that the
    # current branch is not itself another toolchain migration.
    if arguments.ref is None and record is not None:
        completed = record["migration"].get("completed_commit")
        if completed:
            completed_toolchain = toolchain_at(completed)
            if completed_toolchain is None:
                print(
                    "check_migration_adjudicated: cannot read "
                    f"{TOOLCHAIN} at completed migration {completed} — is that "
                    "commit fetched in this checkout?",
                    file=sys.stderr,
                )
                return 1
            if is_ancestor(completed) and completed_toolchain == now:
                print(
                    "check_migration_adjudicated ok: current branch descends from "
                    f"completed migration {completed[:12]} and keeps "
                    f"{now}; not a migration"
                )
                return 0

    before = toolchain_at(ref)
    if before is None:
        print(
            f"check_migration_adjudicated: cannot read {TOOLCHAIN} at {ref} — "
            "is the baseline commit fetched in this checkout?",
            file=sys.stderr,
        )
        return 1

    if before == now:
        print(
            f"check_migration_adjudicated ok: toolchain unchanged against {ref[:12]} "
            f"({now}); not a migration, statement drift stays advisory"
        )
        return 0

    if record is None:
        print(
            f"check_migration_adjudicated: {TOOLCHAIN} moved {before} -> {now} and there "
            f"is no {BASELINE.relative_to(ROOT)}.\nA toolchain bump has to record what it "
            "was measured against and what the measurement said. Run\n"
            f"  python3 scripts/check_statement_drift.py --ref {ref} --fail-on-drift\n"
            "adjudicate every difference, and write the counts into that file.",
            file=sys.stderr,
        )
        return 1

    recorded_commit = record["migration"]["baseline_commit"]
    if not recorded_commit.startswith(ref) and not ref.startswith(recorded_commit):
        print(
            f"check_migration_adjudicated: comparing against {ref} but "
            f"{BASELINE.relative_to(ROOT)} records {recorded_commit}. The adjudication "
            "on file is about a different tree.",
            file=sys.stderr,
        )
        return 1

    blob, _code = run_drift(ref)
    live = measured(blob)
    claimed = {key: record["measured"].get(key) for key in live}
    claimed["adjudications"] = len(record.get("adjudications", []))

    mismatch = {key: (claimed[key], live[key]) for key in live if claimed[key] != live[key]}
    if mismatch:
        print(
            f"check_migration_adjudicated: {TOOLCHAIN} moved {before} -> {now}, and the "
            f"record in {BASELINE.relative_to(ROOT)} no longer matches the tree.",
            file=sys.stderr,
        )
        for key, (was, is_now) in sorted(mismatch.items()):
            print(f"  {key}: recorded {was}, measured {is_now}", file=sys.stderr)
        print(
            "\nEvery difference needs a human verdict before this can go green. Run\n"
            f"  python3 scripts/check_statement_drift.py --ref {ref} --fail-on-drift\n"
            "read what it prints, and update the record once each one is accounted for.",
            file=sys.stderr,
        )
        return 1

    print(
        f"check_migration_adjudicated ok: {before} -> {now} against {ref[:12]}; "
        f"{live['statement_drift_differences']} statement difference(s) and "
        f"{live['adjudications']} adjudication(s), all recorded in "
        f"{BASELINE.relative_to(ROOT)}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
