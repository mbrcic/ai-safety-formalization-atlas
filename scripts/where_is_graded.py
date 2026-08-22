#!/usr/bin/env python3
"""Every place a graded row's scope or fidelity is asserted.

A grade is recorded in one field and *restated* in two to five other files:
the ledger note beside it, the Lean docstring above the statement, the coverage
audit, a provenance document, a registry row.  Changing the field and missing
one of the restatements is the defect this repository has paid for eight times --
`MAIS.lean` calling MAIS-O25 `Mixed` after the ledger said `Same`, the audit
denying a structural layer that existed, `LAND-CAUSAL-STRUCTURAL-001` claiming
one narrowing axis after the audit had split it into two, and a `source_note`
denying a tag in its own YAML object.

The mechanized checks catch the cases they can parse.  This is for the step
before: given a row, print every file that mentions it, so a regrade starts from
a list instead of from memory.  It reads, never writes, and it is advisory --
what it prints is a place to look, not a finding.

    scripts/where_is_graded.py CONJ-006
    scripts/where_is_graded.py LAND-CAUSAL-STRUCTURAL-001
    scripts/where_is_graded.py --all
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

SCOPE_WORDS = ("Same", "Narrower", "Mixed", "Retired", "Beyond", "Wider")
FIDELITY_WORDS = ("Literal", "Selected", "Bridged", "DetermineProblem", "AtlasOriginal")
GRADE_RE = re.compile(r"\b(" + "|".join(SCOPE_WORDS + FIDELITY_WORDS) + r")\b")

# Generated files restate grades faithfully by construction; a regrade fixes
# them by re-running their generator, so listing them is noise.
GENERATED = (
    "docs/status/",
    "docs/agent/",
    "site/",
    "README.md",
    "STATE.md",
    "AISafetyAtlas/Examples/Registry.lean",
)


def ledger_rows() -> dict[str, dict[str, object]]:
    rows: dict[str, dict[str, object]] = {}
    conj = json.loads((ROOT / "conjectures.yaml").read_text(encoding="utf-8"))
    for c in conj["conjectures"]:
        rows[c["id"]] = {
            "scope": c.get("source_scope"),
            "fidelity": c.get("source_fidelity"),
            "lean": c.get("lean"),
            "where": "conjectures.yaml",
        }
    reg = json.loads((ROOT / "registry.yaml").read_text(encoding="utf-8"))
    for r in reg["results"]:
        decls = [
            d
            for f in r.get("formalizations", [])
            for d in f.get("declarations", [])
        ]
        rows[r["id"]] = {
            "scope": None,
            "fidelity": None,
            "lean": decls[0] if decls else None,
            "where": "registry.yaml",
        }
    return rows


DATED_HEADER = re.compile(r"^(?:Date|HEAD):\s*\S", re.MULTILINE)


def is_frozen(path: str) -> bool:
    """A dated audit snapshot, which records what was true when it was written.

    `mais-conjectures-recursive-audit-2026-08-20.md` opens with `Date:` and a
    pinned `HEAD:`. Its grades are *supposed* to disagree with today's ledger --
    that is what a snapshot is -- so listing it as something a regrade must
    visit would train the reader to ignore this tool.
    """
    full = ROOT / path
    if not full.is_file():
        return False
    head = full.read_text(encoding="utf-8", errors="replace")[:600]
    return bool(DATED_HEADER.search(head))


def grep(term: str) -> list[tuple[str, int, str]]:
    """Tracked files mentioning `term`, excluding generated views."""
    proc = subprocess.run(
        ["git", "grep", "-n", "--fixed-strings", term],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    hits: list[tuple[str, int, str]] = []
    for line in (proc.stdout or "").splitlines():
        parts = line.split(":", 2)
        if len(parts) != 3:
            continue
        path, num, text = parts
        if any(path.startswith(g) for g in GENERATED):
            continue
        hits.append((path, int(num), text.strip()))
    return hits


def report(row_id: str, rows: dict[str, dict[str, object]]) -> int:
    if row_id not in rows:
        print(f"where_is_graded: no ledger row named {row_id}", file=sys.stderr)
        return 1
    row = rows[row_id]
    print(f"== {row_id} ==")
    print(f"   recorded in : {row['where']}")
    if row["scope"] is not None:
        print(f"   scope       : {row['scope']}")
        print(f"   fidelity    : {row['fidelity']}")
    if row["lean"]:
        print(f"   statement   : {row['lean']}")
    print()

    terms = [row_id]
    if row["lean"]:
        terms.append(str(row["lean"]).rsplit(".", 1)[-1])

    seen: set[tuple[str, int]] = set()
    by_file: dict[str, list[tuple[int, str, bool]]] = {}
    for term in terms:
        for path, num, text in grep(term):
            if (path, num) in seen:
                continue
            seen.add((path, num))
            by_file.setdefault(path, []).append((num, text, bool(GRADE_RE.search(text))))

    if not by_file:
        print("   no mentions outside the ledger.")
        return 0

    graded = 0
    frozen_lines = 0
    for path in sorted(by_file):
        lines = sorted(by_file[path])
        marks = sum(1 for _, _, g in lines if g)
        if is_frozen(path):
            frozen_lines += marks
            print(f"   {path}  ({len(lines)} mention(s))  -- dated snapshot, leave alone")
            continue
        graded += marks
        flag = "  <- states a grade" if marks else ""
        print(f"   {path}  ({len(lines)} mention(s), {marks} with a grade word){flag}")
        for num, text, is_graded in lines:
            if is_graded:
                print(f"      {num}: {text[:150]}")
    print()
    print(f"   {graded} line(s) restate a grade. A regrade has to visit each one.")
    if frozen_lines:
        print(f"   {frozen_lines} more sit in dated snapshots and must not be edited.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("row", nargs="?", help="a CONJ-* or LAND-* id")
    parser.add_argument("--all", action="store_true", help="every conjecture row")
    args = parser.parse_args()
    rows = ledger_rows()
    if args.all:
        status = 0
        for rid in sorted(r for r in rows if r.startswith("CONJ-")):
            status |= report(rid, rows)
            print()
        return status
    if not args.row:
        parser.error("pass a row id or --all")
    return report(args.row, rows)


if __name__ == "__main__":
    sys.exit(main())
