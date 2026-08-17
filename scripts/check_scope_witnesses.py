#!/usr/bin/env python3
"""Report `Wider` and `Beyond` audit rows that name no worked witness.

**Advisory.** This exits 0 whatever it finds, and is meant to produce a worklist
rather than to block. It exits non-zero only if the audit cannot be parsed at
all, which would mean the report is silently vacuous.

Why this check exists. A `Wider` verdict is a claim that the atlas statement
implies the printed one *and not conversely* — that is, a claim about what the
printed statement **cannot** reach. Nothing in the build tests such a claim: the
file compiles whether the widening is real, vacuous, or backwards. What settles
such a row is a small worked object exhibiting membership of the widened region;
prose alone cannot.

So the standard a row should meet is: name something in `Examples…` that lives
in the widened region and could not be stated at the printed hypotheses. A row
without one is not necessarily wrong — most of the unwitnessed rows here are
fine — it is unfalsifiable by the build, which is a different and weaker thing
than checked.

`Same` rows are not reported: there is no gap to exhibit.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUDIT = ROOT / "docs" / "provenance" / "source-coverage-audit.md"

SECTION_RE = re.compile(r"^## (\d+)\. (.+)$")
# `Examples…Foo` in the prose, or a fully qualified `AISafetyAtlas.Examples.Foo`
WITNESS_RE = re.compile(r"Examples[…\.]")


def rows(text: str):
    """Every six-cell grading row, with the section it sits under."""
    section = None
    for line in text.splitlines():
        heading = SECTION_RE.match(line)
        if line.startswith("## "):
            section = heading.group(2).strip() if heading else None
            continue
        if not line.startswith("|") or section is None:
            continue
        masked = line.replace(r"\|", "\x00")
        cells = masked.split("|")[1:-1]
        if len(cells) != 6:
            continue
        cells = [c.replace("\x00", "|").strip() for c in cells]
        first = cells[0].replace("**", "").strip()
        if first in {"#", "§", "source"} or set(first) <= {"-"}:
            continue
        yield section, cells, line


def main() -> int:
    if not AUDIT.exists():
        print(f"check_scope_witnesses: missing {AUDIT}", file=sys.stderr)
        return 1
    text = AUDIT.read_text()

    graded = witnessed = 0
    gaps: dict[str, list[str]] = {}
    for section, cells, line in rows(text):
        scope = cells[4].replace("**", "").strip()
        if not (scope.startswith("Wider") or scope == "Beyond"):
            continue
        graded += 1
        if WITNESS_RE.search(line):
            witnessed += 1
        else:
            gaps.setdefault(section, []).append(cells[0].replace("**", "").strip())

    if graded == 0:
        print(
            "check_scope_witnesses: no Wider or Beyond rows found — the audit's "
            "table shape must have changed, so this report is vacuous",
            file=sys.stderr,
        )
        return 1

    print(
        f"check_scope_witnesses (advisory): {witnessed}/{graded} Wider and Beyond "
        f"rows name a worked witness; {graded - witnessed} do not"
    )
    for section in sorted(gaps):
        names = gaps[section]
        print(f"  {section} — {len(names)} without a witness")
        for name in names:
            print(f"      {name[:96]}")
    if gaps:
        print(
            "  A row here is not wrong; it is unfalsifiable by the build. To close "
            "one, add an Examples declaration that lives in the widened region and "
            "cannot be stated at the printed hypotheses, then name it in the row."
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
