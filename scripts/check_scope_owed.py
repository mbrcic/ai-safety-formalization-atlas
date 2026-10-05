#!/usr/bin/env python3
"""Report `Narrower` and `Mixed` audit rows that do not declare a state.

**Advisory.** This exits 0 whatever it finds, and is meant to produce a worklist
rather than to block. It exits non-zero only if the audit cannot be parsed at
all, which would mean the report is silently vacuous.

Why this check exists. The audit's standing rule is *scope >= print wherever
that is achievable*, and it says a `Narrower` or `Mixed` cell is a defect unless
the narrowing is discharged -- by regrading a cell that is not a narrowing at
all, by proving it cannot be closed, or by pricing what closing it would take.
The audit's own counting section says the per-cell audit of those cells is owed
and not done, and names what is missing: *"a mechanical check that each
narrowing is closed, proved unclosable, or costed"*. This is that check.

Nothing in the build tests a narrowing. The declarations compile whether the
narrowing is a units restatement, a hard obstruction, or an unpriced gap, and
the three call for completely different work. Without a per-cell state the 43
owed cells are one undifferentiated number, and the number is the same whether
every one of them has been adjudicated or none has.

The vocabulary, which is the audit's own three states:

  `**Narrowing state: regrade.**`
      not a narrowing -- a units restatement or a representation change. The
      note must name the converting lemma. A cell in this state is on its way
      out of the count: the audit says to regrade it rather than carry it, so
      this marker is transitional and a cell should not sit in it.
  `**Narrowing state: unclosable.**`
      provably not closable, with the witness that proves it named in the note.
  `**Narrowing state: open, costed.**`
      open, with what it would take stated in the note or in a document the
      note names.

A row without a marker is not wrong. It is unadjudicated, which is a different
and weaker thing than owed-and-understood -- and it is exactly the state the
audit records itself as being in.

`Narrower, and closed` is terminal and is not reported: the audit excludes it
from the owed count for the reason its own note gives.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUDIT = ROOT / "docs" / "provenance" / "source-coverage-audit.md"

SECTION_RE = re.compile(r"^## (\d+)\. (.+)$")
STATES = ("regrade", "unclosable", "open, costed")
STATE_RE = re.compile(
    r"\*\*Narrowing state: (" + "|".join(re.escape(s) for s in STATES) + r")\.\*\*"
)
# Any other spelling is a marker that no counter will ever see; refuse it rather
# than report the row as unadjudicated, which would hide a typo as a worklist item.
LOOSE_RE = re.compile(r"\*\*Narrowing state:([^*]*)\*\*")


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
        print(f"check_scope_owed: missing {AUDIT}", file=sys.stderr)
        return 1
    text = AUDIT.read_text()

    owed = 0
    states: dict[str, int] = dict.fromkeys(STATES, 0)
    gaps: dict[str, list[str]] = {}
    for section, cells, line in rows(text):
        scope = cells[4].replace("**", "").strip()
        grade = re.split(r"[,(]", scope, maxsplit=1)[0].strip()
        if grade not in {"Narrower", "Mixed"} or "and closed" in scope:
            continue
        owed += 1
        label = cells[0].replace("**", "").strip()
        found = STATE_RE.search(line)
        loose = LOOSE_RE.search(line)
        if loose and not found:
            print(
                f"check_scope_owed: row {label!r} in {section!r} carries an "
                f"unrecognised state {loose.group(1).strip()!r}; the vocabulary is "
                + ", ".join(STATES),
                file=sys.stderr,
            )
            return 1
        if found:
            states[found.group(1)] += 1
        else:
            gaps.setdefault(section, []).append(label)

    if owed == 0:
        print(
            "check_scope_owed: no Narrower or Mixed rows found — the audit's table "
            "shape must have changed, so this report is vacuous",
            file=sys.stderr,
        )
        return 1

    adjudicated = sum(states.values())
    breakdown = ", ".join(f"{states[s]} {s}" for s in STATES)
    print(
        f"check_scope_owed (advisory): {adjudicated}/{owed} owed Narrower and Mixed "
        f"cells declare a state ({breakdown}); {owed - adjudicated} do not"
    )
    for section in sorted(gaps):
        names = gaps[section]
        print(f"  {section} — {len(names)} unadjudicated")
        for name in names:
            print(f"      {name[:96]}")
    if gaps:
        print(
            "  A row here is not wrong; it is unadjudicated. To close one, decide "
            "which of the three states it is in and say so in its note: regrade a "
            "cell that is not a narrowing and name the converting lemma, prove it "
            "unclosable and name the witness, or price what closing it would take."
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
