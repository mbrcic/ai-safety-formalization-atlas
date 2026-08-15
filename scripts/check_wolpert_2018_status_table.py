#!/usr/bin/env python3
"""Keep the Wolpert 2018 inventory synchronized — over the whole paper.

The 2008 transcription needed several review rounds because prose said items
were complete while declarations or source qualifications were missing.  This
gate treats the inventory table in ``wolpert-2018-knowledge.md`` as the
authority: every source item must occur once, with its adjudicated status, and
its Lean cell must name declarations that exist in the tree.

**This gate previously carried a nineteen-item allowlist** of the
physical-knowledge cluster and reported ``19 scoped items``.  Nothing outside
that list could fail it, so §III — Definitions 4 and 6 through 9, and
Propositions 7 through 14 — was invisible: not recorded as missing, not recorded
at all.  A gate whose denominator is its own allowlist measures attention, not
coverage.  ``EXPECTED`` below is now the complete source inventory, so an
unmechanized proposition is a row that says so and a *forgotten* proposition is
a failure.

Two smaller defects went with it.  The row parser skipped any line whose status
was not ``SOURCE-EXACT`` or ``REFUTED``, so a ``SPECIALIZED`` row would have
been read as prose and silently dropped.  And no rule connected a status to the
shape of its row, so ``NOT-MECHANIZED`` could have named a declaration, or an
item could have claimed a status while explaining nothing.

Status vocabulary beyond the four grades fixed by the 2008 map:

``VIA-2008``
    The 2018 statement *is* the 2008 statement; the Lean cell names the 2008
    declaration.  No second transcription is owed.
``CORE-ONLY``
    The mathematics is mechanized; the printed statement's own shape is not
    exposed as one declaration.  Distinguishing this from ``SOURCE-EXACT`` is
    what stops "the core is done" from being read as "it is a theorem here".
``NOT-MECHANIZED``
    No Lean.  The note must give a reason, and the Lean cell must be empty.
``INTERPRETATION``
    The item makes no mathematical claim to transcribe.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "registry.yaml"
PROVENANCE = ROOT / "docs" / "provenance" / "wolpert-2018-knowledge.md"
LEAN_ROOT = ROOT / "AISafetyAtlas"

MECHANIZED = {"SOURCE-EXACT", "SPECIALIZED", "REPAIRED", "REFUTED", "VIA-2008", "CORE-ONLY"}
UNMECHANIZED = {"NOT-MECHANIZED", "INTERPRETATION"}
STATUSES = MECHANIZED | UNMECHANIZED

# A `NOT-MECHANIZED` row that says only "missing" records nothing a reader could
# not have inferred from the empty Lean cell. The reason is the content.
MIN_REASON_CHARS = 60

# The complete inventory of arXiv:1711.03499v3: Definitions 1-11, the twenty-five
# numbered results with their printed sub-parts, the displayed equations, the
# nine examples, and the two notions the paper raises in prose without a
# displayed claim. Adding a source item the paper contains is a change to this
# dict; the table alone cannot grant itself coverage.
EXPECTED = {
    "Def. 1": "VIA-2008",
    "Def. 2": "VIA-2008",
    "Def. 3": "VIA-2008",
    "Def. 4": "SOURCE-EXACT",
    "Def. 5": "VIA-2008",
    "Def. 6": "VIA-2008",
    "Def. 7": "SPECIALIZED",
    "Def. 8": "SOURCE-EXACT",
    "Def. 9": "SPECIALIZED",
    "Def. 10": "VIA-2008",
    "Def. 11": "SOURCE-EXACT",
    "prose after Def. 11": "SOURCE-EXACT",
    "Prop. 1": "VIA-2008",
    "Prop. 2": "VIA-2008",
    "Cor. 3": "SOURCE-EXACT",
    "Prop. 4(i)": "VIA-2008",
    "Prop. 4(ii)": "VIA-2008",
    "Prop. 4, third sentence": "VIA-2008",
    "Prop. 5(i)": "VIA-2008",
    "Prop. 5(ii)": "VIA-2008",
    "Prop. 6": "VIA-2008",
    "Prop. 7(1)": "SOURCE-EXACT",
    "Prop. 7(2)": "SOURCE-EXACT",
    "`cov ≤ 1` and the equality case, prose after Def. 6": "SOURCE-EXACT",
    "universal device, prose after Def. 10": "SOURCE-EXACT",
    "`|U| > 3` sentence, prose after Def. 10": "REPAIRED",
    "`Ĉ(Γ; D)` after Def. 7": "SOURCE-EXACT",
    "Prop. 8": "SOURCE-EXACT",
    "Prop. 9": "SOURCE-EXACT",
    "Prop. 10": "SOURCE-EXACT",
    "Prop. 11": "SOURCE-EXACT",
    "Prop. 12": "REFUTED",
    "Prop. 13": "VIA-2008",
    "Prop. 14": "SOURCE-EXACT",
    "Prop. 15(i)": "VIA-2008",
    "Prop. 15(ii)": "VIA-2008",
    "Prop. 15(iii)": "VIA-2008",
    "Prop. 16(i)": "VIA-2008",
    "Prop. 16(ii)": "VIA-2008",
    "Lemma 17(i)": "SOURCE-EXACT",
    "Lemma 17(ii)": "SOURCE-EXACT",
    "Proposition 18": "SOURCE-EXACT",
    "Corollary 19": "SOURCE-EXACT",
    "Corollary 20(i)": "SOURCE-EXACT",
    "Corollary 20(ii)": "SOURCE-EXACT",
    "Corollary 20(iii)": "SOURCE-EXACT",
    "Corollary 20(iv)": "SOURCE-EXACT",
    "Corollary 21(i)": "SOURCE-EXACT",
    "Corollary 21(ii)": "REPAIRED",
    "Corollary 22": "SOURCE-EXACT",
    "Corollary 23": "SOURCE-EXACT",
    "Corollary 24": "SOURCE-EXACT",
    "Corollary 25": "REFUTED",
    "equations (1)–(4)": "INTERPRETATION",
    "equations (5)–(8), (10)": "INTERPRETATION",
    "equation (9)": "SOURCE-EXACT",
    "equation (11)": "SOURCE-EXACT",
    "Example 1": "INTERPRETATION",
    "Example 2": "INTERPRETATION",
    "Example 3": "INTERPRETATION",
    "Example 4": "INTERPRETATION",
    "Example 5": "INTERPRETATION",
    "Example 6": "REFUTED",
    "Example 7": "INTERPRETATION",
    "Example 8": "INTERPRETATION",
    "Example 9": "SOURCE-EXACT",
    "weaker knowledge, prose after Example 9": "REPAIRED",
    "negative introspection, prose": "INTERPRETATION",
}

# The detailed fidelity table in section 2 repeats a subset of these rows under
# the older long-form item names. It must not drift from the inventory.
DETAIL_ALIASES = {
    "Def. 11": "Def. 11",
    "prose after Def. 11": "prose after Def. 11",
    "Lemma 17(i)": "Lemma 17(i)",
    "Lemma 17(ii)": "Lemma 17(ii)",
    "Proposition 18": "Proposition 18",
    "Corollary 19": "Corollary 19",
    "Corollary 20(i)": "Corollary 20(i)",
    "Corollary 20(ii)": "Corollary 20(ii)",
    "Corollary 20(iii)": "Corollary 20(iii)",
    "Corollary 20(iv)": "Corollary 20(iv)",
    "Corollary 21(i)": "Corollary 21(i)",
    "Corollary 21(ii)": "Corollary 21(ii)",
    "Corollary 22": "Corollary 22",
    "Corollary 3": "Cor. 3",
    "Corollary 23": "Corollary 23",
    "Corollary 24": "Corollary 24",
    "equation (11)": "equation (11)",
    "Corollary 25": "Corollary 25",
    "Example 9": "Example 9",
}

INVENTORY_HEADING = "## 0. Complete source inventory"
DECL_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_.']*)`")
CELL_SPLIT_RE = re.compile(r"(?<!\\)\|")

# ``VIA-2008`` means "the 2018 statement *is* the 2008 statement, already
# proved". That is only the whole truth when the 2008 row it routes through is
# itself ``SOURCE-EXACT``. Routing through a ``SPECIALIZED`` row launders a
# narrowed scope into the mechanized column: the 2018 tally counts the item as
# covered while the restriction lives one document away, recorded against a
# different paper.
#
# This is how Proposition 13 shipped. It is the 2008 Theorem 4 bound at the
# measure length, and 2008 Theorem 4 is ``SPECIALIZED`` -- so the 2018 row
# inherited a countable-to-finite restriction on the setup ranges and said
# nothing about it. A row may still route through a non-exact 2008 item, but
# only by stating the delta itself.
WOLPERT_2008 = ROOT / "docs" / "provenance" / "wolpert-inference-devices.md"
SOURCE_2008_RE = re.compile(r"2008\s+(Def|Thm|Prop|Cor|Lemma)\.?\s*(\d+)(?:\(([ivx]+)\))?")
SCOPE_DELTA_TOKEN = "scope delta:"


def declarations() -> set[str]:
    pattern = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|public\s+)?(?:noncomputable\s+)?"
        r"(?:def|theorem|abbrev|structure|class|instance|inductive|lemma)\s+"
        r"([A-Za-z_][A-Za-z0-9_.']*)"
    )
    names: set[str] = set()
    for path in LEAN_ROOT.rglob("*.lean"):
        for line in path.read_text(encoding="utf-8").splitlines():
            if match := pattern.match(line):
                names.add(match.group(1).split(".")[-1])
    return names


def statuses_2008() -> dict[tuple[str, str, str], str]:
    """The 2008 map's adjudicated status for each numbered item.

    Parsed with the 2008 gate's own reader rather than a second one, so the two
    documents cannot disagree about what a row says.
    """
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import check_wolpert_status_table as gate_2008

    items, *_rest = gate_2008.parse_table(WOLPERT_2008.read_text(encoding="utf-8"))
    return items


def check_via_2008(
    item: str, note: str, statuses: dict[tuple[str, str, str], str]
) -> list[str]:
    """A ``VIA-2008`` row must route through an exact 2008 row, or state the delta."""
    errors: list[str] = []
    for kind, number, part in SOURCE_2008_RE.findall(note):
        key = (kind, number, part or "")
        status = statuses.get(key)
        if status is None:
            errors.append(
                f"{item}: names 2008 {kind} {number}{f'({part})' if part else ''}, "
                "which the 2008 table has no row for"
            )
            continue
        if status != "SOURCE-EXACT" and SCOPE_DELTA_TOKEN not in note:
            errors.append(
                f"{item}: VIA-2008 routes through 2008 {kind} {number}"
                f"{f'({part})' if part else ''}, which is {status}, without stating "
                f"the inherited restriction (expected a {SCOPE_DELTA_TOKEN!r} clause)"
            )
    return errors


def rows_in_section(text: str, heading: str) -> dict[str, tuple[str, str, str]]:
    """Table rows under one `##` heading, keyed by item.

    Scoped to a section on purpose: the document carries a second, narrower
    table of the same rows, and a parser that swept the whole file would read
    each item twice and report every one of them as a duplicate.
    """
    collected: dict[str, tuple[str, str, str]] = {}
    inside = False
    for line in text.splitlines():
        if line.startswith("## "):
            inside = line.strip() == heading
            continue
        if not inside or not line.startswith("|"):
            continue
        # Cardinality bars are written `\|` inside cells, so a naive split on
        # "|" tears `|Γ(U)| ≥ 3` into three columns and drops the row.
        cells = [
            cell.strip().replace("\\|", "|")
            for cell in CELL_SPLIT_RE.split(line.strip().strip("|"))
        ]
        if len(cells) != 4 or cells[1] not in STATUSES:
            continue
        collected.setdefault(cells[0], (cells[1], cells[2], cells[3]))
    return collected


def check_shape(item: str, status: str, lean: str, note: str, known: set[str]) -> list[str]:
    errors: list[str] = []
    names = DECL_RE.findall(lean)
    if status in MECHANIZED:
        if not names:
            errors.append(f"{item}: status {status} names no declaration")
        unknown = [name for name in names if name.split(".")[-1] not in known]
        if unknown:
            errors.append(f"{item}: unknown declarations {unknown}")
    else:
        if names:
            errors.append(
                f"{item}: status {status} must have an empty Lean cell, found {names}"
            )
        if lean not in {"—", "-", ""}:
            errors.append(f"{item}: status {status} expects an em dash Lean cell")
    if status == "NOT-MECHANIZED" and len(note) < MIN_REASON_CHARS:
        errors.append(
            f"{item}: NOT-MECHANIZED needs a stated reason, found {len(note)} "
            f"characters (minimum {MIN_REASON_CHARS})"
        )
    if not note:
        errors.append(f"{item}: empty note")
    return errors


def main() -> int:
    errors: list[str] = []
    text = PROVENANCE.read_text(encoding="utf-8")

    if INVENTORY_HEADING not in text:
        print(
            f"wolpert 2018 status error: {PROVENANCE.name} has no "
            f"{INVENTORY_HEADING!r} section",
            file=sys.stderr,
        )
        return 1

    rows = rows_in_section(text, INVENTORY_HEADING)

    missing = sorted(set(EXPECTED) - set(rows))
    extra = sorted(set(rows) - set(EXPECTED))
    if missing:
        errors.append(f"missing inventory rows: {missing}")
    if extra:
        errors.append(f"unexpected inventory rows: {extra}")

    known = declarations()
    inherited = statuses_2008()
    for item, expected in EXPECTED.items():
        if item not in rows:
            continue
        status, lean, note = rows[item]
        if status != expected:
            errors.append(f"{item}: expected {expected}, found {status}")
        errors.extend(check_shape(item, status, lean, note, known))
        if status == "VIA-2008":
            errors.extend(check_via_2008(item, note, inherited))

    # The narrower fidelity table must agree with the inventory it details.
    detail = rows_in_section(text, "## 2. Epistemic consequences and source defects")
    for detail_item, inventory_item in DETAIL_ALIASES.items():
        if detail_item not in detail:
            errors.append(f"{detail_item}: absent from the section 2 fidelity table")
            continue
        if inventory_item not in rows:
            continue
        if detail[detail_item][0] != rows[inventory_item][0]:
            errors.append(
                f"{detail_item}: section 2 says {detail[detail_item][0]}, "
                f"inventory says {rows[inventory_item][0]}"
            )

    refuted_declarations: dict[str, set[str]] = {
        item: {name.split(".")[-1] for name in DECL_RE.findall(rows[item][1])}
        for item, expected in EXPECTED.items()
        if expected == "REFUTED" and item in rows
    }

    facade = (ROOT / "AISafetyAtlas" / "Inference.lean").read_text(encoding="utf-8")
    for module in (
        "AISafetyAtlas.Inference.PhysicalKnowledge.Epistemic",
        "AISafetyAtlas.Inference.PhysicalKnowledge.Event",
    ):
        if f"public import {module}" not in facade:
            errors.append(f"facade does not publicly import {module}")

    # The ledger must keep promising exactly the refutations the table records.
    #
    # Two printed corollaries are machine-refuted, and they live in a `LAND-`
    # artifact row precisely so that no `EQUIVALENT` grade ever covers a statement
    # the tree contradicts. Dropping a refutation from the table while the row
    # still promises it, or letting that row acquire a statement-match grade, are
    # both silent and both wrong.
    # JSON is dynamically shaped; Any is the honest annotation here.
    registry: Any = json.loads(REGISTRY.read_text(encoding="utf-8"))

    def find_row(node: Any, key: str) -> Any:
        if isinstance(node, dict):
            if node.get("id") == key:
                return node
            for value in node.values():
                found = find_row(value, key)
                if found is not None:
                    return found
        elif isinstance(node, list):
            for value in node:
                found = find_row(value, key)
                if found is not None:
                    return found
        return None

    defects = find_row(registry, "LAND-WOLPERT-KNOW-DEFECTS-001")
    if not isinstance(defects, dict):
        errors.append(
            "LAND-WOLPERT-KNOW-DEFECTS-001 is missing; the refutations have no row"
        )
    else:
        # Every declaration the refuted rows point at must be named by the row
        # that owns them. A refutation dropped from the ledger while the table
        # still records it, or the reverse, is silent otherwise.
        owned: set[str] = set()
        for record in defects.get("formalizations", []):
            for name in record.get("declarations", []):
                owned.add(str(name).split(".")[-1])
        for item, status in EXPECTED.items():
            if status != "REFUTED":
                continue
            for name in refuted_declarations.get(item, set()):
                if name not in owned:
                    errors.append(
                        f"{item} is REFUTED and names `{name}`, which "
                        "LAND-WOLPERT-KNOW-DEFECTS-001 does not own"
                    )
        records = defects.get("formalizations", [])
        if isinstance(records, list):
            for record in records:
                if isinstance(record, dict) and record.get("relationship") in (
                    "EQUIVALENT",
                    "EXACT",
                ):
                    errors.append(
                        "the defects row carries a statement-match grade; a refutation "
                        "is not a match and an artifact row carries no grade"
                    )

    if errors:
        for error in errors:
            print(f"wolpert 2018 status error: {error}", file=sys.stderr)
        return 1

    tally: dict[str, int] = {}
    for status in EXPECTED.values():
        tally[status] = tally.get(status, 0) + 1
    breakdown = ", ".join(f"{tally[key]} {key}" for key in sorted(tally))
    claims = sum(
        count for status, count in tally.items() if status != "INTERPRETATION"
    )
    open_claims = tally.get("NOT-MECHANIZED", 0)
    print(
        f"wolpert 2018 inventory ok: {len(EXPECTED)} source items ({breakdown}); "
        f"{claims - open_claims}/{claims} mathematical claims mechanized"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
