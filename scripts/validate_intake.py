#!/usr/bin/env python3
"""Validate the statement intake lane.

The conjecture ledger is a *curated board*: every row is graded against a
printed source, carries a scope and fidelity verdict, and survives the full
gate. That is the right bar for the board and the wrong bar for the front door.
It means the only way a statement has ever entered this repository is for the
maintainer to transcribe it, and the record shows exactly that -- every
externally-originated row on the board was transcribed by hand from a MAIS
issue, because transcription-by-maintainer was the only path that existed.

This lane is the other half: **a compiling `Prop` and a minimal row, with no
grade of any kind.** It sits below the board, it is never coverage, and nothing
in it is a result.

The authority split is what this file enforces, and it is enforced by
*rejection* rather than by convention. A proposer may deposit a statement. A
proposer may not deposit a grade -- not a source-fidelity verdict, not a scope
verdict, not a statement-match relationship, not a bridge status. Those fields
are refused outright rather than left optional, so "an agent may add statements,
only a human adds gradings" is a check instead of a promise.

Containment is structural, exactly as it is for conjectures: intake modules live
under `AISafetyAtlas.Conjectures.Intake.*`, are never reachable from the atlas
root import, and a `Prop`-valued definition asserts nothing on its own. `sorry`
stays banned repo-wide.

**What this file does not establish.** It resolves a deposited name against the
elaborated declaration index, and checks the recorded kind and module. The index
carries no types -- deliberately, see `generate_declaration_index.py` -- so
nothing here can see that a deposited definition is `Prop`-valued rather than,
say, a `Nat`. `scripts/check_intake_statements.py` elaborates the deposited
names and is what makes the lane's headline promise true. The split is
deliberate: this check is cheap and runs anywhere, that one needs a build.

**Leaving the lane is a decision that gets recorded.** A row is `PROMOTED` when
it becomes a conjecture row -- and must then name the `CONJ-` id it became, so
the two ledgers cannot drift apart -- or `DECLINED` with a reason. Ids are never
reused, so "not in the lane" is never the same as "never arrived".
"""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys
from typing import Any, NoReturn, cast

ROOT = Path(__file__).resolve().parents[1]
INTAKE = ROOT / "intake.yaml"
CONJECTURES = ROOT / "conjectures.yaml"
DECLARATION_INDEX = ROOT / "docs/status/declaration-index.json"

ID_RE = re.compile(r"^IN-(\d{3})$")
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
LEAN_PREFIX = "AISafetyAtlas.Conjectures.Intake."

STATUSES = {"OPEN", "PROMOTED", "DECLINED"}

# What a deposited name may be. The index records `kind`, so this much is free.
# `def` only: the lane takes a statement, and a `theorem` is a *proof*, which is
# a different deposit with a different bar. An `inductive` or a `constructor` is
# neither.
#
# This is a necessary condition and not the check the lane's contract promises.
# `Prop`-valuedness is a fact about the elaborated *type*, which the index does
# not carry by design, and `scripts/check_intake_statements.py` is what
# establishes it.
DEPOSITABLE_KINDS = {"def"}

REQUIRED = ("id", "statement", "lean", "lean_module", "proposed_by", "received", "status")
OPTIONAL = ("why_it_matters", "outcome", "promoted_to")
KNOWN = set(REQUIRED) | set(OPTIONAL)

# Grading vocabulary. Every one of these is a human judgement about how a
# statement stands to a source or to a real system, and none of them may ride
# in on an intake row. This list is the authority boundary, written down.
REFUSED = {
    "source_ref": "a graded source reference",
    "context_source_ref": "a graded source reference",
    "source_scope": "a scope verdict",
    "source_fidelity": "a fidelity verdict",
    "source_note": "a grading note",
    "relationship": "a statement-match grade",
    "ai_bridge_status": "a bridge status",
    "ai_safety_relevance": "an AI-system reading",
    "resolution": "a resolution, which only a settled board row has",
    "refutation": "a refutation clause, which the board requires and this lane does not",
    "kind": "a board row kind",
    "prior_art": "a prior-art survey, which is grading work",
}


def fail(message: str) -> NoReturn:
    print(f"intake error: {message}", file=sys.stderr)
    raise SystemExit(1)


def require_mapping(value: object, message: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(message)
    return cast(dict[str, Any], value)


def nonempty_text(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def main() -> None:
    if not INTAKE.exists():
        fail("intake.yaml is missing; the lane is part of the published surface")
    try:
        data = json.loads(INTAKE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(str(error))
    data = require_mapping(data, "intake.yaml must contain an object")

    rows = data.get("intake")
    if not isinstance(rows, list):
        fail("intake must be a list")
    if not nonempty_text(data.get("description")):
        fail("intake.yaml must carry a description saying what the lane is for")
    next_id = data.get("next_id")
    if not isinstance(next_id, int) or next_id < 1:
        fail("next_id must be a positive integer")

    # name -> (kind, module). The kind and the module both carry weight below:
    # a row's whole content is that a *proposition* compiles and that the module
    # it advertises is the one that supplies it, and a bare name set can check
    # neither.
    declarations: dict[str, tuple[str, str]] = {}
    if DECLARATION_INDEX.exists():
        try:
            index = json.loads(DECLARATION_INDEX.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            fail(f"docs/status/declaration-index.json is unreadable: {error}")
        declarations = {
            entry["name"]: (str(entry.get("kind", "")), str(entry.get("module", "")))
            for entry in index.get("declarations", [])
            if isinstance(entry, dict) and isinstance(entry.get("name"), str)
        }

    conjecture_ids: set[str] = set()
    if CONJECTURES.exists():
        try:
            board = json.loads(CONJECTURES.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            fail(f"conjectures.yaml is unreadable: {error}")
        conjecture_ids = {
            row["id"] for row in board.get("conjectures", []) if isinstance(row.get("id"), str)
        }

    seen: set[str] = set()
    highest = 0
    for row in rows:
        row = require_mapping(row, "intake entries must be objects")
        row_id = row.get("id")
        match = ID_RE.match(row_id) if isinstance(row_id, str) else None
        if match is None:
            fail(f"intake id {row_id!r} must look like IN-001")
        row_id = cast(str, row_id)
        if row_id in seen:
            fail(f"{row_id} appears twice")
        seen.add(row_id)
        highest = max(highest, int(match.group(1)))

        refused = sorted(set(row) & set(REFUSED))
        if refused:
            first = refused[0]
            fail(
                f"{row_id} carries {first}, which is {REFUSED[first]}. The intake lane "
                "takes statements, not grades: deposit the statement here and let a "
                "human grade it on the conjecture board"
            )
        unknown = sorted(set(row) - KNOWN)
        if unknown:
            fail(f"{row_id} has unknown fields {unknown}")
        for field in REQUIRED:
            if not nonempty_text(row.get(field)):
                fail(f"{row_id} must carry a non-empty {field}")

        if not DATE_RE.match(row["received"]):
            fail(f"{row_id} received must be an ISO date, not {row['received']!r}")
        if row["status"] not in STATUSES:
            fail(f"{row_id} status {row['status']!r} must be one of {sorted(STATUSES)}")

        lean = row["lean"]
        if not lean.startswith(LEAN_PREFIX):
            fail(
                f"{row_id} names {lean!r}; an intake statement must live under "
                f"{LEAN_PREFIX}*, which is unreachable from the atlas root import, so "
                "nothing deposited here can reach the public API however it was merged"
            )
        if not row["lean_module"].startswith(LEAN_PREFIX.rstrip(".")):
            fail(f"{row_id} lean_module must be an {LEAN_PREFIX.rstrip('.')} module")

        terminal = row["status"] in {"PROMOTED", "DECLINED"}
        if terminal and not nonempty_text(row.get("outcome")):
            fail(
                f"{row_id} is {row['status']} and must record an outcome; a row never "
                "leaves this lane as an undocumented decision"
            )
        if not terminal and row.get("outcome") is not None:
            fail(f"{row_id} is OPEN and must not record an outcome")
        promoted_to = row.get("promoted_to")
        if row["status"] == "PROMOTED":
            if not nonempty_text(promoted_to):
                fail(f"{row_id} is PROMOTED and must name the conjecture row it became")
            if conjecture_ids and promoted_to not in conjecture_ids:
                fail(
                    f"{row_id} was promoted to {promoted_to}, which is not a row in "
                    "conjectures.yaml; the two ledgers may not drift apart"
                )
        elif promoted_to is not None:
            fail(f"{row_id} is not PROMOTED but names promoted_to")

    if next_id <= highest:
        fail(f"next_id {next_id} must exceed the highest used id IN-{highest:03d}")

    # Resolution against the elaborated index runs last, after every structural
    # rule. A row that breaks both should hear about the cheap defect it can fix
    # from the ledger alone before the one that needs a build.
    #
    # This used to read `if declarations and ...`, which skipped resolution
    # entirely whenever the index was missing or empty -- so a row naming a
    # declaration that does not exist was accepted by an absent build product.
    # A lane whose whole content is "this compiles" must not fail open on the
    # only artifact that could say so.
    if rows and not declarations:
        fail(
            "intake rows are present but docs/status/declaration-index.json is "
            "missing or empty; a row's whole content is that its statement "
            "compiles, so it cannot be admitted without the elaborated index. "
            "Run scripts/generate_declaration_index.py --write after a build"
        )
    for row in rows:
        entry = declarations.get(row["lean"])
        if entry is None:
            fail(
                f"{row['id']} names {row['lean']!r}, which is not in the elaborated "
                "declaration index; an intake row's whole content is that the "
                "statement compiles"
            )
        kind, module = entry
        if kind not in DEPOSITABLE_KINDS:
            fail(
                f"{row['id']} names {row['lean']!r}, which the elaborated index "
                f"records as a {kind or 'declaration of unknown kind'}. The lane "
                f"takes a statement, so it must be one of {sorted(DEPOSITABLE_KINDS)}"
            )
        if module != row["lean_module"]:
            fail(
                f"{row['id']} advertises lean_module {row['lean_module']!r}, but "
                f"{row['lean']!r} is supplied by {module!r}. The module is an import "
                "instruction for a reader, so a wrong one is a broken row rather "
                "than a cosmetic mismatch"
            )

    open_rows = sum(1 for row in rows if row["status"] == "OPEN")
    if not rows:
        print(
            "intake ok: the lane is empty and reports itself that way — the "
            "machinery is live and no statement has been deposited yet"
        )
        return
    print(
        f"intake ok: {len(rows)} row(s) — {open_rows} open, "
        f"{sum(1 for r in rows if r['status'] == 'PROMOTED')} promoted, "
        f"{sum(1 for r in rows if r['status'] == 'DECLINED')} declined; "
        "no row carries a grade"
    )


if __name__ == "__main__":
    main()
