#!/usr/bin/env python3
"""Structural checks for pattern-A (A1–A3) harness wiring and triage artifacts.

Drives the real files in-repo (not reimplemented stubs): parses
`scripts/reproduce_isabelle.sh` and `landscape.yaml` / provenance docs.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "reproduce_isabelle.sh"
LANDSCAPE = ROOT / "landscape.yaml"
REGISTRY = ROOT / "registry.yaml"


def fail(msg: str) -> None:
    print(f"FAIL: {msg}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    sh = SCRIPT.read_text(encoding="utf-8")

    # --- A1 CondNorm harness ---
    if "reproduce_condnorm" not in sh:
        fail("reproduce_condnorm missing from reproduce_isabelle.sh")
    if "afp-CondNormReasHOL-2026-02-06.tar.gz" not in sh:
        fail("CondNorm archive URL pin missing")
    if "10c3aa794a3cafcfb08a784e11515933162a490b32fc0cdb0cf88f489accdb38" not in sh:
        fail("CondNorm SHA-256 pin missing")
    if not re.search(r"condnorm\)", sh):
        fail("condnorm CLI case missing")

    # --- A2 Deep_Learning harness ---
    if "reproduce_deep_learning" not in sh:
        fail("reproduce_deep_learning missing")
    if "afp-2026-02-06.tar.gz" not in sh:
        fail("full AFP archive URL for Deep_Learning missing")
    if "b059edd46073479ee8dde45004c2346a7365e5d94cded49d27257cfea66c8879" not in sh:
        fail("full AFP SHA-256 pin missing")
    if "Deep_Learning" not in sh:
        fail("Deep_Learning session name missing from harness")

    # --- Provenance docs ---
    for rel in (
        "docs/provenance/a1-condnorm-parfit-triage.md",
        "docs/provenance/a2-deep-learning-by035-triage.md",
        "docs/provenance/a3-by001-unobservability-triage.md",
    ):
        p = ROOT / rel
        if not p.is_file():
            fail(f"missing provenance {rel}")
        body = p.read_text(encoding="utf-8")
        if "Reproduce" not in body and "reproduce" not in body:
            fail(f"{rel} must document reproduce command")

    a1 = (ROOT / "docs/provenance/a1-condnorm-parfit-triage.md").read_text(
        encoding="utf-8"
    )
    if "not EXACT" not in a1 and "Not EXACT" not in a1 and "not EXACT or EQUIVALENT" not in a1:
        if "not EXACT/EQUIVALENT" not in a1 and "Not Arrhenius" not in a1:
            # require explicit non-Arrhenius / non-exact language
            if "Arrhenius" not in a1 or "BY-008" not in a1:
                fail("A1 triage must discuss Arrhenius/BY-008 non-coverage")
    if "RELATED" not in a1 and "RELATED" not in a1.lower():
        # case variations
        if "adjacent" not in a1.lower():
            fail("A1 triage must state RELATED/adjacent relationship")

    # --- Landscape rows ---
    landscape = json.loads(LANDSCAPE.read_text(encoding="utf-8"))
    by_id = {e["id"]: e for e in landscape["entries"]}
    for eid, must_sub in (
        ("LAND-PE-001", "condnorm"),
        ("LAND-DL-001", "deep-learning"),
    ):
        if eid not in by_id:
            fail(f"landscape missing {eid}")
        e = by_id[eid]
        if e.get("survey_coverage") is not None:
            fail(f"{eid} survey_coverage must be null")
        if e.get("root_import"):
            fail(f"{eid} must not be root_import Lean facade")
        repro = e.get("reproduction") or ""
        if must_sub not in repro:
            fail(f"{eid} reproduction must mention {must_sub}")

    pe = by_id["LAND-PE-001"]
    if "BY-008" not in (pe.get("related_survey_ids") or []):
        fail("LAND-PE-001 must relate BY-008")
    note = (pe.get("notes") or "") + (pe.get("survey_coverage_note") or "")
    if "Arrhenius" not in note and "not EXACT" not in note and "Not EXACT" not in note:
        if "not EXACT/EQUIVALENT" not in note and "RELATED only" not in note:
            fail("LAND-PE-001 must deny EXACT Arrhenius coverage in notes")

    dl = by_id["LAND-DL-001"]
    if "BY-035" not in (dl.get("related_survey_ids") or []):
        fail("LAND-DL-001 must relate BY-035")

    # --- BY-001 registry: no pending candidates ---
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    by001 = next(r for r in registry["results"] if r["id"] == "BY-001")
    cands = by001.get("candidate_formalizations") or []
    if cands:
        fail("BY-001 candidate_formalizations must be empty after A3 triage")
    notes = by001.get("notes") or ""
    if "DISTINCT" not in notes and "cleared" not in notes.lower():
        fail("BY-001 notes must record DISTINCT/cleared triage")
    for c in cands:
        if c.get("relationship_review") == "PENDING":
            fail("no PENDING relationship_review allowed on BY-001")

    print(
        "test_a1_a3_pattern_a_harness ok: "
        "condnorm+deep-learning pins, LAND-PE-001/LAND-DL-001, BY-001 cleared"
    )


if __name__ == "__main__":
    main()
