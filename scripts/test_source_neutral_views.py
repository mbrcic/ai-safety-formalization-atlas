#!/usr/bin/env python3
"""Regression checks for source-scoped generated views.

The ledger accepts claims from sources other than the closed BY catalogue. Those
claims must remain visible to global views without entering the CSUR-specific
source report, and the CSUR-specific denominator must remain unchanged.
"""

from __future__ import annotations

import copy
import json
from pathlib import Path

import generate_registry_views as views


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    registry = json.loads((ROOT / "registry.yaml").read_text(encoding="utf-8"))
    baseline_claim_count = sum(
        "informal_claim" in result for result in registry["results"]
    )
    # A claim from a source other than the survey: `CLM-`, not `LAND-`, which is
    # for formalizations standing on their own account. The probe also drops the
    # survey-only fields, because a non-survey claim cannot answer them and the
    # validator now rejects a row that pretends otherwise.
    row = copy.deepcopy(next(r for r in registry["results"] if r["id"] == "BY-001"))
    row["id"] = "CLM-AISI-001"
    row["name"] = "AISI source claim regression probe"
    row["original_source_refs"] = ["aisi-alignment-project-2026"]
    for survey_only in ("paper_reference", "survey_proof_assessment",
                        "formal_library_search"):
        row.pop(survey_only, None)
    registry["results"].append(row)

    status = views.render_status(
        registry,
        json.loads((ROOT / "docs/provenance/formalization-search.json").read_text()),
    )
    by_area = views.render_by_area(registry)
    source_report = views.render_survey_source_report(registry)
    expected_claim_count = baseline_claim_count + 1
    if f"| Results stating a source claim | {expected_claim_count} |" not in status:
        raise SystemExit("source-neutral regression: global status did not count the AISI claim")
    if "CLM-AISI-001" not in by_area:
        raise SystemExit("source-neutral regression: AISI claim is absent from the by-area view")
    if "CLM-AISI-001" in source_report:
        raise SystemExit("source-neutral regression: AISI claim entered the CSUR source report")
    if "45 / 44" in status or "44 / 45" in status:
        raise SystemExit("source-neutral regression: CSUR denominator changed")
    if "44 / 44" not in status:
        raise SystemExit("source-neutral regression: CSUR status lost its closed 44/44 count")
    print("source-neutral views ok: non-survey claims stay out of CSUR status/report")


if __name__ == "__main__":
    main()
