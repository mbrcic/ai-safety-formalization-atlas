#!/usr/bin/env python3
"""Regression checks for source-scoped generated views.

The ledger accepts claims from sources other than the closed BY catalogue. Those
claims must remain visible to global views without entering the CSUR-specific
status page or source report.
"""

from __future__ import annotations

import copy
import json
from pathlib import Path

import generate_registry_views as views


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    registry = json.loads((ROOT / "registry.yaml").read_text(encoding="utf-8"))
    row = copy.deepcopy(next(r for r in registry["results"] if r["id"] == "BY-001"))
    row["id"] = "LAND-AISI-001"
    row["name"] = "AISI source claim regression probe"
    row["original_source_refs"] = ["aisi-alignment-project-2026"]
    registry["results"].append(row)

    status = views.render_status(
        registry,
        json.loads((ROOT / "docs/provenance/formalization-search.json").read_text()),
    )
    source_report = views.render_survey_source_report(registry)
    for output, label in ((status, "status"), (source_report, "source report")):
        if "LAND-AISI-001" in output:
            raise SystemExit(f"source-neutral regression: AISI claim entered {label}")
    if "45 / 44" in status or "44 / 45" in status:
        raise SystemExit("source-neutral regression: CSUR denominator changed")
    if "44 / 44" not in status:
        raise SystemExit("source-neutral regression: CSUR status lost its closed 44/44 count")
    print("source-neutral views ok: non-survey claims stay out of CSUR status/report")


if __name__ == "__main__":
    main()
