#!/usr/bin/env python3
"""Audit objective v0.1 release criteria that can be checked locally."""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        print(f"release audit error: {message}", file=sys.stderr)
        raise SystemExit(1)


def main() -> None:
    required_files = [
        "README.md",
        "LICENSE",
        "STATE.md",
        "registry.yaml",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
        "AISafetyAtlas.lean",
        "AISafetyAtlas/Computability.lean",
        "AISafetyAtlas/SocialChoice.lean",
        "AISafetyAtlas/SocialChoice/Utility.lean",
        "AISafetyAtlas/Upstream/Arrow.lean",
        "AISafetyAtlas/Survey/BrcicYampolskiy/HaltingExample.lean",
        "docs/methodology.md",
        "docs/formalization-status.md",
        "docs/external-formalizations.md",
        "docs/formalization-search.json",
        "docs/formalization-search.md",
        "docs/open-work.md",
        "docs/release-v0.1.md",
        "scripts/update_formalization_search.py",
        ".github/workflows/ci.yml",
    ]
    missing = [path for path in required_files if not (ROOT / path).is_file()]
    require(not missing, f"missing required files: {missing}")

    license_text = (ROOT / "LICENSE").read_text(encoding="utf-8")
    require("Apache License" in license_text and "Version 2.0" in license_text,
            "LICENSE is not Apache-2.0")

    registry = json.loads((ROOT / "registry.yaml").read_text(encoding="utf-8"))
    results = registry["results"]
    formalizations = [record for result in results for record in result["formalizations"]]
    lean_declarations = [
        declaration
        for result in results
        if result["lean_artifact"] is not None
        for declaration in result["lean_artifact"]["atlas_declarations"]
    ]
    reproduced_external = [
        record
        for record in formalizations
        if record["framework"] != "Lean" and record["reproduced"]
    ]
    covered_results = sum(bool(result["formalizations"]) for result in results)
    reviewed_bridges = sum(
        result["ai_bridge_status"] != "HUMAN_REVIEW" for result in results
    )
    expected_search_corpora = {
        "mathlib",
        "isabelle-afp",
        "rocq-undecidability",
        "hol4",
        "hol-light",
        "agda-stdlib",
    }

    require(len(results) == 44, "survey inventory must contain exactly 44 Table 1 rows")
    require(5 <= len(formalizations) <= 10,
            "v0.1 requires approximately 5–10 verified formalization records")
    require(5 <= len(lean_declarations) <= 8,
            "v0.1 requires approximately 5–8 Lean facade or bridge theorems")
    require(reproduced_external, "v0.1 requires a reproduced external formalization")
    require(
        all(
            set(result["formal_library_search"]["searched_corpora"])
            == expected_search_corpora
            for result in results
        ),
        "every survey row must have six-corpus formal-library search evidence",
    )
    require(all(result["ai_bridge_status"] == "HUMAN_REVIEW" for result in results),
            "all unreviewed AI-safety bridges must remain HUMAN_REVIEW")

    release_doc = (ROOT / "docs/release-v0.1.md").read_text(encoding="utf-8")
    require(
        f"| Verified formalization records | {len(formalizations)} records | Passed |"
        in release_doc,
        "release document formalization count has drifted from registry",
    )
    require(
        f"| Lean facade or bridge theorems | {len(lean_declarations)} compiled declarations | Passed |"
        in release_doc,
        "release document Lean declaration count has drifted from registry",
    )
    require(
        f"| Verified survey-row coverage | {covered_results} of {len(results)} results | Explicitly partial |"
        in release_doc,
        "release document verified survey-row coverage has drifted from registry",
    )
    require(
        f"| Reviewed AI-system bridge theorems | {reviewed_bridges} | Explicitly deferred |"
        in release_doc,
        "release document AI-system bridge count has drifted from registry",
    )
    approval_match = re.search(
        r"^- Approval ref: `([0-9a-f]{40})`$", release_doc, re.MULTILINE
    )
    require(approval_match is not None,
            "release document must record a full immutable approval ref")
    approved_ref = approval_match.group(1)
    require("- Publication status: approved for publication" in release_doc,
            "release document must record publication approval")
    require(
        f"| Mario approval | Approved for immutable ref `{approved_ref}` | Passed |"
        in release_doc,
        "release document approval evidence does not match its approval ref",
    )

    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    normalized_readme = " ".join(readme.lower().split())
    require("does not by itself establish" in normalized_readme,
            "mandatory machine-checking disclaimer is missing")
    require(
        f"{covered_results} of {len(results)}" in normalized_readme,
        "README must state current verified survey-row coverage",
    )
    require(
        f"{reviewed_bridges} reviewed ai-system bridge theorems" in normalized_readme,
        "README must state the reviewed AI-system bridge count",
    )

    forbidden = re.compile(r"^\s*(sorry|admit|axiom)\b", re.MULTILINE)
    lean_files = list((ROOT / "AISafetyAtlas").rglob("*.lean")) + [ROOT / "AISafetyAtlas.lean"]
    offenders = [str(path.relative_to(ROOT)) for path in lean_files
                 if forbidden.search(path.read_text(encoding="utf-8"))]
    require(not offenders, f"released Lean files contain incomplete proof tokens: {offenders}")

    print(
        "release audit ok: Apache-2.0, "
        f"{len(results)} survey results, {len(formalizations)} formalizations, "
        f"{len(lean_declarations)} Lean facade or bridge theorems, "
        f"{len(reproduced_external)} reproduced external records, "
        "44 six-corpus searches, worked halting example, disclaimer, "
        f"open-work list, no incomplete proofs, approval {approved_ref[:12]}"
    )


if __name__ == "__main__":
    main()
