#!/usr/bin/env python3
"""Validate landscape.yaml: non–Table-1 formalizations outside survey coverage."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
LANDSCAPE = ROOT / "landscape.yaml"
REGISTRY = ROOT / "registry.yaml"

REQUIRED_ENTRY_FIELDS = {
    "id",
    "name",
    "kind",
    "survey_coverage",
    "framework",
    "license",
    "repository",
    "revision",
    "root_import",
    "notes",
}


def fail(message: str) -> None:
    print(f"landscape error: {message}", file=sys.stderr)
    raise SystemExit(1)


def valid_http_url(value: object) -> bool:
    if not isinstance(value, str) or any(character.isspace() for character in value):
        return False
    parsed = urlsplit(value)
    return parsed.scheme in {"http", "https"} and bool(parsed.netloc)


def main() -> None:
    try:
        data = json.loads(LANDSCAPE.read_text(encoding="utf-8"))
        registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(str(error))

    if data.get("schema_version") != 1:
        fail("landscape.yaml must use schema_version 1")
    entries = data.get("entries")
    if not isinstance(entries, list) or not entries:
        fail("landscape entries must be a non-empty list")

    survey_ids = {result["id"] for result in registry["results"]}
    seen_ids: set[str] = set()
    root_import_decls: list[str] = []

    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            fail(f"entry {index} must be an object")
        missing = REQUIRED_ENTRY_FIELDS - entry.keys()
        if missing:
            fail(f"entry {index} missing fields: {sorted(missing)}")
        eid = entry["id"]
        if not isinstance(eid, str) or not eid.startswith("LAND-"):
            fail(f"entry id must start with LAND-: {eid!r}")
        if eid in seen_ids:
            fail(f"duplicate landscape id {eid}")
        seen_ids.add(eid)
        if entry["kind"] != "LANDSCAPE":
            fail(f"{eid} kind must be LANDSCAPE")
        if entry["survey_coverage"] is not None:
            fail(f"{eid} survey_coverage must be null (landscape never counts as survey coverage)")
        if not valid_http_url(entry["repository"]):
            fail(f"{eid} has invalid repository URL")
        if not entry.get("revision") or not entry.get("notes"):
            fail(f"{eid} must record revision and notes")
        if not isinstance(entry["root_import"], bool):
            fail(f"{eid} root_import must be boolean")
        for sid in entry.get("related_survey_ids") or []:
            if sid not in survey_ids:
                fail(f"{eid} related_survey_ids contains unknown {sid}")
        decl = entry.get("atlas_declaration")
        if entry["root_import"]:
            if not decl:
                fail(f"{eid} root_import true requires atlas_declaration")
            root_import_decls.append(decl)

    # Root-import landscape theorems must appear in the public root module text.
    root_lean = (ROOT / "AISafetyAtlas.lean").read_text(encoding="utf-8")
    explain = (ROOT / "AISafetyAtlas" / "Explainability.lean").read_text(encoding="utf-8")
    for decl in root_import_decls:
        # Namespace path: AISafetyAtlas.Explainability.attribution_impossibility
        short = decl.split(".")[-1]
        if short not in explain and decl not in root_lean:
            fail(
                f"root_import declaration {decl} not found in Explainability.lean "
                "or AISafetyAtlas.lean"
            )

    print(
        f"landscape ok: {len(entries)} entries, "
        f"{len(root_import_decls)} root-import landscape theorems"
    )


if __name__ == "__main__":
    main()
