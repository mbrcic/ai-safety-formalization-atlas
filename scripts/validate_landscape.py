#!/usr/bin/env python3
"""Validate landscape.yaml: non–Table-1 formalizations outside survey coverage."""

from __future__ import annotations

import json
import re
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
    "tags",
}
PUBLIC_IMPORT_RE = re.compile(r"^public import ([A-Za-z0-9_'.]+)\s*$")


def fail(message: str) -> None:
    print(f"landscape error: {message}", file=sys.stderr)
    raise SystemExit(1)


def valid_http_url(value: object) -> bool:
    if not isinstance(value, str) or any(character.isspace() for character in value):
        return False
    parsed = urlsplit(value)
    return parsed.scheme in {"http", "https"} and bool(parsed.netloc)


def public_surface_text() -> str:
    """Return the text of every module re-exported from the package root."""
    root_module = ROOT / "AISafetyAtlas.lean"
    pending = ["AISafetyAtlas"]
    seen: set[str] = set()
    sources: list[str] = []
    while pending:
        module = pending.pop(0)
        if module in seen:
            continue
        seen.add(module)
        path = root_module if module == "AISafetyAtlas" else (
            ROOT / (module.replace(".", "/") + ".lean")
        )
        if not path.is_file():
            fail(f"public atlas import missing module: {path.relative_to(ROOT)}")
        source = path.read_text(encoding="utf-8")
        sources.append(source)
        pending.extend(
            match.group(1)
            for line in source.splitlines()
            if (match := PUBLIC_IMPORT_RE.match(line))
            if match.group(1).startswith("AISafetyAtlas")
        )
    return "\n".join(sources)


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
    # One shared tag vocabulary across both ledgers, so the by-area view is a
    # single surface rather than two that drift apart.
    tag_values = set(registry.get("vocabulary", {}).get("tag") or [])
    if not tag_values:
        fail("registry vocabulary.tag must be populated before landscape tags validate")
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
        tags = entry["tags"]
        if not isinstance(tags, list) or not tags:
            fail(f"{eid} must carry at least one tag")
        unknown_tags = [tag for tag in tags if tag not in tag_values]
        if unknown_tags:
            fail(f"{eid} has tags outside the vocabulary: {sorted(unknown_tags)}")
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

    # Root-import landscape theorems must occur anywhere in the transitive
    # public import surface, including nested facade modules.
    surface_text = public_surface_text()
    for decl in root_import_decls:
        short = decl.split(".")[-1]
        if short not in surface_text and decl not in surface_text:
            fail(
                f"root_import declaration {decl} not found in AISafetyAtlas.lean "
                "or its transitive public imports"
            )

    print(
        f"landscape ok: {len(entries)} entries, "
        f"{len(root_import_decls)} root-import landscape theorems"
    )


if __name__ == "__main__":
    main()
