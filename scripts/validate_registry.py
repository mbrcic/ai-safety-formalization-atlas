#!/usr/bin/env python3
"""Validate the JSON-compatible YAML survey registry without third-party packages."""

from __future__ import annotations

import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "registry.yaml"
SEARCH_EVIDENCE = ROOT / "docs/formalization-search.json"


def fail(message: str) -> None:
    print(f"registry error: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    try:
        data = json.loads(REGISTRY.read_text(encoding="utf-8"))
        search_evidence = json.loads(SEARCH_EVIDENCE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(str(error))

    survey = data.get("survey", {})
    results = data.get("results")
    sources = data.get("source_catalog")
    vocabulary = data.get("vocabulary", {})

    if not isinstance(results, list):
        fail("results must be a list")
    if not isinstance(sources, dict):
        fail("source_catalog must be an object")

    expected_count = survey.get("expected_result_count")
    if len(results) != expected_count:
        fail(f"expected {expected_count} results, found {len(results)}")

    expected_ids = [f"BY-{number:03d}" for number in range(1, expected_count + 1)]
    actual_ids = [result.get("id") for result in results]
    if actual_ids != expected_ids:
        fail("result IDs must be unique, ordered, and contiguous from BY-001")

    status_values = set(vocabulary.get("progress_status", []))
    relationship_values = set(vocabulary.get("relationship", []))
    artifact_values = set(vocabulary.get("lean_artifact_type", []))
    if status_values != {"MAPPED", "LEAN_AVAILABLE"}:
        fail("progress_status vocabulary must contain only MAPPED and LEAN_AVAILABLE")

    required_result_fields = {
        "id",
        "name",
        "paper_reference",
        "mechanism_category",
        "domain_category",
        "survey_proof_assessment",
        "informal_claim",
        "formal_library_search",
        "original_source_refs",
        "formalizations",
        "lean_artifact",
        "status",
        "ai_safety_relevance",
        "ai_bridge_status",
        "notes",
    }
    required_formalization_fields = {
        "framework",
        "repository",
        "version",
        "module",
        "declaration",
        "relationship",
        "reproduced",
        "license",
    }

    formalization_count = 0
    reproduced_external_count = 0
    lean_artifact_count = 0
    expected_search_corpora = {
        "mathlib",
        "isabelle-afp",
        "rocq-undecidability",
        "hol4",
        "hol-light",
        "agda-stdlib",
    }
    if search_evidence.get("schema_version") != 2:
        fail("formalization-search.json must use schema version 2")
    if set(search_evidence.get("corpora", {})) != expected_search_corpora:
        fail("formalization-search.json corpus set does not match registry policy")
    evidence_results = search_evidence.get("results")
    if not isinstance(evidence_results, dict) or set(evidence_results) != set(actual_ids):
        fail("formalization-search.json result IDs do not match registry")

    for result in results:
        result_id = result.get("id", "<missing>")
        missing = required_result_fields - result.keys()
        if missing:
            fail(f"{result_id} missing fields: {sorted(missing)}")
        if not result["name"] or not result["informal_claim"]:
            fail(f"{result_id} must have a name and informal claim")
        if result["status"] not in status_values:
            fail(f"{result_id} has unknown status {result['status']!r}")
        expected_status = (
            "LEAN_AVAILABLE" if result["lean_artifact"] is not None else "MAPPED"
        )
        if result["status"] != expected_status:
            fail(
                f"{result_id} status must be {expected_status} for its Lean artifact state"
            )
        if result["ai_bridge_status"] != "HUMAN_REVIEW":
            fail(f"{result_id} bridge status must remain HUMAN_REVIEW for v0.1")

        search = result["formal_library_search"]
        if set(search.get("searched_corpora", [])) != expected_search_corpora:
            fail(f"{result_id} does not cover all required formal-library corpora")
        if not search.get("query_terms"):
            fail(f"{result_id} has no formal-library search terms")
        if search.get("evidence_file") != "docs/formalization-search.json":
            fail(f"{result_id} points to unexpected search evidence")

        result_evidence = evidence_results[result_id]
        queries = search["query_terms"]
        if result_evidence.get("queries") != queries:
            fail(f"{result_id} query terms have drifted from search evidence")
        candidate_hits = result_evidence.get("candidate_hits")
        if not isinstance(candidate_hits, dict) or set(candidate_hits) != expected_search_corpora:
            fail(f"{result_id} search evidence has an invalid corpus set")
        candidate_corpora = {
            corpus for corpus, hit in candidate_hits.items() if hit.get("hit_count", 0)
        }
        if set(search.get("candidate_corpora", [])) != candidate_corpora:
            fail(f"{result_id} candidate corpora have drifted from search evidence")
        for corpus, hit in candidate_hits.items():
            counts = hit.get("query_hit_counts")
            if not isinstance(counts, dict) or list(counts) != queries:
                fail(f"{result_id}/{corpus} lacks ordered per-query hit counts")
            expected_matches = [query for query in queries if counts[query] > 0]
            if hit.get("matched_queries") != expected_matches:
                fail(f"{result_id}/{corpus} matched-query summary is inconsistent")
            paths = hit.get("paths")
            hit_count = hit.get("hit_count")
            if not isinstance(paths, list) or not isinstance(hit_count, int):
                fail(f"{result_id}/{corpus} has invalid hit evidence")
            if hit_count < len(paths) or len(paths) > 12:
                fail(f"{result_id}/{corpus} path sample is inconsistent")

        for source_id in result["original_source_refs"]:
            if source_id not in sources:
                fail(f"{result_id} references missing source {source_id}")

        artifact = result["lean_artifact"]
        if artifact is not None:
            if artifact.get("type") not in artifact_values:
                fail(f"{result_id} has unknown Lean artifact type")
            if not artifact.get("atlas_declarations"):
                fail(f"{result_id} Lean artifact lacks atlas declarations")
            lean_artifact_count += len(artifact["atlas_declarations"])

        if not isinstance(result["formalizations"], list):
            fail(f"{result_id} formalizations must be a list")
        for record in result["formalizations"]:
            missing = required_formalization_fields - record.keys()
            if missing:
                fail(f"{result_id} formalization missing fields: {sorted(missing)}")
            if record["relationship"] not in relationship_values:
                fail(f"{result_id} has unknown relationship")
            formalization_count += 1
            if record["framework"] != "Lean" and record["reproduced"]:
                reproduced_external_count += 1

    print(
        "registry ok: "
        f"{len(results)} results, {len(sources)} sources, "
        f"{formalization_count} formalizations, "
        f"{lean_artifact_count} Lean artifacts, "
        f"{reproduced_external_count} reproduced external records, "
        f"{len(results)} synchronized six-corpus searches"
    )


if __name__ == "__main__":
    main()
