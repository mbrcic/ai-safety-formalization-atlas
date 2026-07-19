#!/usr/bin/env python3
"""Validate the JSON-compatible YAML survey registry without third-party packages."""

from __future__ import annotations

import json
import os
from pathlib import Path
import sys
from urllib.parse import urlsplit


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "registry.yaml"
SEARCH_EVIDENCE = ROOT / "docs/provenance/formalization-search.json"
PROJECT_REPOSITORY = "https://github.com/mbrcic/ai-safety-formalization-atlas"
IN_TREE_VERSION = "IN_TREE"


def fail(message: str) -> None:
    print(f"registry error: {message}", file=sys.stderr)
    raise SystemExit(1)


def valid_http_url(value: object) -> bool:
    if not isinstance(value, str) or any(character.isspace() for character in value):
        return False
    parsed = urlsplit(value)
    return parsed.scheme in {"http", "https"} and bool(parsed.netloc)


BRIDGE_STATUS_VALUES = {"HUMAN_REVIEW", "STATEMENT_REVIEWED", "REVIEWED"}
BRIDGE_REVIEW_FIELDS = {
    "reviewer",
    "date",
    "statement_reviewed",
    "interpretation_reviewed",
    "evidence",
}
CANDIDATE_LEAD_FIELDS = {
    "repository",
    "revision",
    "framework",
    "license",
    "declaration",
    "inspection_state",
    "relationship_review",
    "notes",
}
CANDIDATE_INSPECTION_STATES = {"UNVERIFIED", "SOURCE_INSPECTED", "REPRODUCED"}
CANDIDATE_REVIEW_STATES = {
    "PENDING",
    "EXACT",
    "EQUIVALENT",
    "RELATED",
    "DISTINCT",
    "UNCLEAR",
}


def validate_bridge_review(result_id: str, result: dict) -> None:
    """Enforce the bridge-review lifecycle: HUMAN_REVIEW carries no evidence; any
    graduated status must supply a complete, consistent bridge_review record."""
    status = result["ai_bridge_status"]
    review = result.get("bridge_review")
    if status == "HUMAN_REVIEW":
        if review is not None:
            fail(f"{result_id} is HUMAN_REVIEW and must not carry a bridge_review record")
        return
    if not isinstance(review, dict):
        fail(f"{result_id} bridge status {status} requires a bridge_review record")
    missing = BRIDGE_REVIEW_FIELDS - review.keys()
    if missing:
        fail(f"{result_id} bridge_review missing fields: {sorted(missing)}")
    if not isinstance(review["statement_reviewed"], bool) or not isinstance(
        review["interpretation_reviewed"], bool
    ):
        fail(f"{result_id} bridge_review review flags must be booleans")
    if not review.get("reviewer") or not review.get("date") or not review.get("evidence"):
        fail(f"{result_id} bridge_review must record reviewer, date, and evidence")
    if not review["statement_reviewed"]:
        fail(f"{result_id} graduated bridge status requires statement_reviewed to be true")
    if status == "REVIEWED" and not review["interpretation_reviewed"]:
        fail(f"{result_id} REVIEWED requires interpretation_reviewed to be true")
    if status == "STATEMENT_REVIEWED" and review["interpretation_reviewed"]:
        fail(f"{result_id} STATEMENT_REVIEWED must not claim interpretation_reviewed; use REVIEWED")


def validate_candidate_formalizations(result_id: str, result: dict) -> None:
    """Structured non-coverage leads: manually discovered formalizations that are
    not yet accepted as coverage. They never substitute for a `formalizations` entry."""
    leads = result.get("candidate_formalizations", [])
    if not isinstance(leads, list):
        fail(f"{result_id} candidate_formalizations must be a list")
    for index, lead in enumerate(leads):
        if not isinstance(lead, dict):
            fail(f"{result_id} candidate_formalizations[{index}] must be an object")
        missing = CANDIDATE_LEAD_FIELDS - lead.keys()
        if missing:
            fail(f"{result_id} candidate lead {index} missing fields: {sorted(missing)}")
        if not valid_http_url(lead["repository"]):
            fail(f"{result_id} candidate lead {index} has an invalid repository URL")
        if not lead.get("revision") or not lead.get("declaration") or not lead.get("notes"):
            fail(f"{result_id} candidate lead {index} must record revision, declaration, and notes")
        if lead["inspection_state"] not in CANDIDATE_INSPECTION_STATES:
            fail(f"{result_id} candidate lead {index} has unknown inspection_state {lead['inspection_state']!r}")
        if lead["relationship_review"] not in CANDIDATE_REVIEW_STATES:
            fail(f"{result_id} candidate lead {index} has unknown relationship_review {lead['relationship_review']!r}")


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

    if data.get("schema_version") != 3:
        fail("registry.yaml must use schema version 3")

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
    license_values = set(vocabulary.get("spdx_license", []))
    bridge_status_values = set(vocabulary.get("ai_bridge_status", []))
    if status_values != {"MAPPED", "LEAN_AVAILABLE"}:
        fail("progress_status vocabulary must contain only MAPPED and LEAN_AVAILABLE")
    if bridge_status_values != BRIDGE_STATUS_VALUES:
        fail(
            "ai_bridge_status vocabulary must contain exactly "
            "HUMAN_REVIEW, STATEMENT_REVIEWED, and REVIEWED"
        )
    if not license_values:
        fail("spdx_license vocabulary must not be empty")

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
    required_artifact_declaration_fields = {
        "atlas_declaration",
        "type",
        "source_declarations",
    }

    formalization_count = 0
    reproduced_external_count = 0
    lean_artifact_count = 0
    lean_declaration_names: set[str] = set()
    formalization_keys: set[tuple[str, ...]] = set()
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

    for source_id, source in sources.items():
        if not isinstance(source, dict) or not source.get("citation"):
            fail(f"{source_id} must contain a citation")
        locator = source.get("locator")
        if locator is not None and not valid_http_url(locator):
            fail(f"{source_id} has an invalid locator URL")

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
        if result["ai_bridge_status"] not in bridge_status_values:
            fail(f"{result_id} has unknown ai_bridge_status {result['ai_bridge_status']!r}")
        validate_bridge_review(result_id, result)
        validate_candidate_formalizations(result_id, result)

        search = result["formal_library_search"]
        if set(search.get("searched_corpora", [])) != expected_search_corpora:
            fail(f"{result_id} does not cover all required formal-library corpora")
        if not search.get("query_terms"):
            fail(f"{result_id} has no formal-library search terms")
        if search.get("evidence_file") != "docs/provenance/formalization-search.json":
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
            declarations = artifact.get("declarations")
            if not isinstance(declarations, list) or not declarations:
                fail(f"{result_id} Lean artifact lacks atlas declarations")
            for declaration in declarations:
                missing = required_artifact_declaration_fields - declaration.keys()
                if missing:
                    fail(
                        f"{result_id} Lean artifact declaration missing fields: "
                        f"{sorted(missing)}"
                    )
                if declaration["type"] not in artifact_values:
                    fail(f"{result_id} has unknown Lean artifact type")
                if not declaration["atlas_declaration"]:
                    fail(f"{result_id} has an unnamed Lean artifact declaration")
                if declaration["atlas_declaration"] in lean_declaration_names:
                    fail(
                        f"duplicate Lean artifact declaration: "
                        f"{declaration['atlas_declaration']}"
                    )
                lean_declaration_names.add(declaration["atlas_declaration"])
                if not isinstance(declaration["source_declarations"], list) or not declaration["source_declarations"]:
                    fail(f"{result_id} Lean artifact declaration lacks sources")
            lean_artifact_count += len(declarations)

        if not isinstance(result["formalizations"], list):
            fail(f"{result_id} formalizations must be a list")
        for record in result["formalizations"]:
            missing = required_formalization_fields - record.keys()
            if missing:
                fail(f"{result_id} formalization missing fields: {sorted(missing)}")
            if record["relationship"] not in relationship_values:
                fail(f"{result_id} has unknown relationship")
            if record["license"] not in license_values:
                fail(f"{result_id} has an unknown SPDX license identifier")
            if not valid_http_url(record["repository"]):
                fail(f"{result_id} formalization has an invalid repository URL")
            if not isinstance(record["reproduced"], bool):
                fail(f"{result_id} formalization reproduced flag must be boolean")
            if not all(record[field] for field in ("version", "module", "declaration")):
                fail(f"{result_id} formalization has incomplete provenance")
            if record["repository"] == PROJECT_REPOSITORY:
                if record["version"] != IN_TREE_VERSION:
                    fail(
                        f"{result_id} in-repository formalization must use "
                        f"version {IN_TREE_VERSION}, not a self-referential commit"
                    )
                if record["framework"] != "Lean":
                    fail(f"{result_id} in-repository formalization must use Lean")
                module_path = ROOT / (record["module"].replace(".", "/") + ".lean")
                if not module_path.is_file():
                    fail(
                        f"{result_id} in-repository formalization module is missing: "
                        f"{record['module']}"
                    )
                if record["module"] not in record.get("build_command", ""):
                    fail(
                        f"{result_id} in-repository reproduction command does not "
                        "build its recorded module"
                    )
            elif record["version"] == IN_TREE_VERSION:
                fail(f"{result_id} external formalization cannot use {IN_TREE_VERSION}")
            formalization_key = (
                result_id,
                record["framework"],
                record["repository"],
                record["version"],
                record["module"],
                record["declaration"],
            )
            if formalization_key in formalization_keys:
                fail(f"{result_id} contains a duplicate formalization record")
            formalization_keys.add(formalization_key)
            if record["reproduced"]:
                environment = record.get("build_environment")
                command = record.get("build_command")
                if not environment or not command:
                    fail(
                        f"{result_id} reproduced formalization lacks explicit "
                        "build evidence"
                    )
                command_path = command.split()[0]
                if command_path.startswith("scripts/"):
                    script = ROOT / command_path
                    if not script.is_file() or not os.access(script, os.X_OK):
                        fail(
                            f"{result_id} reproduction command references a missing "
                            "or nonexecutable script"
                        )
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
