#!/usr/bin/env python3
"""Validate the JSON-compatible YAML survey registry without third-party packages."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import sys
from urllib.parse import urlsplit

from validate_current_state import lean_code_without_comments_or_strings


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


def lean_module_name(path: Path) -> str:
    """Return the dotted Lean module name for a repository-relative source."""
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def local_imports(source: str, local_modules: set[str]) -> set[str]:
    """Read local imports without treating external packages as atlas modules."""
    source = lean_code_without_comments_or_strings(source)
    imports: set[str] = set()
    for match in re.finditer(r"^\s*(?:public\s+)?import\s+(.+)$", source, re.M):
        imports.update(
            token for token in match.group(1).split() if token in local_modules
        )
    return imports


def root_import_closure() -> tuple[set[str], set[str]]:
    """Compute the actual local module closure of the public root facade.

    The result-level ``root_import`` flag is published metadata, so it must be
    checked against the same import graph that determines whether a declaration
    is reachable from ``AISafetyAtlas``. Direct-import membership is not enough:
    a facade may re-export a nested module through an intermediate import.
    """
    sources = {
        lean_module_name(path): path
        for path in (ROOT / "AISafetyAtlas").rglob("*.lean")
    }
    root = ROOT / "AISafetyAtlas.lean"
    sources["AISafetyAtlas"] = root
    modules = set(sources)
    graph = {
        module: local_imports(path.read_text(encoding="utf-8"), modules)
        for module, path in sources.items()
    }
    closure: set[str] = set()
    pending = list(graph["AISafetyAtlas"])
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        closure.add(module)
        pending.extend(graph.get(module, set()) - closure)
    return modules, closure


def normalize_module_name(value: str) -> str:
    """Accept the historical slash/``.lean`` spelling as a module name."""
    return value.removesuffix(".lean").replace("/", ".")


SOURCE_ROLES = {"directory", "work"}
SCOPE_DELTA_FIELDS = {"summary", "evidence"}
NOVELTY_CHECK_ID = re.compile(r"NC-\d{3}")
NOVELTY_CHECK_FIELDS = {
    "id",
    "claim",
    "asserted_in",
    "searched_on",
    "searched_by",
    "corpora",
    "method",
    "found",
    "scope_limits",
}
GRADED_RELATIONSHIPS = {"EXACT", "EQUIVALENT", "RELATED"}
ISO_DATE = re.compile(r"\d{4}-\d{2}-\d{2}")
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

    # One ledger, two kinds of row. A claim row states something a source
    # asserted; an artifact row records a formalization that stands on its own.
    # Closure is a property of the catalogued source, not of the file: the BY
    # block stays contiguous and complete, and everything else is open.
    expected_count = survey.get("expected_result_count")
    if not isinstance(expected_count, int) or expected_count < 1:
        fail("survey.expected_result_count must be a positive integer")
    if any(not isinstance(result, dict) for result in results):
        fail("every result must be an object")
    actual_ids = [result.get("id") for result in results]
    if len(set(actual_ids)) != len(actual_ids):
        fail("result IDs must be unique")
    survey_ids = [i for i in actual_ids if i and i.startswith("BY-")]
    expected_ids = [f"BY-{number:03d}" for number in range(1, expected_count + 1)]
    if survey_ids != expected_ids:
        fail(
            f"survey rows must be contiguous BY-001..BY-{expected_count:03d} in order; "
            "the catalogued survey is closed"
        )
    bad = [i for i in actual_ids if not re.fullmatch(r"(BY-\d{3}|LAND-[A-Z0-9-]+)", i or "")]
    if bad:
        fail(f"result ids must be BY-### or LAND-*: {bad}")

    relationship_values = set(vocabulary.get("relationship", []))
    artifact_values = set(vocabulary.get("lean_artifact_type", []))
    license_values = set(vocabulary.get("spdx_license", []))
    bridge_status_values = set(vocabulary.get("ai_bridge_status", []))
    if bridge_status_values != BRIDGE_STATUS_VALUES:
        fail(
            "ai_bridge_status vocabulary must contain exactly "
            "HUMAN_REVIEW, STATEMENT_REVIEWED, and REVIEWED"
        )
    if not license_values:
        fail("spdx_license vocabulary must not be empty")

    # Mathematical area, the axis a contributor navigates by. A controlled
    # vocabulary rather than free text: an unchecked tag fragments the by-area
    # view silently, and a view nobody can trust is a view nobody reads.
    tag_values = vocabulary.get("tag")
    if not isinstance(tag_values, list) or not tag_values:
        fail("tag vocabulary must be a non-empty list")
    if sorted(tag_values) != list(tag_values):
        fail("tag vocabulary must be sorted")
    if len(set(tag_values)) != len(tag_values):
        fail("tag vocabulary must not repeat a tag")
    tag_values = set(tag_values)

    universal_result_fields = {"id", "name", "tags", "notes", "formalizations", "lean_artifact"}
    required_result_fields = {
        "id",
        "name",
        "paper_reference",
        "survey_proof_assessment",
        "informal_claim",
        "original_source_refs",
        "tags",
        "formalizations",
        "lean_artifact",
        "ai_safety_relevance",
        "ai_bridge_status",
        "notes",
    }
    required_formalization_fields = {
        "framework",
        "repository",
        "version",
        "reproduced",
        "license",
    }
    claim_formalization_fields = required_formalization_fields | {
        "module",
        "declaration",
        "relationship",
    }
    required_artifact_declaration_fields = {
        "atlas_declaration",
        "type",
        "source_declarations",
    }

    formalization_count = 0
    claim_formalization_count = 0
    reproduced_external_count = 0
    lean_row_count = 0
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
    if search_evidence.get("schema_version") != 3:
        fail("formalization-search.json must use schema version 3")
    if set(search_evidence.get("corpora", {})) != expected_search_corpora:
        fail("formalization-search.json corpus set does not match registry policy")
    # The six-corpus sweep is one profile — a completeness artifact for one
    # catalogued source — not a standing obligation every new row inherits.
    if search_evidence.get("profile") != "baseline-catalogue":
        fail(
            "formalization-search.json must declare profile 'baseline-catalogue'; "
            "the sweep is scoped to one catalogued source, not to the workbench"
        )
    for field in ("profile_obligation", "novelty_check_obligation"):
        if not isinstance(search_evidence.get(field), str) or not search_evidence[field].strip():
            fail(f"formalization-search.json must state {field}")
    evidence_results = search_evidence.get("results")
    if not isinstance(evidence_results, dict) or set(evidence_results) != set(expected_ids):
        fail(
            "formalization-search.json must cover exactly the catalogued survey rows; "
            "the baseline-catalogue profile is scoped to that source, not to the ledger"
        )

    # A claim that something does not exist is the one claim a reader cannot
    # check for themselves, so it carries what was searched, where, when, and
    # what the search did not cover. Recording one is optional; recording one
    # incompletely is not.
    # A declaration name is verified by the generated
    # AISafetyAtlas/Examples/Registry.lean, which #checks every atlas
    # declaration in the ledger, and by the Lean build, which elaborates it.
    # The result-level root_import flag is checked later against the actual
    # module import closure.

    novelty_checks = search_evidence.get("novelty_checks")
    if not isinstance(novelty_checks, list):
        fail("formalization-search.json must carry a novelty_checks list")
    seen_checks: set[str] = set()
    for index, check in enumerate(novelty_checks):
        if not isinstance(check, dict):
            fail(f"novelty check {index} must be an object")
        missing = NOVELTY_CHECK_FIELDS - check.keys()
        if missing:
            fail(f"novelty check {index} missing fields: {sorted(missing)}")
        cid = check["id"]
        if not isinstance(cid, str) or not NOVELTY_CHECK_ID.fullmatch(cid):
            fail(f"novelty check id must match NC-###: {cid!r}")
        if cid in seen_checks:
            fail(f"duplicate novelty check id {cid}")
        seen_checks.add(cid)
        for field in ("claim", "method", "found", "scope_limits", "searched_by"):
            if not isinstance(check[field], str) or not check[field].strip():
                fail(f"{cid} must record a non-empty {field}")
        if not ISO_DATE.fullmatch(str(check["searched_on"])):
            fail(f"{cid} has an invalid searched_on date {check['searched_on']!r}")
        if not isinstance(check["asserted_in"], list) or not check["asserted_in"]:
            fail(f"{cid} must name where the claim is asserted")
        corpora = check["corpora"]
        if not isinstance(corpora, list) or not corpora:
            fail(f"{cid} must name at least one searched corpus")
        unknown = sorted(set(corpora) - set(search_evidence["corpora"]))
        if unknown:
            fail(f"{cid} names corpora with no pinned revision on record: {unknown}")

    for source_id, source in sources.items():
        if not isinstance(source, dict) or not source.get("citation"):
            fail(f"{source_id} must contain a citation")
        locator = source.get("locator")
        if locator is not None and not valid_http_url(locator):
            fail(f"{source_id} has an invalid locator URL")
        role = source.get("role")
        if role not in SOURCE_ROLES:
            fail(
                f"{source_id} has unknown role {role!r}; "
                f"expected one of {sorted(SOURCE_ROLES)}"
            )
        # A directory is a curated map that hands work to others; it enumerates
        # pointers and has no statement of its own. A work is a single result
        # with a statement and a proof — the only thing a grade can compare to.
        # A living directory (a web page, not a DOI-fixed publication) is
        # rewritten without notice, so what we read must carry a snapshot date.
        living = role == "directory" and (locator is None or "doi.org" not in locator)
        retrieved = source.get("retrieved")
        if living and (
            not isinstance(retrieved, str) or not ISO_DATE.fullmatch(retrieved)
        ):
            fail(
                f"{source_id} is a living directory and must record a `retrieved` "
                "ISO date; a curated list is rewritten and its snapshot must be dated"
            )
        if retrieved is not None and not ISO_DATE.fullmatch(str(retrieved)):
            fail(f"{source_id} has an invalid `retrieved` date {retrieved!r}")

    directories = {
        source_id
        for source_id, source in sources.items()
        if source.get("role") == "directory"
    }

    local_modules, root_closure = root_import_closure()

    for result in results:
        result_id = result.get("id", "<missing>")
        is_claim = "informal_claim" in result
        is_survey_row = result_id in set(expected_ids)
        needed = required_result_fields if is_claim else universal_result_fields
        if is_survey_row:
            needed = needed | {"formal_library_search"}
        missing = needed - result.keys()
        if missing:
            fail(f"{result_id} missing fields: {sorted(missing)}")
        if not isinstance(result["name"], str) or not result["name"].strip():
            fail(f"{result_id} must have a name")
        if not isinstance(result["notes"], str) or not result["notes"].strip():
            fail(f"{result_id} must have non-empty notes")
        if is_claim and (
            not isinstance(result["informal_claim"], str)
            or not result["informal_claim"].strip()
        ):
            fail(f"{result_id} must have an informal claim")
        if not is_claim:
            stray = {"ai_bridge_status", "bridge_review", "candidate_formalizations"} & result.keys()
            if stray:
                fail(
                    f"{result_id} is an artifact row and must not carry claim fields: "
                    f"{sorted(stray)}"
                )
        if "root_import" in result and not isinstance(result["root_import"], bool):
            fail(f"{result_id} root_import must be boolean")
        if result.get("root_import") and result["lean_artifact"] is None:
            fail(f"{result_id} root_import requires an atlas declaration")
        if is_claim and result["ai_bridge_status"] not in bridge_status_values:
            fail(f"{result_id} has unknown ai_bridge_status {result['ai_bridge_status']!r}")
        tags = result["tags"]
        if not isinstance(tags, list) or not tags:
            fail(f"{result_id} must carry at least one tag")
        if any(not isinstance(tag, str) or not tag.strip() for tag in tags):
            fail(f"{result_id} tags must be non-empty strings")
        unknown_tags = [tag for tag in tags if tag not in tag_values]
        if unknown_tags:
            fail(f"{result_id} has tags outside the vocabulary: {sorted(unknown_tags)}")
        if len(set(tags)) != len(tags):
            fail(f"{result_id} repeats a tag")
        if is_claim:
            validate_bridge_review(result_id, result)
        if is_claim:
            validate_candidate_formalizations(result_id, result)

        source_refs = result.get("original_source_refs", [])
        if not isinstance(source_refs, list) or not all(
            isinstance(source_id, str) and source_id for source_id in source_refs
        ):
            fail(f"{result_id} original_source_refs must be a list of non-empty strings")
        related_ids = result.get("related_result_ids", [])
        if not isinstance(related_ids, list) or not all(
            isinstance(related, str) and related for related in related_ids
        ):
            fail(f"{result_id} related_result_ids must be a list of non-empty strings")
        for source_id in source_refs:
            if source_id not in sources:
                fail(f"{result_id} references missing source {source_id}")
        for related in related_ids:
            if related not in {r["id"] for r in results}:
                fail(f"{result_id} related_result_ids names unknown result {related}")
        if not isinstance(result["formalizations"], list):
            fail(f"{result_id} formalizations must be a list")
        for record in result["formalizations"]:
            if not isinstance(record, dict):
                fail(f"{result_id} formalization records must be objects")
        if not is_claim:
            if not result["formalizations"]:
                fail(
                    f"{result_id} records no claim, so it must record at least one "
                    "formalization — otherwise it asserts nothing at all"
                )
            if not result["id"].startswith("LAND-"):
                fail(f"{result_id} has no informal_claim but does not use the LAND- prefix")
        elif result["id"].startswith("LAND-") and is_survey_row:
            fail(f"{result_id} cannot be both a survey row and a LAND- row")

        if result_id in expected_ids:
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


        # `RELATED` is scoped capital, not a failed match — but a reader meeting
        # it on the public API, or on a row whose bridge has been reviewed, is
        # entitled to know what it does not cover. Internal helper material that
        # nothing public exposes stays lighter: the trigger is reach, not grade.
        raw_artifact = result.get("lean_artifact")
        if raw_artifact is not None and not isinstance(raw_artifact, dict):
            fail(f"{result_id} lean_artifact must be an object or null")
        artifact = raw_artifact or {}
        raw_declarations = artifact.get("declarations", [])
        declaration_types: set[str] = set()
        if isinstance(raw_declarations, list):
            declaration_types = {
                d.get("type")
                for d in raw_declarations
                if isinstance(d, dict) and isinstance(d.get("type"), str)
            }
        interpretation_affecting = (
            result.get("ai_bridge_status", "HUMAN_REVIEW") != "HUMAN_REVIEW"
            or "BRIDGE" in declaration_types
        )
        for record in result.get("formalizations") or []:
            if record.get("relationship") != "RELATED" or not source_refs:
                continue
            module = normalize_module_name(
                record.get("atlas_module") or record.get("module") or ""
            )
            public = any(
                module == name or module.startswith(name + ".")
                for name in root_closure
            )
            delta = record.get("scope_delta")
            if not (public or interpretation_affecting):
                continue
            declaration = record.get("declaration", "<unnamed>")
            if not isinstance(delta, dict):
                fail(
                    f"{result_id} RELATED record {declaration} is public or "
                    "interpretation-affecting and must carry a scope_delta"
                )
            missing = SCOPE_DELTA_FIELDS - delta.keys()
            if missing:
                fail(f"{result_id} scope_delta missing fields: {sorted(missing)}")
            if not str(delta["summary"]).strip():
                fail(f"{result_id} scope_delta needs a non-empty summary")
            raw_evidence = str(delta["evidence"])
            if raw_evidence.startswith("/") or ".." in Path(raw_evidence).parts:
                fail(
                    f"{result_id} scope_delta evidence must be a repository-relative "
                    f"path inside the tree: {raw_evidence}"
                )
            evidence = ROOT / raw_evidence
            if not evidence.is_file():
                fail(
                    f"{result_id} scope_delta evidence does not exist: "
                    f"{delta['evidence']}"
                )

        # A directory may be cited as provenance — recording where a claim came
        # from is honest. It may not be the thing a grade compares against: a
        # statement-match grade relates two statements, and a curated list has
        # none. A graded row must therefore name at least one work source.
        graded = any(
            isinstance(record, dict)
            and isinstance(record.get("relationship"), str)
            and record.get("relationship") in GRADED_RELATIONSHIPS
            for record in (result.get("formalizations") or [])
        )
        if graded:
            refs = source_refs
            if refs and not any(source_id not in directories for source_id in refs):
                fail(
                    f"{result_id} carries a statement-match grade but cites only "
                    "directory sources; grade against the work that states the "
                    "theorem, not the list that points at it"
                )

        artifact = result["lean_artifact"]
        if artifact is not None:
            declarations = artifact.get("declarations")
            if not isinstance(declarations, list) or not declarations:
                fail(f"{result_id} Lean artifact lacks atlas declarations")
            row_declaration_names: set[str] = set()
            for declaration in declarations:
                if not isinstance(declaration, dict):
                    fail(f"{result_id} Lean artifact declarations must be objects")
                missing = required_artifact_declaration_fields - declaration.keys()
                if missing:
                    fail(
                        f"{result_id} Lean artifact declaration missing fields: "
                        f"{sorted(missing)}"
                    )
                if (
                    not isinstance(declaration["type"], str)
                    or declaration["type"] not in artifact_values
                ):
                    fail(f"{result_id} has unknown Lean artifact type")
                if not isinstance(declaration["atlas_declaration"], str) or not declaration[
                    "atlas_declaration"
                ].strip():
                    fail(f"{result_id} has an unnamed Lean artifact declaration")
                if declaration["atlas_declaration"] in row_declaration_names:
                    fail(
                        f"duplicate Lean artifact declaration within {result_id}: "
                        f"{declaration['atlas_declaration']}"
                    )
                row_declaration_names.add(declaration["atlas_declaration"])
                lean_declaration_names.add(declaration["atlas_declaration"])
                if not isinstance(declaration["source_declarations"], list):
                    fail(
                        f"{result_id} Lean artifact declaration source_declarations "
                        "must be a list"
                    )
                if any(
                    not isinstance(source, str) or not source.strip()
                    for source in declaration["source_declarations"]
                ):
                    fail(
                        f"{result_id} Lean artifact declaration source_declarations "
                        "must contain non-empty strings"
                    )
                if declaration["type"] != "NEW_PROOF" and not declaration["source_declarations"]:
                    fail(f"{result_id} Lean artifact declaration lacks sources")
            lean_row_count += 1

        for record in result["formalizations"]:
            required = (
                claim_formalization_fields if is_claim else required_formalization_fields
            )
            missing = required - record.keys()
            if missing:
                fail(f"{result_id} formalization missing fields: {sorted(missing)}")
            if not isinstance(record["framework"], str) or not record["framework"].strip():
                fail(f"{result_id} formalization framework must be a non-empty string")
            if not isinstance(record["version"], str) or not record["version"].strip():
                fail(f"{result_id} formalization version must be a non-empty string")
            for optional_field in ("module", "atlas_module", "declaration"):
                if optional_field in record and (
                    not isinstance(record[optional_field], str)
                    or not record[optional_field].strip()
                ):
                    fail(
                        f"{result_id} formalization {optional_field} must be a "
                        "non-empty string when present"
                    )
            if "modules" in record:
                modules = record["modules"]
                if (
                    not isinstance(modules, list)
                    or not modules
                    or any(
                        not isinstance(module, str) or not module.strip()
                        for module in modules
                    )
                ):
                    fail(
                        f"{result_id} formalization modules must be a non-empty list "
                        "of non-empty strings"
                    )
                if "module" in record:
                    fail(f"{result_id} formalization must use module or modules, not both")
            if "upstream_module" in record:
                fail(
                    f"{result_id} uses deprecated upstream_module; use module for "
                    "the referenced repository and atlas_module for the local atlas"
                )
            if "atlas_module" in record:
                atlas_module = normalize_module_name(record["atlas_module"])
                if atlas_module not in local_modules:
                    fail(
                        f"{result_id} atlas_module does not name a local Lean module: "
                        f"{record['atlas_module']}"
                    )
            if "relationship" in record and not isinstance(record["relationship"], str):
                fail(f"{result_id} formalization relationship must be a string")
            if "relationship" in record and record["relationship"] not in relationship_values:
                fail(f"{result_id} has unknown relationship")
            if (
                not isinstance(record["license"], str)
                or record["license"] not in license_values
            ):
                fail(f"{result_id} has an unknown SPDX license identifier")
            if not valid_http_url(record["repository"]):
                fail(f"{result_id} formalization has an invalid repository URL")
            if not isinstance(record["reproduced"], bool):
                fail(f"{result_id} formalization reproduced flag must be boolean")
            provenance_fields = (
                ("version", "module", "declaration") if is_claim else ("version",)
            )
            if not all(record.get(field) for field in provenance_fields):
                fail(f"{result_id} formalization has incomplete provenance")
            if record["repository"] == PROJECT_REPOSITORY:
                if not record.get("module") or not record.get("declaration"):
                    fail(
                        f"{result_id} in-repository formalization must record "
                        "module and declaration"
                    )
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
            if (
                not is_claim
                and artifact is not None
                and record["framework"] == "Lean"
                and record["repository"] != PROJECT_REPOSITORY
                and "atlas_module" not in record
            ):
                fail(
                    f"{result_id} external Lean artifact must record atlas_module "
                    "separately from the referenced repository module"
                )
            formalization_key = (
                result_id,
                str(record["framework"]),
                str(record["repository"]),
                str(record["version"]),
                str(record.get("module", "")),
                str(record.get("modules", "")),
                str(record.get("declaration", "")),
            )
            if formalization_key in formalization_keys:
                fail(f"{result_id} contains a duplicate formalization record")
            formalization_keys.add(formalization_key)
            if record["reproduced"]:
                environment = record.get("build_environment")
                command = record.get("build_command")
                if not isinstance(environment, str) or not environment.strip():
                    fail(
                        f"{result_id} reproduced formalization build_environment "
                        "must be a non-empty string"
                    )
                if not isinstance(command, str) or not command.strip():
                    fail(
                        f"{result_id} reproduced formalization build_command "
                        "must be a non-empty string"
                    )
                command_path = command.split()[0]
                if command_path.startswith("scripts/"):
                    script = ROOT / command_path
                    if not script.is_file() or not os.access(script, os.X_OK):
                        fail(
                            f"{result_id} reproduction command references a missing "
                            "or nonexecutable script"
                        )
            else:
                for evidence_field in ("build_environment", "build_command"):
                    if evidence_field in record and not isinstance(
                        record[evidence_field], str
                    ):
                        fail(
                            f"{result_id} formalization {evidence_field} must be a "
                            "string when present"
                        )
            formalization_count += 1
            if is_claim:
                claim_formalization_count += 1
            if record["framework"] != "Lean" and record["reproduced"]:
                reproduced_external_count += 1

        if "root_import" in result and result["lean_artifact"] is not None:
            atlas_modules = set()
            for record in result["formalizations"]:
                if record.get("repository") == PROJECT_REPOSITORY and record.get("module"):
                    atlas_modules.add(normalize_module_name(record["module"]))
                elif record.get("atlas_module"):
                    atlas_modules.add(normalize_module_name(record["atlas_module"]))
            if not atlas_modules:
                fail(f"{result_id} root_import requires a recorded atlas module")
            expected_root_import = any(module in root_closure for module in atlas_modules)
            if result["root_import"] != expected_root_import:
                fail(
                    f"{result_id} root_import={result['root_import']} disagrees with "
                    f"the public root import closure ({expected_root_import})"
                )

    claims = sum(1 for r in results if "informal_claim" in r)
    print(
        "registry ok: "
        f"{len(results)} results ({claims} claims + {len(results) - claims} artifacts), "
        f"{len(sources)} sources, "
        f"{formalization_count} formalization records ({claim_formalization_count} on claim rows), "
        f"{lean_row_count} rows with atlas Lean, "
        f"{len(lean_declaration_names)} unique atlas declarations, "
        f"{reproduced_external_count} reproduced external records, "
        f"{len(expected_ids)} synchronized six-corpus searches"
    )


if __name__ == "__main__":
    main()
