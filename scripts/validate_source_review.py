#!/usr/bin/env python3
"""Validate the generated, complete source metadata and rights audit."""

from __future__ import annotations

from datetime import date, datetime
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any, NoReturn, cast
from urllib.parse import urlsplit


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "registry.yaml"
REVIEW = ROOT / "docs/provenance/source-review.json"
DISPOSITIONS = ROOT / "docs/provenance/source-review-dispositions.json"

sys.path.insert(0, str(ROOT / "scripts"))
from source_review.findings import (  # noqa: E402
    actionable_findings,
    compute_finding_fingerprint,
)

SCHEMA_VERSION = 4
METADATA_FIELDS = (
    "identifier",
    "title",
    "authors",
    "date",
    "venue",
    "volume_issue",
    "pages",
    "locator",
)
OUTCOMES = {
    "MATCH",
    "NOT_APPLICABLE",
    "POSSIBLE_CONFLICT",
    "MISSING_IN_CATALOGUE",
    "MISSING_IN_SOURCE",
    "UNAVAILABLE",
}
REVIEW_OUTCOMES = OUTCOMES - {"MATCH", "NOT_APPLICABLE"}
RIGHTS_OUTCOMES = {
    "RIGHTS_RECORDED",
    "NO_EXPLICIT_RIGHTS",
    "RIGHTS_UNAVAILABLE",
}
LOOKUP_STATUSES = {"OK", "MISSING_LOCATOR", "HTTP_ERROR", "PARSE_ERROR"}
RECORD_STATUSES = {"NO_AUTOMATED_FOLLOWUP", "AUTOMATED_CLEAR", "NEEDS_HUMAN", "LOOKUP_FAILED"}
DISPOSITION_STATUSES = {"REVIEWED_NO_CHANGE"}
PROVIDERS = {"arxiv", "crossref", "html", "none"}
SHA256 = re.compile(r"[0-9a-f]{64}")
ISO_DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


def fail(message: str) -> NoReturn:
    print(f"source review error: {message}", file=sys.stderr)
    raise SystemExit(1)


def mapping(value: object, message: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(message)
    return cast("dict[str, Any]", value)


def text(value: object, message: str, *, allow_empty: bool = False) -> str:
    if not isinstance(value, str) or (not allow_empty and not value.strip()):
        fail(message)
    return value


def http_url(value: object, message: str, *, allow_empty: bool = False) -> str:
    value = text(value, message, allow_empty=allow_empty)
    if not value and allow_empty:
        return value
    parsed = urlsplit(value)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        fail(message)
    return value


def utc_timestamp(value: object, message: str) -> str:
    value = text(value, message)
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        fail(message)
    if parsed.tzinfo is None:
        fail(message)
    return value


def fingerprint(value: object) -> str:
    encoded = json.dumps(value, ensure_ascii=False, sort_keys=True).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def work_sources(registry: dict[str, Any]) -> dict[str, dict[str, Any]]:
    catalogue = mapping(
        registry.get("source_catalog"), "registry.yaml source_catalog must be an object"
    )
    return {
        source_id: source
        for source_id, source in catalogue.items()
        if isinstance(source, dict) and source.get("role") == "work"
    }


def source_input_fingerprint(source: dict[str, Any]) -> str:
    return fingerprint({"citation": source["citation"], "locator": source.get("locator")})


def expected_status(
    lookup_status: str,
    comparisons: list[dict[str, Any]],
    rights: dict[str, Any],
    related_dois: list[dict[str, Any]],
) -> str:
    if lookup_status in {"HTTP_ERROR", "PARSE_ERROR"}:
        return "LOOKUP_FAILED"
    if any(comparison["outcome"] in REVIEW_OUTCOMES for comparison in comparisons):
        return "NEEDS_HUMAN"
    if rights["outcome"] != "RIGHTS_RECORDED":
        return "NEEDS_HUMAN"
    if related_dois:
        return "NEEDS_HUMAN"
    return "NO_AUTOMATED_FOLLOWUP"


def validate_record(source_id: str, source: dict[str, Any], value: object) -> str:
    record = mapping(value, f"{source_id} review record must be an object")
    required = {
        "input_fingerprint",
        "provider",
        "lookup_status",
        "checked_url",
        "checked_on",
        "metadata",
        "rights",
        "related_dois",
        "status",
        "notes",
    }
    if set(record) != required:
        fail(f"{source_id} review record must contain exactly {sorted(required)}")
    input_hash = text(record.get("input_fingerprint"), f"{source_id} input_fingerprint")
    if not SHA256.fullmatch(input_hash):
        fail(f"{source_id} input_fingerprint must be a SHA-256 digest")
    if input_hash != source_input_fingerprint(source):
        fail(f"{source_id} input_fingerprint does not match registry.yaml")
    provider = text(record.get("provider"), f"{source_id} provider")
    if provider not in PROVIDERS:
        fail(f"{source_id} has unknown provider {provider!r}")
    lookup_status = text(record.get("lookup_status"), f"{source_id} lookup_status")
    if lookup_status not in LOOKUP_STATUSES:
        fail(f"{source_id} has unknown lookup_status {lookup_status!r}")
    checked_url = http_url(
        record.get("checked_url"),
        f"{source_id} checked_url must be HTTP(S) or empty for no locator",
        allow_empty=lookup_status == "MISSING_LOCATOR",
    )
    if lookup_status != "MISSING_LOCATOR" and not checked_url:
        fail(f"{source_id} checked_url must not be empty")
    utc_timestamp(record.get("checked_on"), f"{source_id} checked_on must be a UTC timestamp")
    metadata_value = record.get("metadata")
    if not isinstance(metadata_value, list) or len(metadata_value) != len(METADATA_FIELDS):
        fail(f"{source_id} metadata must contain one comparison for every field")
    comparisons: list[dict[str, Any]] = []
    seen_fields: set[str] = set()
    for index, raw_comparison in enumerate(metadata_value):
        comparison = mapping(
            raw_comparison, f"{source_id} metadata entry {index} must be an object"
        )
        if set(comparison) != {
            "field",
            "catalogue_value",
            "source_value",
            "outcome",
        }:
            fail(
                f"{source_id} metadata entry {index} must contain exactly "
                "['catalogue_value', 'field', 'outcome', 'source_value']"
            )
        field = text(comparison.get("field"), f"{source_id} metadata entry {index} field")
        if field not in METADATA_FIELDS or field in seen_fields:
            fail(f"{source_id} metadata has invalid or repeated field {field!r}")
        seen_fields.add(field)
        text(
            comparison.get("catalogue_value"),
            f"{source_id} metadata entry {index} catalogue_value",
        )
        text(
            comparison.get("source_value"),
            f"{source_id} metadata entry {index} source_value",
        )
        outcome = text(
            comparison.get("outcome"), f"{source_id} metadata entry {index} outcome"
        )
        if outcome not in OUTCOMES:
            fail(f"{source_id} metadata entry {index} has unknown outcome {outcome!r}")
        comparisons.append(comparison)
    if seen_fields != set(METADATA_FIELDS):
        fail(f"{source_id} metadata does not cover every required field")
    related_dois_value = record.get("related_dois")
    if not isinstance(related_dois_value, list):
        fail(f"{source_id} related_dois must be a list")
    related_dois: list[dict[str, Any]] = []
    seen_dois: set[str] = set()
    for index, value in enumerate(related_dois_value):
        related = mapping(value, f"{source_id} related DOI {index} must be an object")
        if set(related) != {"doi", "url"}:
            fail(f"{source_id} related DOI {index} must contain exactly ['doi', 'url']")
        doi = text(related.get("doi"), f"{source_id} related DOI {index} doi")
        if doi in seen_dois:
            fail(f"{source_id} repeats related DOI {doi!r}")
        seen_dois.add(doi)
        http_url(related.get("url"), f"{source_id} related DOI {index} URL")
        related_dois.append(related)
    rights = mapping(record.get("rights"), f"{source_id} rights must be an object")
    if set(rights) not in ({"outcome", "details", "url"}, {"outcome", "details", "url", "entries"}):
        fail(
            f"{source_id} rights must contain details, outcome, url and optional entries"
        )
    rights_outcome = text(rights.get("outcome"), f"{source_id} rights outcome")
    if rights_outcome not in RIGHTS_OUTCOMES:
        fail(f"{source_id} rights has unknown outcome {rights_outcome!r}")
    text(rights.get("details"), f"{source_id} rights details")
    http_url(
        rights.get("url"),
        f"{source_id} rights URL must be HTTP(S) or empty when unavailable",
        allow_empty=rights_outcome != "RIGHTS_RECORDED",
    )
    if "entries" in rights:
        entries = rights["entries"]
        if not isinstance(entries, list) or not entries:
            fail(f"{source_id} rights entries must be a non-empty list")
        for index, raw_entry in enumerate(entries):
            entry = mapping(raw_entry, f"{source_id} rights entry {index}")
            if set(entry) != {"url", "content_version", "start"}:
                fail(f"{source_id} rights entry {index} has invalid fields")
            http_url(entry["url"], f"{source_id} rights entry {index} URL")
            text(entry["content_version"], f"{source_id} rights entry {index} version", allow_empty=True)
            text(entry["start"], f"{source_id} rights entry {index} start", allow_empty=True)
    text(record.get("notes"), f"{source_id} notes", allow_empty=True)
    status = text(record.get("status"), f"{source_id} status")
    if status not in RECORD_STATUSES:
        fail(f"{source_id} has unknown status {status!r}")
    if status != expected_status(lookup_status, comparisons, rights, related_dois):
        fail(f"{source_id} status does not match its recorded outcomes")
    return status


def validate_dispositions(
    sources: dict[str, dict[str, Any]],
    records: dict[str, dict[str, Any]],
    dispositions_path: Path,
) -> int:
    """Validate human review dispositions against current active machine findings.

    Invariants enforced:
    1. The dispositions file exists and uses schema_version 1.
    2. Every source ID must exist in registry.yaml as a work.
    3. Every finding ID must exist as an active actionable finding on that record.
    4. reviewed_by must be a non-empty identity string naming the human
       responsible for the substantive review decision. An AI agent may
       mechanically record a disposition entry only upon explicit instruction
       from that human decision-maker.
    5. The recorded finding_fingerprint must match the computed substantive fingerprint.
    """
    try:
        data = mapping(
            json.loads(dispositions_path.read_text(encoding="utf-8")),
            "source-review-dispositions.json",
        )
    except (OSError, json.JSONDecodeError) as error:
        fail(f"source-review-dispositions.json: {error}")

    allowed_top_keys = {"schema_version", "dispositions", "description"}
    if not {"schema_version", "dispositions"}.issubset(set(data)):
        fail("source-review-dispositions.json must contain 'schema_version' and 'dispositions'")
    if set(data) - allowed_top_keys:
        fail(f"source-review-dispositions.json has extra keys: {sorted(set(data) - allowed_top_keys)}")
    if data.get("schema_version") != 1:
        fail("source-review-dispositions.json must use schema_version 1")

    dispositions = mapping(data.get("dispositions"), "dispositions must be an object")
    total_reviewed = 0

    for source_id, source_disps in sorted(dispositions.items()):
        if source_id not in sources:
            fail(f"source-review-dispositions.json names unknown work source {source_id!r}")
        source = sources[source_id]
        record = records.get(source_id)
        if not record:
            fail(f"source-review-dispositions.json references un-audited source {source_id!r}")
        if not isinstance(source_disps, dict) or not source_disps:
            fail(f"{source_id} dispositions must be a non-empty object")

        active_findings = actionable_findings(source_id, source, record)

        for finding_id, disp_entry in sorted(source_disps.items()):
            if finding_id not in active_findings:
                fail(
                    f"{source_id} has disposition for nonexistent or inactive finding {finding_id!r}; "
                    "dispositions may only target active machine findings"
                )
            finding = active_findings[finding_id]
            entry = mapping(disp_entry, f"{source_id}/{finding_id} disposition must be an object")
            required_keys = {"finding_fingerprint", "status", "reviewed_by", "reviewed_on", "reason"}
            if set(entry) != required_keys:
                fail(f"{source_id}/{finding_id} disposition must contain exactly {sorted(required_keys)}")

            status = text(entry.get("status"), f"{source_id}/{finding_id} status")
            if status not in DISPOSITION_STATUSES:
                fail(f"{source_id}/{finding_id} status must be one of {sorted(DISPOSITION_STATUSES)}")

            reviewed_by = text(entry.get("reviewed_by"), f"{source_id}/{finding_id} reviewed_by")
            if not reviewed_by.strip():
                fail(f"{source_id}/{finding_id} reviewed_by must be a non-empty identity string")

            reviewed_on = text(entry.get("reviewed_on"), f"{source_id}/{finding_id} reviewed_on")
            if not ISO_DATE.fullmatch(reviewed_on):
                fail(f"{source_id}/{finding_id} reviewed_on must be an ISO date YYYY-MM-DD ({reviewed_on!r})")
            try:
                date.fromisoformat(reviewed_on)
            except ValueError:
                fail(f"{source_id}/{finding_id} reviewed_on must be a valid calendar date ({reviewed_on!r})")

            text(entry.get("reason"), f"{source_id}/{finding_id} reason")

            recorded_fp = text(entry.get("finding_fingerprint"), f"{source_id}/{finding_id} finding_fingerprint")
            if not SHA256.fullmatch(recorded_fp):
                fail(f"{source_id}/{finding_id} finding_fingerprint must be a SHA-256 digest")
            expected_fp = compute_finding_fingerprint(finding)
            if recorded_fp != expected_fp:
                fail(
                    f"{source_id} finding {finding_id!r} disposition fingerprint is stale "
                    f"(recorded={recorded_fp}, current={expected_fp}); underlying evidence changed, re-review required"
                )
            total_reviewed += 1

    return total_reviewed


def main() -> None:
    try:
        registry = mapping(json.loads(REGISTRY.read_text(encoding="utf-8")), "registry.yaml")
        review = mapping(json.loads(REVIEW.read_text(encoding="utf-8")), "source-review.json")
    except (OSError, json.JSONDecodeError) as error:
        fail(str(error))
    required = {"schema_version", "generated_at", "source_fingerprint", "records"}
    if set(review) != required:
        fail(f"source-review.json must contain exactly {sorted(required)}")
    if review.get("schema_version") != SCHEMA_VERSION:
        fail(f"source-review.json must use schema version {SCHEMA_VERSION}")
    utc_timestamp(review.get("generated_at"), "source-review.json generated_at must be a UTC timestamp")
    sources = work_sources(registry)
    source_hash = text(review.get("source_fingerprint"), "source-review.json source_fingerprint")
    if not SHA256.fullmatch(source_hash):
        fail("source-review.json source_fingerprint must be a SHA-256 digest")
    if source_hash != fingerprint(sources):
        fail("source-review.json is stale for the current source catalogue")
    records = mapping(review.get("records"), "source-review.json records must be an object")
    if set(records) != set(sources):
        missing = sorted(set(sources) - set(records))
        extra = sorted(set(records) - set(sources))
        fail(
            "source-review.json must evaluate every work source "
            f"(missing={missing}, extra={extra})"
        )
    counts: dict[str, int] = {}
    for source_id, source in sources.items():
        status = validate_record(source_id, source, records[source_id])
        counts[status] = counts.get(status, 0) + 1
    reviewed_count = validate_dispositions(sources, records, DISPOSITIONS)
    print(
        "source review ok: "
        + ", ".join(f"{status}={count}" for status, count in sorted(counts.items()))
        + f", dispositions={reviewed_count}"
    )


if __name__ == "__main__":
    main()
