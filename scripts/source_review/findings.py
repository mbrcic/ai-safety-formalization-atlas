"""Canonical finding enumeration, taxonomy, and staleness fingerprinting.

This module defines stable identities and substantive payloads for actionable
machine findings produced during source metadata and rights audits. Each finding
represents an individual defect or review item that can be independently
triaged and tracked in human review dispositions.
"""

from __future__ import annotations

from typing import Any

from .schema import REVIEW_OUTCOMES, RIGHTS_RECORDED, stable_fingerprint


FINDING_CATEGORIES = (
    "lookup",
    "related_doi",
    "metadata",
    "rights",
)


def lookup_finding_id() -> str:
    """Return the stable finding identifier for source lookup failures or gaps."""
    return "lookup"


def related_doi_finding_id(doi: str) -> str:
    """Return the stable finding identifier for an associated published journal DOI."""
    return f"related_doi:{doi.strip().lower()}"


def metadata_finding_id(field: str) -> str:
    """Return the stable finding identifier for a bibliographic metadata comparison."""
    return f"metadata:{field}"


def rights_finding_id() -> str:
    """Return the stable finding identifier for unrecorded or missing reuse rights."""
    return "rights"


def lookup_finding_payload(
    source_id: str,
    locator: str,
    lookup_status: str,
    checked_url: str = "",
) -> dict[str, Any]:
    """Construct the substantive fingerprint payload for a lookup finding."""
    return {
        "source_id": source_id,
        "locator": locator,
        "lookup_status": lookup_status,
        "checked_url": checked_url,
    }


def related_doi_finding_payload(
    source_id: str,
    locator: str,
    doi: str,
    url: str = "",
) -> dict[str, Any]:
    """Construct the substantive fingerprint payload for an associated published DOI."""
    return {
        "source_id": source_id,
        "locator": locator,
        "doi": doi.lower(),
        "url": url,
    }


def metadata_finding_payload(
    source_id: str,
    locator: str,
    field: str,
    outcome: str,
    catalogue_value: str = "—",
    source_value: str = "—",
) -> dict[str, Any]:
    """Construct the substantive fingerprint payload for a metadata comparison finding."""
    return {
        "source_id": source_id,
        "locator": locator,
        "field": field,
        "catalogue_value": catalogue_value,
        "source_value": source_value,
        "outcome": outcome,
    }


def rights_finding_payload(
    source_id: str,
    locator: str,
    outcome: str,
    details: str = "",
    url: str = "",
) -> dict[str, Any]:
    """Construct the substantive fingerprint payload for a rights finding."""
    return {
        "source_id": source_id,
        "locator": locator,
        "outcome": outcome,
        "details": details,
        "url": url,
    }


def actionable_findings(
    source_id: str,
    source: dict[str, Any],
    record: dict[str, Any],
) -> dict[str, dict[str, Any]]:
    """Enumerate the current per-record findings and their stable finding_ids.

    A work has no actionable findings if and only if its status is NO_AUTOMATED_FOLLOWUP.
    Each finding carries a substantive payload used to compute its staleness fingerprint.
    """
    findings: dict[str, dict[str, Any]] = {}
    locator = source.get("locator", "")

    # 1. Retrieval or locator gaps
    lookup_status = record.get("lookup_status", "")
    if lookup_status in {"HTTP_ERROR", "PARSE_ERROR", "MISSING_LOCATOR"}:
        fid = lookup_finding_id()
        payload = lookup_finding_payload(
            source_id=source_id,
            locator=locator,
            lookup_status=lookup_status,
            checked_url=record.get("checked_url", ""),
        )
        findings[fid] = {
            "finding_id": fid,
            "category": "lookup",
            "source_id": source_id,
            "locator": locator,
            "payload": payload,
            "summary": f"Lookup status: {lookup_status}",
        }
        return findings

    # 2. Associated published DOI findings (keyed by specific reported DOI)
    for related in record.get("related_dois", []):
        doi = related.get("doi", "").strip()
        if not doi:
            continue
        fid = related_doi_finding_id(doi)
        payload = related_doi_finding_payload(
            source_id=source_id,
            locator=locator,
            doi=doi,
            url=related.get("url", ""),
        )
        findings[fid] = {
            "finding_id": fid,
            "category": "related_doi",
            "source_id": source_id,
            "locator": locator,
            "doi": doi,
            "url": related.get("url", ""),
            "payload": payload,
            "summary": f"Published journal DOI reported: {doi}",
        }

    # 3. Metadata comparison findings (keyed by metadata field)
    raw_metadata = record.get("metadata", [])
    if isinstance(raw_metadata, dict):
        comparisons = [
            {"field": k, **v} if isinstance(v, dict) else {"field": k}
            for k, v in raw_metadata.items()
        ]
    elif isinstance(raw_metadata, list):
        comparisons = raw_metadata
    else:
        comparisons = []

    for comparison in comparisons:
        if not isinstance(comparison, dict):
            continue
        outcome = comparison.get("outcome", "")
        if outcome in REVIEW_OUTCOMES:
            field = comparison.get("field", "")
            fid = metadata_finding_id(field)
            cat_val = comparison.get("catalogue_value", "—")
            src_val = comparison.get("source_value", "—")
            payload = metadata_finding_payload(
                source_id=source_id,
                locator=locator,
                field=field,
                outcome=outcome,
                catalogue_value=cat_val,
                source_value=src_val,
            )
            findings[fid] = {
                "finding_id": fid,
                "category": "metadata",
                "source_id": source_id,
                "locator": locator,
                "field": field,
                "outcome": outcome,
                "catalogue_value": cat_val,
                "source_value": src_val,
                "payload": payload,
                "summary": f"Metadata {outcome} for {field}",
            }

    # 4. Rights findings (only when rights were not recorded)
    rights = record.get("rights", {})
    if rights.get("outcome") != RIGHTS_RECORDED:
        fid = rights_finding_id()
        payload = rights_finding_payload(
            source_id=source_id,
            locator=locator,
            outcome=rights.get("outcome", ""),
            details=rights.get("details", ""),
            url=rights.get("url", ""),
        )
        findings[fid] = {
            "finding_id": fid,
            "category": "rights",
            "source_id": source_id,
            "locator": locator,
            "outcome": rights.get("outcome", ""),
            "details": rights.get("details", ""),
            "url": rights.get("url", ""),
            "payload": payload,
            "summary": f"Rights outcome: {rights.get('outcome', '')}",
        }

    return findings


def compute_finding_fingerprint(finding: dict[str, Any]) -> str:
    """Return the SHA-256 hex digest of the substantive payload for an actionable finding."""
    return stable_fingerprint(finding["payload"])
