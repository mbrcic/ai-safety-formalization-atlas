"""Tests for human review dispositions on source audit findings."""

from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
scripts = str(ROOT / "scripts")
if scripts not in sys.path:
    sys.path.insert(0, scripts)

import generate_registry_views as views  # noqa: E402
from source_review.findings import (  # noqa: E402
    actionable_findings,
    compute_finding_fingerprint,
)
from source_review.schema import NO_AUTOMATED_FOLLOWUP  # noqa: E402
import validate_source_review as validator  # noqa: E402


def _sample_source() -> dict:
    return {
        "citation": "Author A, Title A, 2020.",
        "role": "work",
        "locator": "https://doi.org/10.1000/1",
    }


def _sample_record() -> dict:
    return {
        "input_fingerprint": "a" * 64,
        "provider": "crossref",
        "lookup_status": "OK",
        "checked_url": "https://api.crossref.org/works/10.1000/1",
        "checked_on": "2026-08-31T12:00:00Z",
        "metadata": [
            {
                "field": "title",
                "catalogue_value": "Title A",
                "source_value": "Title B",
                "outcome": "POSSIBLE_CONFLICT",
            },
            {
                "field": "date",
                "catalogue_value": "2020",
                "source_value": "2020",
                "outcome": "MATCH",
            },
            {
                "field": "pages",
                "catalogue_value": "—",
                "source_value": "1-10",
                "outcome": "MISSING_IN_CATALOGUE",
            },
        ],
        "rights": {
            "outcome": "NO_EXPLICIT_RIGHTS",
            "details": "No license declared",
            "url": "",
        },
        "related_dois": [
            {
                "doi": "10.1000/2",
                "relationship": "version-of-record",
                "source": "arxiv-api",
                "url": "https://doi.org/10.1000/2",
                "record_url": "https://api.crossref.org/works/10.1000/2",
            }
        ],
        "status": "NEEDS_HUMAN",
        "notes": "",
    }


def test_one_source_with_multiple_independent_findings() -> None:
    source = _sample_source()
    record = _sample_record()
    findings = actionable_findings("src-1", source, record)

    # Must contain title, pages, rights, and related_doi
    assert "metadata:title" in findings
    assert "metadata:pages" in findings
    assert "rights" in findings
    assert "related_doi:10.1000/2" in findings
    # MATCH outcomes must not be actionable findings
    assert "metadata:date" not in findings

    # Fingerprints must be distinct non-empty sha256 digests
    fps = {fid: compute_finding_fingerprint(f) for fid, f in findings.items()}
    assert len(fps) == 4
    assert len(set(fps.values())) == 4
    for fp in fps.values():
        assert len(fp) == 64


def test_reviewing_one_finding_without_affecting_another() -> None:
    source = _sample_source()
    record = _sample_record()
    findings = actionable_findings("src-1", source, record)
    title_finding = findings["metadata:title"]
    title_fp = compute_finding_fingerprint(title_finding)

    dispositions_doc = {
        "schema_version": 1,
        "description": "Source review triage",
        "dispositions": {
            "src-1": {
                "metadata:title": {
                    "finding_fingerprint": title_fp,
                    "status": "REVIEWED_NO_CHANGE",
                    "reason": "Retrieved title is an author preprint typo; atlas citation is correct",
                    "reviewed_by": "alice-reviewer",
                    "reviewed_on": "2026-09-01",
                }
            }
        },
    }

    with tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".json") as tmp:
        tmp.write(json.dumps(dispositions_doc))
        tmp.flush()
        reviewed_count = validator.validate_dispositions(
            {"src-1": source}, {"src-1": record}, Path(tmp.name)
        )
        assert reviewed_count == 1

    registry = {"source_catalog": {"src-1": source}}
    review = {
        "generated_at": "2026-08-31T12:00:00Z",
        "records": {"src-1": record},
    }
    report = views.render_source_review(registry, review, dispositions_doc)

    # Title is reviewed; pages and rights are pending
    assert "✅ **Reviewed (no change)**: *Retrieved title is an author preprint typo" in report
    assert "⏳ Pending review" in report


def test_unrelated_metadata_changes_not_staling_disposition() -> None:
    source = _sample_source()
    record = _sample_record()
    findings_before = actionable_findings("src-1", source, record)
    title_fp_before = compute_finding_fingerprint(findings_before["metadata:title"])

    # Mutate unrelated metadata (pages) and crawler timestamp
    record["checked_on"] = "2026-09-05T00:00:00Z"
    for comp in record["metadata"]:
        if comp["field"] == "pages":
            comp["source_value"] = "1-20"
    record["metadata"].append({
        "field": "venue",
        "catalogue_value": "—",
        "source_value": "Journal of AI",
        "outcome": "MISSING_IN_CATALOGUE",
    })

    findings_after = actionable_findings("src-1", source, record)
    title_fp_after = compute_finding_fingerprint(findings_after["metadata:title"])

    # Title fingerprint must be completely unchanged
    assert title_fp_before == title_fp_after


def test_relevant_evidence_changes_make_only_affected_disposition_stale() -> None:
    source = _sample_source()
    record = _sample_record()

    findings_1 = actionable_findings("src-1", source, record)
    title_fp_1 = compute_finding_fingerprint(findings_1["metadata:title"])
    rights_fp_1 = compute_finding_fingerprint(findings_1["rights"])

    # Change title queried evidence
    for comp in record["metadata"]:
        if comp["field"] == "title":
            comp["source_value"] = "Title C (Revised)"

    findings_2 = actionable_findings("src-1", source, record)
    title_fp_2 = compute_finding_fingerprint(findings_2["metadata:title"])
    rights_fp_2 = compute_finding_fingerprint(findings_2["rights"])

    # Title fingerprint must change
    assert title_fp_1 != title_fp_2
    # Rights fingerprint must NOT change
    assert rights_fp_1 == rights_fp_2


def test_source_locator_changes_invalidate_relevant_dispositions() -> None:
    source = _sample_source()
    record = _sample_record()

    findings_1 = actionable_findings("src-1", source, record)
    title_fp_1 = compute_finding_fingerprint(findings_1["metadata:title"])

    # Edit source locator
    source["locator"] = "https://doi.org/10.1000/changed-locator"

    findings_2 = actionable_findings("src-1", source, record)
    title_fp_2 = compute_finding_fingerprint(findings_2["metadata:title"])

    assert title_fp_1 != title_fp_2


def test_orphan_and_invalid_dispositions_rejected() -> None:
    source = _sample_source()
    record = _sample_record()
    findings = actionable_findings("src-1", source, record)
    title_fp = compute_finding_fingerprint(findings["metadata:title"])

    def _validate(doc: dict) -> str | None:
        try:
            with tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".json") as tmp:
                tmp.write(json.dumps(doc))
                tmp.flush()
                validator.validate_dispositions({"src-1": source}, {"src-1": record}, Path(tmp.name))
            return None
        except SystemExit:
            return "failed"

    # Valid baseline
    valid_doc = {
        "schema_version": 1,
        "dispositions": {
            "src-1": {
                "metadata:title": {
                    "finding_fingerprint": title_fp,
                    "status": "REVIEWED_NO_CHANGE",
                    "reason": "Valid reason",
                    "reviewed_by": "human-reviewer",
                    "reviewed_on": "2026-09-01",
                }
            }
        },
    }
    assert _validate(valid_doc) is None

    # Orphan source
    orphan_src_doc = json.loads(json.dumps(valid_doc))
    orphan_src_doc["dispositions"]["unknown-src"] = orphan_src_doc["dispositions"].pop("src-1")
    assert _validate(orphan_src_doc) == "failed"

    # Orphan / inactive finding
    orphan_finding_doc = json.loads(json.dumps(valid_doc))
    orphan_finding_doc["dispositions"]["src-1"]["metadata:venue"] = (
        orphan_finding_doc["dispositions"]["src-1"].pop("metadata:title")
    )
    assert _validate(orphan_finding_doc) == "failed"

    # Empty or whitespace reviewed_by rejected
    for empty_val in ["", "   ", "\t"]:
        empty_doc = json.loads(json.dumps(valid_doc))
        empty_doc["dispositions"]["src-1"]["metadata:title"]["reviewed_by"] = empty_val
        assert _validate(empty_doc) == "failed"

    # Legitimate contributor handles (including those containing substrings) are accepted
    for valid_handle in ["alex-chen", "contributor_bot_maintainer", "claude_user", "ada"]:
        valid_handle_doc = json.loads(json.dumps(valid_doc))
        valid_handle_doc["dispositions"]["src-1"]["metadata:title"]["reviewed_by"] = valid_handle
        assert _validate(valid_handle_doc) is None

    # Stale fingerprint
    stale_doc = json.loads(json.dumps(valid_doc))
    stale_doc["dispositions"]["src-1"]["metadata:title"]["finding_fingerprint"] = "0" * 64
    assert _validate(stale_doc) == "failed"


def test_corrected_findings_disappear_naturally() -> None:
    source = _sample_source()
    record = _sample_record()

    # Initially there is a title discrepancy
    findings_before = actionable_findings("src-1", source, record)
    assert "metadata:title" in findings_before

    # Now the human operator fixes the citation in registry.yaml to match the source
    source["citation"] = "Author A, Title B, 2020."
    for comp in record["metadata"]:
        if comp["field"] == "title":
            comp["outcome"] = "MATCH"
            comp["catalogue_value"] = "Title B"

    findings_after = actionable_findings("src-1", source, record)
    # The title discrepancy naturally disappeared from active findings
    assert "metadata:title" not in findings_after


def test_dashboard_pending_reviewed_rendering_and_ordering() -> None:
    source_1 = _sample_source()
    source_2 = dict(_sample_source(), locator="https://doi.org/10.1000/2")
    record_1 = _sample_record()
    record_2 = _sample_record()

    # Both records have title findings
    f1 = actionable_findings("src-1", source_1, record_1)
    f2 = actionable_findings("src-2", source_2, record_2)

    # Review src-1 only
    dispositions_doc = {
        "schema_version": 1,
        "dispositions": {
            "src-1": {
                "metadata:title": {
                    "finding_fingerprint": compute_finding_fingerprint(f1["metadata:title"]),
                    "status": "REVIEWED_NO_CHANGE",
                    "reason": "Title variant accepted",
                    "reviewed_by": "human-curator",
                    "reviewed_on": "2026-09-02",
                }
            }
        },
    }

    registry = {"source_catalog": {"src-1": source_1, "src-2": source_2}}
    review = {
        "generated_at": "2026-08-31T12:00:00Z",
        "records": {"src-1": record_1, "src-2": record_2},
    }
    report = views.render_source_review(registry, review, dispositions_doc)

    # In "Potential metadata differences" table, pending finding (src-2) must appear before reviewed (src-1)
    diff_section = report[report.find("## Potential metadata differences") :]
    pos_pending = diff_section.find("src-2")
    pos_reviewed = diff_section.find("src-1")
    # Finding for src-2 is pending (sort_order 0), src-1 is reviewed (sort_order 1)
    assert pos_pending != -1 and pos_reviewed != -1
    assert pos_pending < pos_reviewed

    # Summary table must reflect the disposition counts
    assert "| Potential difference | 2 | 1 | 1 |" in report


def test_disposition_rejects_impossible_calendar_date() -> None:
    source = _sample_source()
    record = _sample_record()
    findings = actionable_findings("src-1", source, record)
    title_fp = compute_finding_fingerprint(findings["metadata:title"])

    invalid_date_doc = {
        "schema_version": 1,
        "dispositions": {
            "src-1": {
                "metadata:title": {
                    "finding_fingerprint": title_fp,
                    "status": "REVIEWED_NO_CHANGE",
                    "reason": "Valid reason",
                    "reviewed_by": "human-reviewer",
                    "reviewed_on": "2026-99-99",
                }
            }
        },
    }
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".json") as tmp:
        tmp.write(json.dumps(invalid_date_doc))
        tmp.flush()
        try:
            validator.validate_dispositions({"src-1": source}, {"src-1": record}, Path(tmp.name))
            assert False, "Expected validator to exit on impossible calendar date"
        except SystemExit:
            pass


if __name__ == "__main__":
    for name, func in list(globals().items()):
        if name.startswith("test_") and callable(func):
            func()
            print(f"ok {name}")
