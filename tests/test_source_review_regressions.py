"""Regression cases for conservative comparisons and complete lookup evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import socket
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from source_review.comparisons import author_match, pages_match, text_match, venue_match, volume_issue_match
from source_review.metadata import arxiv_metadata, crossref_external
from source_review.report import _rights_recorded_rows
from source_review import snapshot


@pytest.mark.parametrize("cited,retrieved", [
    ("John Smith", ["John Doe"]),
    ("Alice Smith and Bob Jones", ["Alice Smith"]),
    ("Alice Smith", ["Alice Smith", "Bob Jones"]),
    ("A. Smith and B. Jones", ["Bob Jones", "Alice Smith"]),
    ("B. Smith", ["Alice Smith"]),
    ("Bob Smith", ["Alice Smith"]),
    ("B. Jones et al.", ["Alice Smith", "Bob Jones"]),
])
def test_author_differences_require_review(cited, retrieved) -> None:
    assert author_match(cited, retrieved) == "POSSIBLE_CONFLICT"


@pytest.mark.parametrize("cited,retrieved", [
    ("A. Smith and B. Jones", ["Alice Smith", "Bob Jones"]),
    ("A. Smith", ["Smith, Alice"]),
    ("Smith et al.", ["Alice Smith", "Bob Jones"]),
    ("A. Smith et al.", ["Alice Smith", "Bob Jones"]),
])
def test_explicit_author_abbreviations_remain_supported(cited, retrieved) -> None:
    assert author_match(cited, retrieved) == "MATCH"


def test_title_extensions_are_not_silently_accepted() -> None:
    assert text_match("Safety is possible", "Safety is possible only with supervision") == "POSSIBLE_CONFLICT"
    assert text_match("An example: a theorem", "An example—a theorem.") == "MATCH"


def test_dns_failure_does_not_prevent_other_records_or_persistence(monkeypatch, tmp_path) -> None:
    sources = {
        "broken": {"citation": "Example", "locator": "https://example.org/paper", "role": "work"},
        "next": {"citation": "Another example", "role": "work"},
    }
    registry_path = tmp_path / "registry.yaml"
    registry_path.write_text(json.dumps({"source_catalog": sources}))
    monkeypatch.setattr(snapshot, "REGISTRY", registry_path)
    monkeypatch.setattr(snapshot, "load_cached_records", lambda: {})
    attempts = []

    def dns_failure(*args):
        attempts.append(args)
        raise socket.gaierror("temporary DNS failure")

    monkeypatch.setattr(socket, "getaddrinfo", dns_failure)
    monkeypatch.setattr("source_review.lookups.time.sleep", lambda _: None)
    args = argparse.Namespace(
        force=True, sources=None, reclassify=False, crossref_delay=0,
        arxiv_delay=0, web_delay=0, max_age_days=30, timeout=1,
        max_bytes=1000, retries=1, user_agent="unit-test", mailto=None,
    )
    result = snapshot.build_snapshot(args)
    assert len(attempts) == 2
    assert result["records"]["broken"]["status"] == "LOOKUP_FAILED"
    assert "temporary DNS failure" in result["records"]["broken"]["notes"]
    assert result["records"]["next"]["lookup_status"] == "MISSING_LOCATOR"
    path = tmp_path / "snapshot.json"
    snapshot.write_snapshot(result, path)
    assert json.loads(path.read_text()) == result


def test_all_crossref_licenses_and_effective_dates_reach_report() -> None:
    message = {"license": [
        {"URL": "https://publisher.example/terms", "content-version": "vor"},
        {"URL": "https://creativecommons.org/licenses/by/4.0/", "content-version": "am",
         "start": {"date-time": "2030-01-01T00:00:00Z"}},
        {"URL": "https://publisher.example/tdm", "content-version": "tdm"},
    ]}
    rights = crossref_external(message)["rights"]
    assert len(rights["entries"]) == 3
    assert rights["entries"][1]["start"] == "2030-01-01T00:00:00Z"
    assert "entries" not in crossref_external({})["rights"]
    rows = _rights_recorded_rows(
        [("example", {"locator": "https://example.org/paper"})],
        {"example": {"lookup_status": "OK", "provider": "crossref", "rights": rights,
                     "checked_url": "https://api.crossref.org/works/10.1000/example"}},
    )
    assert len(rows) == 1  # Summary counts works, not licence entries.
    for entry in message["license"]:
        url = entry["URL"]
        assert isinstance(url, str)
        assert url in rows[0]
    assert "accepted manuscript" in rows[0]
    assert "2030-01-01T00:00:00Z" in rows[0]


@pytest.mark.parametrize("cited,retrieved", [
    ("vol. 8, no. 7", "vol. 8"),
    ("vol. 8", "vol. 8, no. 7"),
    ("no. 7", "vol. 8, no. 7"),
    ("vol. 8, no. 7 (Supplement)", "vol. 8, no. 7"),
    ("vol. 8, no. 7/8", "vol. 8, no. 7"),
])
def test_partial_volume_issue_agreement_requires_review(cited, retrieved) -> None:
    assert volume_issue_match(cited, retrieved) == "POSSIBLE_CONFLICT"


def test_volume_issue_label_normalization_preserves_equivalence() -> None:
    assert volume_issue_match("volume 8, issue 7", "vol. 8, no. 7") == "MATCH"
    assert volume_issue_match("vol. 8", "volume 8") == "MATCH"


@pytest.mark.parametrize("cited,retrieved", [
    ("199-200", "199-1200"),
    ("S12-S19", "12-19"),
    ("12-19, 25-30", "12-19"),
    ("12-19", "12-19, 25-30"),
    ("article e12", "12"),
    ("199-02", "199-202"),
])
def test_ambiguous_page_ranges_require_review(cited, retrieved) -> None:
    assert pages_match(cited, retrieved) == "POSSIBLE_CONFLICT"
    assert pages_match(retrieved, cited) == "POSSIBLE_CONFLICT"


@pytest.mark.parametrize("cited,retrieved", [
    ("1341-90", "1341–1390"),
    ("345-63", "345 — 363"),
    ("S12–S19", "S12-S19"),
    ("e123", "e123"),
])
def test_unambiguous_page_formatting_still_matches(cited, retrieved) -> None:
    assert pages_match(cited, retrieved) == "MATCH"
    assert pages_match(retrieved, cited) == "MATCH"


@pytest.mark.parametrize("cited,retrieved", [
    ("Journal of Applied Physics", "Journal of Applied Psychology"),
    ("Journal of Applied Physics", "Journal of Applied Physics Letters"),
    ("Proc. Example Math. Soc.", "Proceedings of the Example Mathematical Society"),
])
def test_venue_overlap_and_abbreviations_require_review(cited, retrieved) -> None:
    assert venue_match(cited, retrieved) == "POSSIBLE_CONFLICT"


def test_venue_formatting_still_matches() -> None:
    assert venue_match("Example Journal: Series A", "EXAMPLE JOURNAL — SERIES A") == "MATCH"


def _arxiv_entry(identifier: str) -> bytes:
    return (
        '<feed xmlns="http://www.w3.org/2005/Atom"><entry>'
        f'<id>{identifier}</id><title>Example</title></entry></feed>'
    ).encode()


@pytest.mark.parametrize("identifier", [
    "", "https://arxiv.org/api/errors#incorrect_id_format",
    "https://arxiv.org/abs/not-a-paper", "https://arxiv.org/abs/2001.00002v1",
    "https://arxiv.org/abs/2001.00001v2", "https://arxiv.org/abs/2001.00001",
])
def test_arxiv_rejects_missing_invalid_or_wrong_identifiers(identifier) -> None:
    with pytest.raises(ValueError):
        arxiv_metadata(_arxiv_entry(identifier), "2001.00001v1")


def test_arxiv_accepts_matching_version_and_unversioned_request() -> None:
    body = _arxiv_entry("https://arxiv.org/abs/2001.00001v2")
    assert arxiv_metadata(body, "2001.00001v2")[0]["identifier"] == "arxiv:2001.00001v2"
    assert arxiv_metadata(body, "2001.00001")[0]["identifier"] == "arxiv:2001.00001"


def test_invalid_arxiv_response_uses_existing_html_fallback(monkeypatch) -> None:
    from source_review import lookups

    calls = []

    def fake_fetch(url, *args):
        calls.append(url)
        if len(calls) == 1:
            return _arxiv_entry("https://arxiv.org/api/errors#incorrect_id_format"), url, ""
        return b'<meta name="citation_title" content="Example">', url, ""

    monkeypatch.setattr(lookups, "fetch", fake_fetch)
    source = {"citation": 'A. Example, “Example,” 2020.', "locator": "https://arxiv.org/abs/2001.00001"}
    args = argparse.Namespace(user_agent="unit-test", timeout=1, max_bytes=1000, retries=0)
    record = lookups.evaluate_source(source, args, lookups.HostRateLimiter(0, 0, 0))
    assert len(calls) == 2
    assert record["provider"] == "html"
    assert record["status"] == "NEEDS_HUMAN"
    assert "Could not parse arXiv API metadata" in record["notes"]
