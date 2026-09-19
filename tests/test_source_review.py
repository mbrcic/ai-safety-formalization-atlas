"""Regression tests for the complete, exception-first source audit."""

from __future__ import annotations

import argparse
import copy
import importlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
from types import SimpleNamespace

import pytest


ROOT = Path(__file__).resolve().parents[1]
REVIEW = "docs/provenance/source-review.json"


def _refresh_module():
    scripts = str(ROOT / "scripts")
    if scripts not in sys.path:
        sys.path.insert(0, scripts)
    return importlib.import_module("source_review")


def _registry() -> dict:
    return json.loads((ROOT / "registry.yaml").read_text(encoding="utf-8"))


def _example_source() -> dict:
    """A stable unit-test record, deliberately unrelated to the live catalogue."""
    return {
        "citation": (
            "A. Example, \u201cExample paper,\u201d Example Journal, vol. 8, no. 7, "
            "pp. 1391\u20131420, 2026, doi: 10.1000/example."
        ),
        "locator": "https://doi.org/10.1000/example",
        "role": "work",
    }


def _complete_failed_snapshot() -> dict:
    refresh = _refresh_module()
    sources = refresh.source_catalogue(_registry())
    records = {
        source_id: refresh.failed_record(
            source,
            "html",
            "HTTP_ERROR",
            "https://example.com/checked-record",
            "Synthetic lookup failure used only by this test.",
        )
        for source_id, source in sources.items()
    }
    return {
        "schema_version": refresh.SCHEMA_VERSION,
        "generated_at": "2026-08-31T12:00:00Z",
        "source_fingerprint": refresh.catalogue_fingerprint(sources),
        "records": records,
    }


def _run_validator(tmp_path: Path, review: dict) -> subprocess.CompletedProcess[str]:
    (tmp_path / "docs/provenance").mkdir(parents=True)
    (tmp_path / "scripts").mkdir()
    shutil.copy2(ROOT / "registry.yaml", tmp_path / "registry.yaml")
    shutil.copy2(
        ROOT / "scripts/validate_source_review.py",
        tmp_path / "scripts/validate_source_review.py",
    )
    shutil.copytree(
        ROOT / "scripts/source_review",
        tmp_path / "scripts/source_review",
    )
    shutil.copy2(
        ROOT / "docs/provenance/source-review-dispositions.json",
        tmp_path / "docs/provenance/source-review-dispositions.json",
    )
    (tmp_path / REVIEW).write_text(
        json.dumps(review, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return subprocess.run(
        [sys.executable, "scripts/validate_source_review.py"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
    )


def _crossref_message(title: str) -> dict:
    return {
        "DOI": "10.1000/example",
        "title": [title],
        "author": [{"given": "Ada", "family": "Example"}],
        "published-print": {"date-parts": [[2026, 8]]},
        "container-title": ["Example Journal"],
        "volume": "8",
        "issue": "7",
        "page": "1391-1420",
        "license": [
            {
                "URL": "https://example.com/license",
                "content-version": "vor",
            }
        ],
    }


def test_crossref_comparison_checks_core_metadata_and_rights() -> None:
    refresh = _refresh_module()
    source = _example_source()
    external = refresh.crossref_external(
        _crossref_message("Example paper")
    )
    comparisons = refresh.metadata_comparisons(
        source, external, True, source["locator"]
    )
    outcomes = {comparison["field"]: comparison["outcome"] for comparison in comparisons}

    assert outcomes["identifier"] == "MATCH"
    assert outcomes["title"] == "MATCH"
    assert outcomes["authors"] == "MATCH"
    assert outcomes["pages"] == "MATCH"
    assert external["rights"]["outcome"] == "RIGHTS_RECORDED"



def test_html_parser_uses_standard_citation_and_license_tags() -> None:
    refresh = _refresh_module()
    external = refresh.html_external(
        b"""<html><head>
        <meta name='citation_title' content='Example title'>
        <meta name='citation_author' content='Ada Lovelace'>
        <meta name='citation_publication_date' content='2026-08-31'>
        <meta name='citation_doi' content='10.1000/example'>
        <link rel='license' href='https://example.com/license'>
        </head><body></body></html>""",
        "https://example.com/paper",
    )

    assert external["title"] == "Example title"
    assert external["authors"] == ["Ada Lovelace"]
    assert external["identifier"] == "doi:10.1000/example"
    assert external["rights"]["outcome"] == "RIGHTS_RECORDED"


def test_html_parser_extracts_article_heading_for_document_title() -> None:
    refresh = _refresh_module()
    html_doc = """<html><head>
    <title>MAIS/open-problems/MAIS-O23.md at main · lionellevine/MAIS</title>
    </head><body>
    <article class="markdown-body">
      <h1>Do margins imply behavioral identifiability of causal models?</h1>
      <p>Some text</p>
    </article>
    </body></html>""".encode("utf-8")
    external = refresh.html_external(
        html_doc,
        "https://github.com/lionellevine/MAIS/blob/main/open-problems/MAIS-O23.md",
    )
    assert external["title"] == "Do margins imply behavioral identifiability of causal models?"


def test_doi_and_author_comparison_handle_ordinary_legacy_formats() -> None:
    refresh = _refresh_module()

    assert refresh.extract_doi(
        "doi: 10.1000/(SICI)1234-5678(199707)5:3<305::AID-EXAMPLE>3.0.CO;2-4"
    ) == "10.1000/(sici)1234-5678(199707)5:3<305::aid-example>3.0.co;2-4"
    assert (
        refresh.author_match(
            "S. Example and J. Sample", ["Example, Sam", "Sample, Jordan"]
        )
        == "MATCH"
    )
    assert (
        refresh.venue_match(
            "Proc. Example Math. Soc.",
            "Proceedings of the Example Mathematical Society",
        )
        == "POSSIBLE_CONFLICT"
    )
    assert refresh.citation_pages("P. Example, \u201cExample\u201d") == ""
    assert refresh.citation_pages("Example, pp. 44-48") == "44-48"


def test_reclassification_reuses_saved_values_without_requerying() -> None:
    refresh = _refresh_module()
    source = {
        "citation": "A. Example, \u201cExample paper,\u201d arXiv:1234.5678, 2026.",
        "locator": "https://arxiv.org/abs/1234.5678",
        "role": "work",
    }
    external = {
        "identifier": "arxiv:1234.5678",
        "title": "Example paper",
        "authors": ["Example, A."],
        "date": "2026-01-01",
        "venue": "",
        "volume_issue": "",
        "pages": "",
        "rights": {
            "outcome": "RIGHTS_RECORDED",
            "details": "Synthetic test license.",
            "url": "https://example.com/license",
        },
    }
    record = refresh.successful_record(
        source,
        "arxiv",
        refresh.arxiv_api_url("1234.5678"),
        "https://arxiv.org/abs/1234.5678",
        external,
    )
    for comparison in record["metadata"]:
        if comparison["field"] == "venue":
            comparison.update(
                {
                    "catalogue_value": "arXiv:1234.5678",
                    "outcome": "MISSING_IN_SOURCE",
                }
            )

    reclassified = refresh.reclassify_record(source, record)
    outcomes = {
        comparison["field"]: comparison["outcome"]
        for comparison in reclassified["metadata"]
    }

    assert outcomes["venue"] == "NOT_APPLICABLE"
    locator = next(
        comparison
        for comparison in reclassified["metadata"]
        if comparison["field"] == "locator"
    )
    assert locator["source_value"] == source["locator"]
    assert reclassified["checked_on"] == record["checked_on"]


def test_crossref_not_found_falls_back_to_the_public_locator(monkeypatch) -> None:
    refresh = _refresh_module()
    source = {
        "citation": "A. Example, \u201cExample paper,\u201d 2026, doi: 10.1000/example.",
        "locator": "https://doi.org/10.1000/example",
        "role": "work",
    }
    calls: list[str] = []

    def fake_fetch(url, *_args):
        calls.append(url)
        if "api.crossref.org" in url:
            return None, url, "HTTP 404"
        return (
            b"<html><head><meta name='citation_title' content='Example paper'>"
            b"<meta name='citation_author' content='Example, A.'></head></html>",
            "https://example.com/paper",
            "",
        )

    monkeypatch.setattr(refresh.lookups, "fetch", fake_fetch)
    args = SimpleNamespace(
        mailto=None,
        user_agent="test",
        timeout=1.0,
        max_bytes=1024,
        retries=0,
    )
    record = refresh.evaluate_source(source, args, refresh.HostRateLimiter(0, 0, 0))

    assert len(calls) == 2
    assert record["provider"] == "html"
    assert record["lookup_status"] == "OK"
    assert record["checked_url"] == "https://example.com/paper"
    assert "Crossref returned HTTP 404" in record["notes"]


def test_arxiv_lookup_preserves_the_preprint_identifier_and_license(monkeypatch) -> None:
    refresh = _refresh_module()
    source = {
        "citation": (
            "A. Example, “Example preprint,” arXiv:1234.5678, 2026, "
            "doi: 10.1000/published-version."
        ),
        "locator": "https://arxiv.org/abs/1234.5678",
        "role": "work",
    }
    calls: list[str] = []

    def fake_fetch(url, *_args):
        calls.append(url)
        if "export.arxiv.org" in url:
            return (
                b"""<feed xmlns='http://www.w3.org/2005/Atom'
                xmlns:arxiv='http://arxiv.org/schemas/atom'><entry>
                <id>http://arxiv.org/abs/1234.5678v2</id>
                <published>2026-08-31T12:00:00Z</published>
                <title>Example preprint</title>
                <author><name>Ada Example</name></author>
                <arxiv:journal_ref>Example Journal 8 (2026)</arxiv:journal_ref>
                <arxiv:doi>10.1000/published-version</arxiv:doi>
                </entry></feed>""",
                url,
                "",
            )
        return (
            b"<html><body><a href='/licenses/nonexclusive-distrib/1.0/'>"
            b"view license</a></body></html>",
            source["locator"],
            "",
        )

    monkeypatch.setattr(refresh.lookups, "fetch", fake_fetch)
    args = SimpleNamespace(
        mailto=None,
        user_agent="test",
        timeout=1.0,
        max_bytes=1024,
        retries=0,
    )
    record = refresh.evaluate_source(source, args, refresh.HostRateLimiter(0, 0, 0))
    outcomes = {comparison["field"]: comparison["outcome"] for comparison in record["metadata"]}

    assert calls == [refresh.arxiv_api_url("1234.5678"), source["locator"]]
    assert record["provider"] == "arxiv"
    assert record["checked_url"] == refresh.arxiv_api_url("1234.5678")
    assert outcomes["identifier"] == "MATCH"
    assert record["rights"] == {
        "outcome": "RIGHTS_RECORDED",
        "details": "Per-paper license link on the arXiv abstract page.",
        "url": "https://arxiv.org/licenses/nonexclusive-distrib/1.0/",
    }
    assert record["related_dois"] == [
        {
            "doi": "10.1000/published-version",
            "url": "https://doi.org/10.1000/published-version",
        }
    ]
    assert record["status"] == "NEEDS_HUMAN"


def test_arxiv_lookup_invalidates_legacy_html_cache() -> None:
    refresh = _refresh_module()
    source = {
        "citation": "A. Example, “Example preprint,” arXiv:1234.5678, 2026.",
        "locator": "https://arxiv.org/abs/1234.5678",
        "role": "work",
    }

    assert not refresh.cached_record_is_compatible(
        source, {"provider": "html", "notes": "", "related_dois": []}
    )
    assert refresh.cached_record_is_compatible(
        source,
        {
            "provider": "html",
            "notes": "arXiv API lookup failed (HTTP 503); checked the source locator instead.",
            "related_dois": [],
        },
    )
    assert refresh.cached_record_is_compatible(
        source, {"provider": "arxiv", "notes": "", "related_dois": []}
    )


def test_complete_snapshot_is_accepted_and_a_missing_source_is_not(tmp_path: Path) -> None:
    snapshot = _complete_failed_snapshot()
    accepted = _run_validator(tmp_path / "accepted", snapshot)
    assert accepted.returncode == 0, accepted.stderr + accepted.stdout

    arxiv_provider = copy.deepcopy(snapshot)
    next(iter(arxiv_provider["records"].values()))["provider"] = "arxiv"
    accepted_arxiv = _run_validator(tmp_path / "accepted-arxiv", arxiv_provider)
    assert accepted_arxiv.returncode == 0, accepted_arxiv.stderr + accepted_arxiv.stdout

    incomplete = copy.deepcopy(snapshot)
    incomplete["records"].pop(next(iter(incomplete["records"])))
    rejected = _run_validator(tmp_path / "incomplete", incomplete)
    output = rejected.stderr + rejected.stdout
    assert rejected.returncode != 0, output
    assert "must evaluate every work source" in output


def test_archive_org_wayback_chrome_stripped_to_avoid_false_conflict() -> None:
    refresh = _refresh_module()
    html_doc = """<!DOCTYPE html>
    <html><head>
    <title>Wayback Machine</title>
    </head><body><p>Archived content</p></body></html>""".encode("utf-8")
    external = refresh.html_external(
        html_doc,
        "https://web.archive.org/web/20220222045551/http://www.cs.uu.nl/groups/AD/UU-PCS-2021-02.pdf",
    )
    assert external["title"] == ""


def test_date_match_compares_extracted_year_not_access_date() -> None:
    refresh = _refresh_module()
    citation = "Author, “Paper Title,” 2019. Accessed: Jun. 29, 2021."
    # Extracted year is 2019; external record reports 2021. Even though 2021 is in citation,
    # it must be a POSSIBLE_CONFLICT rather than MATCH.
    assert refresh.date_match("2019", "2021", citation) == "POSSIBLE_CONFLICT"
    assert refresh.date_match("2019", "2019", citation) == "MATCH"
    assert refresh.date_match("2019", "2019-06-15", citation) == "MATCH"


def test_identifier_match_canonical_exact_not_substring() -> None:
    refresh = _refresh_module()
    # DOIs must not match by partial substring
    assert refresh.identifier_match("doi:10.1000/1", "doi:10.1000/10") == "POSSIBLE_CONFLICT"
    assert refresh.identifier_match("doi:10.1000/10", "doi:10.1000/1") == "POSSIBLE_CONFLICT"
    assert refresh.identifier_match("doi:10.1000/abc", "doi:10.1000/ABC") == "MATCH"

    # arXiv IDs must compare base or exact, not substring
    assert refresh.identifier_match("arxiv:2101.0101", "arxiv:2101.01011") == "POSSIBLE_CONFLICT"
    assert refresh.identifier_match("arxiv:2101.0101", "arxiv:2101.0101v2") == "MATCH"
    assert refresh.identifier_match("arxiv:2101.0101v1", "arxiv:2101.0101v2") == "MATCH"


def test_volume_issue_and_pages_numeric_boundaries() -> None:
    refresh = _refresh_module()
    # Volume / issue numeric boundaries
    assert refresh.volume_issue_match("vol. 8", "vol. 80") == "POSSIBLE_CONFLICT"
    assert refresh.volume_issue_match("vol. 8, no. 1", "vol. 8, no. 10") == "POSSIBLE_CONFLICT"
    assert refresh.volume_issue_match("vol. 8, no. 1", "vol. 8, no. 1") == "MATCH"
    assert refresh.volume_issue_match("vol. 8", "vol. 8, no. 1") == "POSSIBLE_CONFLICT"

    # Page range numeric boundaries
    assert refresh.pages_match("134", "1341-1390") == "POSSIBLE_CONFLICT"
    assert refresh.pages_match("1341-1390", "1341–1390") == "MATCH"
    assert refresh.pages_match("1341-1390", "1341-90") == "MATCH"
    assert refresh.pages_match("1341", "1341-1390") == "POSSIBLE_CONFLICT"


def test_author_match_et_al_abbreviation() -> None:
    refresh = _refresh_module()
    # Catalogue intentionally uses "et al." abbreviation:
    # All retrieved authors do NOT need to appear in the citation, but leading author must.
    retrieved = ["David H. Wolpert", "William G. Macready", "Third Author", "Fourth Author"]
    assert refresh.author_match("D. H. Wolpert et al.", retrieved) == "MATCH"
    assert refresh.author_match("Wolpert et al.", retrieved) == "MATCH"

    # If the leading author does not match, it must conflict
    assert refresh.author_match("J. Smith et al.", retrieved) == "POSSIBLE_CONFLICT"


def test_arxiv_metadata_uses_updated_date_for_versioned_locator() -> None:
    refresh = _refresh_module()
    atom_xml = b"""<?xml version="1.0" encoding="UTF-8"?>
    <feed xmlns="http://www.w3.org/2005/Atom">
      <entry>
        <id>http://arxiv.org/abs/physics/0104007v2</id>
        <published>2001-04-02T19:08:52Z</published>
        <updated>2001-04-06T12:34:56Z</updated>
        <title>Versioned Preprint Title</title>
        <author><name>Author Name</name></author>
      </entry>
    </feed>"""
    # Versioned request should yield updated date
    ver_meta, _ = refresh.arxiv_metadata(atom_xml, "physics/0104007v2")
    assert ver_meta["date"] == "2001-04-06T12:34:56Z"
    assert ver_meta["published"] == "2001-04-02T19:08:52Z"
    assert ver_meta["updated"] == "2001-04-06T12:34:56Z"

    # Unversioned request should yield published date
    unver_meta, _ = refresh.arxiv_metadata(atom_xml, "physics/0104007")
    assert unver_meta["date"] == "2001-04-02T19:08:52Z"


def test_github_blob_chrome_tex_treated_as_not_extracted() -> None:
    refresh = _refresh_module()
    html_doc = """<html><head>
    <title>MAIS/agendas/A2/MAIS-A2.tex at 9dd29f8bf5ccd1e7701e300039b09ed4096b6516 · lionellevine/MAIS · GitHub</title>
    </head><body>
    <table class="highlight"><tr><td>\\section{Behavioral tomography}</td></tr></table>
    </body></html>""".encode("utf-8")
    external = refresh.html_external(
        html_doc,
        "https://github.com/lionellevine/MAIS/blob/9dd29f8bf5ccd1e7701e300039b09ed4096b6516/agendas/A2/MAIS-A2.tex",
    )
    # GitHub blob chrome should be discarded, leaving title not extracted
    assert external["title"] == ""


def test_crossref_multiple_licenses_prefers_vor_over_tdm() -> None:
    refresh = _refresh_module()
    message = {
        "DOI": "10.1000/example",
        "title": ["Example Paper"],
        "license": [
            {"URL": "https://example.com/tdm-license", "content-version": "tdm"},
            {"URL": "https://example.com/vor-license", "content-version": "vor"},
        ],
    }
    external = refresh.crossref_external(message)
    assert external["rights"]["outcome"] == "RIGHTS_RECORDED"
    assert external["rights"]["url"] == "https://example.com/vor-license"
    assert "vor" in external["rights"]["details"]


def test_failed_lookup_exposes_only_lookup_finding() -> None:
    refresh = _refresh_module()
    source = {"citation": "Example citation", "locator": "https://example.com/fail"}
    record = {
        "lookup_status": "HTTP_ERROR",
        "checked_url": "https://example.com/fail",
        "metadata": [
            {"field": "title", "catalogue_value": "Example", "source_value": "—", "outcome": "UNAVAILABLE"},
            {"field": "date", "catalogue_value": "2020", "source_value": "—", "outcome": "UNAVAILABLE"},
        ],
        "rights": {"outcome": "RIGHTS_UNAVAILABLE", "details": "Lookup failed.", "url": ""},
    }
    findings = refresh.actionable_findings("src-fail", source, record)
    assert list(findings.keys()) == ["lookup"]
    assert findings["lookup"]["category"] == "lookup"

    # Same for MISSING_LOCATOR
    record_missing = {
        "lookup_status": "MISSING_LOCATOR",
        "metadata": [],
        "rights": {"outcome": "RIGHTS_UNAVAILABLE", "details": "No locator", "url": ""},
    }
    findings_missing = refresh.actionable_findings("src-missing", {"citation": "Test"}, record_missing)
    assert list(findings_missing.keys()) == ["lookup"]


def test_selective_refresh_rejects_unknown_id(monkeypatch) -> None:
    refresh = _refresh_module()
    registry = {
        "source_catalog": {
            "src-1": {"citation": "Source 1", "role": "work", "locator": "https://example.com/1"},
        }
    }
    monkeypatch.setattr(
        "pathlib.Path.read_text",
        lambda self, encoding="utf-8": json.dumps(registry) if "registry.yaml" in str(self) else "{}",
    )
    args = SimpleNamespace(
        sources="src-unknown",
        reclassify=False,
        crossref_delay=0,
        arxiv_delay=0,
        web_delay=0,
    )
    import pytest
    with pytest.raises(ValueError, match="unknown source ID"):
        refresh.build_snapshot(args)


def test_selective_refresh_rejects_stale_non_target(monkeypatch) -> None:
    refresh = _refresh_module()
    registry = {
        "source_catalog": {
            "src-target": {"citation": "Target Source", "role": "work", "locator": "https://example.com/target"},
            "src-other": {"citation": "Other Source Updated", "role": "work", "locator": "https://example.com/other"},
        }
    }
    # Cached record for src-other has stale fingerprint
    cached_snapshot = {
        "records": {
            "src-target": {
                "input_fingerprint": refresh.input_fingerprint(registry["source_catalog"]["src-target"]),
                "lookup_status": "OK",
                "checked_on": "2026-09-01T00:00:00Z",
                "related_dois": [],
            },
            "src-other": {
                "input_fingerprint": "old_fingerprint",
                "lookup_status": "OK",
                "checked_on": "2026-09-01T00:00:00Z",
                "related_dois": [],
            },
        }
    }
    def mock_read(self, encoding="utf-8"):
        if "registry.yaml" in str(self):
            return json.dumps(registry)
        if "source-review.json" in str(self):
            return json.dumps(cached_snapshot)
        return "{}"

    monkeypatch.setattr("pathlib.Path.read_text", mock_read)
    args = SimpleNamespace(
        sources="src-target",
        reclassify=False,
        crossref_delay=0,
        arxiv_delay=0,
        web_delay=0,
    )
    import pytest
    with pytest.raises(ValueError, match="stale for current registry.*src-other"):
        refresh.build_snapshot(args)


def test_validate_public_url_rejects_unsafe_schemes_and_userinfo() -> None:
    from source_review.lookups import UnsafeURLError, validate_public_url
    import pytest
    with pytest.raises(UnsafeURLError, match="unsupported scheme 'file'"):
        validate_public_url("file:///etc/passwd")
    with pytest.raises(UnsafeURLError, match="unsupported scheme 'ftp'"):
        validate_public_url("ftp://ftp.example.com/file")
    with pytest.raises(UnsafeURLError, match="userinfo is not permitted"):
        validate_public_url("https://user:pass@example.com/resource")


def test_validate_public_url_rejects_private_and_non_global_ips() -> None:
    from source_review.lookups import UnsafeURLError, validate_public_url
    import pytest
    for bad_url in [
        "http://127.0.0.1/test",
        "http://[::1]/test",
        "http://10.0.0.1/admin",
        "http://192.168.1.1/",
        "http://172.16.0.1/",
        "http://169.254.169.254/latest/meta-data/",
        "http://localhost/test",
        "http://service.localhost/",
    ]:
        with pytest.raises(UnsafeURLError):
            validate_public_url(bad_url)


def test_validate_public_url_resolves_hostname_and_rejects_private(monkeypatch) -> None:
    from source_review.lookups import UnsafeURLError, validate_public_url
    import pytest
    import socket
    def mock_getaddrinfo(host, port):
        return [(socket.AF_INET, socket.SOCK_STREAM, 6, "", ("127.0.0.1", 80))]
    monkeypatch.setattr(socket, "getaddrinfo", mock_getaddrinfo)
    with pytest.raises(UnsafeURLError, match="loopback address rejected"):
        validate_public_url("https://example.com/test")


def test_validate_public_url_accepts_valid_public_http(monkeypatch) -> None:
    from source_review.lookups import validate_public_url
    import socket
    def mock_getaddrinfo(host, port):
        return [(socket.AF_INET, socket.SOCK_STREAM, 6, "", ("93.184.216.34", 80))]
    monkeypatch.setattr(socket, "getaddrinfo", mock_getaddrinfo)
    # Must not raise
    validate_public_url("https://example.com/test")


def test_fetch_rejects_redirect_to_private_address() -> None:
    from urllib.request import Request
    from source_review.lookups import SafeRedirectHandler, UnsafeURLError
    import pytest
    handler = SafeRedirectHandler()
    req = Request("https://example.com/start")
    with pytest.raises(UnsafeURLError, match="private address rejected|loopback address rejected"):
        handler.redirect_request(req, None, 302, "Found", {}, "http://192.168.1.1/secret")


def test_fetch_succeeds_on_mocked_public_destination(monkeypatch) -> None:
    refresh = _refresh_module()
    import socket
    def mock_getaddrinfo(host, port):
        return [(socket.AF_INET, socket.SOCK_STREAM, 6, "", ("93.184.216.34", 80))]
    monkeypatch.setattr(socket, "getaddrinfo", mock_getaddrinfo)

    from io import BytesIO
    class MockResponse:
        def __init__(self):
            self.fp = BytesIO(b"public content")
        def read(self, n):
            return self.fp.read(n)
        def geturl(self):
            return "https://example.com/ok"
        def __enter__(self):
            return self
        def __exit__(self, *args):
            pass

    monkeypatch.setattr("urllib.request.OpenerDirector.open", lambda self, req, timeout: MockResponse())
    limiter = refresh.HostRateLimiter(0.0, 0.0, 0.0)
    body, final_url, err = refresh.fetch("https://example.com/ok", limiter, "test-agent", 1.0, 1000, 0)
    assert body == b"public content"
    assert final_url == "https://example.com/ok"
    assert err == ""


def test_refresh_aborts_on_unsafe_locator_without_writing_snapshot(monkeypatch, tmp_path: Path) -> None:
    from source_review.lookups import UnsafeURLError
    from source_review.snapshot import load_cached_records as real_load_cached_records
    _refresh_module()
    import refresh_source_review
    import pytest

    snapshot_path = tmp_path / "source-review.json"
    initial_content = '{"schema_version": 3, "records": {"existing": {}}}\n'
    snapshot_path.write_text(initial_content, encoding="utf-8")

    registry_path = tmp_path / "registry.yaml"
    registry = {
        "source_catalog": {
            "src-unsafe": {
                "citation": "Unsafe source, 2026.",
                "role": "work",
                "locator": "http://127.0.0.1/admin",
            }
        }
    }
    registry_path.write_text(json.dumps(registry), encoding="utf-8")

    # Verify any attempted network open fails the test
    def mock_network(*args, **kwargs):
        raise AssertionError("Network request was attempted for an unsafe locator!")

    monkeypatch.setattr("urllib.request.urlopen", mock_network)
    monkeypatch.setattr("urllib.request.OpenerDirector.open", mock_network)

    # Point registry and review to controlled test paths without touching real repo
    monkeypatch.setattr("source_review.snapshot.REGISTRY", registry_path)
    monkeypatch.setattr("source_review.snapshot.REVIEW", snapshot_path)
    monkeypatch.setattr(
        "source_review.snapshot.load_cached_records",
        lambda path=snapshot_path: real_load_cached_records(path),
    )

    write_called = False
    def sentinel_write_snapshot(snapshot, path=None):
        nonlocal write_called
        write_called = True

    monkeypatch.setattr(refresh_source_review, "write_snapshot", sentinel_write_snapshot)

    args = argparse.Namespace(
        sources="src-unsafe",
        force=True,
        reclassify=False,
        crossref_delay=0,
        arxiv_delay=0,
        web_delay=0,
        max_age_days=30,
        timeout=10,
        max_bytes=1_000_000,
        retries=0,
        user_agent="test-agent",
        mailto=None,
    )
    monkeypatch.setattr(refresh_source_review, "parse_args", lambda: args)

    with pytest.raises(UnsafeURLError):
        refresh_source_review.main()

    assert not write_called
    # The existing snapshot file must remain genuinely unchanged via unmocked filesystem read
    assert snapshot_path.read_text(encoding="utf-8") == initial_content



def test_pages_match_range_vs_single_page_is_possible_conflict() -> None:
    refresh = _refresh_module()
    # Range vs single page
    assert refresh.pages_match("345–363", "345") == "POSSIBLE_CONFLICT"
    assert refresh.pages_match("345", "345-363") == "POSSIBLE_CONFLICT"

    # Both express ranges: equivalent dashes and abbreviations
    assert refresh.pages_match("345–363", "345-363") == "MATCH"
    assert refresh.pages_match("345-363", "345-63") == "MATCH"
    assert refresh.pages_match("345–363", "345–63") == "MATCH"
    assert refresh.pages_match("345-363", "345-364") == "POSSIBLE_CONFLICT"

    # Both single pages
    assert refresh.pages_match("345", "345") == "MATCH"
    assert refresh.pages_match("345", "346") == "POSSIBLE_CONFLICT"


@pytest.mark.parametrize("old_version", [2, 3])
def test_load_cached_records_rejects_incompatible_schema(tmp_path: Path, old_version: int) -> None:
    from source_review.snapshot import load_cached_records
    cache_file = tmp_path / "cache.json"
    cache_file.write_text(
        json.dumps({
            "schema_version": old_version,
            "records": {
                "src-1": {
                    "lookup_status": "OK",
                    "checked_on": "2026-09-01T00:00:00Z",
                }
            }
        }),
        encoding="utf-8",
    )
    loaded = load_cached_records(cache_file)
    assert loaded == {}

    cache_file.write_text(
        json.dumps({
            "schema_version": _refresh_module().SCHEMA_VERSION,
            "records": {
                "src-1": {
                    "lookup_status": "OK",
                    "checked_on": "2026-09-01T00:00:00Z",
                }
            }
        }),
        encoding="utf-8",
    )
    loaded = load_cached_records(cache_file)
    assert "src-1" in loaded


def test_write_snapshot_is_atomic(tmp_path: Path) -> None:
    refresh = _refresh_module()
    target_file = tmp_path / "snapshot.json"
    snapshot = {"schema_version": 3, "records": {}}
    refresh.write_snapshot(snapshot, target_file)
    assert target_file.exists()
    assert json.loads(target_file.read_text(encoding="utf-8")) == snapshot
    assert not target_file.with_suffix(".tmp").exists()
    assert list(tmp_path.glob(".*.tmp")) == []


def test_write_snapshot_does_not_follow_predictable_symlink(tmp_path: Path) -> None:
    refresh = _refresh_module()
    target_file = tmp_path / "snapshot.json"
    victim = tmp_path / "victim.txt"
    victim.write_text("KEEP", encoding="utf-8")

    # Create the old predictable snapshot.tmp as a symlink pointing to victim.txt
    predictable_tmp = target_file.with_suffix(".tmp")
    predictable_tmp.symlink_to(victim)

    snapshot = {"schema_version": 3, "records": {"src-1": {"status": "OK"}}}
    refresh.write_snapshot(snapshot, target_file)

    # Assert victim.txt was not overwritten
    assert victim.read_text(encoding="utf-8") == "KEEP"
    # Assert destination file received the new snapshot
    assert json.loads(target_file.read_text(encoding="utf-8")) == snapshot
    # Assert the predictable symlink was neither used nor overwritten
    assert predictable_tmp.is_symlink()
    assert predictable_tmp.resolve() == victim.resolve()
    assert list(tmp_path.glob(".*.tmp")) == []


def test_write_snapshot_cleans_up_temporary_file_on_error(
    tmp_path: Path, monkeypatch
) -> None:
    refresh = _refresh_module()
    target_file = tmp_path / "snapshot.json"
    snapshot = {"schema_version": 3, "records": {}}

    def mock_replace(src, dst):
        raise OSError("simulated atomic replacement failure")

    monkeypatch.setattr("os.replace", mock_replace)
    with pytest.raises(OSError, match="simulated atomic replacement failure"):
        refresh.write_snapshot(snapshot, target_file)

    assert not target_file.exists()
    assert list(tmp_path.glob(".*.tmp")) == []



def test_refresh_cli_rejects_sources_with_reclassify() -> None:
    cmd = [
        sys.executable,
        str(ROOT / "scripts/refresh_source_review.py"),
        "--sources", "src-1",
        "--reclassify",
    ]
    res = subprocess.run(cmd, capture_output=True, text=True)
    assert res.returncode != 0
    assert "--sources and --reclassify cannot be used together" in res.stderr


def test_report_escapes_adversarial_external_metadata() -> None:
    from source_review.report import _safe_md_text, _safe_external_url, _rights_presentation

    adv_title = "[Link](https://example.com) ![img](https://example.com/image.png) <script>alert(1)</script> | pipe"
    rendered = _safe_md_text(adv_title)
    assert "\\[Link\\]" in rendered
    assert "!\\[img\\]" in rendered
    assert "&lt;script&gt;" in rendered
    assert "\\|" in rendered
    assert "[Link](" not in rendered
    assert "![img](" not in rendered
    assert "<script>" not in rendered

    cases = {
        "_italic_": ("\\_italic\\_", "_italic_"),
        "**bold**": ("\\*\\*bold\\*\\*", "**bold**"),
        "`code`": ("\\`code\\`", "`code`"),
        "~~strike~~": ("\\~\\~strike\\~\\~", "~~strike~~"),
        "<https://example.com>": ("&lt;https\\://example.com&gt;", "<https://example.com>"),
        "https://evil.example/path": ("https\\://evil.example/path", "https://evil.example/path"),
        "http://evil.example": ("http\\://evil.example", "http://evil.example"),
        "www.evil.example": ("www\\.evil.example", "www.evil.example"),
        "attacker@example.com": ("attacker\\@example.com", "attacker@example.com"),
    }
    for raw_input, (expected_escaped, active_syntax) in cases.items():
        escaped = _safe_md_text(raw_input)
        assert escaped == expected_escaped
        assert active_syntax not in escaped

    assert _safe_external_url("javascript:alert(1)") is None
    assert _safe_external_url("file:///etc/passwd") is None
    assert _safe_external_url("https://example.com/ok") == "https://example.com/ok"

    rights = {
        "outcome": "RIGHTS_RECORDED",
        "details": "Custom rights statement",
        "url": "javascript:alert(1)",
    }
    _, _, scope = _rights_presentation(rights)
    assert "<script>" not in scope
