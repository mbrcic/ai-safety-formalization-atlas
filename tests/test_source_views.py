"""Tests for generated source review dashboard views."""

from __future__ import annotations

import importlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
scripts = str(ROOT / "scripts")
if scripts not in sys.path:
    sys.path.insert(0, scripts)

import generate_registry_views as views  # noqa: E402


def _refresh_module():
    return importlib.import_module("source_review")


def _registry() -> dict:
    return json.loads((ROOT / "registry.yaml").read_text(encoding="utf-8"))


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


def test_rights_presentation_names_a_license_without_overclaiming_terms() -> None:
    from source_review import report as source_report

    cc_by = source_report._rights_presentation(
        {
            "details": "Crossref rights metadata (vor)",
            "url": "https://creativecommons.org/licenses/by/4.0/",
        }
    )
    tdm = source_report._rights_presentation(
        {
            "details": "Crossref rights metadata (tdm)",
            "url": "https://www.springer.com/tdm",
        }
    )
    version_of_record = source_report._rights_presentation(
        {
            "details": "Crossref rights metadata (vor)",
            "url": "https://www.acm.org/publications/policies/copyright_policy#Background",
        }
    )
    arxiv_distribution = source_report._rights_presentation(
        {
            "details": "Per-paper license link on the arXiv abstract page.",
            "url": "https://arxiv.org/licenses/nonexclusive-distrib/1.0/",
        }
    )
    assumed_arxiv_distribution = source_report._rights_presentation(
        {
            "details": "Per-paper license link on the arXiv abstract page.",
            "url": "https://arxiv.org/licenses/assumed-1991-2003/",
        }
    )

    assert cc_by[1] == "CC BY 4.0 license"
    assert "version of record" in cc_by[2]
    assert tdm[1] == "Text-and-data-mining terms"
    assert "not identified as a general reuse license" in tdm[2]
    assert version_of_record[1] == "ACM copyright policy"
    assert "version of record" in version_of_record[2]
    assert arxiv_distribution[1] == "arXiv non-exclusive distribution license"
    assert "not a general public reuse license" in arxiv_distribution[2]
    assert (
        assumed_arxiv_distribution[1]
        == "arXiv assumed distribution license (1991–2003)"
    )
    assert "not a general public reuse license" in assumed_arxiv_distribution[2]
    assert "%3C" in source_report._source_locator_link(
        {
            "locator": (
                "https://doi.org/10.1002/(SICI)1097-0312(199608)"
                "50:2<234::AID-CPA4>3.0.CO;2-8"
            )
        }
    )


def test_review_board_shows_machine_findings_not_a_manual_unreviewed_queue() -> None:
    refresh = _refresh_module()
    registry = _registry()
    snapshot = _complete_failed_snapshot()
    source_id, source = next(
        (source_id, source)
        for source_id, source in sorted(refresh.source_catalogue(registry).items())
        if refresh.extract_title(source["citation"])
    )
    external = refresh.crossref_external(_crossref_message("Different title"))
    comparisons = refresh.metadata_comparisons(
        source, external, True, source.get("locator", "")
    )
    rights = external["rights"]
    related_dois = [
        {
            "doi": "10.1000/example",
            "url": "https://doi.org/10.1000/example",
        }
    ]
    snapshot["records"][source_id] = {
        "input_fingerprint": refresh.input_fingerprint(source),
        "provider": "crossref",
        "lookup_status": "OK",
        "checked_url": "https://example.com/record",
        "checked_on": "2026-08-31T12:00:00Z",
        "metadata": comparisons,
        "rights": rights,
        "related_dois": related_dois,
        "status": refresh.classify("OK", comparisons, rights, related_dois),
        "notes": "",
    }
    report = views.render_source_review(registry, snapshot)

    assert f"**{len(refresh.source_catalogue(registry))}** works evaluated" in report
    assert "## Rights and license metadata" in report
    assert "### Rights, licenses, and terms identified" in report
    assert "| Source | Cited material | Rights / license result | What the record establishes | Lookup record |" in report
    assert "## Potential metadata differences" in report
    assert (
        "| Source | Cited material | Field | Atlas citation value | "
        "Retrieved-record value | Lookup record | Human disposition |"
    ) in report
    assert "| [open](<" in report
    assert f"| [`{source_id}`](source-catalog.md#{source_id}) |" in report
    assert "| `title` |" in report
    assert "## Possible published versions of cited preprints" in report
    assert "doi:10.1000/example" in report
    assert "https://api.crossref.org/v1/works/10.1000%2Fexample" in report
    assert "Publisher terms for the version of record" in report
    assert "Different title" in report
    assert "Not yet reviewed" not in report
    assert "Evidence says" not in report
    assert "Checked value" not in report
    assert "Crossref rights metadata" not in report


def test_review_board_supports_multiple_methods_for_findings() -> None:
    refresh = _refresh_module()
    registry = _registry()
    snapshot = _complete_failed_snapshot()
    arxiv_source_id = next(
        sid
        for sid, s in sorted(refresh.source_catalogue(registry).items())
        if s.get("locator", "").startswith("http://arxiv.org/abs/")
        or s.get("locator", "").startswith("https://arxiv.org/abs/")
    )
    source = registry["source_catalog"][arxiv_source_id]
    comparisons = refresh.metadata_comparisons(
        source,
        {
            "identifier": "arxiv:example",
            "title": "Example Title",
            "authors": ["Author One"],
            "date": "2020-01-01",
            "venue": "Example Journal",
            "volume_issue": "",
            "pages": "",
            "rights": {
                "outcome": "RIGHTS_RECORDED",
                "details": "Per-paper license link on the arXiv abstract page.",
                "url": "https://arxiv.org/licenses/nonexclusive-distrib/1.0/",
            },
        },
        True,
        source["locator"],
    )
    snapshot["records"][arxiv_source_id] = {
        "input_fingerprint": refresh.input_fingerprint(source),
        "provider": "arxiv",
        "lookup_status": "OK",
        "checked_url": "https://export.arxiv.org/api/query?id_list=example",
        "checked_on": "2026-08-31T12:00:00Z",
        "metadata": comparisons,
        "rights": {
            "outcome": "RIGHTS_RECORDED",
            "details": "Per-paper license link on the arXiv abstract page.",
            "url": "https://arxiv.org/licenses/nonexclusive-distrib/1.0/",
        },
        "related_dois": [
            {
                "doi": "10.1145/example",
                "relationship": "version-of-record",
                "source": "arxiv-api",
                "url": "https://doi.org/10.1145/example",
                "record_url": "https://api.crossref.org/v1/works/10.1145%2Fexample",
            }
        ],
        "status": "NEEDS_HUMAN",
        "notes": (
            "Metadata came from the arXiv API; "
            "arXiv reported an associated DOI for a published version; "
            "the abstract page was retrieved for rights metadata."
        ),
    }
    snapshot["records"]["survey-ref-078"] = refresh.failed_record(
        registry["source_catalog"]["survey-ref-078"],
        "html",
        "HTTP_ERROR",
        "https://doi.org/10.13140/RG.2.2.13245.28641",
        "Crossref returned HTTP 404; checked the source locator instead. HTTP 403",
    )
    report = views.render_source_review(registry, snapshot)
    assert (
        "[arXiv API](https://export.arxiv.org/api/query?id_list=example) · "
        "[Crossref](https://api.crossref.org/v1/works/10.1145%2Fexample)"
    ) in report
    assert (
        "[arXiv API](https://export.arxiv.org/api/query?id_list=example) · "
        "[Abstract page](<"
    ) in report
    assert "[Crossref](https://api.crossref.org/v1/works/10.13140" in report
    assert "[Source page](<https://doi.org/10.13140/RG.2.2.13245.28641>)" in report


def test_source_catalog_renders_cited_in_atlas_links() -> None:
    _refresh_module()

    registry = {
        "results": [
            {
                "id": "ST-1",
                "name": "Statement 1",
                "original_source_refs": ["src-a", "src-b"],
            },
        ],
        "source_catalog": {
            "src-a": {"citation": "Source A citation", "role": "work", "locator": "https://doi.org/10.1/a"},
            "src-b": {"citation": "Source B citation", "role": "work", "locator": "https://doi.org/10.1/b"},
        },
    }
    review = {
        "records": {
            "src-a": {"status": "NO_AUTOMATED_FOLLOWUP"},
            "src-b": {"status": "NO_AUTOMATED_FOLLOWUP"},
        }
    }
    catalog = views.render_source_catalog(registry, review, {"conjectures": []})
    assert "- **Cited in Atlas:** [`ST-1`](../formalization-status.md) (*Statement 1*)" in catalog


def test_source_catalog_escapes_legacy_doi_locators_and_uses_observational_wording() -> None:
    refresh = _refresh_module()

    legacy_doi = "https://doi.org/10.1002/(SICI)1234-981X(199707)5:3<305::AID-EURO184>3.0.CO;2-4"
    registry = {
        "results": [],
        "source_catalog": {
            "src-legacy": {
                "citation": "Author, “Paper,” 1997.",
                "role": "work",
                "locator": legacy_doi,
            },
        },
    }
    review = {
        "records": {
            "src-legacy": {
                "status": "NO_AUTOMATED_FOLLOWUP",
            },
        },
    }
    catalog = views.render_source_catalog(registry, review, {"conjectures": []})
    # Must use percent-encoding for < and > in the link URL
    assert "%3C305::AID-EURO184%3E" in catalog
    assert "<https://doi.org/10.1002/" in catalog
    assert "(https://doi.org/10.1002/(SICI)1234-981X(199707)5:3<" not in catalog

    # Observational wording in review_signal_links
    clear_signals = refresh.catalog.review_signal_links("src-1", {"status": "NO_AUTOMATED_FOLLOWUP"})
    assert clear_signals == ["[No automated follow-up flagged](source-review.md#clear-src-1)"]

    missing_cat_signals = refresh.catalog.review_signal_links(
        "src-2",
        {
            "status": "NEEDS_HUMAN",
            "metadata": [{"field": "title", "outcome": "MISSING_IN_CATALOGUE"}],
        },
    )
    assert missing_cat_signals == ["[title not extracted from Atlas citation](source-review.md#missing-cat-src-2-title)"]

    missing_src_signals = refresh.catalog.review_signal_links(
        "src-3",
        {
            "status": "NEEDS_HUMAN",
            "metadata": [{"field": "venue", "outcome": "MISSING_IN_SOURCE"}],
        },
    )
    assert missing_src_signals == ["[Retrieved record did not expose venue](source-review.md#missing-src-src-3-venue)"]



if __name__ == "__main__":
    for name, func in list(globals().items()):
        if name.startswith("test_") and callable(func):
            func()
            print(f"ok {name}")
