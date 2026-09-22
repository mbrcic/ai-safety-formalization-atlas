"""Public facade for the source-review scripts and their focused regression tests."""

from .catalog import render_source_catalog
from .lookups import (
    HostRateLimiter,
    crossref_url,
    evaluate_source,
    failed_record,
    fetch,
    successful_record,
)
from .metadata import (
    arxiv_api_url,
    arxiv_metadata,
    arxiv_rights,
    crossref_external,
    html_external,
)
from .findings import (
    actionable_findings,
    compute_finding_fingerprint,
)
from .report import render_source_review
from .comparisons import (
    author_match,
    classify,
    date_match,
    identifier_match,
    metadata_comparisons,
    pages_match,
    venue_match,
    volume_issue_match,
)
from .schema import (
    NO_AUTOMATED_FOLLOWUP,
    SCHEMA_VERSION,
    catalogue_fields,
    catalogue_fingerprint,
    citation_pages,
    extract_doi,
    extract_title,
    input_fingerprint,
    source_catalogue,
)
from .snapshot import (
    build_snapshot,
    cached_record_is_compatible,
    reclassify_record,
    write_snapshot,
)

__all__ = [
    "HostRateLimiter",
    "NO_AUTOMATED_FOLLOWUP",
    "SCHEMA_VERSION",
    "actionable_findings",
    "arxiv_api_url",
    "arxiv_metadata",
    "arxiv_rights",
    "author_match",
    "build_snapshot",
    "cached_record_is_compatible",
    "catalogue_fields",
    "catalogue_fingerprint",
    "citation_pages",
    "classify",
    "compute_finding_fingerprint",
    "crossref_external",
    "crossref_url",
    "date_match",
    "evaluate_source",
    "extract_doi",
    "extract_title",
    "failed_record",
    "fetch",
    "html_external",
    "identifier_match",
    "input_fingerprint",
    "metadata_comparisons",
    "pages_match",
    "reclassify_record",
    "render_source_catalog",
    "render_source_review",
    "source_catalogue",
    "successful_record",
    "venue_match",
    "volume_issue_match",
    "write_snapshot",
]
