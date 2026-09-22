"""Source-catalogue fields, citation parsing, and shared audit constants."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
from html import unescape
import json
import re
from typing import Any
import unicodedata


# Schema version acts as the cache and extraction compatibility boundary.
# Increment this version whenever provider extraction semantics change in a
# way that makes stored extracted evidence stale, invalidating the cache.
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
MATCH = "MATCH"
POSSIBLE_CONFLICT = "POSSIBLE_CONFLICT"
MISSING_IN_CATALOGUE = "MISSING_IN_CATALOGUE"
MISSING_IN_SOURCE = "MISSING_IN_SOURCE"
NOT_APPLICABLE = "NOT_APPLICABLE"
UNAVAILABLE = "UNAVAILABLE"
REVIEW_OUTCOMES = {
    POSSIBLE_CONFLICT,
    MISSING_IN_CATALOGUE,
    MISSING_IN_SOURCE,
    UNAVAILABLE,
}
RIGHTS_RECORDED = "RIGHTS_RECORDED"
NO_EXPLICIT_RIGHTS = "NO_EXPLICIT_RIGHTS"
RIGHTS_UNAVAILABLE = "RIGHTS_UNAVAILABLE"
NO_AUTOMATED_FOLLOWUP = "NO_AUTOMATED_FOLLOWUP"
AUTOMATED_CLEAR = NO_AUTOMATED_FOLLOWUP

DOI_RE = re.compile(
    r"(?:https?://(?:dx\.)?doi\.org/|doi:\s*)(10\.\d{4,9}/[-._;()/:<>a-z0-9]+)",
    re.IGNORECASE,
)
ARXIV_RE = re.compile(r"arxiv\.org/(?:abs|pdf)/([^?#]+)", re.IGNORECASE)
SMART_TITLE_RE = re.compile(r"“([^”]+)”")
PLAIN_TITLE_RE = re.compile(r'"([^\"]+)"')
YEAR_RE = re.compile(r"\b(?:1[6-9]\d{2}|20\d{2})\b")
VOLUME_RE = re.compile(r"\bvol\.\s*([^,.;]+)", re.IGNORECASE)
ISSUE_RE = re.compile(r"\bno\.\s*([^,.;]+)", re.IGNORECASE)
PAGES_RE = re.compile(r"\bpp?\.\s*([^,.;]+)", re.IGNORECASE)
VENUE_STOP_WORDS = {"a", "an", "and", "for", "in", "of", "on", "the", "to"}


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace(
        "+00:00", "Z"
    )


def display(value: object) -> str:
    if value is None:
        return "—"
    value = str(value).strip()
    return value or "—"


def normalize(value: object) -> str:
    value = unicodedata.normalize("NFKD", display(value)).casefold()
    value = "".join(
        character for character in value if not unicodedata.combining(character)
    )
    return re.sub(r"[^a-z0-9]+", " ", value).strip()


def strip_html(value: object) -> str:
    return re.sub(r"<[^>]+>", "", unescape(display(value))).strip()


def source_catalogue(registry: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        source_id: source
        for source_id, source in registry["source_catalog"].items()
        if source.get("role") == "work"
    }


def stable_fingerprint(value: object) -> str:
    encoded = json.dumps(value, ensure_ascii=False, sort_keys=True).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def catalogue_fingerprint(sources: dict[str, dict[str, Any]]) -> str:
    return stable_fingerprint(sources)


def input_fingerprint(source: dict[str, Any]) -> str:
    return stable_fingerprint(
        {"citation": source["citation"], "locator": source.get("locator")}
    )


def clean_doi(value: str) -> str:
    return value.strip().rstrip(".,;").lower()


def extract_doi(value: str) -> str | None:
    match = DOI_RE.search(value)
    return clean_doi(match.group(1)) if match else None


def extract_arxiv_id(value: str) -> str | None:
    match = ARXIV_RE.search(value)
    if not match:
        return None
    return match.group(1).removesuffix(".pdf").rstrip("/")


def arxiv_base_id(arxiv_id: str) -> str:
    """Ignore a revision only when matching the identifier returned by arXiv."""
    return re.sub(r"v\d+$", "", arxiv_id, flags=re.IGNORECASE)


def source_arxiv_id(source: dict[str, Any]) -> str | None:
    """Return an arXiv ID only when arXiv is the source being checked."""
    return extract_arxiv_id(source.get("locator", ""))


def extract_title(citation: str) -> str:
    match = SMART_TITLE_RE.search(citation) or PLAIN_TITLE_RE.search(citation)
    return match.group(1).strip() if match else ""


def citation_prefix(citation: str, title: str) -> str:
    if not title:
        return ""
    marker = f"“{title}”" if f"“{title}”" in citation else f'"{title}"'
    return citation.split(marker, 1)[0].strip(" ,")


def citation_venue(citation: str, title: str) -> str:
    if not title:
        return ""
    marker = f"“{title}”" if f"“{title}”" in citation else f'"{title}"'
    tail = citation.split(marker, 1)[-1].lstrip(" ,")
    if not tail:
        return ""
    return tail.split(", vol.", 1)[0].split(", no.", 1)[0].strip(" ,.")


def citation_volume_issue(citation: str) -> str:
    volume = VOLUME_RE.search(citation)
    issue = ISSUE_RE.search(citation)
    values = []
    if volume:
        values.append(f"vol. {volume.group(1).strip()}")
    if issue:
        values.append(f"no. {issue.group(1).strip()}")
    return ", ".join(values)


def citation_pages(citation: str) -> str:
    match = PAGES_RE.search(citation)
    if not match:
        return ""
    pages = match.group(1).strip()
    # An author initial such as "P. Pajunen" is not a page range. Every
    # catalogue page notation used here contains a number.
    return pages if any(character.isdigit() for character in pages) else ""


def catalogue_fields(source: dict[str, Any]) -> dict[str, str]:
    citation = source["citation"]
    locator = source.get("locator", "")
    locator_arxiv_id = extract_arxiv_id(locator)
    title = extract_title(citation)
    doi = extract_doi(locator) or extract_doi(citation)
    arxiv_id = locator_arxiv_id or extract_arxiv_id(citation)
    if locator_arxiv_id or (arxiv_id and not doi):
        identifier = f"arxiv:{arxiv_id}"
    else:
        identifier = f"doi:{doi}" if doi else ""
    years = YEAR_RE.findall(citation)
    venue = citation_venue(citation, title)
    # An arXiv identifier is already compared as the record identifier. The
    # abstract page does not separately expose it as a venue.
    if arxiv_id and normalize(venue).startswith("arxiv"):
        venue = ""
    return {
        "identifier": identifier,
        "title": title,
        "authors": citation_prefix(citation, title),
        "date": years[0] if years else "",
        "venue": venue,
        "volume_issue": citation_volume_issue(citation),
        "pages": citation_pages(citation),
        "locator": locator,
    }
