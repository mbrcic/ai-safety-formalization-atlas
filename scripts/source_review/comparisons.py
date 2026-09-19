"""Bibliographic comparison, field matching rules, and record classification."""

from __future__ import annotations

import re
from typing import Any

from .schema import (
    MATCH,
    METADATA_FIELDS,
    MISSING_IN_CATALOGUE,
    MISSING_IN_SOURCE,
    NO_AUTOMATED_FOLLOWUP,
    NOT_APPLICABLE,
    POSSIBLE_CONFLICT,
    REVIEW_OUTCOMES,
    RIGHTS_RECORDED,
    YEAR_RE,
    arxiv_base_id,
    catalogue_fields,
    clean_doi,
    display,
    extract_arxiv_id,
    extract_doi,
    normalize,
)


def text_match(catalogue_value: str, source_value: str) -> str:
    if not catalogue_value and not source_value:
        return NOT_APPLICABLE
    if not catalogue_value:
        return "MISSING_IN_CATALOGUE"
    if not source_value:
        return "MISSING_IN_SOURCE"
    catalogue_normal = normalize(catalogue_value)
    source_normal = normalize(source_value)
    if catalogue_normal == source_normal:
        return MATCH
    return "POSSIBLE_CONFLICT"


def identifier_match(catalogue_value: str, source_value: str) -> str:
    if not catalogue_value and not source_value:
        return NOT_APPLICABLE
    if not catalogue_value:
        return "MISSING_IN_CATALOGUE"
    if not source_value:
        return "MISSING_IN_SOURCE"

    cat_val = catalogue_value.strip()
    src_val = source_value.strip()

    # Canonical DOI comparison
    cat_doi = extract_doi(cat_val) or (clean_doi(cat_val[4:]) if cat_val.lower().startswith("doi:") else None)
    src_doi = extract_doi(src_val) or (clean_doi(src_val[4:]) if src_val.lower().startswith("doi:") else None)
    if cat_doi and src_doi:
        return MATCH if cat_doi == src_doi else "POSSIBLE_CONFLICT"

    # Canonical arXiv comparison
    cat_arx = extract_arxiv_id(cat_val) or (cat_val[6:].strip() if cat_val.lower().startswith("arxiv:") else None)
    src_arx = extract_arxiv_id(src_val) or (src_val[6:].strip() if src_val.lower().startswith("arxiv:") else None)
    if cat_arx and src_arx:
        cat_base = arxiv_base_id(cat_arx).lower()
        src_base = arxiv_base_id(src_arx).lower()
        return MATCH if cat_base == src_base else "POSSIBLE_CONFLICT"

    # Exact normalized equality fallback (no generic substring matching)
    return MATCH if normalize(cat_val) == normalize(src_val) else "POSSIBLE_CONFLICT"


def author_match(catalogue_value: str, authors: list[str]) -> str:
    if not catalogue_value and not authors:
        return NOT_APPLICABLE
    if not catalogue_value:
        return "MISSING_IN_CATALOGUE"
    if not authors:
        return "MISSING_IN_SOURCE"

    def name_parts(name: str) -> tuple[str, list[str]]:
        # Retrieved names may be "Family, Given"; catalogue names are
        # "Given Family". Ambiguous compound names remain review questions.
        if "," in name:
            family, given = name.split(",", 1)
            return normalize(family), normalize(given).split()
        tokens = normalize(name).split()
        return (tokens[-1], tokens[:-1]) if tokens else ("", [])

    def same_person(cited: str, retrieved: str) -> bool:
        family, given = name_parts(cited)
        other_family, other_given = name_parts(retrieved)
        if not family or family != other_family:
            return False
        if not given:
            return True  # An explicitly surname-only citation.
        if len(given) != len(other_given):
            return False
        return all(
            left == right or (min(len(left), len(right)) == 1 and left[0] == right[0])
            for left, right in zip(given, other_given)
        )

    et_al = re.search(r"\bet\s+al\b", catalogue_value, flags=re.IGNORECASE)
    leading = catalogue_value[:et_al.start()] if et_al else catalogue_value
    cited_authors = [
        part.strip(" ,;")
        for part in re.split(r",|;|\band\b|&", leading)
        if part.strip(" ,;")
    ]
    if not cited_authors or len(cited_authors) > len(authors):
        return POSSIBLE_CONFLICT
    if not et_al and len(cited_authors) != len(authors):
        return POSSIBLE_CONFLICT
    # Compare authors in order, without letting one shared first name or a
    # repeated surname stand in for several different people.
    return MATCH if all(
        same_person(cited, retrieved)
        for cited, retrieved in zip(cited_authors, authors)
    ) else POSSIBLE_CONFLICT


def date_match(catalogue_value: str, source_value: str, citation: str | None = None) -> str:
    if not catalogue_value and not source_value:
        return NOT_APPLICABLE
    if not catalogue_value:
        return "MISSING_IN_CATALOGUE"
    if not source_value:
        return "MISSING_IN_SOURCE"
    catalogue_years = YEAR_RE.findall(catalogue_value)
    source_years = YEAR_RE.findall(source_value)
    if catalogue_years and source_years:
        return MATCH if catalogue_years[0] == source_years[0] else "POSSIBLE_CONFLICT"
    return MATCH if normalize(catalogue_value) == normalize(source_value) else "POSSIBLE_CONFLICT"


def volume_issue_match(catalogue_value: str, source_value: str) -> str:
    if not catalogue_value and not source_value:
        return NOT_APPLICABLE
    if not catalogue_value:
        return "MISSING_IN_CATALOGUE"
    if not source_value:
        return "MISSING_IN_SOURCE"

    def canonical(value: str) -> str:
        # Normalize labels, not values: a matching volume cannot establish
        # agreement about an absent issue or a discarded supplement suffix.
        value = re.sub(r"\b(?:volume|vol)\b\.?", "vol", value, flags=re.IGNORECASE)
        value = re.sub(r"\b(?:number|issue|no)\b\.?", "no", value, flags=re.IGNORECASE)
        return normalize(value)

    return MATCH if canonical(catalogue_value) == canonical(source_value) else POSSIBLE_CONFLICT


def pages_match(catalogue_value: str, source_value: str) -> str:
    if not catalogue_value and not source_value:
        return NOT_APPLICABLE
    if not catalogue_value:
        return "MISSING_IN_CATALOGUE"
    if not source_value:
        return "MISSING_IN_SOURCE"

    def canonical(value: str) -> str:
        value = re.sub(r"\s*[-–—]\s*", "-", value.strip()).casefold()
        # Only expand a shortened end in a simple numeric range. Keep page
        # prefixes, additional ranges, and article identifiers intact.
        match = re.fullmatch(r"([0-9]+)-([0-9]+)", value)
        if match:
            start, end = match.groups()
            if len(end) < len(start):
                expanded = start[:-len(end)] + end
                if int(expanded) >= int(start):
                    return f"{start}-{expanded}"
        return value

    return MATCH if canonical(catalogue_value) == canonical(source_value) else POSSIBLE_CONFLICT


def venue_match(catalogue_value: str, source_value: str) -> str:
    # Shared words or plausible abbreviations are not proof of journal identity.
    return text_match(catalogue_value, source_value)


def metadata_comparisons(
    source: dict[str, Any], external: dict[str, Any], lookup_ok: bool, final_url: str
) -> list[dict[str, str]]:
    catalogue = catalogue_fields(source)
    external_authors = external.get("authors", [])
    source_values = {
        "identifier": display(external.get("identifier")),
        "title": display(external.get("title")),
        "authors": "; ".join(external_authors) if external_authors else "—",
        "date": display(external.get("date")),
        "venue": display(external.get("venue")),
        "volume_issue": display(external.get("volume_issue")),
        "pages": display(external.get("pages")),
        "locator": display(final_url),
    }
    outcomes = {
        "identifier": identifier_match(
            catalogue["identifier"], external.get("identifier", "")
        ),
        "title": text_match(catalogue["title"], external.get("title", "")),
        "authors": author_match(catalogue["authors"], external_authors),
        "date": date_match(
            catalogue["date"], external.get("date", ""), source.get("citation")
        ),
        "venue": venue_match(catalogue["venue"], external.get("venue", "")),
        "volume_issue": volume_issue_match(
            catalogue["volume_issue"], external.get("volume_issue", "")
        ),
        "pages": pages_match(catalogue["pages"], external.get("pages", "")),
        "locator": MATCH if lookup_ok and catalogue["locator"] else "MISSING_IN_CATALOGUE",
    }
    return [
        {
            "field": field,
            "catalogue_value": display(catalogue[field]),
            "source_value": source_values[field],
            "outcome": outcomes[field],
        }
        for field in METADATA_FIELDS
    ]


def unavailable_comparisons(source: dict[str, Any], outcome: str) -> list[dict[str, str]]:
    catalogue = catalogue_fields(source)
    return [
        {
            "field": field,
            "catalogue_value": display(catalogue[field]),
            "source_value": "—",
            "outcome": outcome if catalogue[field] else NOT_APPLICABLE,
        }
        for field in METADATA_FIELDS
    ]


def classify(
    lookup_status: str,
    comparisons: list[dict[str, str]],
    rights: dict[str, str],
    related_dois: list[dict[str, str]] | None = None,
) -> str:
    if lookup_status in {"HTTP_ERROR", "PARSE_ERROR"}:
        return "LOOKUP_FAILED"
    if any(comparison["outcome"] in REVIEW_OUTCOMES for comparison in comparisons):
        return "NEEDS_HUMAN"
    if rights["outcome"] != RIGHTS_RECORDED:
        return "NEEDS_HUMAN"
    if related_dois:
        return "NEEDS_HUMAN"
    return NO_AUTOMATED_FOLLOWUP
