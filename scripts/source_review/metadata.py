"""Small parsers for Crossref, public HTML pages, and arXiv Atom records."""

from __future__ import annotations

from html.parser import HTMLParser
import re
from typing import Any
from urllib.parse import quote, urlencode, urljoin, urlparse
from xml.etree import ElementTree

from .schema import (
    NO_EXPLICIT_RIGHTS,
    RIGHTS_RECORDED,
    arxiv_base_id,
    clean_doi,
    display,
    extract_arxiv_id,
    extract_doi,
    strip_html,
)


def date_from_parts(value: object) -> str:
    if not isinstance(value, dict):
        return ""
    parts = value.get("date-parts")
    if not isinstance(parts, list) or not parts or not isinstance(parts[0], list):
        return ""
    numbers = [str(part) for part in parts[0][:3] if isinstance(part, int)]
    return "-".join(numbers)


def first_text(value: object) -> str:
    if isinstance(value, list):
        return strip_html(value[0]) if value else ""
    return strip_html(value)


def crossref_external(message: dict[str, Any]) -> dict[str, Any]:
    authors = []
    for author in message.get("author", []):
        if not isinstance(author, dict):
            continue
        name = " ".join(
            value
            for value in (author.get("given", ""), author.get("family", ""))
            if isinstance(value, str) and value.strip()
        )
        if not name and isinstance(author.get("name"), str):
            name = author["name"]
        if name:
            authors.append(name)
    date = ""
    for key in ("published-print", "published-online", "issued", "created"):
        date = date_from_parts(message.get(key))
        if date:
            break
    valid_licenses = [
        license_
        for license_ in message.get("license", [])
        if isinstance(license_, dict)
        and isinstance(license_.get("URL"), str)
        and license_["URL"].strip()
    ]

    def _lic_pref(lic: dict[str, Any]) -> int:
        ver = str(lic.get("content-version", "")).strip().lower()
        if ver == "vor":
            return 0
        if ver == "am":
            return 1
        if not ver or ver == "unspecified":
            return 2
        if ver == "tdm":
            return 4
        return 3

    if valid_licenses:
        chosen = min(valid_licenses, key=lambda l: (_lic_pref(l), str(l.get("URL"))))
        ver = str(chosen.get("content-version", "")).strip().lower()
        details = (
            f"Crossref rights metadata ({ver})"
            if ver
            else "Crossref rights metadata (unspecified version)"
        )
        rights = {
            "outcome": RIGHTS_RECORDED,
            "details": details,
            "url": chosen["URL"].strip(),
            "entries": [
                {
                    "url": license_["URL"].strip(),
                    "content_version": str(license_.get("content-version", "")).strip(),
                    "start": (
                        str(license_["start"].get("date-time", "")).strip()
                        if isinstance(license_.get("start"), dict) else ""
                    ),
                }
                for license_ in valid_licenses
            ],
        }
    else:
        rights = {
            "outcome": NO_EXPLICIT_RIGHTS,
            "details": "Crossref returned no explicit license or rights metadata.",
            "url": "",
        }
    doi = message.get("DOI") if isinstance(message.get("DOI"), str) else ""
    return {
        "identifier": f"doi:{clean_doi(doi)}" if doi else "",
        "title": first_text(message.get("title")),
        "authors": authors,
        "date": date,
        "venue": first_text(message.get("container-title")),
        "volume_issue": ", ".join(
            f"{label} {message[key]}"
            for key, label in (("volume", "vol."), ("issue", "no."))
            if isinstance(message.get(key), str) and message[key].strip()
        ),
        "pages": display(message.get("page")) if message.get("page") else "",
        "rights": rights,
    }


class MetadataHTMLParser(HTMLParser):
    """A deliberately narrow extractor for widely used citation and rights tags."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.meta: dict[str, list[str]] = {}
        self.licenses: list[str] = []
        self.license_anchors: list[tuple[str, str]] = []
        self.title_parts: list[str] = []
        self.headings: list[str] = []
        self.article_headings: list[str] = []
        self._in_title = False
        self._in_article = False
        self._in_h1 = False
        self._h1_parts: list[str] = []
        self._anchor_href: str | None = None
        self._anchor_parts: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = {key.casefold(): value or "" for key, value in attrs}
        tag_cf = tag.casefold()
        if tag_cf == "meta":
            key = (values.get("name") or values.get("property") or "").casefold()
            content = values.get("content", "").strip()
            if key and content:
                self.meta.setdefault(key, []).append(content)
        elif tag_cf == "link":
            rel = values.get("rel", "").casefold().split()
            href = values.get("href", "").strip()
            if "license" in rel and href:
                self.licenses.append(href)
        elif tag_cf == "a":
            href = values.get("href", "").strip()
            if href:
                self._anchor_href = href
                self._anchor_parts = []
        elif tag_cf == "title":
            self._in_title = True
        elif tag_cf == "article":
            self._in_article = True
        elif tag_cf == "h1":
            self._in_h1 = True
            self._h1_parts = []

    def handle_endtag(self, tag: str) -> None:
        tag_cf = tag.casefold()
        if tag_cf == "a" and self._anchor_href:
            label = " ".join(part.strip() for part in self._anchor_parts if part.strip())
            if "license" in label.casefold() or "/licenses/" in self._anchor_href.casefold():
                self.license_anchors.append((label, self._anchor_href))
            self._anchor_href = None
            self._anchor_parts = []
        elif tag_cf == "title":
            self._in_title = False
        elif tag_cf == "article":
            self._in_article = False
        elif tag_cf == "h1":
            heading = " ".join("".join(self._h1_parts).split())
            if heading:
                self.headings.append(heading)
                if self._in_article:
                    self.article_headings.append(heading)
            self._in_h1 = False

    def handle_data(self, data: str) -> None:
        if self._in_title:
            self.title_parts.append(data)
        if self._anchor_href:
            self._anchor_parts.append(data)
        if self._in_h1:
            self._h1_parts.append(data)

    def first(self, *keys: str) -> str:
        for key in keys:
            values = self.meta.get(key.casefold(), [])
            if values:
                return strip_html(values[0])
        return ""

    def all(self, *keys: str) -> list[str]:
        values: list[str] = []
        for key in keys:
            values.extend(
                strip_html(value) for value in self.meta.get(key.casefold(), [])
            )
        return list(dict.fromkeys(value for value in values if value))


def parse_source_html(body: bytes) -> MetadataHTMLParser:
    parser = MetadataHTMLParser()
    parser.feed(body.decode("utf-8", errors="replace"))
    parser.close()
    return parser


def html_rights(parser: MetadataHTMLParser, final_url: str) -> dict[str, str]:
    """Extract an explicit rights signal, including a visible license link."""
    rights_text = parser.first(
        "citation_license", "dc.rights", "dcterms.rights", "rights", "license"
    )
    link_label = ""
    raw_url = ""
    if parser.licenses:
        raw_url = parser.licenses[0]
    elif parser.license_anchors:
        link_label, raw_url = parser.license_anchors[0]
    rights_url = urljoin(final_url, raw_url) if raw_url else ""
    if rights_text or rights_url:
        details = rights_text
        if not details and link_label:
            details = f"Explicit license link on source page ({link_label})."
        if not details:
            details = "Explicit license link in source HTML."
        return {
            "outcome": RIGHTS_RECORDED,
            "details": details,
            "url": rights_url or final_url,
        }
    return {
        "outcome": NO_EXPLICIT_RIGHTS,
        "details": "No explicit rights or license metadata was found in the source HTML.",
        "url": final_url,
    }


def clean_page_title(title: str, url: str) -> str:
    """Strip repository host chrome such as issue numbering or site suffixes."""
    host = urlparse(url).netloc.casefold()
    if "github.com" in host:
        title = re.sub(r"\s+·\s+Issue\s+#\d+\s+·.*$", "", title, flags=re.IGNORECASE)
        title = re.sub(r"\s+·\s+GitHub$", "", title, flags=re.IGNORECASE)
    if "archive.org" in host:
        title = re.sub(r"^Internet Archive:\s*", "", title, flags=re.IGNORECASE)
        title = re.sub(r"^Wayback Machine\s*[:-]\s*", "", title, flags=re.IGNORECASE)
        title = re.sub(r"^Wayback Machine$", "", title, flags=re.IGNORECASE)
        title = re.sub(r"\s*[-|·]\s*Wayback Machine$", "", title, flags=re.IGNORECASE)
    return title.strip()


def html_external(body: bytes, final_url: str) -> dict[str, Any]:
    parser = parse_source_html(body)
    has_structured_title = False
    title = parser.first("citation_title", "dc.title", "dcterms.title")
    if title:
        has_structured_title = True
    elif parser.article_headings:
        title = parser.article_headings[0]
        has_structured_title = True
    elif parser.first("og:title"):
        title = parser.first("og:title")
    elif parser.headings:
        title = parser.headings[0]
    else:
        title = " ".join(part.strip() for part in parser.title_parts if part.strip())
    title = clean_page_title(title, final_url)

    # Recognizable GitHub blob chrome is not bibliographic title metadata
    parsed_url = urlparse(final_url)
    if (
        not has_structured_title
        and "github.com" in parsed_url.netloc.casefold()
        and "/blob/" in parsed_url.path
    ):
        if (
            re.search(r"\bat\s+[0-9a-fA-F]{7,40}\s+·\s+[^·]+$", title)
            or re.search(r"\bat\s+[a-zA-Z0-9_.-]+\s+·\s+[^·]+$", title)
        ):
            title = ""
    raw_doi = parser.first("citation_doi", "dc.identifier.doi")
    doi = extract_doi(raw_doi) or clean_doi(raw_doi)
    arxiv_id = extract_arxiv_id(final_url)
    identifier = f"doi:{clean_doi(doi)}" if doi else f"arxiv:{arxiv_id}" if arxiv_id else ""
    first_page = parser.first("citation_firstpage")
    last_page = parser.first("citation_lastpage")
    pages = "–".join(value for value in (first_page, last_page) if value)
    return {
        "identifier": identifier,
        "title": title,
        "authors": parser.all("citation_author", "dc.creator", "dcterms.creator", "author"),
        "date": parser.first(
            "citation_publication_date",
            "citation_date",
            "dc.date",
            "dcterms.issued",
            "article:published_time",
        ),
        "venue": parser.first("citation_journal_title", "citation_conference_title", "dc.source"),
        "volume_issue": ", ".join(
            f"{label} {value}"
            for label, value in (
                ("vol.", parser.first("citation_volume")),
                ("no.", parser.first("citation_issue")),
            )
            if value
        ),
        "pages": pages,
        "rights": html_rights(parser, final_url),
    }


ATOM_NAMESPACE = "{http://www.w3.org/2005/Atom}"
ARXIV_NAMESPACE = "{http://arxiv.org/schemas/atom}"


def arxiv_api_url(arxiv_id: str) -> str:
    return "https://export.arxiv.org/api/query?" + urlencode({"id_list": arxiv_id})


def xml_text(element: ElementTree.Element, path: str) -> str:
    value = element.findtext(path)
    return " ".join(strip_html(value).split()) if isinstance(value, str) else ""


def arxiv_metadata(body: bytes, requested_id: str) -> tuple[dict[str, Any], str]:
    """Parse arXiv Atom metadata while keeping the cited preprint as primary."""
    root = ElementTree.fromstring(body)
    entry = root.find(f"{ATOM_NAMESPACE}entry")
    if entry is None:
        raise ValueError("arXiv API response contains no entry")
    returned_id = extract_arxiv_id(xml_text(entry, f"{ATOM_NAMESPACE}id"))
    if not returned_id or not re.fullmatch(
        r"(?:[0-9]{4}\.[0-9]{4,5}|[a-zA-Z][a-zA-Z.-]*/[0-9]{7})(?:v[0-9]+)?",
        returned_id,
    ):
        raise ValueError("arXiv API response contains no valid preprint identifier")
    if arxiv_base_id(returned_id) != arxiv_base_id(requested_id):
        raise ValueError("arXiv API response identifies a different preprint")
    if re.search(r"v\d+$", requested_id, re.IGNORECASE) and returned_id != requested_id:
        raise ValueError("arXiv API response identifies a different preprint version")
    authors = [
        name
        for author in entry.findall(f"{ATOM_NAMESPACE}author")
        if (name := xml_text(author, f"{ATOM_NAMESPACE}name"))
    ]
    journal_ref = xml_text(entry, f"{ARXIV_NAMESPACE}journal_ref")
    associated_doi = clean_doi(xml_text(entry, f"{ARXIV_NAMESPACE}doi"))
    related_dois = []
    if associated_doi:
        related_dois.append(
            {
                "doi": associated_doi,
                "url": "https://doi.org/" + quote(associated_doi, safe="/"),
            }
        )
    published = xml_text(entry, f"{ATOM_NAMESPACE}published")
    updated = xml_text(entry, f"{ATOM_NAMESPACE}updated")
    is_versioned = bool(re.search(r"v\d+$", requested_id, re.IGNORECASE))
    date = (updated or published) if is_versioned else (published or updated)
    return (
        {
            "identifier": f"arxiv:{requested_id}",
            "title": xml_text(entry, f"{ATOM_NAMESPACE}title"),
            "authors": authors,
            "date": date,
            "published": published,
            "updated": updated,
            "venue": journal_ref,
            "volume_issue": "",
            "pages": "",
            "related_dois": related_dois,
        },
        "",
    )


def arxiv_rights(abstract_body: bytes, abstract_url: str) -> dict[str, str]:
    """Read arXiv's visible, per-paper ``view license`` link when it exists."""
    parser = parse_source_html(abstract_body)
    if parser.license_anchors:
        _, raw_url = parser.license_anchors[0]
        return {
            "outcome": RIGHTS_RECORDED,
            "details": "Per-paper license link on the arXiv abstract page.",
            "url": urljoin(abstract_url, raw_url),
        }
    return {
        "outcome": NO_EXPLICIT_RIGHTS,
        "details": "The arXiv abstract page did not expose a per-paper license link.",
        "url": abstract_url,
    }
